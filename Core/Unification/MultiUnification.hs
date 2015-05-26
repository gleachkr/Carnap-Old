{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes #-}

module Carnap.Core.Unification.MultiUnification (
  UniformlyEquaitable, eq, neq,
  Paring(UnifiablePairing),
  FreeVar(FreeVar), isMember,
  Mapping(Mapping), fvLookup,
  MultiSubst,
  EquaitableVar, getLikeSchema,
  MultiMatchable, multiMatch,
  MultiHilbert, multiFreeVars, multiApply,
  MultiUnifiable, multiMatchVar, multiMakeTerm,
  UnificationError(UnableToUnify, ErrWrapper, OccursCheck, SubError),
  unify, 
) where

import Data.List

import Control.Monad.Identity

--------------------------------------------------------
--0. We need some helper classes first
--------------------------------------------------------

--might want to factor this out as it seems like a very useful concept
class UniformlyEquaitable f where
    eq :: f a -> f b -> Bool
    eq x y = not (neq x y)
    neq :: f a -> f b -> Bool
    neq x y = not (eq x y)

--------------------------------------------------------
--1. Define exisitinesal types for homogenous data
--------------------------------------------------------

--allows for sub parts to be paired up for matching
data Paring var where
    UnifiablePairing :: MultiUnifiable schema' var => schema' -> schema' -> Paring var

--allows for abitrary kinds of varibles
data FreeVar var where
    FreeVar :: (UniformlyEquaitable var) => var schema' -> FreeVar var

--like FreeVar except it adds in a schmea'
data Mapping var where
    Mapping :: (MultiUnifiable schema' var) => var schema' -> schema' -> Mapping var

--just defines a quick alias
type MultiSubst var = [Mapping var]

--define an Eq instance for FreeVar so that we can use union with it
--it just falls back on being uniformly equaitable
instance Eq (FreeVar var) where
    (FreeVar v1) == (FreeVar v2) = eq v1 v2

instance Show (Mapping var) where
    show (Mapping v s) = show v ++ " -> " ++ show s

--we can also define equality on mappings if EquaitableVar is defined on var
--instance (EquaitableVar var) => Eq (Mapping var) where
  --(Mapping v1 s1) == (Mapping v2 s2) = case getLikeSchema v1 v2 s2 of
    --                                        Just s2' -> s2' == s1
      --                                      Nothing  -> False

--------------------------------------------------------
--2. Define the predicates that
--------------------------------------------------------

--this is just to help people out with creating
--code that performs subtititutions
--it is not actully used by the unification code
class EquaitableVar var where
  --turns the schema' into a schema if the varibles are equal
  getLikeSchema :: var schema -> var schema' -> schema' -> Maybe schema

instance EquaitableVar var => UniformlyEquaitable var where
  eq v1 v2 = case getLikeSchema v1 v2 undefined of
      Just _  -> True  --do not evaluate the argument of this
      Nothing -> False

--defines how sub parts can be paired up for matching
class MultiMatchable schema var | schema -> var where
    multiMatch :: schema -> schema -> Maybe [Paring var]

--defines how to get free varibles and how to perform substiutions
class (UniformlyEquaitable var, Show (var schema), Eq schema, Show schema) => MultiHilbert schema var | schema -> var where
    multiFreeVars :: schema -> [FreeVar var]
    multiApply :: MultiSubst var -> schema -> schema

--finally we need a few more helper terms to define how unification works
class (MultiMatchable schema var, MultiHilbert schema var) => MultiUnifiable schema var | schema -> var where
    multiMatchVar :: schema -> schema -> Maybe (Mapping var)
    multiMakeTerm :: var schema -> schema

--------------------------------------------------------
--3. Unification errors
--------------------------------------------------------

data UnificationError var t where
    UnableToUnify :: Show t => t -> t -> UnificationError var t
    ErrWrapper :: MultiUnifiable t' var => UnificationError (var t') t' -> UnificationError (var t) t
    SubError :: (Show t) => UnificationError var t -> t -> t -> UnificationError var t
    OccursCheck :: (Show var, Show t) => var -> t -> UnificationError var t

instance Show (UnificationError var t) where
    show (UnableToUnify a b) = "Unable to unify " ++ show a ++ " with " ++ show b
    show (ErrWrapper e) = show e
    show (SubError err a b)  = "When matching " ++ show a ++ " with " ++ show b ++ ",\n" ++ show err
    show (OccursCheck v t)   = "Cannot construct infinite type " ++ show v ++ " = " ++ show t

--------------------------------------------------------
--4. Helper functions for unification
--------------------------------------------------------

applySubToMapping :: MultiSubst var -> Mapping var -> Mapping var
applySubToMapping subst (Mapping v s) = Mapping v (multiApply subst s)

--we need a way to compose mappings
(...) :: MultiSubst var -> MultiSubst var -> MultiSubst var
x ... y = (map (applySubToMapping y) x) ++ y

--maps a function over both elements of a paring
paringMap :: (forall schema'. MultiUnifiable schema' var => schema' -> schema') -> Paring var -> Paring var
paringMap f (UnifiablePairing x y) = UnifiablePairing (f x) (f y)

applySub :: MultiUnifiable schema' var => MultiSubst var -> schema' -> schema'
applySub subst s = multiApply subst s

--maps a function over a Right
(Left x) .<. f = Left (f x)
e        .<. _ = e

--maps a function over a right

(Right x) .>. f = Right (f x)
e         .>. _ = e

--check if a varible is a member of a list of FreeVars
isMember :: UniformlyEquaitable var => var schema -> [FreeVar var] -> Bool
isMember v (FreeVar v' : _) | eq v v' = True
isMember v (_:xs)                      = isMember v xs
isMember _ []                          = False

--------------------------------------------------------
--5. Unification code 
--------------------------------------------------------

unifyChildren :: (MultiUnifiable schema var) => [Paring var] -> Either (UnificationError (var schema) schema) (MultiSubst var)
unifyChildren ((UnifiablePairing a b):xs) = case unify a b of
    Left err  -> Left (ErrWrapper err)
    Right subst -> let children = map (paringMap (applySub subst)) xs
                  in (unifyChildren children) .>. (subst ...) .<. ErrWrapper
unifyChildren [] = Right []

occursCheck :: (MultiUnifiable schema' var) => var schema' -> schema' -> Either (UnificationError (var schema) schema) (MultiSubst var)
occursCheck v term | multiMakeTerm v == term           = Right $ []
occursCheck v term | v `isMember` (multiFreeVars term) = Left $ ErrWrapper (OccursCheck v term)
occursCheck v term                                     = Right $ [Mapping v term]

unify :: (MultiUnifiable schema var) => schema -> schema -> Either (UnificationError (var schema) schema) (MultiSubst var)
unify a b = case (multiMatchVar a b, multiMatchVar b a) of
  (Just (Mapping v tm), _) -> occursCheck v tm
  (_, Just (Mapping v tm)) -> occursCheck v tm
  _           -> case multiMatch a b of
      Just children -> unifyChildren children .<. (\e -> SubError e a b)
      Nothing       -> Left $ UnableToUnify a b

--------------------------------------------------------
--5.1 Want to give users a nice lookup function
--------------------------------------------------------

fvLookup :: EquaitableVar var => var schema -> MultiSubst var -> Maybe schema
fvLookup v ((Mapping v' tm):xs) = case getLikeSchema v v' tm of
    Just tm' -> Just tm'
    Nothing  -> fvLookup v xs
fvLookup _ []                   = Nothing
