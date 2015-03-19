{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes #-}

module MultiUnification (
  UniformlyEquaitable, eq, neq,
  Paring(UnifiablePairing),
  FreeVar(FreeVar),
  Mapping(Mapping),
  MultiSubst,
  EquaitableVar, getLikeSchema,
  MultiMatchable, multiMatch,
  MultiHilbert, multiFreeVars, multiApply,
  MultiUnifiable, multiMatchVar, multiMakeTerm,
  UnificationError(UnableToUnify, ErrWrapper, OccursCheck, SubError),
  unify, fvLookup
) where

import Data.List

import Control.Monad.Identity

--for automatic testing
import Test.QuickCheck
import Test.QuickCheck.Property

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

--------------------------------------------------------
--2. Define the predicates that
--------------------------------------------------------

--this is just to help people out with creating
--code that performs subtititutions
--it is not actully used by the unification code
class EquaitableVar var where
  --turns the schema' into a schema if the varibles are equal
  getLikeSchema :: var schema -> var schema' -> schema' -> Maybe schema

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
    ErrWrapper :: UnificationError var' t' -> UnificationError var t
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

--maps a function over a Left
(Left x) .<. f = Left (f x)
e        .<. f = e

--maps a function over a right
(Right x) .>. f = Right (f x)
e         .>. f = e

--check if a varible is a member of a list of FreeVars
isMember :: UniformlyEquaitable var => var schema -> [FreeVar var] -> Bool
isMember v (FreeVar v' : xs) | eq v v' = True
isMember v (_:xs)                      = isMember v xs
isMember v []                          = False

--------------------------------------------------------
--5. Unification code 
--------------------------------------------------------

unifyChildren :: [Paring var] -> Either (MultiSubst var) (UnificationError (var schema) schema)
unifyChildren ((UnifiablePairing a b):xs) = case unify a b of
    Left subst -> let children = map (paringMap (applySub subst)) xs
                  in (unifyChildren children) .<. (subst ...) .>. (\e -> ErrWrapper $ e)
    Right err  -> Right (ErrWrapper $ (SubError err a b))
unifyChildren [] = Left []

occursCheck :: (MultiUnifiable schema' var) => var schema' -> schema' -> Either (MultiSubst var) (UnificationError (var schema) schema)
occursCheck v term | multiMakeTerm v == term           = Left $ []
occursCheck v term | v `isMember` (multiFreeVars term) = Right $ ErrWrapper (OccursCheck v term)
occursCheck v term                                     = Left $ [Mapping v term]

unify :: (MultiUnifiable schema var) => schema -> schema -> Either (MultiSubst var) (UnificationError (var schema) schema)
unify a b = case (multiMatchVar a b, multiMatchVar b a) of
  (Just (Mapping v tm), _) -> occursCheck v tm
  (_, Just (Mapping v tm)) -> occursCheck v tm
  _           -> case multiMatch a b of
      Just children -> unifyChildren children
      Nothing       -> Right $ UnableToUnify a b

--------------------------------------------------------
--5.1 Want to give users a nice lookup function
--------------------------------------------------------

fvLookup :: EquaitableVar var => var schema -> MultiSubst var -> Maybe schema
fvLookup v ((Mapping v' tm):xs) = case getLikeSchema v v' tm of
    Just tm' -> Just tm'
    Nothing  -> fvLookup v xs
fvLookup v []                   = Nothing

--------------------------------------------------------
--6. Define an example
--------------------------------------------------------

--define a data type for simply typed lambda calculus
--eventully we will perform multi unification
data Var t where
    TermVar :: String -> Var Term
    TypeVar :: String -> Var Type

--define some instances real quick for varibles
instance Show (Var a) where
    show (TermVar s) = s
    show (TypeVar s) = s

instance EquaitableVar Var where
    getLikeSchema (TermVar s) (TermVar s') t | s == s' = Just t
    getLikeSchema (TypeVar s) (TypeVar s') t | s == s' = Just t
    getLikeSchema _           _            _           = Nothing

instance Eq (Var a) where
    (TermVar s) == (TermVar s') = s == s'
    (TypeVar s) == (TypeVar s') = s == s'
    _           == _            = False

instance UniformlyEquaitable Var where
    eq (TermVar s) (TermVar s') = s == s'
    eq (TypeVar s) (TypeVar s') = s == s'
    eq _           _            = False

--now define the actual language terms

--these are simple types
data Type = Type :-> Type
          | BasicType String
          | TyVar (Var Type)
    deriving(Eq, Show)

--and these are simply typed lambda terms
data Term = Lam String Type Term
          | Term :$: Term
          | BasicTerm String
          | TmVar (Var Term)
    deriving(Eq, Show)

--------------------------------------------------------
--6.1 Define instances for the lambda terms
--------------------------------------------------------

--first lets do types 
instance MultiMatchable Type Var where
    multiMatch (t1 :-> t1')  (t2 :-> t2') = Just [UnifiablePairing t1 t2, UnifiablePairing t1' t2']
    multiMatch (BasicType a) (BasicType b)
        | a == b = Just []
    multiMatch (TyVar _) _ = Just []
    multiMatch _ (TyVar _) = Just []
    multiMatch _ _         = Nothing

instance MultiHilbert Type Var where
    multiFreeVars (t :-> t')    = (multiFreeVars t) `union` (multiFreeVars t')
    multiFreeVars (BasicType a) = []
    multiFreeVars (TyVar v)     = [FreeVar v]  

    multiApply subst (t :-> t') = (multiApply subst t) :-> (multiApply subst t')
    multiApply subst (TyVar v)  = case fvLookup v subst of
        Just tm -> tm
        Nothing -> TyVar v
    multiApply _     x          = x

instance MultiUnifiable Type Var where
    multiMatchVar (TyVar v) tm = Just $ Mapping v tm
    multiMatchVar tm (TyVar v) = Just $ Mapping v tm
    multiMatchVar _  _         = Nothing

    multiMakeTerm = TyVar

--now lets do terms

instance MultiMatchable Term Var where
    multiMatch (Lam v tau tm) (Lam v' tau' tm') | v == v' = Just [UnifiablePairing tau tau', UnifiablePairing tm tm']
    multiMatch (BasicTerm a)  (BasicTerm b)     | a == b  = Just []
    multiMatch (t1 :$: t1')   (t2 :$: t2')                = Just [UnifiablePairing t1 t2, UnifiablePairing t1' t2']
    multiMatch (TmVar v)      _                           = Just []
    multiMatch _              (TmVar v)                   = Just []
    multiMatch _              _                           = Nothing

instance MultiHilbert Term Var where
    multiFreeVars (t :$: t')    = (multiFreeVars t) `union` (multiFreeVars t')
    multiFreeVars (BasicTerm a) = []
    multiFreeVars (TmVar v)     = [FreeVar v]  

    multiApply subst (Lam v tau tm) = Lam v (multiApply subst tau) (multiApply subst tm)
    multiApply subst (t :$: t')     = (multiApply subst t) :$: (multiApply subst t')
    multiApply subst (TmVar v)      = case fvLookup v subst of
        Just tm -> tm
        Nothing -> TmVar v
    multiApply _     x              = x

instance MultiUnifiable Term Var where
    multiMatchVar (TmVar v) tm = Just $ Mapping v tm
    multiMatchVar tm (TmVar v) = Just $ Mapping v tm
    multiMatchVar _  _         = Nothing

    multiMakeTerm = TmVar
