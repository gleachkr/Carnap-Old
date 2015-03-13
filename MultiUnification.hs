{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes #-}


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
data Paring schema var where
    UnifiablePairing :: MultiUnifiable schema' var => schema' -> schema' -> Paring schema var

--allows for abitrary kinds of varibles
data FreeVar schema var where
    FreeVar :: UniformlyEquaitable var => var schema' -> FreeVar schema var

--like FreeVar except it adds in a schmea'
data Mapping schema var where
    Mapping :: (MultiUnifiable schema' var) => var schema' -> schema' -> Mapping schema var

--just defines a quick alias
type MultiSubst schema var = [Mapping schema var]
 
--------------------------------------------------------
--2. Define the predicates that
--------------------------------------------------------

--defines how sub parts can be paired up for matching
class MultiMatchable schema var | schema -> var where
    multiMatch :: schema -> schema -> Maybe [Paring schema var]

--defines how to get free varibles and how to perform substiutions
class (UniformlyEquaitable var, Show (var schema), Eq schema, Show schema) => MultiHilbert schema var | schema -> var where
    multiFreeVars :: schema -> [FreeVar schema var]
    multiApply :: MultiSubst schema var -> schema -> schema

--finally we need a few more helper terms to define how unification works
class (MultiMatchable schema var, MultiHilbert schema var) => MultiUnifiable schema var | schema -> var where
    multiMatchVar :: schema -> Maybe (Mapping schema var)
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

mutateMapping :: Mapping schema var -> Mapping schema' var
mutateMapping (Mapping v s) = Mapping v s

mutateSub = map mutateMapping

applySubToMapping :: MultiSubst schema var -> Mapping schema var -> Mapping schema var
applySubToMapping subst (Mapping v s) = Mapping v (multiApply (mutateSub subst) s)

--we need a way to compose mappings
(...) :: MultiSubst schema var -> MultiSubst schema var -> MultiSubst schema var
x ... y = (map (applySubToMapping y) x) ++ y

--maps a function over both elements of a paring
paringMap :: (forall schema'. MultiUnifiable schema' var => schema' -> schema') -> Paring schema var -> Paring schema var
paringMap f (UnifiablePairing x y) = UnifiablePairing (f x) (f y)

applySub :: MultiUnifiable schema' var => MultiSubst schema var -> schema' -> schema'
applySub subst s = multiApply (mutateSub subst) s

--maps a function over a Left
(Left x) .<. f = Left (f x)
e        .<. f = e

--maps a function over a right
(Right x) .>. f = Right (f x)
e         .>. f = e

--check if a varible is a member of a list of FreeVars
isMember :: UniformlyEquaitable var => var schema -> [FreeVar schema var] -> Bool
isMember v (FreeVar v' : xs) | eq v v' = True
isMember v (_:xs)                      = isMember v xs

--------------------------------------------------------
--5. Unification code 
--------------------------------------------------------

unifyChildren :: [Paring schema var] -> Either (MultiSubst schema var) (UnificationError (var schema) schema)
unifyChildren ((UnifiablePairing a b):xs) = case unify a b of
    Left subst -> let children = map (paringMap (applySub subst)) xs
                  in (unifyChildren children) .<. (mutateSub . (subst ...) . mutateSub) .>. (\e -> ErrWrapper $ e)
    Right err  -> Right (ErrWrapper $ (SubError err a b))
unifyChildren [] = Left []

occursCheck :: (MultiUnifiable schema' var) => var schema' -> schema' -> Either (MultiSubst schema var) (UnificationError (var schema) schema)
occursCheck v term | multiMakeTerm v == term           = Left $ []
occursCheck v term | v `isMember` (multiFreeVars term) = Right $ ErrWrapper (OccursCheck v term)
occursCheck v term                                     = Left $ mutateSub [Mapping v term]


unify :: (MultiUnifiable schema var) => schema -> schema -> Either (MultiSubst schema var) (UnificationError (var schema) schema)
unify a b = case (multiMatchVar a, multiMatchVar b) of
  (Just (Mapping v tm), _) -> occursCheck v tm
  (_, Just (Mapping v tm)) -> occursCheck v tm
  _           -> case multiMatch a b of
      Just children -> unifyChildren children
      Nothing       -> Right $ UnableToUnify a b

--------------------------------------------------------
--6. Define an example
--------------------------------------------------------

--define a data type for simply typed lambda calculus
--eventully we will perform multi unification
data Var t where
    TermVar :: String -> Var Term
    TypeVar :: String -> Var Type

data Type = Type :-> Type
          | BasicType String
          | TyVar (Var Type)

data Term = Lam String Type Term
          | Term :$: Term
          | BasicTerm String
          | TmVar (Var Term)



