{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes #-}


import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad.Identity

--for automatic testing
import Test.QuickCheck
import Test.QuickCheck.Property

type Set = Set.Set

--------------------------------------------------------
--1. Define exisitinesal types for homogenous data
--------------------------------------------------------

--allows for sub parts to be paired up for matching
data Paring schema sub var where
    EqParings :: Eq schema' => sub schema schema' -> schema' -> schema' -> Paring schema sub var
    UnifiablePairing :: MultiUnifiable schema' sub var => sub schema schema' -> schema' -> schema' -> Paring schema sub var

--allows for abitrary kinds of varibles
data FreeVar schema sub var where
    FreeVar :: Eq (var schema') => sub schema schema' -> var schema' -> FreeVar schema sub var

--like FreeVar except it adds in a schmea'
data Mapping schema sub var where
    Mapping :: Eq (var schema') => sub schema schema' -> var schema' -> schema' -> Mapping schema sub var

--just defines a quick alias
type MultiSubst schema sub var = [Mapping schema sub var]

--------------------------------------------------------
--1. Define exisitinesal types for homogenous data
--------------------------------------------------------

--defines how sub parts can be paired up for matching
class MultiMatchable schema sub var | schema -> sub var where
    multiMatch :: schema -> Maybe [Paring schema sub var]

--defines how to get free varibles and how to perform substiutions
class (Eq schema, Show schema) => MultiHilbert schema sub var | schema -> var sub where
    multiFreeVars :: schema -> Set (FreeVar schema sub var)
    multiApply :: MultiSubst schema sub var -> schema

--finally we need a few more helper terms to define how unification works
class (MultiMatchable schema sub var, MultiHilbert schema sub var) => MultiUnifiable schema sub var | schema -> var sub where
    multiMatchVar :: schema -> schema -> Maybe (Mapping schema sub var)
    multiMakeTerm :: var schema -> schema

--------------------------------------------------------
--2. Unification errors
--------------------------------------------------------

data UnificationError var t where
    UnableToUnify :: Show t => t -> t -> UnificationError var t
    SubError :: (Show var, Show t', Show t) => UnificationError var t' -> t -> t -> UnificationError var t
    OccursCheck :: (Show var, Show t) => var -> t -> UnificationError var t

instance Show (UnificationError var t) where
    show (UnableToUnify a b) = "Unable to unify " ++ show a ++ " with " ++ show b
    show (SubError err a b)  = "When matching " ++ show a ++ " with " ++ show b ++ ",\n" ++ show err
    show (OccursCheck v t)   = "Cannot construct infinite type " ++ show v ++ " = " ++ show t

--------------------------------------------------------
--3. Helper functions for unification
--------------------------------------------------------

--we need a way to compose mappings
x ... y = (map (multiApply y) x) `union` y

--maps a function over both elements of a paring
paringMap :: (Paring schema sub var -> Paring schema sub var) -> Paring schema sub var -> Paring schema sub var
paringMap f (EqParings s x y)        = EqParings s (f x) (f y)
paringMap f (UnifiablePairing s x y) = UnifiablePairing s (f x) (f y)

--maps a function over a Left
(Left x) .<. f = Left (f x)
e        .<. f = e

--maps a function over a right
(Right x) .>. f = Right (f x)
e         .>. f = e

--------------------------------------------------------
--4. Unification code 
--------------------------------------------------------

unifyChildren :: [Paring schema sub var] -> Either (MultiSubst schema sub var) (UnificationError (var schema) schema)
unifyChildren ((EqParings _ a b):xs)
    | a == b    = Left []
    | otherwise = Right $ UnableToUnify a b
unifyChildren ((UnifiablePairing _ a b):xs) = case unify a b of
    Left sub  -> let children = map (paringMap (multiApply sub)) xs -- apply the mapping
                 in (unifyChildren children) .<. (sub ...) .>.  (\e -> SubError e a b)
    Right err -> Right (SubError err a b)

--unifyChildren :: (Unifiable var t) => [(t, t)] -> Either (Subst var t) (UnificationError var t)
--unifyChildren ((x, y):xs) = case unify x y of
--  Left  sub -> (unifyChildren $ pmap (apply sub) xs) .<. (sub ...) .>. (\e -> SubError e x y)
--  Right err -> Right (SubError err x y)
--unifyChildren [] = Left $ Map.empty

unify :: (MultiUnifiable schema sub var) => schema -> schema -> Either (MultiSubst schema sub var) (UnificationError (var schema) schema)
unify a b = case (multiMatchVar a, multiMatchVar b) of
  (Just m, _) -> Left [m] --no occurs check
  (_, Just m) -> Left [m] --no occurs check
  _           -> case multiMatch a b of
      Just children -> unifyChildren children
      Nothing       -> Right $ UnableToUnify a b
