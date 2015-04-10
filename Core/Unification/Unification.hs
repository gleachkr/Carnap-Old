{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}

module Carnap.Core.Unification.Unification (
  Hilbert, Subst, Unifiable, Matchable,
  ftv, apply, match, matchVar, makeTerm,
  UnificationError(UnableToUnify, SubError, OccursCheck), 
  unifyChildren, pmap, (.<.), (.>.), (...),
  unify, compositeUnify) where

import qualified Data.Map as Map
import qualified Data.Set as Set

type Subst = Map.Map
type Set = Set.Set

--------------------------------------------------------
--1. typeclasses for unifiable like things
--------------------------------------------------------

--anything that has structure that can be matched
class Matchable t sub where
    match :: t -> t -> Maybe [(sub, sub)]

--Things that have free varibles and can have those things substituted
--I may be using Hilbert (as in Hilbert System) wrongly here. Correct if needed
class (Show var, Show schema, Eq schema, Eq var, Ord var) => Hilbert var schema sub | schema -> var sub where
  ftv :: schema -> Set var
  apply ::  Subst var sub -> schema -> schema

--Things that can be unified. That is things with structure and children that can
--also be free varibles.
class (Matchable schema schema, Hilbert var schema schema) => Unifiable var schema | schema -> var where
  --match :: t -> t -> Maybe [(t, t)]
  matchVar :: schema -> schema -> Maybe (var, schema)
  makeTerm :: var -> schema

--------------------------------------------------------
--1.1 Useful instances
--------------------------------------------------------

instance Matchable [sub] sub where
  match (x:xs) (y:ys) = fmap ((x, y) :) (match xs ys)
  match []     []     = Just []
  match _      _      = Nothing

instance Hilbert var schema sub => Hilbert var [schema] sub where
  ftv xs = Set.unions (map ftv xs)
  apply sub xs = map (apply sub) xs

instance (Ord schema, Hilbert var schema sub) => Hilbert var (Set schema) sub where
  ftv xs = (Set.unions . Set.toList) (Set.map ftv xs)
  apply sub xs = Set.map (apply sub) xs

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
--3. Helpers
--------------------------------------------------------

--compose two substitutions
x ... y = (Map.map (apply y) x) `Map.union` y

--maps a function over a Left
(Left x) .<. f = Left (f x)
e        .<. f = e

--maps a function over a right
(Right x) .>. f = Right (f x)
e         .>. f = e

--maps a function over like pairs of things
pmap f = map (\(x, y) -> (f x, f y)) 

occursCheck :: (Unifiable var t) => var -> t -> Either (Subst var t) (UnificationError var t)
occursCheck v sub | makeTerm v == sub            = Left $ Map.empty
occursCheck v sub | not $ Set.member v (ftv sub) = Left $ Map.singleton v sub
occursCheck v sub                                = Right $ OccursCheck v sub

--------------------------------------------------------
--4. Unification
--------------------------------------------------------
unifyChildren :: (Unifiable var t) => [(t, t)] -> Either (Subst var t) (UnificationError var t)
unifyChildren ((x, y):xs) = case unify x y of
  Left  sub -> (unifyChildren $ pmap (apply sub) xs) .<. (sub ...) .>. (\e -> SubError e x y)
  Right err -> Right (SubError err x y)
unifyChildren [] = Left $ Map.empty

unify :: (Unifiable var t) => t -> t -> Either (Subst var t) (UnificationError var t)
unify a b = case (matchVar a b, matchVar b a) of
  (Just (v, sub), _) -> occursCheck v sub
  (_, Just (v, sub)) -> occursCheck v sub
  _                  -> case match a b of
    Just    children -> unifyChildren children
    Nothing          -> Right $ UnableToUnify a b

--allows us to unify things which contain unifiable things
compositeUnify :: (Show t, Unifiable var sub, Matchable t sub) 
               => t -> t -> Either (Subst var sub) (UnificationError var t)
compositeUnify a b = case match a b of
  Just parts -> case unifyChildren parts of
      Left sub  -> Left sub
      Right err -> Right $ SubError err a b
  Nothing    -> Right $ UnableToUnify a b

