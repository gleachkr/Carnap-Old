{-#LANGUAGE GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, RankNTypes, FunctionalDependencies #-}

module Unification where

import qualified Data.Map as Map
import qualified Data.Set as Set

type Subst = Map.Map
type Set = Set.Set

class Ord var => Types var t | t -> var where
  ftv :: t -> Set var
  apply ::  Subst var t -> t -> t

class Types var t => Unifiable var t | t -> var where
  match :: t -> t -> Maybe [(t, t)]
  matchVar :: t -> t -> Maybe (var, t)

--these are things that can't quite be unified but contain things that can be
--for instance proofs can be "unified" with proof sketches to see if they match up
--however the varibles are in the 
class Unifiable var t' => CompositeUnifiable var t' t | t -> var t' where
  matchParts :: t -> t -> Maybe [(t', t')]
  applySub :: Subst var t' -> t -> t

x ... y = (Map.map (apply y) x) `Map.union` y

data UnificationError var t where
    UnableToUnify :: t -> t -> UnificationError var t
    SubError :: UnificationError var t' -> t -> t -> UnificationError var t
    OccursCheck :: var -> t -> UnificationError var t

(Left x) .<. f = Left (f x)
e        .<. f = e

(Right x) .>. f = Right (f x)
e         .>. f = e

--maps a function over like pairs of things
pmap f = map (\(x, y) -> (f x, f y)) 

occursCheck v sub | v `Set.member` (ftv sub) = Left $ Map.singleton v sub
occursCheck v sub                            = Right $ OccursCheck v sub

unify :: (Unifiable var t) => t -> t -> Either (Subst var t) (UnificationError var t)
unify a b = case (matchVar a b, matchVar b a) of
  (Just (v, sub), _) -> occursCheck v sub
  (_, Just (v, sub)) -> occursCheck v sub
  _                -> case match a b of
    Just    children -> unifyChildren children
    Nothing          -> Right $ UnableToUnify a b
  where unifyChildren ((x, y):xs) = case unify x y of
          Left  sub -> (unifyChildren $ pmap (apply sub) xs) .<. (... sub) .>. (\e -> SubError e x y)
          Right err -> Right (SubError err x y)

compositeUnify a b = case matchParts a b of
    f
    