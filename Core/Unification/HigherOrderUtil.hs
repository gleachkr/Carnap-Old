{-#LANGUAGE GADTs, KindSignatures, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes, ImpredicativeTypes, ScopedTypeVariables #-}

module Carnap.Core.Unification.HigherOrderUtil(MultiPlated, multiplate, makeSub) where

import Control.Lens
import Control.Monad.State.Lazy
import Data.Functor
import Carnap.Core.Unification.HigherOrderMatching
import Control.Applicative
import Data.List

_child :: (Plated a) => Int -> Simple Traversal a a
_child = elementOf plate

{-
findSubs pairs [] whole = [whole]
findSubs pairs ((path, node):stk) whole = (concatMap (uncurry pmatch) pairs) ++ no_sub
    where with_subs v subs = nub $ concatMap (\sub -> findSubs (applySub sub) new_stk (set path (makeTerm v) whole)) subs
          no_sub = (findSubs pairs new_stk whole)
          childs = children node
          new_stk = (map mk_pair (zip [0..] childs)) ++ stk
          mk_pair (idx, child) = (path . _child idx, child)
          applySub sub = map (\(v, sm) -> (v, apply sub sm)) pairs
          pmatch v sm = case patternMatch sm node of
              Left subs -> with_subs v subs
              Right _    -> []
-}

--it's easier to see how this would generalize to 3rd order matching!!
--in fact I wonder if this could generalize to abitrary order!
findSubsInfix :: (MultiPlated super schema, Matchable schema var)
              => [(var schema, schema)]
              -> (forall a b. MultiPlated a b => Simple Traversal a b)
              -> schema
              -> (super -> super)
              -> [super -> super]
findSubsInfix pairs path node delta = fold (delta, pairs) ++ (pairs >>= pmatch)
    where nextChild ps (idx, child) deltas = deltas >>= (findSubsInfix ps (path . _child idx) child)
          fold (dlt, ps) = foldr (nextChild ps) [dlt] (zip [0..] (children node))
          applySub sub = map (\(v, sm) -> (v, apply sub sm)) pairs
          pmatch (v, sm) = case patternMatch sm node of
              Left subs -> fold (set path (makeTerm v) . delta, subs >>= applySub)
              Right _   -> []

findSubsInit :: (MultiPlated super schema, Matchable schema var)
          => [(var schema, schema)]
          -> super
          -> [super -> super]
findSubsInit pairs node = foldr nextChild [id] (zip [0..] (toListOf multiplate node))
    where nextChild (idx, child) deltas = deltas >>= (findSubsInfix pairs (multiplate . _child idx) child)

--a generalization of Plated that accounts for children being of diffrent types than the parent
--multiplated is reflexive if Plated is defiend
--multiplated is transative (or should be if you did stuff right)

class Plated a' => MultiPlated a a' where
    multiplate :: Simple Traversal a a'

instance Plated a => MultiPlated a a where
    multiplate = id


makeSub :: forall super schema var. (MultiPlated super schema, Matchable schema var, Matchable super var) 
        => var super
        -> [(var schema, schema)]
        -> super 
        -> [Mapping var]
makeSub bv pairs node = map (abstraction . ($ node)) (findSubsInit pairs node)
    where abstraction = LambdaMapping bv (map (FreeVar . fst) pairs)


