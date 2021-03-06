{-#LANGUAGE GADTs, KindSignatures, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes, ImpredicativeTypes, ScopedTypeVariables #-}
{- Copyright (C) 2015 Jake Ehrlich and Graham Leach-Krouse <gleachkr@ksu.edu>

This file is part of Carnap 

Carnap is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Carnap is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with Carnap. If not, see <http://www.gnu.org/licenses/>.
- -}

module Carnap.Core.Unification.HigherOrderUtil(MultiPlated, multiplate, makeSub) where

import Control.Lens
import Control.Monad.State.Lazy
import Data.Functor
import Carnap.Core.Unification.HigherOrderMatching
import Control.Applicative
import Data.List

_child :: (Plated a) => Int -> Simple Traversal a a
_child = elementOf plate


findSubs pairs [] whole = [whole]
findSubs pairs ((path, node):stk) whole = concatMap (uncurry pmatch) pairs ++ no_sub
    where with_subs v subs = nub $ concatMap (\sub -> findSubs (applySub sub) new_stk (set path (makeTerm v) whole)) subs
          no_sub = findSubs pairs new_stk whole
          childs = children node
          new_stk = map mk_pair (zip [0..] childs) ++ stk
          mk_pair (idx, child) = (path . _child idx, child)
          applySub sub = map (\(v, sm) -> (v, apply sub sm)) pairs
          pmatch v sm = case patternMatch sm node of
              Right subs -> with_subs v subs
              Left _    -> []

--it's easier to see how this would generalize to 3rd order matching!!
--in fact I wonder if this could generalize to abitrary order!
findSubsInfix :: (MultiPlated super schema, Matchable schema var)
              => [(var schema, schema)]
              -> (forall a b. MultiPlated a b => Simple Traversal a b)
              -> schema
              -> (super -> super)
              -> [super -> super]
findSubsInfix pairs path node delta = fold (delta, pairs) ++ (pairs >>= pmatch)
    where nextChild ps (idx, child) deltas = deltas >>= findSubsInfix ps (path . _child idx) child
          fold (dlt, ps) = foldr (nextChild ps) [dlt] (zip [0..] (children node))
          applySub sub = map (\(v, sm) -> (v, apply sub sm)) pairs
          pmatch (v, sm) = case patternMatch sm node of
              Right subs -> fold (set path (makeTerm v) . delta, subs >>= applySub)
              Left _   -> []

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

multiChildrenGenericPaths node = zip paths (toListOf multiplate node)
    where paths = map (\idx -> elementOf multiplate idx) [0..]

{-
makeSub :: forall super schema var. (MultiPlated super schema, Matchable schema var, Matchable super var) 
        => var super
        -> [(var schema, schema)]
        -> super 
        -> [Mapping var]
makeSub bv pairs node = map (abstraction . ($ node)) (findSubsInit pairs node)
    where abstraction = LambdaMapping bv (map (FreeVar . fst) pairs)
-}

makeSub :: forall super schema var. (MultiPlated super schema, Matchable schema var, Matchable super var) 
        => var super
        -> [(var schema, schema)]
        -> super 
        -> [Mapping var]
makeSub bv pairs node = map abstraction $ findSubs pairs childs node
    where abstraction = LambdaMapping bv (map (FreeVar . fst) pairs)
          childs = multiChildrenGenericPaths node
