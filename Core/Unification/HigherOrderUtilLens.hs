{-#LANGUAGE GADTs, KindSignatures, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes, ImpredicativeTypes, ScopedTypeVariables #-}

module Carnap.Core.Unification.HigherOrderUtilLens(makeSub, MultiPlated, multiplate, findSubs) where

import Control.Lens
import Control.Monad.State.Lazy
import Data.Functor
import Carnap.Core.Unification.HigherOrderPatternMatching
import Control.Applicative
import Data.List

type Path g a b = forall (f :: * -> *). Applicative f => g ((b -> f b) -> a -> f a)

_child :: (Plated a) => Path ((->) Int) a a
_child = elementOf plate

type FindSubsType var schema schema' concrete t = [(var schema, schema)] -> [(t, concrete)] -> schema' -> [schema']

--It is important to note that I could not figure out how to type this properly
--the type check was capable however so I don't really 
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

--a generalization of Plated that accounts for children being of diffrent types
--multiplated is reflexive if Plated is defiend
--multiplated is transative
--note that 
class Plated a' => MultiPlated a a' where
    multiplate :: Simple Traversal a a'

instance Plated a => MultiPlated a a where
    multiplate = id

_mchild :: MultiPlated a b => Path ((->) Int) a b
_mchild = elementOf multiplate

type MultiChildType a b t = a -> [(t, b)]

multiChildrenGenericPaths :: forall a' b' a b. (MultiPlated a' b', MultiPlated a b) => Path (MultiChildType a b) a' b'
multiChildrenGenericPaths node = zip paths (toListOf multiplate node)
    where paths = map (\idx -> _mchild idx) [0..]

--again I wasn't able to figure out how to type this. I'm very confused on the matter
makeSub bv pairs c = map (LambdaMapping bv (map (FreeVar . fst) pairs)) (findSubs pairs childs (toSchema c))
    where childs = multiChildrenGenericPaths c


