{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, ImpredicativeTypes, ScopedTypeVariables #-}

module HigherOrderUtil() where

import Control.Lens
import Control.Monad.State.Lazy
import Data.Functor
import Carnap.Core.Unification.HigherOrderPatternMatching
    
{-
the output for the following problem:
f(a) = a -> f(f(a)) = a

[
    f(a) = a -> [
      alpha = a,
      f([alpha, f(a)]) = a
    ]
    alpha = a -> [
      f([alpha, f(a)]) = a
    ]
]

the choice operators are not nested the way I would have liked the algorithm to produce this is very simple
and after thinking a bit more about it I'm not sure how much of a gain I will get from nesting the choice operators
more deeplly. If it becomes an issue I can implement somthing that pushes the choice operators in

the algorithm maintains a stack of 
-}

type Path a = Simple Traversal a a

_child :: (Plated a) => Int -> Path a
_child = elementOf plate

--schema, concrete, and var are scopped
--this allows me to refer to them in where clauses
--this is the only way to (neatly) use ImpredicativeTypes here
--we need ImpredicativeTypes to allow for a stack of lenses
findSubs :: forall schema concrete var. (Plated schema, Plated concrete, Matchable concrete schema var) => 
           [(var schema, schema)] ->
           [(Path schema, concrete)] -> 
           schema -> 
           [schema]
findSubs pairs [] whole = [whole]
findSubs pairs ((path, node):stk) whole = (concatMap (uncurry pmatch) pairs) ++ no_sub
    where with_sub v sub = (findSubs (applySub sub) new_stk (set path (makeTerm v) whole))
          no_sub = (findSubs pairs new_stk whole)
          childs = children node :: [concrete]
          new_stk = (map mk_pair (zip [0..] childs)) ++ stk
          mk_pair (idx, child) = (path . _child idx, child) :: (Path schema, concrete)
          applySub sub = map (\(v, sm) -> (v, apply sub sm)) pairs
          pmatch v sm = case patternMatch sm node of
              Left sub -> with_sub v sub
              Right _  -> []

makeSub :: (Plated schema', Plated concrete, Matchable concrete schema' var, Matchable concrete schema var) =>
           var schema -> [(var schema', schema')] -> concrete -> Mapping var
makeSub bv pairs c = LambdaMapping bv (map (FreeVar . fst) pairs) (findSubs pairs [(id, c)] (toSchema c))

