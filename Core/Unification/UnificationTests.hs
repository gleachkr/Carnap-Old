{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}
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
module Carnap.Core.Unification.UnificationTests where

import Carnap.Core.Unification.Unification
import qualified Data.Map as Map
import qualified Data.Set as Set

--for automatic testing
import Test.QuickCheck

--a very basic unifiable term
data TestTerm = Constructor String [TestTerm]
              | FreeVar String
    deriving(Show, Eq, Ord)
 
--------------------------------------------------------
--5.1 Implement the typeclasses from above
--------------------------------------------------------    
instance Hilbert String TestTerm TestTerm where
  ftv (Constructor s ps) = foldr (Set.union . ftv) Set.empty ps
  ftv (FreeVar nm)       = Set.singleton nm

  apply sub (Constructor s ps) = Constructor s (map (apply sub) ps)
  apply sub (FreeVar nm)       = case Map.lookup nm sub of
      Just t  -> apply sub t --recursivlly apply the substitution to make sure nothing gets passed us
      Nothing -> FreeVar nm

instance Matchable TestTerm TestTerm where
    match (Constructor a xs) (Constructor b ys) 
        | a == b && (length xs == length ys)  = Just $ zip xs ys
    match (FreeVar a)        _           = Just []
    match _                  (FreeVar a) = Just []
    match _                  _           = Nothing

instance Unifiable String TestTerm where

  matchVar (FreeVar a) x = Just $ (a, x)
  matchVar _           _ = Nothing

  makeTerm = FreeVar

--------------------------------------------------------
--5.1 Implement Arbitrary for use with QuickCheck
-------------------------------------------------------- 
instance Arbitrary TestTerm where
    arbitrary     = do
       (s, n) <- oneof $ map return [("P", 2), ("S", 1), ("Cons", 2), ("->", 2), ("0", 0), ("Nil", 0), ("t", 0)]
       children <- vector n
       v <- oneof $ map return ["A", "B", "C", "D", "E"]
       oneof $ map return [FreeVar v, Constructor s children]

    shrink (FreeVar v) = []
    shrink (Constructor s children) = children ++ (concatMap shrink children)

--------------------------------------------------------
--5.2 Laws that should always hold
--------------------------------------------------------

-- if sub=unify(x, y) then x(sub) == y(sub)
unifyProp :: (TestTerm, TestTerm) -> Bool
unifyProp (a, b) = case unify a b of
  Left sub -> (apply sub a) == (apply sub b)
  Right _  -> True

x `implies` y = not x || y

-- a formula with no free varibles should always unify with itself
-- addtionally it should unify to the empty set
unifySame :: TestTerm -> Bool
unifySame a = (ftv a == Set.empty) `implies` case unify a a of
  Left sub -> sub == Map.empty
  Right _  -> False

--------------------------------------------------------
--5.3 Testing the laws
--------------------------------------------------------
--we are going to perform 10000 tests with no more than 300000 failures
--individual trees should not be very big (20 nodes is plenty)
args = Args {replay = Nothing, chatty = True, maxSuccess = 10000, maxDiscardRatio = 3, maxSize = 20}
--veryify both of the properties
testUnifyProp = quickCheckWith args unifyProp
testUnifySame = quickCheckWith args unifySame
