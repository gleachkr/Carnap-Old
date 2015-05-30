{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes, TupleSections #-}

module FiniteTupleSetChecker () where

import Carnap.Core.ModelChecker.SatSolver
import qualified Data.Map as Map

--A language of set thoretic operations inspired by alloy
data Set = Union Set Set
         | Diff Set Set
         | Inter Set Set
         | Compose Set Set
         | Cross Set Set
         | Trans Set
         | Iden
         | Empty
         | All
         | SetBuilder [Int] Formula
         | S Int

x `U` y = Union x y
x ./. y = Diff x y
x .&. y = Inter x y
x ... y = Compose x y
x `X` y = Cross x y
v `such` f = SetBuilder v f

--Forall 0 ((S 0) `U` ([1, 2, 3] `such` (SetVar))) (0 .:. S 4)

--this language inspired by Alloy
data Formula = Not Formula
             | Formula :& Formula
             | Formula :| Formula
             | Formula :-> Formula
             | Formula :<-> Formula
             | Formula :+ Formula
             | Set :< Set
             | Set := Set
             | Int :== Int
             | Member Int Set 
             | Forall Int Set Formula
             | Some Int Set Formula

x .:. s = Member x s

data Model

data Problem = Problem Formula Int

--a problem should be a formula and a set size
--so we are missing the assignment part of this
--somthing needs to be maintained in state that explains how to map
--Sat varibles to build the sets up
instance SatReduction Problem Model where
    toFormula prob = undefined
    toModel model = undefined    