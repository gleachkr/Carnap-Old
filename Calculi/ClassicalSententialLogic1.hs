{-#LANGUAGE MultiParamTypeClasses, GADTs, TypeSynonymInstances, OverlappingInstances, FlexibleInstances, FlexibleContexts #-}
{-Copyright 2015 (C) Jake Ehrlich and Graham Leach-Krouse

This file is part of Carnap. 

Carnap is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Carnap is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Carnap If not, see <http://www.gnu.org/licenses/>.
-}
module Carnap.Calculi.ClassicalSententialLogic1 where

import Carnap.Core.Data.AbstractDerivationDataTypes
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching
import Carnap.Languages.Sentential.PropositionalLanguage

import Carnap.Languages.Util.LanguageClasses
import Carnap.Core.Data.Rules
import Data.Set as Set

--------------------------------------------------------
--1 Unification-Oriented Rules
--------------------------------------------------------

--We need to be able to check whether two SSequents can be unified. For
--this, we can use compositeUnification.
--
--We don't yet have the ability to check to make sure that the
--side-formulas are handled correctly in a given inference; this would
--require unification at the level of sequents, so that we could treat the
--rules themselves as composite unifiables, and check to see if a rule like 
--"Δ|-phi,Δ'|-phi' ∴ Δ,Δ'|-phi/\phi'" could be unified with the inference.
--As it is, we, in effect, check to see if "Δ|-phi,Δ'|-phi' ∴ Γ|-phi/\phi'"
--can be unified with the inference, and rely on the sequent-construction
--algorithm (which keeps track of the premises active at each stage of the
--proof) to work properly

directDerivation :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv)) => AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
directDerivation = [[delta 1] ⊢ phi 1] ∴ [delta 1] ⊢ phi 1 

adjunction_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
adjunction_1 = [
               [delta 1] ⊢ phi 1, 
               [delta 2] ⊢ phi 2]
               ∴ 
               [delta 1, delta 2] ⊢ SeqList [phi 1 ./\. phi 2]

conditionalProof_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
conditionalProof_1 = [
                     [phi 1, delta 1] ⊢ phi 2]
                     ∴
                     [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

conditionalProof_2 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
conditionalProof_2 = [ [delta 1] ⊢ phi 2 ] ∴ [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

biconditionalProof_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
biconditionalProof_1 = [
                     [phi 1, delta 1] ⊢ phi 2,
                     [phi 2, delta 2] ⊢ phi 1]
                     ∴
                     [delta 1, delta 2] ⊢ SeqList [phi 1 .<=>. phi 2]

biconditionalProof_2 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
biconditionalProof_2 = [
                     [delta 1] ⊢ phi 2,
                     [phi 2, delta 2] ⊢ phi 1]
                     ∴
                     [delta 1, delta 2] ⊢ SeqList [phi 1 .<=>. phi 2]

biconditionalProof_3 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
biconditionalProof_3 = [
                     [phi 1, delta 1] ⊢ phi 2,
                     [delta 2] ⊢ phi 1]
                     ∴
                     [delta 1, delta 2] ⊢ SeqList [phi 1 .<=>. phi 2]

biconditionalProof_4 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
biconditionalProof_4 = [
                     [delta 1] ⊢ phi 2,
                     [delta 2] ⊢ phi 1]
                     ∴
                     [delta 1, delta 2] ⊢ SeqList [phi 1 .<=>. phi 2]

disjunctiveSyllogism_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
disjunctiveSyllogism_1 = [
                     [delta 1] ⊢ SeqList [phi 1 .\/. phi 2],
                     [phi 1, delta 2] ⊢ phi 3,
                     [phi 2, delta 3] ⊢ phi 3]
                     ∴
                     [delta 1, delta 2, delta 3] ⊢ SeqList [phi 3]

disjunctiveSyllogism_2 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
disjunctiveSyllogism_2 = [
                     [delta 1] ⊢ SeqList [phi 1 .\/. phi 2],
                     [delta 2] ⊢ phi 3,
                     [phi 2, delta 3] ⊢ phi 3]
                     ∴
                     [delta 1, delta 2, delta 3] ⊢ SeqList [phi 3]

disjunctiveSyllogism_3 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
disjunctiveSyllogism_3 = [
                     [delta 1] ⊢ SeqList [phi 1 .\/. phi 2],
                     [phi 1, delta 2] ⊢ phi 3,
                     [delta 3] ⊢ phi 3]
                     ∴
                     [delta 1, delta 2, delta 3] ⊢ SeqList [phi 3]

disjunctiveSyllogism_4 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
disjunctiveSyllogism_4 = [
                     [delta 1] ⊢ SeqList [phi 1 .\/. phi 2],
                     [delta 2] ⊢ phi 3,
                     [delta 3] ⊢ phi 3]
                     ∴
                     [delta 1, delta 2, delta 3] ⊢ SeqList [phi 3]

indirectDerivation_1_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
indirectDerivation_1_1 = [  
                         [ phi 1, delta 1] ⊢ phi 2,
                         [ phi 1, delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_2 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
indirectDerivation_1_2 = [  
                         [ delta 1] ⊢ phi 2,
                         [ phi 1, delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_3 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
indirectDerivation_1_3 = [  
                         [ phi 1, delta 1] ⊢ phi 2,
                         [ delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_4 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
indirectDerivation_1_4 = [  
                         [ delta 1] ⊢ phi 2,
                         [ delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_2_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
indirectDerivation_2_1 = [  
                         [ SeqList [lneg (phi 1)], delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ SeqList [lneg (phi 1)], delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_2 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
indirectDerivation_2_2 = [  
                         [ delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ SeqList [lneg (phi 1)], delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_3 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
indirectDerivation_2_3 = [  
                         [ SeqList [lneg (phi 1)], delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_4 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
indirectDerivation_2_4 = [  
                         [ delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

modusPonens_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
modusPonens_1 = [
                [delta 1] ⊢ phi 1, 
                [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]
                ]
                ∴ 
                [delta 1, delta 2] ⊢ phi 2

modusTolens_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
modusTolens_1 = [
                [delta 1] ⊢ SeqList [lneg (phi 2)],
                [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]
                ]
                ∴ 
                [delta 1, delta 2] ⊢ SeqList [lneg (phi 1)]

simplification_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
simplification_1 = [
                   [delta 1] ⊢ SeqList [phi 1 ./\. phi 2]
                   ]
                   ∴
                   [delta 1] ⊢ phi 1

simplification_2 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
simplification_2 = [ 
                   [delta 1] ⊢ SeqList [phi 1 ./\. phi 2]]
                   ∴
                   [delta 1] ⊢ phi 2

addition_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
addition_1 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [phi 1 .\/. phi 2]

addition_2 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
addition_2 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1]

modusTollendo_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
modusTollendo_1 = [ 
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1],
            [delta 2] ⊢ SeqList [lneg (phi 2)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 1]

modusTollendo_2 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
modusTollendo_2 = [ 
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1],
            [delta 2] ⊢ SeqList [lneg (phi 1)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 2]

doubleNegation_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
doubleNegation_1 = [ 
            [delta 1] ⊢ SeqList [lneg $ lneg $ phi 1]]
            ∴
            [delta 1] ⊢ phi 1

doubleNegation_2 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
doubleNegation_2 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [lneg $ lneg $ phi 1]

conditionalBiconditional_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
conditionalBiconditional_1 = [
            [delta 1] ⊢ SeqList [phi 2 .=>. phi 1],
            [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 1 .<=>. phi 2]

biconditionalConditional_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
biconditionalConditional_1 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]]
            ∴
            [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

biconditionalConditional_2 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
biconditionalConditional_2 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]]
            ∴
            [delta 1] ⊢ SeqList [phi 2 .=>. phi 1]

biconditionalElimination_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
biconditionalElimination_1 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ phi 1]
            ∴
            [delta 1, delta 2] ⊢ phi 2

biconditionalElimination_2 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
biconditionalElimination_2 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ phi 2]
            ∴
            [delta 1, delta 2] ⊢ phi 1

interchangeEquivalents_1 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv()), PropositionalContexts (SchematicForm pred con quant f sv ())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
interchangeEquivalents_1 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ SeqList [propContext 1 $ phi 1]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [propContext 1 $ phi 2]

interchangeEquivalents_2 :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv()), PropositionalContexts (SchematicForm pred con quant f sv ())) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
interchangeEquivalents_2 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ SeqList [propContext 1 $ phi 2]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [propContext 1 $ phi 1]

repetition :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv)) => 
    AbsRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
repetition = [[delta 1] ⊢ phi 1] ∴  [delta 1] ⊢ phi 1

--------------------------------------------------------
--Ambiguous Rules
--------------------------------------------------------

adjunction_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
adjunction_s = AmbiguousRulePlus [adjunction_1] "ADJ"

conjunctionIntroduction_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
conjunctionIntroduction_s = adjunction_s{ruleNamePlus="AI"}

conditionalProof_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
conditionalProof_s = AmbiguousRulePlus [conditionalProof_1, conditionalProof_2] "CD"

conditionalIntroduction_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
conditionalIntroduction_s = conditionalProof_s{ruleNamePlus="CI"}

disjunctiveSyllogism_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
disjunctiveSyllogism_s = AmbiguousRulePlus [  disjunctiveSyllogism_1
                                           ,  disjunctiveSyllogism_2 
                                           ,  disjunctiveSyllogism_3
                                           ,  disjunctiveSyllogism_4] "DS"

disjunctionElimination_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
disjunctionElimination_s = disjunctiveSyllogism_s{ruleNamePlus="DE"} 
                          
modusPonens_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
modusPonens_s = AmbiguousRulePlus [modusPonens_1] "MP"

conditionalElimination_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
conditionalElimination_s = modusPonens_s{ruleNamePlus= "CE"}

modusTolens_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
modusTolens_s = AmbiguousRulePlus [modusTolens_1] "MT"

simplification_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
simplification_s = AmbiguousRulePlus [simplification_1, simplification_2] "S"

conjunctionElimination_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
conjunctionElimination_s = simplification_s{ruleNamePlus="AE"}

addition_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
addition_s = AmbiguousRulePlus [addition_1,addition_2] "ADD"

disjunctionIntroduction_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
disjunctionIntroduction_s = addition_s{ruleNamePlus="DI"}

doubleNegation_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
doubleNegation_s = AmbiguousRulePlus [doubleNegation_1,doubleNegation_2] "DN"

modusTollendo_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
modusTollendo_s = AmbiguousRulePlus [ modusTollendo_1,  modusTollendo_2] "MTP"

conditionalBiconditional_s:: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
conditionalBiconditional_s = AmbiguousRulePlus [conditionalBiconditional_1] "CB"

biconditionalConditional_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
biconditionalConditional_s = AmbiguousRulePlus [biconditionalConditional_2, biconditionalConditional_1] "BC"

biconditionalIntroduction_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
biconditionalIntroduction_s = AmbiguousRulePlus [  biconditionalProof_1
                                                ,  biconditionalProof_2
                                                ,  biconditionalProof_3
                                                ,  biconditionalProof_4] "BI"

biconditionalElimination_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
biconditionalElimination_s = AmbiguousRulePlus [biconditionalElimination_1,  biconditionalElimination_2] "BE"

interchangeEquivalents_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv()), PropositionalContexts (SchematicForm pred con quant f sv ())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
interchangeEquivalents_s = AmbiguousRulePlus [interchangeEquivalents_1, interchangeEquivalents_2] "IE"

indirectDerivation_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
indirectDerivation_s = AmbiguousRulePlus  [ indirectDerivation_1_1 ,
                                        indirectDerivation_1_2 ,
                                        indirectDerivation_1_3 ,
                                        indirectDerivation_1_4 ,
                                        indirectDerivation_2_1 , 
                                        indirectDerivation_2_2 ,
                                        indirectDerivation_2_3 ,
                                        indirectDerivation_2_4] "ID"

negationIntroduction_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
negationIntroduction_s = AmbiguousRulePlus [ indirectDerivation_1_1
                                           , indirectDerivation_1_2
                                           , indirectDerivation_1_3
                                           , indirectDerivation_1_4] "NI"

negationElimination_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
negationElimination_s = AmbiguousRulePlus [ indirectDerivation_2_1
                                          , indirectDerivation_2_2
                                          , indirectDerivation_2_3
                                          , indirectDerivation_2_4] "NE"

directDerivation_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv), BooleanLanguage (SchematicForm pred con quant f sv ()), S_PropositionalConstants (SchematicForm pred con quant f sv())) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
directDerivation_s = AmbiguousRulePlus [directDerivation] "DD"

repetition_s :: (SItemConstants (SSequentItem pred con quant f sv), S_PropositionalConstants(SSequentItem pred con quant f sv)) => 
    AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())
repetition_s = AmbiguousRulePlus [repetition] "R"

--------------------------------------------------------
--Rule Sets
--------------------------------------------------------

permuteAll (AmbiguousRulePlus l n) = (`AmbiguousRulePlus` n) $ concatMap premisePermutationsPlus l

--we'll then do a lookup by rule-name, on the basis of the rule cited in
--justification

prettyClassicalSLruleSet :: Set.Set (AmbiguousRulePlus (Sequent PItem) Pvar)
prettyClassicalSLruleSet = Set.fromList [
                            adjunction_s, 
                            conditionalProof_s, 
                            disjunctiveSyllogism_s,
                            modusPonens_s,
                            modusTolens_s,
                            modusTollendo_s,
                            simplification_s,
                            doubleNegation_s,
                            addition_s,
                            indirectDerivation_s,
                            directDerivation_s,
                            conditionalBiconditional_s,
                            biconditionalConditional_s,
                            interchangeEquivalents_s,
                            repetition_s
                            ]

classicalSLruleSet = Set.map permuteAll prettyClassicalSLruleSet

prettyLogicBookSDruleSet :: Set.Set (AmbiguousRulePlus (Sequent PItem) Pvar)
prettyLogicBookSDruleSet = Set.fromList [ conjunctionIntroduction_s
                                  , conjunctionElimination_s
                                  , disjunctionIntroduction_s
                                  , disjunctionElimination_s
                                  , conditionalIntroduction_s
                                  , conditionalElimination_s
                                  , negationIntroduction_s
                                  , negationElimination_s
                                  , biconditionalIntroduction_s
                                  , biconditionalElimination_s
                                  , repetition_s
                                  ]

logicBookSDruleSet = Set.map permuteAll prettyLogicBookSDruleSet

--------------------------------------------------------
--Rule Lists
--------------------------------------------------------

--A list of rules, which are Left if they're for direct inferences, and
--Right if they're for using subproofs.

classicalSLRules :: RulesAndArity
classicalSLRules "IE"  = Just (Left 2)
classicalSLRules "CB"  = Just (Left 2)
classicalSLRules "BC"  = Just (Left 1)
classicalSLRules "MP"  = Just (Left 2)
classicalSLRules "MT"  = Just (Left 2)
classicalSLRules "DD"  = Just (Right 1)
classicalSLRules "CD"  = Just (Right 1)
classicalSLRules "DS"  = Just (Right 3)
classicalSLRules "ID"  = Just (Right 2)
classicalSLRules "ADJ" = Just (Left 2)
classicalSLRules "ADD" = Just (Left 1)
classicalSLRules "MTP" = Just (Left 2)
classicalSLRules "S"   = Just (Left 1)
classicalSLRules "DN"  = Just (Left 1)
classicalSLRules "R"   = Just (Left 1)
classicalSLRules _     = Nothing

logicBookSDrules :: RulesAndArity
logicBookSDrules "AI" = Just (Left 2)
logicBookSDrules "AE" = Just (Left 1)
logicBookSDrules "DI" = Just (Left 1)
logicBookSDrules "DE" = Just (Right 3)
logicBookSDrules "CI" = Just (Right 1)
logicBookSDrules "CE" = Just (Left 2)
logicBookSDrules "NI" = Just (Right 2)
logicBookSDrules "NE" = Just (Right 2)
logicBookSDrules "BI" = Just (Right 2)
logicBookSDrules "BE" = Just (Left 2)
logicBookSDrules "R"  = Just (Left 1)
logicBookSDrules _    = Nothing
