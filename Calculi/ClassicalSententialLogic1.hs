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

directDerivation :: AbsRulePlus (Sequent PItem) Pvar
directDerivation = [[delta 1] ⊢ phi 1] ∴ [delta 1] ⊢ phi 1 

adjunction_1 :: AbsRulePlus (Sequent PItem) Pvar
adjunction_1 = [
               [delta 1] ⊢ phi 1, 
               [delta 2] ⊢ phi 2]
               ∴ 
               [delta 1, delta 2] ⊢ SeqList [phi 1 ./\. phi 2]

conditionalProof_1 :: AbsRulePlus (Sequent PItem) Pvar
conditionalProof_1 = [
                     [phi 1, delta 1] ⊢ phi 2]
                     ∴
                     [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

conditionalProof_2 :: AbsRulePlus (Sequent PItem) Pvar
conditionalProof_2 = [ [delta 1] ⊢ phi 2 ] ∴ [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

biconditionalProof_1 :: AbsRulePlus (Sequent PItem) Pvar
biconditionalProof_1 = [
                     [phi 1, delta 1] ⊢ phi 2,
                     [phi 2, delta 1] ⊢ phi 1]
                     ∴
                     [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]

biconditionalProof_2 :: AbsRulePlus (Sequent PItem) Pvar
biconditionalProof_2 = [
                     [delta 1] ⊢ phi 2,
                     [phi 2, delta 1] ⊢ phi 1]
                     ∴
                     [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]

biconditionalProof_3 :: AbsRulePlus (Sequent PItem) Pvar
biconditionalProof_3 = [
                     [phi 1, delta 1] ⊢ phi 2,
                     [delta 1] ⊢ phi 1]
                     ∴
                     [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]

biconditionalProof_4 :: AbsRulePlus (Sequent PItem) Pvar
biconditionalProof_4 = [
                     [delta 1] ⊢ phi 2,
                     [delta 1] ⊢ phi 1]
                     ∴
                     [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]

disjunctiveSyllogism_1 :: AbsRulePlus (Sequent PItem) Pvar
disjunctiveSyllogism_1 = [
                     [delta 1] ⊢ SeqList [phi 1 .\/. phi 2],
                     [phi 1, delta 2] ⊢ phi 3,
                     [phi 2, delta 3] ⊢ phi 3]
                     ∴
                     [delta 1, delta 2, delta 3] ⊢ SeqList [phi 3]

disjunctiveSyllogism_2 :: AbsRulePlus (Sequent PItem) Pvar
disjunctiveSyllogism_2 = [
                     [delta 1] ⊢ SeqList [phi 1 .\/. phi 2],
                     [delta 2] ⊢ phi 3,
                     [phi 2, delta 3] ⊢ phi 3]
                     ∴
                     [delta 1, delta 2, delta 3] ⊢ SeqList [phi 3]

disjunctiveSyllogism_3 :: AbsRulePlus (Sequent PItem) Pvar
disjunctiveSyllogism_3 = [
                     [delta 1] ⊢ SeqList [phi 1 .\/. phi 2],
                     [phi 1, delta 2] ⊢ phi 3,
                     [delta 3] ⊢ phi 3]
                     ∴
                     [delta 1, delta 2, delta 3] ⊢ SeqList [phi 3]

disjunctiveSyllogism_4 :: AbsRulePlus (Sequent PItem) Pvar
disjunctiveSyllogism_4 = [
                     [delta 1] ⊢ SeqList [phi 1 .\/. phi 2],
                     [delta 2] ⊢ phi 3,
                     [delta 3] ⊢ phi 3]
                     ∴
                     [delta 1, delta 2, delta 3] ⊢ SeqList [phi 3]

indirectDerivation_1_1 :: AbsRulePlus (Sequent PItem) Pvar
indirectDerivation_1_1 = [  
                         [ phi 1, delta 1] ⊢ phi 2,
                         [ phi 1, delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_2 :: AbsRulePlus (Sequent PItem) Pvar
indirectDerivation_1_2 = [  
                         [ delta 1] ⊢ phi 2,
                         [ phi 1, delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_3 :: AbsRulePlus (Sequent PItem) Pvar
indirectDerivation_1_3 = [  
                         [ phi 1, delta 1] ⊢ phi 2,
                         [ delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_4 :: AbsRulePlus (Sequent PItem) Pvar
indirectDerivation_1_4 = [  
                         [ delta 1] ⊢ phi 2,
                         [ delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_2_1 :: AbsRulePlus (Sequent PItem) Pvar
indirectDerivation_2_1 = [  
                         [ SeqList [lneg (phi 1)], delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ SeqList [lneg (phi 1)], delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_2 :: AbsRulePlus (Sequent PItem) Pvar
indirectDerivation_2_2 = [  
                         [ delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ SeqList [lneg (phi 1)], delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_3 :: AbsRulePlus (Sequent PItem) Pvar
indirectDerivation_2_3 = [  
                         [ SeqList [lneg (phi 1)], delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_4 :: AbsRulePlus (Sequent PItem) Pvar
indirectDerivation_2_4 = [  
                         [ delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

modusPonens_1 :: AbsRulePlus (Sequent PItem) Pvar
modusPonens_1 = [
                [delta 1] ⊢ phi 1, 
                [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]
                ]
                ∴ 
                [delta 1, delta 2] ⊢ phi 2

modusTolens_1 :: AbsRulePlus (Sequent PItem) Pvar
modusTolens_1 = [
                [delta 1] ⊢ SeqList [lneg (phi 2)],
                [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]
                ]
                ∴ 
                [delta 1, delta 2] ⊢ SeqList [lneg (phi 1)]

simplification_1 :: AbsRulePlus (Sequent PItem) Pvar
simplification_1 = [
                   [delta 1] ⊢ SeqList [phi 1 ./\. phi 2]
                   ]
                   ∴
                   [delta 1] ⊢ phi 1

simplification_2 :: AbsRulePlus (Sequent PItem) Pvar
simplification_2 = [ 
                   [delta 1] ⊢ SeqList [phi 1 ./\. phi 2]]
                   ∴
                   [delta 1] ⊢ phi 2

addition_1 :: AbsRulePlus (Sequent PItem) Pvar
addition_1 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [phi 1 .\/. phi 2]

addition_2 :: AbsRulePlus (Sequent PItem) Pvar
addition_2 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1]

modusTolleno_1 :: AbsRulePlus (Sequent PItem) Pvar
modusTolleno_1 = [ 
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1],
            [delta 2] ⊢ SeqList [lneg (phi 2)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 1]

modusTolleno_2 :: AbsRulePlus (Sequent PItem) Pvar
modusTolleno_2 = [ 
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1],
            [delta 2] ⊢ SeqList [lneg (phi 1)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 2]

doubleNegation_1 :: AbsRulePlus (Sequent PItem) Pvar
doubleNegation_1 = [ 
            [delta 1] ⊢ SeqList [lneg $ lneg $ phi 1]]
            ∴
            [delta 1] ⊢ phi 1

doubleNegation_2 :: AbsRulePlus (Sequent PItem) Pvar
doubleNegation_2 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [lneg $ lneg $ phi 1]

conditionalBiconditional_1 :: AbsRulePlus (Sequent PItem) Pvar
conditionalBiconditional_1 = [
            [delta 1] ⊢ SeqList [phi 2 .=>. phi 1],
            [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 1 .<=>. phi 2]

biconditionalConditional_1 :: AbsRulePlus (Sequent PItem) Pvar
biconditionalConditional_1 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]]
            ∴
            [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

biconditionalConditional_2 :: AbsRulePlus (Sequent PItem) Pvar
biconditionalConditional_2 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]]
            ∴
            [delta 1] ⊢ SeqList [phi 2 .=>. phi 1]

biconditionalEliminiation_1 :: AbsRulePlus (Sequent PItem) Pvar
biconditionalEliminiation_1 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ phi 1]
            ∴
            [delta 1, delta 2] ⊢ phi 2

biconditionalEliminiation_2 :: AbsRulePlus (Sequent PItem) Pvar
biconditionalEliminiation_2 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ phi 2]
            ∴
            [delta 1, delta 2] ⊢ phi 1

interchangeEquivalents_1 :: AbsRulePlus (Sequent PItem) Pvar
interchangeEquivalents_1 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ SeqList [propContext 1 $ phi 1]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [propContext 1 $ phi 2]

interchangeEquivalents_2 :: AbsRulePlus (Sequent PItem) Pvar
interchangeEquivalents_2 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ SeqList [propContext 1 $ phi 2]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [propContext 1 $ phi 1]

repetition :: AbsRulePlus (Sequent PItem) Pvar
repetition = [[delta 1] ⊢ phi 1] ∴  [delta 1] ⊢ phi 1

--------------------------------------------------------
--Ambiguous Rules
--------------------------------------------------------

adjunction_s :: AmbiguousRulePlus (Sequent PItem) Pvar
adjunction_s = AmbiguousRulePlus (premisePermutationsPlus adjunction_1) "ADJ"

conjunctionIntroduction_s :: AmbiguousRulePlus (Sequent PItem) Pvar
conjunctionIntroduction_s = adjunction_s{ruleNamePlus="AI"}

conditionalProof_s :: AmbiguousRulePlus (Sequent PItem) Pvar
conditionalProof_s = AmbiguousRulePlus [conditionalProof_1, conditionalProof_2] "CD"

conditionalIntroduction_s :: AmbiguousRulePlus (Sequent PItem) Pvar
conditionalIntroduction_s = conditionalProof_s{ruleNamePlus="CI"}

disjunctiveSyllogism_s :: AmbiguousRulePlus (Sequent PItem) Pvar
disjunctiveSyllogism_s = AmbiguousRulePlus ( premisePermutationsPlus disjunctiveSyllogism_1
                                          ++ premisePermutationsPlus disjunctiveSyllogism_2 
                                          ++ premisePermutationsPlus disjunctiveSyllogism_3
                                          ++ premisePermutationsPlus disjunctiveSyllogism_4) "DS"

disjunctionElimination_s :: AmbiguousRulePlus (Sequent PItem) Pvar
disjunctionElimination_s = disjunctiveSyllogism_s{ruleNamePlus="DE"} 
                          

modusPonens_s :: AmbiguousRulePlus (Sequent PItem) Pvar
modusPonens_s = AmbiguousRulePlus (premisePermutationsPlus modusPonens_1) "MP"

conditionalElimination_s :: AmbiguousRulePlus (Sequent PItem) Pvar 
conditionalElimination_s = modusPonens_s{ruleNamePlus= "CE"}

modusTolens_s :: AmbiguousRulePlus (Sequent PItem) Pvar
modusTolens_s = AmbiguousRulePlus (premisePermutationsPlus modusTolens_1) "MT"

simplification_s :: AmbiguousRulePlus (Sequent PItem) Pvar
simplification_s = AmbiguousRulePlus [simplification_1, simplification_2] "S"

conjunctionElimination_s :: AmbiguousRulePlus (Sequent PItem) Pvar
conjunctionElimination_s = simplification_s{ruleNamePlus="AE"}

addition_s :: AmbiguousRulePlus (Sequent PItem) Pvar
addition_s = AmbiguousRulePlus [addition_1,addition_2] "ADD"

disjunctionIntroduction_s :: AmbiguousRulePlus (Sequent PItem) Pvar
disjunctionIntroduction_s = addition_s{ruleNamePlus="DE"}

doubleNegation_s :: AmbiguousRulePlus (Sequent PItem) Pvar
doubleNegation_s = AmbiguousRulePlus [doubleNegation_1,doubleNegation_2] "DN"

modusTolleno_s :: AmbiguousRulePlus (Sequent PItem) Pvar
modusTolleno_s = AmbiguousRulePlus (premisePermutationsPlus modusTolleno_1 
                                   ++ premisePermutationsPlus modusTolleno_2) "MTP"

conditionalBiconditional_s :: AmbiguousRulePlus (Sequent PItem) Pvar
conditionalBiconditional_s = AmbiguousRulePlus (premisePermutationsPlus conditionalBiconditional_1) "CB"

biconditionalConditional_s :: AmbiguousRulePlus (Sequent PItem) Pvar
biconditionalConditional_s = AmbiguousRulePlus [biconditionalConditional_2, biconditionalConditional_1] "BC"

biconditionalIntroduction_s :: AmbiguousRulePlus (Sequent PItem) Pvar
biconditionalIntroduction_s = AmbiguousRulePlus (  premisePermutationsPlus biconditionalProof_1
                                                ++ premisePermutationsPlus biconditionalProof_2
                                                ++ premisePermutationsPlus biconditionalProof_3
                                                ++ premisePermutationsPlus biconditionalProof_4)
                                                "BI"

biconditionalEliminiation_s :: AmbiguousRulePlus (Sequent PItem) Pvar
biconditionalEliminiation_s = AmbiguousRulePlus (premisePermutationsPlus biconditionalEliminiation_1 
                                                ++ premisePermutationsPlus biconditionalEliminiation_2) "BE"

interchangeEquivalents_s :: AmbiguousRulePlus (Sequent PItem) Pvar
interchangeEquivalents_s = AmbiguousRulePlus (premisePermutationsPlus interchangeEquivalents_1 
                                             ++ premisePermutationsPlus interchangeEquivalents_2) "IE"

indirectDerivation_s :: AmbiguousRulePlus (Sequent PItem) Pvar
indirectDerivation_s = AmbiguousRulePlus  (premisePermutationsPlus indirectDerivation_1_1 ++
                                       premisePermutationsPlus indirectDerivation_1_2 ++
                                       premisePermutationsPlus indirectDerivation_1_3 ++
                                       premisePermutationsPlus indirectDerivation_1_4 ++
                                       premisePermutationsPlus indirectDerivation_2_1 ++ 
                                       premisePermutationsPlus indirectDerivation_2_2 ++
                                       premisePermutationsPlus indirectDerivation_2_3 ++
                                       premisePermutationsPlus indirectDerivation_2_4) "ID"

negationIntroduction_s :: AmbiguousRulePlus (Sequent PItem) Pvar
negationIntroduction_s = AmbiguousRulePlus (  premisePermutationsPlus indirectDerivation_1_1
                                           ++ premisePermutationsPlus indirectDerivation_1_2
                                           ++ premisePermutationsPlus indirectDerivation_1_3
                                           ++ premisePermutationsPlus indirectDerivation_1_4 ) "NI"

negationElimination_s:: AmbiguousRulePlus (Sequent PItem) Pvar
negationElimination_s = AmbiguousRulePlus [ indirectDerivation_2_1
                                          , indirectDerivation_2_2
                                          , indirectDerivation_2_3
                                          , indirectDerivation_2_4] "NE"

directDerivation_s :: AmbiguousRulePlus (Sequent PItem) Pvar
directDerivation_s = AmbiguousRulePlus [directDerivation] "DD"

repetition_s :: AmbiguousRulePlus (Sequent PItem) Pvar
repetition_s = AmbiguousRulePlus [repetition] "R"

--------------------------------------------------------
--Rule Sets
--------------------------------------------------------
--we'll then do a lookup by rule-name, on the basis of the rule cited in
--justification

classicalSLruleSet :: Set.Set (AmbiguousRulePlus (Sequent PItem) Pvar)
classicalSLruleSet = Set.fromList [
                            adjunction_s, 
                            conditionalProof_s, 
                            disjunctiveSyllogism_s,
                            modusPonens_s,
                            modusTolens_s,
                            modusTolleno_s,
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

logicBookSDruleSet :: Set.Set (AmbiguousRulePlus (Sequent PItem) Pvar)
logicBookSDruleSet = Set.fromList [ conjunctionIntroduction_s
                                  , conjunctionElimination_s
                                  , disjunctionIntroduction_s
                                  , disjunctionElimination_s
                                  , conditionalIntroduction_s
                                  , conditionalElimination_s
                                  , negationIntroduction_s
                                  , negationElimination_s
                                  , biconditionalIntroduction_s
                                  , biconditionalEliminiation_s
                                  , repetition_s
                                  ]

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
