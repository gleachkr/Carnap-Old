{-#LANGUAGE MultiParamTypeClasses, GADTs, TypeSynonymInstances, OverlappingInstances, FlexibleInstances, FlexibleContexts #-}

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
module Carnap.Calculi.ClassicalFirstOrderLogic1 where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractDerivationDataTypes
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching
import Carnap.Core.Unification.HigherOrderMatching
import Carnap.Languages.FirstOrder.QuantifiedLanguage
import Carnap.Languages.Util.LanguageClasses
import Carnap.Core.Data.Rules as Rules
import Data.Set as Set
import Data.List (nub)

instance GatherConstants (Sequent QItem) where
        constants s = constants (premises s) ++ constants (Rules.conclusion s)

instance GatherConstants (AbsRule (Sequent QItem)) where
        constants s = constants (premises s) ++ constants (Rules.conclusion s)

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

directDerivation :: AbsRulePlus (Sequent QItem) Qvar
directDerivation = [[delta 1] ⊢ phi 1] ∴ [delta 1] ⊢ phi 1 

adjunction_1 :: AbsRulePlus (Sequent QItem) Qvar
adjunction_1 = [
               [delta 1] ⊢ phi 1, 
               [delta 2] ⊢ phi 2]
               ∴ 
               [delta 1, delta 2] ⊢ SeqList [phi 1 ./\. phi 2]

conditionalProof_1 :: AbsRulePlus (Sequent QItem) Qvar
conditionalProof_1 = [
                     [phi 1, delta 1] ⊢ phi 2]
                     ∴
                     [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

conditionalProof_2 :: AbsRulePlus (Sequent QItem) Qvar
conditionalProof_2 = [ [delta 1] ⊢ phi 2 ] ∴ [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

disjunctiveSyllogism_1 :: AbsRulePlus (Sequent QItem) Qvar
disjunctiveSyllogism_1 = [
                     [delta 1] ⊢ SeqList [phi 1 .\/. phi 2],
                     [phi 1, delta 2] ⊢ phi 3,
                     [phi 2, delta 3] ⊢ phi 3]
                     ∴
                     [delta 1, delta 2, delta 3] ⊢ SeqList [phi 3]

disjunctiveSyllogism_2 :: AbsRulePlus (Sequent QItem) Qvar
disjunctiveSyllogism_2 = [
                     [delta 1] ⊢ SeqList [phi 1 .\/. phi 2],
                     [delta 2] ⊢ phi 3,
                     [phi 2, delta 3] ⊢ phi 3]
                     ∴
                     [delta 1, delta 2, delta 3] ⊢ SeqList [phi 3]

disjunctiveSyllogism_3 :: AbsRulePlus (Sequent QItem) Qvar
disjunctiveSyllogism_3 = [
                     [delta 1] ⊢ SeqList [phi 1 .\/. phi 2],
                     [phi 1, delta 2] ⊢ phi 3,
                     [delta 3] ⊢ phi 3]
                     ∴
                     [delta 1, delta 2, delta 3] ⊢ SeqList [phi 3]

disjunctiveSyllogism_4 :: AbsRulePlus (Sequent QItem) Qvar
disjunctiveSyllogism_4 = [
                     [delta 1] ⊢ SeqList [phi 1 .\/. phi 2],
                     [delta 2] ⊢ phi 3,
                     [delta 3] ⊢ phi 3]
                     ∴
                     [delta 1, delta 2, delta 3] ⊢ SeqList [phi 3]

indirectDerivation_1_1 :: AbsRulePlus (Sequent QItem) Qvar
indirectDerivation_1_1 = [  
                         [ phi 1, delta 1] ⊢ phi 2,
                         [ phi 1, delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_2 :: AbsRulePlus (Sequent QItem) Qvar
indirectDerivation_1_2 = [  
                         [ delta 1] ⊢ phi 2,
                         [ phi 1, delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_3 :: AbsRulePlus (Sequent QItem) Qvar
indirectDerivation_1_3 = [  
                         [ phi 1, delta 1] ⊢ phi 2,
                         [ delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_2_1 :: AbsRulePlus (Sequent QItem) Qvar
indirectDerivation_2_1 = [  
                         [ SeqList [lneg (phi 1)], delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ SeqList [lneg (phi 1)], delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_2 :: AbsRulePlus (Sequent QItem) Qvar
indirectDerivation_2_2 = [  
                         [ delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ SeqList [lneg (phi 1)], delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_3 :: AbsRulePlus (Sequent QItem) Qvar
indirectDerivation_2_3 = [  
                         [ SeqList [lneg (phi 1)], delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_4 :: AbsRulePlus (Sequent QItem) Qvar
indirectDerivation_2_4 = [  
                         [ delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

modusPonens_1 :: AbsRulePlus (Sequent QItem) Qvar
modusPonens_1 = [
                [delta 1] ⊢ phi 1, 
                [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]
                ]
                ∴ 
                [delta 1, delta 2] ⊢ phi 2

modusTolens_1 :: AbsRulePlus (Sequent QItem) Qvar
modusTolens_1 = [
                [delta 1] ⊢ SeqList [lneg (phi 2)],
                [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]
                ]
                ∴ 
                [delta 1, delta 2] ⊢ SeqList [lneg (phi 1)]

simplification_1 :: AbsRulePlus (Sequent QItem) Qvar
simplification_1 = [
                   [delta 1] ⊢ SeqList [phi 1 ./\. phi 2]
                   ]
                   ∴
                   [delta 1] ⊢ phi 1

simplification_2 :: AbsRulePlus (Sequent QItem) Qvar
simplification_2 = [ 
                   [delta 1] ⊢ SeqList [phi 1 ./\. phi 2]]
                   ∴
                   [delta 1] ⊢ phi 2

addition_1 :: AbsRulePlus (Sequent QItem) Qvar
addition_1 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [phi 1 .\/. phi 2]

addition_2 :: AbsRulePlus (Sequent QItem) Qvar
addition_2 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1]

modusTolleno_1 :: AbsRulePlus (Sequent QItem) Qvar
modusTolleno_1 = [ 
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1],
            [delta 2] ⊢ SeqList [lneg (phi 2)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 1]

modusTolleno_2 :: AbsRulePlus (Sequent QItem) Qvar
modusTolleno_2 = [ 
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1],
            [delta 2] ⊢ SeqList [lneg (phi 1)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 2]

doubleNegation_1 :: AbsRulePlus (Sequent QItem) Qvar
doubleNegation_1 = [ 
            [delta 1] ⊢ SeqList [lneg $ lneg $ phi 1]]
            ∴
            [delta 1] ⊢ phi 1

doubleNegation_2 :: AbsRulePlus (Sequent QItem) Qvar
doubleNegation_2 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [lneg $ lneg $ phi 1]

conditionalBiconditional_1 :: AbsRulePlus (Sequent QItem) Qvar
conditionalBiconditional_1 = [
            [delta 1] ⊢ SeqList [phi 2 .=>. phi 1],
            [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 1 .<=>. phi 2]

biconditionalConditional_1 :: AbsRulePlus (Sequent QItem) Qvar
biconditionalConditional_1 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]]
            ∴
            [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

biconditionalConditional_2 :: AbsRulePlus (Sequent QItem) Qvar
biconditionalConditional_2 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]]
            ∴
            [delta 1] ⊢ SeqList [phi 2 .=>. phi 1]

interchangeEquivalents_1 :: AbsRulePlus (Sequent QItem) Qvar
interchangeEquivalents_1 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ SeqList [propContext 1 $ phi 1]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [propContext 1 $ phi 2]

interchangeEquivalents_2 :: AbsRulePlus (Sequent QItem) Qvar
interchangeEquivalents_2 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ SeqList [propContext 1 $ phi 2]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [propContext 1 $ phi 1]

universalInstantiation :: AbsRulePlus (Sequent QItem) Qvar
universalInstantiation = [
            [delta 1] ⊢ SeqList [ub "x" $ \x -> phi1 1 (liftToScheme x)]]
            ∴
            [delta 1] ⊢ SeqList [phi1 1 (tau 1)]

universalDerivation :: AbsRulePlus (Sequent QItem) Qvar
universalDerivation = [
            [delta 1] ⊢ SeqList [phi1 1 (tau 1)]]
            ∴
            [delta 1] ⊢ SeqList [ub "x" $ \x -> phi1 1 (liftToScheme x)]
            `withCheck`
            upperEigenvariableCondition

existentialDerivation :: AbsRulePlus (Sequent QItem) Qvar
existentialDerivation = [
            [SeqList [phi1 1 (tau 1)], delta 1] ⊢ phi 1,
            [delta 2] ⊢ SeqList [eb "x" $ \x -> phi1 1 (liftToScheme x)]]
            ∴
            [delta 1, delta 2] ⊢ phi 1
            `withCheck`
            upperEigenvariableCondition

upperEigenvariableCondition :: AbsRule (Sequent QItem) -> Subst Qvar -> Maybe String
upperEigenvariableCondition r s = case apply s (tau 1 :: FirstOrderTermScheme) of
                                      S_ConstantTermBuilder _ -> if (length . nub . constants $ Rules.premises r) > (length . nub . constants $ Rules.conclusion r) 
                                                                    then Nothing 
                                                                    else Just $ "violation of the Eigenvariable conditions: there are " 
                                                                        ++ show (length . nub . constants $ Rules.premises r) 
                                                                        ++ " constants in the premises and "
                                                                        ++ show (length . nub . constants $ Rules.conclusion r) 
                                                                        ++ " constants in the conclusion"
                                      _ -> Just "you appear to be generalizing on something other than a constant symbol"

existentialGeneralization :: AbsRulePlus (Sequent QItem) Qvar
existentialGeneralization = [
            [delta 1] ⊢ SeqList [phi1 1 (tau 1)]]
            ∴
            [delta 1] ⊢ SeqList [eb "x" $ \x -> phi1 1 (liftToScheme x)]

leibnizLaw_1 :: AbsRulePlus (Sequent QItem) Qvar
leibnizLaw_1 = [
               [delta 1] ⊢ SeqList [equals (tau 1) (tau 2)],
               [delta 2] ⊢ SeqList [phi1 1 (tau 1)]]
               ∴
               [delta 1, delta 2] ⊢ SeqList [phi1 1 (tau 2)]

leibnizLaw_2 :: AbsRulePlus (Sequent QItem) Qvar
leibnizLaw_2 = [
               [delta 1] ⊢ SeqList [tau 1 `equals` tau 2],
               [delta 2] ⊢ SeqList [phi1 1 (tau 2)]]
               ∴
               [delta 1, delta 2] ⊢ SeqList [phi1 1 (tau 1)]

reflexivity :: AbsRulePlus (Sequent QItem) Qvar
reflexivity = [] ∴ [] ⊢ SeqList [tau 1 `equals` tau 1]

adjunction_s :: AmbiguousRulePlus (Sequent QItem) Qvar
adjunction_s = AmbiguousRulePlus [adjunction_1] "ADJ"

conditionalProof_s :: AmbiguousRulePlus (Sequent QItem) Qvar
conditionalProof_s = AmbiguousRulePlus [conditionalProof_1, conditionalProof_2] "CD"

disjunctiveSyllogism_s :: AmbiguousRulePlus (Sequent QItem) Qvar
disjunctiveSyllogism_s = AmbiguousRulePlus [disjunctiveSyllogism_1, disjunctiveSyllogism_2, disjunctiveSyllogism_3, disjunctiveSyllogism_4] "DS"

modusPonens_s :: AmbiguousRulePlus (Sequent QItem) Qvar
modusPonens_s = AmbiguousRulePlus [modusPonens_1] "MP"

modusTolens_s :: AmbiguousRulePlus (Sequent QItem) Qvar
modusTolens_s = AmbiguousRulePlus [modusTolens_1] "MT"

simplification_s :: AmbiguousRulePlus (Sequent QItem) Qvar
simplification_s = AmbiguousRulePlus [simplification_1, simplification_2] "S"

addition_s :: AmbiguousRulePlus (Sequent QItem) Qvar
addition_s = AmbiguousRulePlus [addition_1,addition_2] "ADD"

doubleNegation_s :: AmbiguousRulePlus (Sequent QItem) Qvar
doubleNegation_s = AmbiguousRulePlus [doubleNegation_1,doubleNegation_2] "DN"

modusTolleno_s :: AmbiguousRulePlus (Sequent QItem) Qvar
modusTolleno_s = AmbiguousRulePlus [modusTolleno_1, modusTolleno_2] "MTP"

conditionalBiconditional_s :: AmbiguousRulePlus (Sequent QItem) Qvar
conditionalBiconditional_s = AmbiguousRulePlus [conditionalBiconditional_1] "CB"

biconditionalConditional_s :: AmbiguousRulePlus (Sequent QItem) Qvar
biconditionalConditional_s = AmbiguousRulePlus [biconditionalConditional_2, biconditionalConditional_1] "BC"

universalInstantiation_s :: AmbiguousRulePlus (Sequent QItem) Qvar
universalInstantiation_s = AmbiguousRulePlus [universalInstantiation] "UI"

existentialGeneralization_s :: AmbiguousRulePlus (Sequent QItem) Qvar
existentialGeneralization_s = AmbiguousRulePlus [existentialGeneralization] "EG"

leibnizLaw_s :: AmbiguousRulePlus (Sequent QItem) Qvar
leibnizLaw_s = AmbiguousRulePlus [leibnizLaw_1, leibnizLaw_2] "LL"

reflexivity_s :: AmbiguousRulePlus (Sequent QItem) Qvar
reflexivity_s = AmbiguousRulePlus [reflexivity] "R"

interchangeEquivalents_s :: AmbiguousRulePlus (Sequent QItem) Qvar
interchangeEquivalents_s = AmbiguousRulePlus [interchangeEquivalents_1, interchangeEquivalents_2] "IE"

indirectDerivation_s :: AmbiguousRulePlus (Sequent QItem) Qvar
indirectDerivation_s = AmbiguousRulePlus [indirectDerivation_1_1,
                                         indirectDerivation_1_2,
                                         indirectDerivation_1_3,
                                         indirectDerivation_2_1,
                                         indirectDerivation_2_2,
                                         indirectDerivation_2_3,
                                         indirectDerivation_2_4] "ID"

directDerivation_s :: AmbiguousRulePlus (Sequent QItem) Qvar
directDerivation_s = AmbiguousRulePlus [directDerivation] "DD"

universalDerivation_s :: AmbiguousRulePlus (Sequent QItem) Qvar
universalDerivation_s = AmbiguousRulePlus [universalDerivation] "UD"

existentialDerivation_s :: AmbiguousRulePlus (Sequent QItem) Qvar
existentialDerivation_s = AmbiguousRulePlus [existentialDerivation] "ED"

--we'll then do a lookup by rule-name, on the basis of the rule cited in
--justification
prettyClassicalQLruleSet :: Set.Set (AmbiguousRulePlus (Sequent QItem) Qvar)
prettyClassicalQLruleSet = Set.fromList [
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
                            leibnizLaw_s,
                            reflexivity_s,
                            existentialGeneralization_s,
                            universalInstantiation_s,
                            universalDerivation_s,
                            existentialDerivation_s
                            ]

permuteAll :: AmbiguousRulePlus (Sequent QItem) Qvar -> AmbiguousRulePlus (Sequent QItem) Qvar
permuteAll (AmbiguousRulePlus l n) = (`AmbiguousRulePlus` n) $ concatMap premisePermutationsPlus l
                                                               
classicalQLruleSet :: Set.Set (AmbiguousRulePlus (Sequent QItem) Qvar)
classicalQLruleSet = Set.map permuteAll prettyClassicalQLruleSet

--A list of rules, which are Left if they're for direct inferences, and
--Right if they're for closing subproofs.
classicalRules :: RulesAndArity
classicalRules "IE"  = Just (Left 2)
classicalRules "CB"  = Just (Left 2)
classicalRules "LL"  = Just (Left 2)
classicalRules "EG"  = Just (Left 1)
classicalRules "UI"  = Just (Left 1)
classicalRules "BC"  = Just (Left 1)
classicalRules "MP"  = Just (Left 2)
classicalRules "MT"  = Just (Left 2)
classicalRules "DD"  = Just (Right 1)
classicalRules "UD"  = Just (Right 1)
classicalRules "ED"  = Just (Right 2)
classicalRules "DS"  = Just (Right 3)
classicalRules "CD"  = Just (Right 1)
classicalRules "ID"  = Just (Right 2)
classicalRules "ADJ" = Just (Left 2)
classicalRules "ADD" = Just (Left 1)
classicalRules "MTP" = Just (Left 2)
classicalRules "S"   = Just (Left 1)
classicalRules "DN"  = Just (Left 1)
classicalRules "R"   = Just (Left 0)
classicalRules _     = Nothing


