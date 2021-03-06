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
import Carnap.Calculi.ClassicalSententialLogic1
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
                                      S_ConstantSchematicTermBuilder (ConstantTermVar "τ_1") -> Nothing
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

--------------------------------------------------------
--2. Ambiguous Rules
--------------------------------------------------------

universalInstantiation_s :: AmbiguousRulePlus (Sequent QItem) Qvar
universalInstantiation_s = AmbiguousRulePlus [universalInstantiation] "UI"

existentialGeneralization_s :: AmbiguousRulePlus (Sequent QItem) Qvar
existentialGeneralization_s = AmbiguousRulePlus [existentialGeneralization] "EG"

leibnizLaw_s :: AmbiguousRulePlus (Sequent QItem) Qvar
leibnizLaw_s = AmbiguousRulePlus [leibnizLaw_1, leibnizLaw_2] "LL"

reflexivity_s :: AmbiguousRulePlus (Sequent QItem) Qvar
reflexivity_s = AmbiguousRulePlus [reflexivity] "RF"

universalDerivation_s :: AmbiguousRulePlus (Sequent QItem) Qvar
universalDerivation_s = AmbiguousRulePlus [universalDerivation] "UD"

existentialDerivation_s :: AmbiguousRulePlus (Sequent QItem) Qvar
existentialDerivation_s = AmbiguousRulePlus [existentialDerivation] "ED"

--------------------------------------------------------
--Rule Sets
--------------------------------------------------------

--we'll then do a lookup by rule-name, on the basis of the rule cited in
--justification
prettyClassicalQLruleSet :: Set.Set (AmbiguousRulePlus (Sequent QItem) Qvar)
prettyClassicalQLruleSet = Set.fromList [
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
                            leibnizLaw_s,
                            reflexivity_s,
                            repetition_s,
                            existentialGeneralization_s,
                            universalInstantiation_s,
                            universalDerivation_s,
                            existentialDerivation_s
                            ]

classicalQLruleSet :: Set.Set (AmbiguousRulePlus (Sequent QItem) Qvar)
classicalQLruleSet = Set.map permuteAll prettyClassicalQLruleSet

prettyLogicBookSDruleSetQL :: Set.Set (AmbiguousRulePlus (Sequent QItem) Qvar)
prettyLogicBookSDruleSetQL = Set.fromList [ conjunctionIntroduction_s
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

logicBookSDruleSetQL :: Set.Set (AmbiguousRulePlus (Sequent QItem) Qvar)
logicBookSDruleSetQL = Set.map permuteAll prettyLogicBookSDruleSetQL 

--------------------------------------------------------
--Rule Lists
--------------------------------------------------------

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
classicalRules "RF"  = Just (Left 0)
classicalRules "R"  = Just (Left 1)
classicalRules _     = Nothing
