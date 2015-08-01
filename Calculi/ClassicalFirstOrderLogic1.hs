{-#LANGUAGE MultiParamTypeClasses, GADTs, TypeSynonymInstances, OverlappingInstances, FlexibleInstances, FlexibleContexts #-}
module Carnap.Calculi.ClassicalFirstOrderLogic1 where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractDerivationDataTypes
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching
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

directDerivation :: AbsRulePlus (Sequent QItem)
directDerivation = [[delta 1] ⊢ phi 1] ∴ [delta 1] ⊢ phi 1 

adjunction_1 :: AbsRulePlus (Sequent QItem)
adjunction_1 = [
               [delta 1] ⊢ phi 1, 
               [delta 2] ⊢ phi 2]
               ∴ 
               [delta 1, delta 2] ⊢ SeqList [phi 1 ./\. phi 2]

conditionalProof_1 :: AbsRulePlus (Sequent QItem)
conditionalProof_1 = [
                     [phi 1, delta 1] ⊢ phi 2]
                     ∴
                     [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

conditionalProof_2 :: AbsRulePlus (Sequent QItem)
conditionalProof_2 = [ [delta 1] ⊢ phi 2 ] ∴ [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

indirectDerivation_1_1 :: AbsRulePlus (Sequent QItem)
indirectDerivation_1_1 = [  
                         [ phi 1, delta 1] ⊢ phi 2,
                         [ phi 1, delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_2 :: AbsRulePlus (Sequent QItem)
indirectDerivation_1_2 = [  
                         [ delta 1] ⊢ phi 2,
                         [ phi 1, delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_3 :: AbsRulePlus (Sequent QItem)
indirectDerivation_1_3 = [  
                         [ phi 1, delta 1] ⊢ phi 2,
                         [ delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_4 :: AbsRulePlus (Sequent QItem)
indirectDerivation_1_4 = [  
                         [ delta 1] ⊢ phi 2,
                         [ delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_2_1 :: AbsRulePlus (Sequent QItem)
indirectDerivation_2_1 = [  
                         [ SeqList [lneg (phi 1)], delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ SeqList [lneg (phi 1)], delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_2 :: AbsRulePlus (Sequent QItem)
indirectDerivation_2_2 = [  
                         [ delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ SeqList [lneg (phi 1)], delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_3 :: AbsRulePlus (Sequent QItem)
indirectDerivation_2_3 = [  
                         [ SeqList [lneg (phi 1)], delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_4 :: AbsRulePlus (Sequent QItem)
indirectDerivation_2_4 = [  
                         [ delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

modusPonens_1 :: AbsRulePlus (Sequent QItem)
modusPonens_1 = [
                [delta 1] ⊢ phi 1, 
                [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]
                ]
                ∴ 
                [delta 1, delta 2] ⊢ phi 2

modusTolens_1 :: AbsRulePlus (Sequent QItem)
modusTolens_1 = [
                [delta 1] ⊢ SeqList [lneg (phi 2)],
                [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]
                ]
                ∴ 
                [delta 1, delta 2] ⊢ SeqList [lneg (phi 1)]

simplification_1 :: AbsRulePlus (Sequent QItem)
simplification_1 = [
                   [delta 1] ⊢ SeqList [phi 1 ./\. phi 2]
                   ]
                   ∴
                   [delta 1] ⊢ phi 1

simplification_2 :: AbsRulePlus (Sequent QItem)
simplification_2 = [ 
                   [delta 1] ⊢ SeqList [phi 1 ./\. phi 2]]
                   ∴
                   [delta 1] ⊢ phi 2

addition_1 :: AbsRulePlus (Sequent QItem)
addition_1 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [phi 1 .\/. phi 2]

addition_2 :: AbsRulePlus (Sequent QItem)
addition_2 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1]

modusTolleno_1 :: AbsRulePlus (Sequent QItem)
modusTolleno_1 = [ 
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1],
            [delta 2] ⊢ SeqList [lneg (phi 2)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 1]

modusTolleno_2 :: AbsRulePlus (Sequent QItem)
modusTolleno_2 = [ 
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1],
            [delta 2] ⊢ SeqList [lneg (phi 1)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 2]

doubleNegation_1 :: AbsRulePlus (Sequent QItem)
doubleNegation_1 = [ 
            [delta 1] ⊢ SeqList [lneg $ lneg $ phi 1]]
            ∴
            [delta 1] ⊢ phi 1

doubleNegation_2 :: AbsRulePlus (Sequent QItem)
doubleNegation_2 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [lneg $ lneg $ phi 1]

conditionalBiconditional_1 :: AbsRulePlus (Sequent QItem)
conditionalBiconditional_1 = [
            [delta 1] ⊢ SeqList [phi 2 .=>. phi 1],
            [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 1 .<=>. phi 2]

biconditionalConditional_1 :: AbsRulePlus (Sequent QItem)
biconditionalConditional_1 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]]
            ∴
            [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

biconditionalConditional_2 :: AbsRulePlus (Sequent QItem)
biconditionalConditional_2 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]]
            ∴
            [delta 1] ⊢ SeqList [phi 2 .=>. phi 1]

interchangeEquivalents_1 :: AbsRulePlus (Sequent QItem)
interchangeEquivalents_1 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ SeqList [propContext 1 $ phi 1]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [propContext 1 $ phi 2]

interchangeEquivalents_2 :: AbsRulePlus (Sequent QItem)
interchangeEquivalents_2 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ SeqList [propContext 1 $ phi 2]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [propContext 1 $ phi 1]

universalInstantiation :: AbsRulePlus (Sequent QItem)
universalInstantiation = [
            [delta 1] ⊢ SeqList [ub $ \x -> phi1 1 (liftToScheme x)]]
            ∴
            [delta 1] ⊢ SeqList [phi1 1 (tau 1)]

universalDerivation :: AbsRulePlus (Sequent QItem)
universalDerivation = [
            [delta 1] ⊢ SeqList [phi1 1 (tau 1)]]
            ∴
            [delta 1] ⊢ SeqList [ub $ \x -> phi1 1 (liftToScheme x)]
            `withCheck`
            upperEigenvariableCondition

existentialDerivation :: AbsRulePlus (Sequent QItem)
existentialDerivation = [
            [SeqList [phi1 1 (tau 1)], delta 1] ⊢ phi 1,
            [delta 2] ⊢ SeqList [eb $ \x -> phi1 1 (liftToScheme x)]]
            ∴
            [delta 1, delta 2] ⊢ phi 1
            `withCheck`
            upperEigenvariableCondition

--XXX:going to need to modify this (or the definition of constants for
--terms) when we get to function symbols, since
--tau has to actually be a constant symbol, and the count might be driven
--down by just removing a constant symbol that's inside a function symbol.
upperEigenvariableCondition r = if (length . nub . constants $ Rules.premises r) > (length . nub . constants $ Rules.conclusion r) 
                                    then Nothing 
                                    else Just $ "violation of the Eigenvariable conditions: there are " 
                                        ++ show (length . nub . constants $ Rules.premises r) 
                                        ++ " constants in the premises and "
                                        ++ show (length . nub . constants $ Rules.conclusion r) 
                                        ++ " constants in the conclusion"

--XXX:going to need to modify this (or the definition of constants for
--terms) when we get to function symbols, since
--tau has to actually be a constant symbol, and the count might be driven
--down by just removing a constant symbol that's inside a function symbol.
lowerEigenvariableCondition r = if (length . nub . constants $ Rules.premises r) < (length . nub . constants $ Rules.conclusion r) 
                                    then Nothing 
                                    else Just "violation of the Eigenvariable conditions"

existentialGeneralization :: AbsRulePlus (Sequent QItem)
existentialGeneralization = [
            [delta 1] ⊢ SeqList [phi1 1 (tau 1)]]
            ∴
            [delta 1] ⊢ SeqList [eb $ \x -> phi1 1 (liftToScheme x)]

leibnizLaw_1 :: AbsRulePlus (Sequent QItem)
leibnizLaw_1 = [
               [delta 1] ⊢ SeqList [equals (tau 1) (tau 2)],
               [delta 2] ⊢ SeqList [phi1 1 (tau 1)]]
               ∴
               [delta 1, delta 2] ⊢ SeqList [phi1 1 (tau 2)]

leibnizLaw_2 :: AbsRulePlus (Sequent QItem)
leibnizLaw_2 = [
               [delta 1] ⊢ SeqList [equals (tau 1) (tau 2)],
               [delta 2] ⊢ SeqList [phi1 1 (tau 2)]]
               ∴
               [delta 1, delta 2] ⊢ SeqList [phi1 1 (tau 1)]

adjunction_s :: AmbiguousRulePlus (Sequent QItem)
adjunction_s = AmbiguousRulePlus (premisePermutationsPlus adjunction_1) "ADJ"

conditionalProof_s :: AmbiguousRulePlus (Sequent QItem)
conditionalProof_s = AmbiguousRulePlus [conditionalProof_1, conditionalProof_2] "CD"

modusPonens_s :: AmbiguousRulePlus (Sequent QItem)
modusPonens_s = AmbiguousRulePlus (premisePermutationsPlus modusPonens_1) "MP"

modusTolens_s :: AmbiguousRulePlus (Sequent QItem)
modusTolens_s = AmbiguousRulePlus (premisePermutationsPlus modusTolens_1) "MT"

simplification_s :: AmbiguousRulePlus (Sequent QItem)
simplification_s = AmbiguousRulePlus [simplification_1, simplification_2] "S"

addition_s :: AmbiguousRulePlus (Sequent QItem)
addition_s = AmbiguousRulePlus [addition_1,addition_2] "ADD"

doubleNegation_s :: AmbiguousRulePlus (Sequent QItem)
doubleNegation_s = AmbiguousRulePlus [doubleNegation_1,doubleNegation_2] "DN"

modusTolleno_s :: AmbiguousRulePlus (Sequent QItem)
modusTolleno_s = AmbiguousRulePlus (premisePermutationsPlus modusTolleno_1 ++ premisePermutationsPlus modusTolleno_2) "MTP"

conditionalBiconditional_s :: AmbiguousRulePlus (Sequent QItem)
conditionalBiconditional_s = AmbiguousRulePlus (premisePermutationsPlus conditionalBiconditional_1) "CB"

biconditionalConditional_s :: AmbiguousRulePlus (Sequent QItem)
biconditionalConditional_s = AmbiguousRulePlus [biconditionalConditional_2, biconditionalConditional_1] "BC"

universalInstantiation_s :: AmbiguousRulePlus (Sequent QItem)
universalInstantiation_s = AmbiguousRulePlus [universalInstantiation] "UI"

existentialGeneralization_s :: AmbiguousRulePlus (Sequent QItem)
existentialGeneralization_s = AmbiguousRulePlus [existentialGeneralization] "EG"

leibnizLaw_s :: AmbiguousRulePlus (Sequent QItem)
leibnizLaw_s = AmbiguousRulePlus (premisePermutationsPlus leibnizLaw_1 ++ premisePermutationsPlus leibnizLaw_2) "LL"

interchangeEquivalents_s :: AmbiguousRulePlus (Sequent QItem)
interchangeEquivalents_s = AmbiguousRulePlus (premisePermutationsPlus interchangeEquivalents_1 ++ premisePermutationsPlus interchangeEquivalents_2) "IE"

indirectDerivation_s :: AmbiguousRulePlus (Sequent QItem)
indirectDerivation_s = AmbiguousRulePlus  (premisePermutationsPlus indirectDerivation_1_1 ++
                                       premisePermutationsPlus indirectDerivation_1_2 ++
                                       premisePermutationsPlus indirectDerivation_1_3 ++
                                       premisePermutationsPlus indirectDerivation_1_4 ++
                                       premisePermutationsPlus indirectDerivation_2_1 ++ 
                                       premisePermutationsPlus indirectDerivation_2_2 ++
                                       premisePermutationsPlus indirectDerivation_2_3 ++
                                       premisePermutationsPlus indirectDerivation_2_4) "ID"

directDerivation_s :: AmbiguousRulePlus (Sequent QItem)
directDerivation_s = AmbiguousRulePlus [directDerivation] "DD"

universalDerivation_s :: AmbiguousRulePlus (Sequent QItem)
universalDerivation_s = AmbiguousRulePlus [universalDerivation] "UD"

existentialDerivation_s :: AmbiguousRulePlus (Sequent QItem)
existentialDerivation_s = AmbiguousRulePlus (premisePermutationsPlus existentialDerivation) "ED"

--we'll then do a lookup by rule-name, on the basis of the rule cited in
--justification
classicalQLruleSet :: Set.Set (AmbiguousRulePlus (Sequent QItem))
classicalQLruleSet = Set.fromList [
                            adjunction_s, 
                            conditionalProof_s, 
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
                            existentialGeneralization_s,
                            universalInstantiation_s,
                            universalDerivation_s,
                            existentialDerivation_s
                            ]

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
classicalRules "CD"  = Just (Right 1)
classicalRules "ID"  = Just (Right 2)
classicalRules "ADJ" = Just (Left 2)
classicalRules "ADD" = Just (Left 1)
classicalRules "MTP" = Just (Left 2)
classicalRules "S"   = Just (Left 1)
classicalRules "DN"  = Just (Left 1)
classicalRules _     = Nothing


