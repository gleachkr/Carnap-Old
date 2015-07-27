module Carnap.Calculi.ClassicalSententialLogic1 where

import Carnap.Core.Data.AbstractDerivationDataTypes
--import Carnap.Core.Data.AbstractSyntaxMultiUnification()
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

directDerivation :: AbsRule (Sequent PItem)
directDerivation = [[delta 1] ⊢ phi 1] ∴ [delta 1] ⊢ phi 1 

adjunction_1 :: AbsRule (Sequent PItem)
adjunction_1 = [
               [delta 1] ⊢ phi 1, 
               [delta 2] ⊢ phi 2]
               ∴ 
               [delta 1, delta 2] ⊢ SeqList [phi 1 ./\. phi 2]

conditionalProof_1 :: AbsRule (Sequent PItem)
conditionalProof_1 = [
                     [phi 1, delta 1] ⊢ phi 2]
                     ∴
                     [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

conditionalProof_2 :: AbsRule (Sequent PItem)
conditionalProof_2 = [ [delta 1] ⊢ phi 2 ] ∴ [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

indirectDerivation_1_1 :: AbsRule (Sequent PItem)
indirectDerivation_1_1 = [  
                         [ phi 1, delta 1] ⊢ phi 2,
                         [ phi 1, delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_2 :: AbsRule (Sequent PItem)
indirectDerivation_1_2 = [  
                         [ delta 1] ⊢ phi 2,
                         [ phi 1, delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_3 :: AbsRule (Sequent PItem)
indirectDerivation_1_3 = [  
                         [ phi 1, delta 1] ⊢ phi 2,
                         [ delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_1_4 :: AbsRule (Sequent PItem)
indirectDerivation_1_4 = [  
                         [ delta 1] ⊢ phi 2,
                         [ delta 2] ⊢ SeqList [lneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [lneg (phi 1)]

indirectDerivation_2_1 :: AbsRule (Sequent PItem)
indirectDerivation_2_1 = [  
                         [ SeqList [lneg (phi 1)], delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ SeqList [lneg (phi 1)], delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_2 :: AbsRule (Sequent PItem)
indirectDerivation_2_2 = [  
                         [ delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ SeqList [lneg (phi 1)], delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_3 :: AbsRule (Sequent PItem)
indirectDerivation_2_3 = [  
                         [ SeqList [lneg (phi 1)], delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

indirectDerivation_2_4 :: AbsRule (Sequent PItem)
indirectDerivation_2_4 = [  
                         [ delta 2] ⊢ SeqList [lneg (phi 2)],
                         [ delta 1] ⊢ phi 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi 1

modusPonens_1 :: AbsRule (Sequent PItem)
modusPonens_1 = [
                [delta 1] ⊢ phi 1, 
                [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]
                ]
                ∴ 
                [delta 1, delta 2] ⊢ phi 2

modusTolens_1 :: AbsRule (Sequent PItem)
modusTolens_1 = [
                [delta 1] ⊢ SeqList [lneg (phi 2)],
                [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]
                ]
                ∴ 
                [delta 1, delta 2] ⊢ SeqList [lneg (phi 1)]

simplification_1 :: AbsRule (Sequent PItem)
simplification_1 = [
                   [delta 1] ⊢ SeqList [phi 1 ./\. phi 2]
                   ]
                   ∴
                   [delta 1] ⊢ phi 1

simplification_2 :: AbsRule (Sequent PItem)
simplification_2 = [ 
                   [delta 1] ⊢ SeqList [phi 1 ./\. phi 2]]
                   ∴
                   [delta 1] ⊢ phi 2

addition_1 :: AbsRule (Sequent PItem)
addition_1 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [phi 1 .\/. phi 2]

addition_2 :: AbsRule (Sequent PItem)
addition_2 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1]

modusTolleno_1 :: AbsRule (Sequent PItem)
modusTolleno_1 = [ 
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1],
            [delta 2] ⊢ SeqList [lneg (phi 2)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 1]

modusTolleno_2 :: AbsRule (Sequent PItem)
modusTolleno_2 = [ 
            [delta 1] ⊢ SeqList [phi 2 .\/. phi 1],
            [delta 2] ⊢ SeqList [lneg (phi 1)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 2]

doubleNegation_1 :: AbsRule (Sequent PItem)
doubleNegation_1 = [ 
            [delta 1] ⊢ SeqList [lneg $ lneg $ phi 1]]
            ∴
            [delta 1] ⊢ phi 1

doubleNegation_2 :: AbsRule (Sequent PItem)
doubleNegation_2 = [ 
            [delta 1] ⊢ phi 1]
            ∴
            [delta 1] ⊢ SeqList [lneg $ lneg $ phi 1]

conditionalBiconditional_1 :: AbsRule (Sequent PItem)
conditionalBiconditional_1 = [
            [delta 1] ⊢ SeqList [phi 2 .=>. phi 1],
            [delta 2] ⊢ SeqList [phi 1 .=>. phi 2]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 1 .<=>. phi 2]

biconditionalConditional_1 :: AbsRule (Sequent PItem)
biconditionalConditional_1 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]]
            ∴
            [delta 1] ⊢ SeqList [phi 1 .=>. phi 2]

biconditionalConditional_2 :: AbsRule (Sequent PItem)
biconditionalConditional_2 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2]]
            ∴
            [delta 1] ⊢ SeqList [phi 2 .=>. phi 1]

interchangeEquivalents_1 :: AbsRule (Sequent PItem)
interchangeEquivalents_1 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ SeqList [propContext 1 $ phi 1]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [propContext 1 $ phi 2]

interchangeEquivalents_2 :: AbsRule (Sequent PItem)
interchangeEquivalents_2 = [
            [delta 1] ⊢ SeqList [phi 1 .<=>. phi 2],
            [delta 2] ⊢ SeqList [propContext 1 $ phi 2]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [propContext 1 $ phi 1]

adjunction_s :: AmbiguousRule (Sequent PItem)
adjunction_s = AmbiguousRule (premisePermutations adjunction_1) "ADJ"

conditionalProof_s :: AmbiguousRule (Sequent PItem)
conditionalProof_s = AmbiguousRule [conditionalProof_1, conditionalProof_2] "CD"

modusPonens_s :: AmbiguousRule (Sequent PItem)
modusPonens_s = AmbiguousRule (premisePermutations modusPonens_1) "MP"

modusTolens_s :: AmbiguousRule (Sequent PItem)
modusTolens_s = AmbiguousRule (premisePermutations modusTolens_1) "MT"

simplification_s :: AmbiguousRule (Sequent PItem)
simplification_s = AmbiguousRule [simplification_1, simplification_2] "S"

addition_s :: AmbiguousRule (Sequent PItem)
addition_s = AmbiguousRule [addition_1,addition_2] "ADD"

doubleNegation_s :: AmbiguousRule (Sequent PItem)
doubleNegation_s = AmbiguousRule [doubleNegation_1,doubleNegation_2] "DN"

modusTolleno_s :: AmbiguousRule (Sequent PItem)
modusTolleno_s = AmbiguousRule (premisePermutations modusTolleno_1 ++ premisePermutations modusTolleno_2) "MTP"

conditionalBiconditional_s :: AmbiguousRule (Sequent PItem)
conditionalBiconditional_s = AmbiguousRule (premisePermutations conditionalBiconditional_1) "CB"

biconditionalConditional_s :: AmbiguousRule (Sequent PItem)
biconditionalConditional_s = AmbiguousRule [biconditionalConditional_2, biconditionalConditional_1] "BC"

interchangeEquivalents_s :: AmbiguousRule (Sequent PItem)
interchangeEquivalents_s = AmbiguousRule (premisePermutations interchangeEquivalents_1 ++ premisePermutations interchangeEquivalents_2) "IE"

indirectDerivation_s :: AmbiguousRule (Sequent PItem)
indirectDerivation_s = AmbiguousRule  (premisePermutations indirectDerivation_1_1 ++
                                       premisePermutations indirectDerivation_1_2 ++
                                       premisePermutations indirectDerivation_1_3 ++
                                       premisePermutations indirectDerivation_1_4 ++
                                       premisePermutations indirectDerivation_2_1 ++ 
                                       premisePermutations indirectDerivation_2_2 ++
                                       premisePermutations indirectDerivation_2_3 ++
                                       premisePermutations indirectDerivation_2_4) "ID"

directDerivation_s :: AmbiguousRule (Sequent PItem)
directDerivation_s = AmbiguousRule [directDerivation] "DD"

--we'll then do a lookup by rule-name, on the basis of the rule cited in
--justification
classicalSLruleSet :: Set.Set (AmbiguousRule (Sequent PItem))
classicalSLruleSet = Set.fromList [
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
                            interchangeEquivalents_s
                            ]

--A list of rules, which are Left if they're for direct inferences, and
--Right if they're for closing subproofs.
classicalRules :: RulesAndArity
classicalRules "IE"  = Just (Left 2)
classicalRules "CB"  = Just (Left 2)
classicalRules "BC"  = Just (Left 1)
classicalRules "MP"  = Just (Left 2)
classicalRules "MT"  = Just (Left 2)
classicalRules "DD"  = Just (Right 1)
classicalRules "CD"  = Just (Right 1)
classicalRules "ID"  = Just (Right 2)
classicalRules "ADJ" = Just (Left 2)
classicalRules "ADD" = Just (Left 1)
classicalRules "MTP" = Just (Left 2)
classicalRules "S"   = Just (Left 1)
classicalRules "DN"  = Just (Left 1)
classicalRules _     = Nothing
