module ClassicalSententialLogic where

import AbstractDerivationDataTypes
import AbstractSyntaxMultiUnification
import PropositionalLanguage
import Rules
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

adjunction_1 :: AbsRule (Sequent PItem)
adjunction_1 = [
               [delta 1] ⊢ phi_ 1, 
               [delta 2] ⊢ phi_ 2]
               ∴ 
               [delta 1, delta 2] ⊢ SeqList [sland (phi 1) (phi 2)]

adjunction_2 :: AbsRule (Sequent PItem)
adjunction_2 = [
               [delta 1] ⊢ phi_ 2, 
               [delta 2] ⊢ phi_ 1
               ]
               ∴ 
               [delta 1, delta 2] ⊢ SeqList [sland (phi 1) (phi 2)]

conditionalProof_1 :: AbsRule (Sequent PItem)
conditionalProof_1 = [ [delta 1] ⊢ phi_ 2 ] ∴ [delta 1] ⊢ SeqList [slif (phi 1) (phi 2)]

conditionalProof_2 :: AbsRule (Sequent PItem)
conditionalProof_2 = [
                     [phi_ 1, delta 1] ⊢ phi_ 2]
                     ∴
                     [delta 1] ⊢ SeqList [slif (phi 1) (phi 2)]

indirectDerivation_1_1 :: AbsRule (Sequent PItem)
indirectDerivation_1_1 = [  
                         [ phi_ 1, delta 1] ⊢ phi_ 2,
                         [ phi_ 1, delta 2] ⊢ SeqList [slneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [slneg (phi 1)]

indirectDerivation_1_2 :: AbsRule (Sequent PItem)
indirectDerivation_1_2 = [  
                         [ delta 1] ⊢ phi_ 2,
                         [ phi_ 1, delta 2] ⊢ SeqList [slneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [slneg (phi 1)]

indirectDerivation_1_3 :: AbsRule (Sequent PItem)
indirectDerivation_1_3 = [  
                         [ phi_ 1, delta 1] ⊢ phi_ 2,
                         [ delta 2] ⊢ SeqList [slneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [slneg (phi 1)]

indirectDerivation_1_4 :: AbsRule (Sequent PItem)
indirectDerivation_1_4 = [  
                         [ delta 1] ⊢ phi_ 2,
                         [ delta 2] ⊢ SeqList [slneg (phi 2)]
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [slneg (phi 1)]

indirectDerivation_2_1 :: AbsRule (Sequent PItem)
indirectDerivation_2_1 = [  
                         [ phi_ 1, delta 2] ⊢ SeqList [slneg (phi 2)],
                         [ phi_ 1, delta 1] ⊢ phi_ 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [slneg (phi 1)]

indirectDerivation_2_2 :: AbsRule (Sequent PItem)
indirectDerivation_2_2 = [  
                         [ delta 2] ⊢ SeqList [slneg (phi 2)],
                         [ phi_ 1, delta 1] ⊢ phi_ 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [slneg (phi 1)]

indirectDerivation_2_3 :: AbsRule (Sequent PItem)
indirectDerivation_2_3 = [  
                         [ phi_ 1, delta 2] ⊢ SeqList [slneg (phi 2)],
                         [ delta 1] ⊢ phi_ 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [slneg (phi 1)]

indirectDerivation_2_4 :: AbsRule (Sequent PItem)
indirectDerivation_2_4 = [  
                         [ delta 2] ⊢ SeqList [slneg (phi 2)],
                         [ delta 1] ⊢ phi_ 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ SeqList [slneg (phi 1)]

indirectDerivation_3_1 :: AbsRule (Sequent PItem)
indirectDerivation_3_1 = [  
                         [ SeqList [slneg (phi 1)], delta 2] ⊢ SeqList [slneg (phi 2)],
                         [ SeqList [slneg (phi 1)], delta 1] ⊢ phi_ 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi_ 1

indirectDerivation_3_2 :: AbsRule (Sequent PItem)
indirectDerivation_3_2 = [  
                         [ delta 2] ⊢ SeqList [slneg (phi 2)],
                         [ SeqList [slneg (phi 1)], delta 1] ⊢ phi_ 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi_ 1

indirectDerivation_3_3 :: AbsRule (Sequent PItem)
indirectDerivation_3_3 = [  
                         [ SeqList [slneg (phi 1)], delta 2] ⊢ SeqList [slneg (phi 2)],
                         [ delta 1] ⊢ phi_ 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi_ 1

indirectDerivation_3_4 :: AbsRule (Sequent PItem)
indirectDerivation_3_4 = [  
                         [ delta 2] ⊢ SeqList [slneg (phi 2)],
                         [ delta 1] ⊢ phi_ 2
                         ]
                         ∴ 
                         [delta 1,delta 2] ⊢ phi_ 1

modusPonens_1 :: AbsRule (Sequent PItem)
modusPonens_1 = [
                [delta 1] ⊢ phi_ 1, 
                [delta 2] ⊢ SeqList [slif (phi 1) (phi 2)]
                ]
                ∴ 
                [delta 1, delta 2] ⊢ phi_ 2

modusPonens_2 :: AbsRule (Sequent PItem)
modusPonens_2 = [
                [delta 1] ⊢ SeqList [slif (phi 1) (phi 2)],
                [delta 2] ⊢ phi_ 1
                ]
                ∴ 
                [delta 1, delta 2] ⊢ phi_ 2

simplification_1 :: AbsRule (Sequent PItem)
simplification_1 = [
                   [delta 1] ⊢ SeqList [sland (phi 1) (phi 2)]
                   ]
                   ∴
                   [delta 1] ⊢ phi_ 1

simplification_2 :: AbsRule (Sequent PItem)
simplification_2 = [ 
                   [delta 1] ⊢ SeqList [sland (phi 1) (phi 2)]]
                   ∴
                   [delta 1] ⊢ phi_ 2

addition_1 :: AbsRule (Sequent PItem)
addition_1 = [ 
            [delta 1] ⊢ phi_ 1]
            ∴
            [delta 1] ⊢ SeqList [slor (phi 1) (phi 2)]

addition_2 :: AbsRule (Sequent PItem)
addition_2 = [ 
            [delta 1] ⊢ phi_ 1]
            ∴
            [delta 1] ⊢ SeqList [slor (phi 2) (phi 1)]

modusTolleno_1 :: AbsRule (Sequent PItem)
modusTolleno_1 = [ 
            [delta 1] ⊢ SeqList [slor (phi 2) (phi 1)],
            [delta 2] ⊢ SeqList [slneg (phi 1)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 2]

modusTolleno_2 :: AbsRule (Sequent PItem)
modusTolleno_2 = [ 
            [delta 1] ⊢ SeqList [slor (phi 2) (phi 1)],
            [delta 2] ⊢ SeqList [slneg (phi 1)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 2]

modusTolleno_3 :: AbsRule (Sequent PItem)
modusTolleno_3 = [ 
            [delta 2] ⊢ SeqList [slneg (phi 1)],
            [delta 1] ⊢ SeqList [slor (phi 2) (phi 1)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [phi 2]

modusTolleno_4 :: AbsRule (Sequent PItem)
modusTolleno_4 = [ 
            [delta 1] ⊢ SeqList [slor (phi 2) (phi 1)],
            [delta 2] ⊢ SeqList [slneg (phi 1)]]
            ∴
            [delta 1, delta 2] ⊢ SeqList [(phi 2)]

doubleNegation_1 :: AbsRule (Sequent PItem)
doubleNegation_1 = [ 
            [delta 1] ⊢ SeqList [slneg $ slneg $ phi 1]]
            ∴
            [delta 1] ⊢ phi_ 1

doubleNegation_2 :: AbsRule (Sequent PItem)
doubleNegation_2 = [ 
            [delta 1] ⊢ phi_ 1]
            ∴
            [delta 1] ⊢ SeqList [slneg $ slneg $ phi 1]

adjunction_s :: AmbiguousRule (Sequent PItem)
adjunction_s = AmbiguousRule (Set.fromList [adjunction_1, adjunction_2]) "ADJ"

conditionalProof_s :: AmbiguousRule (Sequent PItem)
conditionalProof_s = AmbiguousRule (Set.fromList [conditionalProof_1, conditionalProof_2]) "CD"

modusPonens_s :: AmbiguousRule (Sequent PItem)
modusPonens_s = AmbiguousRule (Set.fromList [modusPonens_1, modusPonens_2]) "MP"

simplification_s :: AmbiguousRule (Sequent PItem)
simplification_s = AmbiguousRule (Set.fromList [simplification_1, simplification_2]) "S"

addition_s :: AmbiguousRule (Sequent PItem)
addition_s = AmbiguousRule (Set.fromList [addition_1,addition_2]) "ADD"

doubleNegation_s :: AmbiguousRule (Sequent PItem)
doubleNegation_s = AmbiguousRule (Set.fromList [doubleNegation_1,doubleNegation_2]) "DN"

modusTolleno_s :: AmbiguousRule (Sequent PItem)
modusTolleno_s = AmbiguousRule (Set.fromList 
                    [modusTolleno_1,modusTolleno_2, modusTolleno_3, modusTolleno_4]) "MTP"

indirectDerivation_s :: AmbiguousRule (Sequent PItem)
indirectDerivation_s = AmbiguousRule (Set.fromList [indirectDerivation_1_1, 
                                                    indirectDerivation_1_2,
                                                    indirectDerivation_1_3,
                                                    indirectDerivation_1_4,
                                                    indirectDerivation_2_1,
                                                    indirectDerivation_2_2,
                                                    indirectDerivation_2_3,
                                                    indirectDerivation_2_4,
                                                    indirectDerivation_3_1,
                                                    indirectDerivation_3_2,
                                                    indirectDerivation_3_3,
                                                    indirectDerivation_3_4]) "ID"

--we'll then do a lookup by rule-name, on the basis of the rule cited in
--justification
classicalSLruleSet :: Set.Set (AmbiguousRule (Sequent PItem))
classicalSLruleSet = Set.fromList [
                            adjunction_s, 
                            conditionalProof_s, 
                            modusPonens_s,
                            modusTolleno_s,
                            simplification_s,
                            addition_s,
                            indirectDerivation_s]

--A list of rules, which are Left if they're for direct inferences, and
--Right if they're for closing subproofs.
classicalRules :: RulesAndArity
classicalRules "MP"  = Just (Left 2)
classicalRules "CD"  = Just (Right 1)
classicalRules "ID"  = Just (Right 2)
classicalRules "ADJ" = Just (Left 2)
classicalRules "ADD" = Just (Left 1)
classicalRules "MTP" = Just (Left 2)
classicalRules "S"   = Just (Left 1)
classicalRules "DN"   = Just (Left 1)
classicalRules _     = Nothing
