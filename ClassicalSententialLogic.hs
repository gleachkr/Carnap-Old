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

conditionalProof_1 = [ [delta 1] ⊢ phi_ 2 ] ∴ [delta 1] ⊢ SeqList [slif (phi 1) (phi 2)]

conditionalProof_2 = [
                     [phi_ 1, delta 1] ⊢ phi_ 2]
                     ∴
                     [delta 1] ⊢ SeqList [slif (phi 1) (phi 2)]

modusPonens_1 = [
                [delta 1] ⊢ phi_ 1, 
                [delta 2] ⊢ SeqList [slif (phi 1) (phi 2)]
                ]
                ∴ 
                [delta 1, delta 2] ⊢ phi_ 2

modusPonens_2 = [
                [delta 1] ⊢ SeqList [slif (phi 1) (phi 2)],
                [delta 2] ⊢ phi_ 1
                ]
                ∴ 
                [delta 1, delta 2] ⊢ phi_ 2

adjunction_s :: AmbiguousRule (Sequent PItem)
adjunction_s = AmbiguousRule (Set.fromList [adjunction_1, adjunction_2]) "ADJ"

conditionalProof_s :: AmbiguousRule (Sequent PItem)
conditionalProof_s = AmbiguousRule (Set.fromList [conditionalProof_1, conditionalProof_2]) "CP"

modusPonens_s :: AmbiguousRule (Sequent PItem)
modusPonens_s = AmbiguousRule (Set.fromList [modusPonens_1, modusPonens_2]) "MP"

--we'll then do a lookup by rule-name, on the basis of the rule cited in
--justification
classicalSLruleSet :: Set.Set (AmbiguousRule (Sequent PItem))
classicalSLruleSet = Set.fromList [adjunction_s, conditionalProof_s, modusPonens_s]

--A list of rules, which are Left if they're for direct inferences, and
--Right if they're for closing subproofs.
classicalRules :: RulesAndArity
classicalRules "MP"  = Just (Left 2)
classicalRules "ADJ" = Just (Left 2)
classicalRules "CP"  = Just (Right 1)
classicalRules _     = Nothing

