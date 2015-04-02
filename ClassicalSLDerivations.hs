{-#LANGUAGE MultiParamTypeClasses, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module ClassicalSLDerivations where

import AbstractDerivationDataTypes
import AbstractSyntaxMultiUnification
import AbstractDerivationMultiUnification()
import PropositionalDerivations
import PropositionalLanguage
import AbstractSyntaxDataTypes
import MultiUnification
import Rules

import Data.Set as Set

--This module houses a function that checks a derivation for validity in
--a system that currently contains MP, ADJ, Pr, and Conditional Proof (and
--which will, in the near future, contain rules that are complete for
--classical SL)

--------------------------------------------------------
--1 Rule Checkers
--------------------------------------------------------

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

conditionalProof_s = AmbiguousRule (Set.fromList [conditionalProof_1, conditionalProof_2]) "CP"

modusPonens_s = AmbiguousRule (Set.fromList [modusPonens_1, modusPonens_2]) "MP"

--we'll then do a lookup by rule-name, on the basis of the rule cited in
--justification
ruleSet :: Set.Set (AmbiguousRule (Sequent PItem))
ruleSet = Set.fromList [adjunction_s, conditionalProof_s, modusPonens_s]

--A list of rules, which are Left if they're for direct inferences, and
--Right if they're for closing subproofs.
classicalRules :: RulesAndArity
classicalRules "MP"  = Just (Left 2)
classicalRules "ADJ" = Just (Left 2)
classicalRules "CP"  = Just (Right 1)
classicalRules _     = Nothing

lookupRule :: String -> Set.Set (AmbiguousRule (Sequent PItem)) -> AmbiguousRule (Sequent PItem)
lookupRule rule set = findMin $ Set.filter (\r -> ruleName r == rule) set 

--converts a Psequent to a Sequent of PItems. The premises are in one large
--SeqList, thus: [phi_1 .. phi_n] ⊢ [chi]
toSchematicSequent :: Psequent -> Sequent PItem
toSchematicSequent s = Sequent [SeqList $ Prelude.map liftToScheme $ premises s] (SeqList [liftToScheme $ Rules.conclusion s])

--positions n PItems for matching
freeSome :: Int -> Sequent PItem -> Sequent PItem
freeSome n (Sequent ((SeqList fs):etc) c) = Sequent ((SeqList $ take n fs):(SeqList $ drop n fs):etc) c
freeSome _ x = x

--gets the size of an inital SeqList
blockSize :: Sequent PItem -> Int
blockSize (Sequent ((SeqList fs):_) _) = length fs

--aligns s1 sequent for matching with s2, where s1 is assumed to be of the
--form [phi_1 .. phi_n] ⊢ [chi]. The premises of s2 are assumed to contain
--at most one seqvar.
align s1 s2 = case s2 of 
                Sequent ((SeqList _):_) _ -> freeSome (blockSize s2) s1
                Sequent [SeqVar _] _ -> s1

--flattens the premises of a sequent, for alignment; 
flatten ((SeqList fs):etc) = fs ++ flatten etc
flatten _ = []

seek p fs = if elem p fs then  p:(Prelude.filter (\x -> not (x == p)) fs) else fs

clean (Sequent ps c) = Sequent [SeqList $ flatten ps] c

maybeSeekandClean mp s = case mp of 
                            Just p -> case clean s of
                                          Sequent [SeqList fs] c -> Sequent [SeqList (seek p fs)] c
                                          _ -> clean s
                            Nothing -> clean s

--converts some schematic sequents, and a statement they're being used to support,
--to a putative rule-instance, which we can then check for unification. It
--incorporates a number of interchange and contraction inferences, to try
--to get the premise sequents into shape.
toInstanceOfAbs :: AbsRule (Sequent PItem) -> [Sequent PItem] -> PropositionalFormula -> AbsRule (Sequent PItem)
toInstanceOfAbs rule ps c = AbsRule (zipWith interchange ps (premises rule))
                                 (Sequent (premises $ Rules.conclusion rule) $ SeqList [sc])
                        where sc = liftToScheme c
                              conc (Sequent _ (SeqList [x])) = x
                              initialSub = case unify (conc $ Rules.conclusion rule) sc of
                                            Left s -> s
                                            Right _ -> []
                              firstOf p = case premises p of 
                                            (SeqList fs):_ -> Just $ multiApply initialSub $ head fs
                                            _ -> Nothing 
                              interchange x y = align (maybeSeekandClean (firstOf y) x) y


checkWithAmbig :: AmbiguousRule (Sequent PItem) -> [Sequent PItem] -> PropositionalFormula -> Maybe (Sequent PItem)
checkWithAmbig rule ps c = if Set.null matches then Nothing
                                           else case unify theMatch theInstance of
                                                    Left sub -> Just $ multiApply sub (Rules.conclusion theInstance)
                                                    _ -> Nothing
                        where match r = case unify (toInstanceOfAbs r ps c) r of 
                                            Left _  -> True
                                            Right _ -> False
                              matches = Set.filter match (ruleVersions rule)
                              theMatch = findMax matches
                              --XXX: there's an issue here when we have
                              --more than one rule-matching, as happens
                              --e.g. with the different forms of CP.
                              --Ultimately, we're going to want to be able
                              --to control the priorities of our AbsRules
                              --directly; probably adding an Int for
                              --a precidence number would be enough
                              theInstance = toInstanceOfAbs theMatch ps c

derivationProves :: PropositionalJudgement -> Maybe (Sequent PItem)
derivationProves (Line p Premise) = Just $ Sequent [SeqList [liftToScheme p]] ( SeqList [liftToScheme p])
derivationProves (Line c (Inference s l)) = do
        l' <- mapM derivationProves l 
        checkWithAmbig (lookupRule s ruleSet) l' c
