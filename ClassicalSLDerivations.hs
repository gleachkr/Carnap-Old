{-#LANGUAGE MultiParamTypeClasses, EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module ClassicalSLDerivations where

import AbstractDerivationDataTypes
import AbstractSyntaxMultiUnification
import AbstractDerivationMultiUnification
import PropositionalDerivations
import PropositionalLanguage
import AbstractSyntaxDataTypes
import MultiUnification
import Rules

import Data.List (nub)
import Data.Set as Set

--This module houses a function that checks a derivation for validity in
--a system that currently contains MP, ADJ, Pr, and Conditional Proof (and
--which will, in the near future, contain rules that are complete for
--classical SL)

--------------------------------------------------------
--1 Rule Checkers
--------------------------------------------------------

--------------------------------------------------------
--1.0 Simple Rule Checkers
--------------------------------------------------------

--these functions check whether some formulas actually support a concusion.
--They'd probably be made obsolete by a more general unification-based
--derivation-checker.

modusPonens :: PropositionalFormula -> PropositionalFormula -> PropositionalFormula -> Bool
modusPonens x@(BinaryConnect If y z) w@(BinaryConnect If s t) c = (s == x && c == t ) || (y == w && c == z)
modusPonens x (BinaryConnect If s t) c = s == x && c == t 
modusPonens (BinaryConnect If y z) w c = y == w && c == z
modusPonens  _ _ _ = False

adjunction :: PropositionalFormula -> PropositionalFormula -> PropositionalFormula -> Bool
adjunction x y z = z == (BinaryConnect And x y) || z == (BinaryConnect And y x)

--the case of a conditional proof is included derivationProves. It would
--probably be cleaner to either fold all of these into that, or to factor
--them all out in a uniform way.

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

delta :: Int -> PItem
delta n = SeqVar (SideForms $ "delta_" ++ show n)

phi_ n = SeqList [phi n]

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

derivationProvesU :: PropositionalJudgement -> Maybe (Sequent PItem)
derivationProvesU (Line p Premise) = Just $ Sequent [SeqList [liftToScheme p]] ( SeqList [liftToScheme p])
derivationProvesU (Line c (Inference s l)) = do
        l' <- mapM derivationProvesU l 
        checkWithAmbig (lookupRule s ruleSet) l' c

--------------------------------------------------------
--2. Checking Derivations
--------------------------------------------------------

--------------------------------------------------------
--2.1 Simple Checker
--------------------------------------------------------
--this is a simple prototype checker, which will be made obsolete by the
--advent of MultiUnification. these functions are used to actually
--determine whether a judgement (a big tree of formulas and their
--justifications) supports some argument

--This converts a given propositionalJudgement into an argument
--XXX: maybe it'd be more elegant to fold modusPonens and other conditions in
--here as guards.

derivationProves :: PropositionalJudgement -> Maybe Psequent
derivationProves (Line p Premise) = Just $ Sequent [p] p
derivationProves (Line c (Inference "MP" [l1@(Line p1 _), l2@(Line p2 _)])) = 
        if modusPonens p1 p2 c 
        then do arg1 <- derivationProves l1
                arg2 <- derivationProves l2
                return $ Sequent (unitePremises arg1 arg2) c
        else Nothing
derivationProves (Line c (Inference "ADJ" [l1@(Line p1 _), l2@(Line p2 _)])) = 
        if adjunction p1 p2 c 
        then do arg1 <- derivationProves l1
                arg2 <- derivationProves l2
                return $ Sequent (unitePremises arg1 arg2) c
        else Nothing
derivationProves (Line c@(BinaryConnect If antec conseq) (Inference "CP" [l])) = 
        case derivationProves l of
                Just (Sequent [] conc) -> if conc == conseq then Just (Sequent [] c) else Nothing
                Just (Sequent prems conc) -> guardEx (nub prems) conc
                _ -> Nothing
        where guardEx prems@(ass:etc) conc
                | ass == antec && conseq == conc = Just $ Sequent etc c
                | conseq == conc = Just $ Sequent prems c
                --we don't want to strictly require that 
                --assumptions are used when constructing 
                --a conditional proof.
                | otherwise = Nothing
derivationProves _ = Nothing

--------------------------------------------------------
--Helper functions for Derivations
--------------------------------------------------------

--a helper function for combining the premises of two arguments. At the
--moment, repeated premises are dropped. This could be modified if we wanted
--to think about substructural logics.
unitePremises :: Psequent -> Psequent -> [PropositionalFormula]
unitePremises s1 s2 = nub $ premises s1 ++ premises s2

--These are helper functions for building derivations with monadic 'do'
--syntax.

mpRule :: a -> PropositionalJudgement -> PropositionalJudgement -> Derivation (Judgement a PropJustification)
mpRule x y z = assert $ Line x $ Inference "MP" [y, z]

adRule :: a -> PropositionalJudgement -> PropositionalJudgement -> Derivation (Judgement a PropJustification)
adRule x y z = assert $ Line x $ Inference "Adj" [y, z]

--finishes a subderivation, returning the attached derivation type, to feed
--into a show line
cdRule :: PropositionalJudgement -> Derivation (PropositionalJudgement,
                                               PropositionalJudgement ->
                                               PropJustification)
cdRule y = return (y, (\x -> Inference "CP" [x]))
