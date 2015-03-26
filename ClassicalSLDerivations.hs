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

adjunction_1 :: AbsRule (Sequent PItem)
adjunction_1 = [
               [delta 1] ⊢ SeqList [phi 1], 
               [delta 2] ⊢ SeqList [phi 2]]
               ∴ 
               [delta 1, delta 2] ⊢ SeqList [sland (phi 1) (phi 2)]

adjunction_s :: AmbiguousRule (Sequent PItem)
adjunction_s = AmbiguousRule (Set.singleton adjunction_1) "ADJ"

--we'll then do a lookup by rule-name, on the basis of the rule cited in
--justification
ruleSet :: Set.Set (AmbiguousRule (Sequent PItem))
ruleSet = Set.singleton adjunction_s


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

--a helper function for combining the premises of two arguments. At the
--moment, repeated premises are dropped. This could be modified if we wanted
--to think about substructural logics.
unitePremises :: Psequent -> Psequent -> [PropositionalFormula]
unitePremises s1 s2 = nub $ premises s1 ++ premises s2

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
