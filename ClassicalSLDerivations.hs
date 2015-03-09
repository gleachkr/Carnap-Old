{-#LANGUAGE MultiParamTypeClasses, EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module ClassicalSLDerivations where

import AbstractDerivationDataTypes
import PropositionalDerivations
import PropositionalLanguage
import AbstractSyntaxDataTypes
import Unification
import Rules

import Data.List (nub)
import Data.Map as Map
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

type PSubstError = UnificationError SSymbol PSSequent
type RSubstError = UnificationError SSymbol AbsPSequentRule

--XXX:Redundancy. These are nearly verbatim copies of composite unify and
--unifyChildren. One abstraction should cover all these instances.

unifySSequentList :: [(PSSequent,PSSequent)] -> Either PSubst PSubstError
unifySSequentList ((s1,s2):ss) = case compositeUnify s1 s2 of
  Left  sub -> (unifySSequentList $ pmap (apply sub) ss) .<. (sub ...) .>. (\e -> SubError e s1 s2)
  Right err -> Right (SubError err s1 s2)
unifySSequentList [] = Left Map.empty

unifyAbsPSequentRule :: AbsPSequentRule -> AbsPSequentRule -> Either PSubst RSubstError
unifyAbsPSequentRule r1@(AbsRule ps1 c1) r2@(AbsRule ps2 c2) = case match ps1 ps2 of
                        Just parts -> case (unifySSequentList $ (c1,c2):parts) of
                                          Left s -> Left s
                                          Right _ -> Right $ UnableToUnify r1 r2
                        Nothing -> Right $ UnableToUnify r1 r2

andIntroduction1 :: AbsPSequentRule
andIntroduction1 = AbsRule [SSequent [] (phi 1), SSequent [] (phi 2)] (SSequent [] $ s_land (phi 1) (phi 2))

andIntroduction2 :: AbsPSequentRule
andIntroduction2 = AbsRule [SSequent [] (phi 1), SSequent [] (phi 2)] (SSequent [] $ s_land (phi 2) (phi 1))

andIntroduction :: AmbiguousRule PSSequent
andIntroduction = AmbiguousRule (Set.union (Set.singleton andIntroduction1) (Set.singleton andIntroduction2)) "Adj"

--TODO:Going to need to rejigger justifications so that we can get some kind of
--useful pattern-matching here.

--------------------------------------------------------
--2. Checking Derivations
--------------------------------------------------------

--------------------------------------------------------
--2.1 Simple Checker
--------------------------------------------------------
--this is a simple prototype checker, which will be made obsolete by the
--advent of MultiUnification. these functions are used to actually determine whether a judgement (a big
--tree of formulas and their justifications) supports some argument

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
                Just (Sequent prems@(ass:etc) conc) -> guardEx prems ass etc conc
                Just (Sequent [] conc) -> if conc == conseq then Just (Sequent [] c) else Nothing
                _ -> Nothing
        where guardEx prems ass etc conc
                | ass == antec && conseq == conc = Just $ Sequent etc c
                | conseq == conc = Just $ Sequent prems c
                --we don't want to strictly require that 
                --assumptions are used when constructing 
                --a conditional proof.
                | otherwise = Nothing
derivationProves _ = Nothing


--------------------------------------------------------
--2.2 Unification Based Checker
--------------------------------------------------------

--TODO

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
