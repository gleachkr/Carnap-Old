{-#LANGUAGE MultiParamTypeClasses, EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module PropositionalDerivations where

import PropositionalLanguage
import AbstractSyntaxDataTypes
import AbstractDerivationDataTypes
import Data.List (nub)

--This module contains functions and types specializing Abstract
--derivations to deal with Propositional Logic.

--------------------------------------------------------
--Propositional Logic Datatypes
--------------------------------------------------------

type PropositionalJudgement = Judgement PropositionalFormula PropJustification

type PropDerivation = Derivation PropositionalJudgement

--an argument, intuitively, is a list of premises used, plus a conclusion
--supported.
type Argument = ([PropositionalFormula], PropositionalFormula)

--These construct justifications, which, paired with justified formulas,
--make judgements
data PropJustification = Premise
                       | ConditionalProof PropositionalJudgement 
                       | ModusPonens PropositionalJudgement PropositionalJudgement
                       | Adjunction PropositionalJudgement PropositionalJudgement 

--It's useful to have a single concrete type that gives all the rules that
--might be cited on a line.
data PropRule = PR | MP | CP | ADJ | SHOW
              deriving Show

--------------------------------------------------------
--Rule Checkers
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
--Checking Derivations
--------------------------------------------------------

--these functions are used to actually determine whether a judgement (a big
--tree of formulas and their justifications)
--supports some argument

--a helper formula for combining the premises of two arguments. At the
--moment, repeated premises are dropped. This could be dropped if we wanted
--to think about substructural logics.
unitePremises :: Argument -> Argument -> [PropositionalFormula]
unitePremises (ps1, _ ) (ps2, _ ) = nub (ps1 ++ ps2)

--This converts a given propositionalJudgement into an argument
--XXX: maybe it'd be more elegant to fold modusPonens and other conditions in
--here as guards.
derivationProves :: PropositionalJudgement -> Maybe ([PropositionalFormula],PropositionalFormula)
derivationProves (Line p Premise) = Just ([p],p)
derivationProves (Line c (ModusPonens l1@(Line p1 _) l2@(Line p2 _))) = if modusPonens p1 p2 c 
                                                                        then do arg1 <- derivationProves l1
                                                                                arg2 <- derivationProves l2
                                                                                return (unitePremises arg1 arg2, c)
                                                                        else Nothing
derivationProves (Line c (Adjunction l1@(Line p1 _) l2@(Line p2 _))) = if adjunction p1 p2 c 
                                                                       then do arg1 <- derivationProves l1
                                                                               arg2 <- derivationProves l2
                                                                               return (unitePremises arg1 arg2, c)
                                                                       else Nothing
derivationProves (Line c@(BinaryConnect If antec conseq) (ConditionalProof l)) = case derivationProves l of
                                                                                     Just (antec:etc,conseq) -> Just (etc,c)
                                                                                     --we don't want to strictly require that 
                                                                                     --assumptions are used when constructing 
                                                                                     --a conditional proof.
                                                                                     Just (etc,conseq) -> Just (etc,c)
                                                                                     _ -> Nothing
derivationProves _ = Nothing


--------------------------------------------------------
--Helper functions for Derivations
--------------------------------------------------------

--These are helper functions for building derivations with monadic 'do'
--syntax.

mpRule :: a -> PropositionalJudgement -> PropositionalJudgement -> Derivation (Judgement a PropJustification)
mpRule x y z = assert $ Line x $ ModusPonens y z

adRule :: a -> PropositionalJudgement -> PropositionalJudgement -> Derivation (Judgement a PropJustification)
adRule x y z = assert $ Line x $ Adjunction y z

--finishes a subderivation, returning the attached derivation type, to feed
--into a show line
cdRule :: PropositionalJudgement -> Derivation (PropositionalJudgement,
                                               PropositionalJudgement ->
                                               PropJustification)
cdRule y = return (y,ConditionalProof)

prRule :: a -> Derivation (Judgement a PropJustification)
prRule x     = assert $ Line x Premise

prove :: PropositionalFormula -> Derivation (PropositionalJudgement, PropositionalJudgement -> PropJustification) -> PropDerivation
prove phi subder = assert $ Line phi $ (snd $ subproof subder) (fst $ subproof subder) 
