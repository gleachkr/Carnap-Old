{-#LANGUAGE MultiParamTypeClasses, EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module PropositionalDerivations where

import PropositionalLanguage
import AbstractDerivationDataTypes
import Rules


--This module contains functions and types specializing Abstract
--derivations to deal with Propositional Logic.

--------------------------------------------------------
--1. Propositional Logic Datatypes
--------------------------------------------------------

type PropositionalJudgement = Judgement PropositionalFormula PropJustification

type PropDerivation = Derivation PropositionalJudgement

--a sequent, intuitively, is a list of premises used, plus a conclusion
--supported.
type Psequent = Sequent PropositionalFormula

type PSSequent = SSequent PropositionalScheme

type AbsPSequentRule = AbsRule PSSequent

--These construct justifications, which, paired with justified formulas,
--make judgements
data PropJustification = Premise | Inference PropRule [PropositionalJudgement]

--It's useful to have a single concrete type that gives all the rules that
--might be cited on a line.
type PropRule = String

--------------------------------------------------------
--2. Helper Functions for Derivations
--------------------------------------------------------

--these are highly general functions for building derivations with monadic
--'do' notation.

prRule :: a -> Derivation (Judgement a PropJustification)
prRule x     = assert $ Line x Premise

prove :: PropositionalFormula -> Derivation (PropositionalJudgement, PropositionalJudgement -> PropJustification) -> PropDerivation
prove p subder = assert $ Line p $ (snd $ subproof subder) (fst $ subproof subder) 
