{-#LANGUAGE MultiParamTypeClasses, EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module Carnap.Languages.Sentential.PropositionalDerivations where

import Carnap.Languages.Sentential.PropositionalLanguage
import Carnap.Core.Data.AbstractDerivationDataTypes
import Carnap.Core.Data.Rules

--This module contains functions and types specializing Abstract
--derivations to deal with Propositional Logic.

--------------------------------------------------------
--1. Propositional Logic Datatypes
--------------------------------------------------------

type PropositionalJudgement = Judgement PropositionalFormula PropJustification

type PropDerivation = Derivation PropositionalJudgement

--a Psequent, intuitively, is a list of premises used, plus a conclusion
--supported.
type Psequent = Sequent PropositionalFormula

--These construct justifications, which, paired with justified formulas,
--make judgements
type PropJustification = SimpleJustification PropositionalFormula
