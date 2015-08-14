{- Copyright (C) 2015 Jake Ehrlich and Graham Leach-Krouse <gleachkr@ksu.edu>

This file is part of Carnap 

Carnap is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Carnap is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with Carnap. If not, see <http://www.gnu.org/licenses/>.
- -}
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
