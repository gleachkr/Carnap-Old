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

module Carnap.Systems.NaturalDeduction.ProofTreeDataTypes where
import Carnap.Core.Data.AbstractDerivationDataTypes
import Data.Tree

--------------------------------------------------------
--Data types
--------------------------------------------------------

--A ProofTree is a tree of possible lines. The intention is that Leaves
--contain formulas that are justified by previous assertions. Other nodes
--contain formulas that are either so far unjustified (these lines have
--SHOW as their rule) or formulas that are justified by the subderivation
--that is beneath them in the tree (these lines have a termination rule,
--like CD, with the line numbers used in the termination)
type ProofTree form = Tree (PossibleLine form)

type ProofForest form = Forest (PossibleLine form)

--a termination is something that might end a subproof, indicating how the
--subproof is to be used by the preceeding show line.
type Termination = (InferenceRule,[Int])

--a possible line is either an error string or a formula with a rule and
--line numbers
type PossibleLine form = Either String (form, InferenceRule, [Int])

--A PreProofTree is a tree of PrePossible lines. The intention is that one
--first parses a tree into a bunch of PrePossible lines, then maps the
--PreProof tree down to a bunch of PossibleLines.
type PreProofTree = Tree PrePossibleLine

type PreProofForest = Forest PrePossibleLine

type PrePossibleLine = String
