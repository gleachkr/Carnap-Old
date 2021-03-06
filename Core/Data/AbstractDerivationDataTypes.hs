{-#LANGUAGE GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-Copyright 2015 (C) Jake Ehrlich and Graham Leach-Krouse

This file is part of Carnap. 

Carnap is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Carnap is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Carnap If not, see <http://www.gnu.org/licenses/>.
-}

module Carnap.Core.Data.AbstractDerivationDataTypes where 

import Control.Monad.Identity

--This module contains some datatypes for derivations, at a level of
--abstraction where they will hopefully be applicable to many particuar
--deductive systems

--------------------------------------------------------
--1. Abstract Derivatons
--------------------------------------------------------                            

--------------------------------------------------------
--1.1 Data Types
--------------------------------------------------------

--A judgement is a basic unit of derivation. It contains a formula, which
--is asserted, and a justification, which will be, in the propositional
--case, usually something constructed by applying an inference rule to
--several other judgements. In more general cases, a justification might
--contain other things, e.g. a context relative to which the assertion is
--being made. 
data Judgement contents justification where
                            Line :: {lineContents :: contents, lineJustification :: justification} 
                                -> Judgement contents justification

type InferenceRule = String

data SimpleJustification contents = Premise | Inference InferenceRule [Judgement contents (SimpleJustification contents)]

type RulesAndArity = InferenceRule -> Maybe (Either Int Int) --returns the
-- number of premises used by a given rule, and (at the type-level) 
-- whether the rule closes a subproof, or justifies an immediate inference
--
--------------------------------------------------------
--2. The Derivation Monad
--------------------------------------------------------

--it turns out that natural deduction mirrors the identity monad. This
--makes it easy construct derivations in haskell syntax, for testing
--purposes.

--Derivation is a wrapper type using the identity monad that makes it easy
--to use monadic 'do' syntax to construct judgements.
type Derivation = Identity

--this introduces a new judgement into a derivation.
assert :: Judgement a b -> Derivation (Judgement a b)
assert = Identity

--this extracts the final judgement from a derivation.
conclusion :: Derivation (Judgement a b) -> Judgement a b
conclusion = runIdentity

--this takes a derivation containing a pair of a derived judgement, and
--something that constructs justifications from judgements (e.g. the
--conditional proof constructor), and unwraps both of them (probably so
--that you can apply the second to the first.
subproof :: Derivation (Judgement a b, Judgement a b -> b) -> (Judgement a b, Judgement a b -> b)
subproof = runIdentity

prRule :: a -> Derivation (Judgement a (SimpleJustification judgement))
prRule x = assert $ Line x Premise

prove :: a -> Derivation (Judgement a1 b, Judgement a1 b -> b) -> Derivation (Judgement a b)
prove p subder = assert $ Line p $ (snd $ subproof subder) (fst $ subproof subder) 
