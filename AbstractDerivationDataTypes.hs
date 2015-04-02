{-#LANGUAGE GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}

module AbstractDerivationDataTypes where 

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
