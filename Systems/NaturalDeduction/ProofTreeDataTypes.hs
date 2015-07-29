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
