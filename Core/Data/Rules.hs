{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts, UndecidableInstances #-}
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

module Carnap.Core.Data.Rules (
    Sequent(Sequent), AmbiguousRule(AmbiguousRule), AbsRule(AbsRule), RuleLike,
    ruleVersions, ruleName, premises, conclusion, (⊢) , (∴), premisePermutations,
    AbsRulePlus(AbsRulePlus,rule,check), premisePermutationsPlus,
    AmbiguousRulePlus(AmbiguousRulePlus,ruleVersionsPlus,ruleNamePlus), losePlus,
    withCheck
) where

import Carnap.Core.Unification.Unification
import qualified Data.Set as Set
import Data.List (permutations, intercalate)

--------------------------------------------------------
--1. Rules Like and Rules Like things
--------------------------------------------------------
--somthing is rules like (not Infrence Rule Like) if it has premeses and a conclusion
--So many things (judgements, sequents, inference rules, etc...) are all RuleLike
class RuleLike term t | t -> term where
    premises :: t -> [term]
    conclusion :: t -> term

--A concrete sequent, which is of the form "[prems] |- conclusion"
data Sequent formula = Sequent [formula] formula
    deriving(Eq, Ord)

instance Show a => Show (Sequent a) where
        show (Sequent l c) = intercalate ", " (map show l) ++ " ⊢ " ++ show c

(⊢) :: [formula] -> formula -> Sequent formula
(⊢) = Sequent
    
data AbsRule term = AbsRule {needed :: [term],  given :: term}
    deriving(Eq, Ord)

data AbsRulePlus term = AbsRulePlus {rule :: AbsRule term, check :: AbsRule term -> Maybe String}

simpleRule :: AbsRule term -> AbsRulePlus term
simpleRule r = AbsRulePlus r (const Nothing)


instance Show a => Show (AbsRule a) where
        show (AbsRule l c) = show l ++ " ∴ " ++ show c

(∴) :: [term] -> term -> AbsRulePlus term
(∴) ps c = simpleRule $ AbsRule ps c

withCheck :: AbsRulePlus term -> (AbsRule term -> Maybe String) -> AbsRulePlus term
withCheck (AbsRulePlus r c) c' = AbsRulePlus r (\t -> case c t of 
                                                          Just s -> Just s
                                                          Nothing -> c' t)

infixl 0 `withCheck`
infixl 1 ∴
infixl 2 ⊢

premisePermutations :: AbsRule term -> [AbsRule term]
premisePermutations r = map (\prs -> AbsRule prs (given r)) thePerms
    where thePerms = permutations (needed r)

premisePermutationsPlus :: AbsRulePlus term -> [AbsRulePlus term]
premisePermutationsPlus r = map (\x -> AbsRulePlus x $ check r) (premisePermutations $ rule r)
    

--when a user uses a rule we do not know which rule is being checked
--for instance bicondtional rules and things like &E
data AmbiguousRule term = AmbiguousRule { ruleVersions :: [AbsRule term], ruleName :: String }
    deriving(Show, Eq, Ord)

data AmbiguousRulePlus term = AmbiguousRulePlus { ruleVersionsPlus :: [AbsRulePlus term], ruleNamePlus :: String }

losePlus :: AmbiguousRulePlus term -> AmbiguousRule term
losePlus r = AmbiguousRule (map rule (ruleVersionsPlus r)) (ruleNamePlus r)

instance Eq term => Eq (AmbiguousRulePlus term) where
        (==) r1 r2 = losePlus r1 == losePlus r2

instance (Eq term, Ord term) => Ord (AmbiguousRulePlus term) where
        (<=) r1 r2 = losePlus r1 <= losePlus r2

--------------------------------------------------------
--2. RuleLike Instances
--------------------------------------------------------
instance RuleLike term (Sequent term) where
    premises (Sequent p _) = p
    conclusion (Sequent _ c) = c

--make sure only to export these and not 'needed' and 'given'
instance RuleLike term (AbsRule term) where
    premises = needed
    conclusion = given

--------------------------------------------------------
--4. Define how matching works
--------------------------------------------------------

instance Matchable (Sequent sub) sub where
    match (Sequent p c) (Sequent p' c')
        | length p == length p' = Just $ (c, c') : zip p p'
    match _             _       = Nothing

instance Matchable (AbsRule sub) sub where
    match r r'
        | lengthp r == lengthp r' = Just $ conclude : premisesM
        where lengthp   = length . premises
              conclude  = (conclusion r, conclusion r')
              premisesM = zip (premises r) (premises r')
    match _             _       = Nothing

--------------------------------------------------------
--4.1 Define how matching of sequent calculus rules work
--------------------------------------------------------

--quick helper to combine sub parts
concatMatches :: [Maybe [a]] -> Maybe [a]
concatMatches [] = undefined
concatMatches (x:xs) = do
    first <- x
    rest <- concatMatches xs
    return $ first ++ rest
--helper type
type Match1Type sub = AbsRule (Sequent sub) -> AbsRule (Sequent sub) -> Maybe [(Sequent sub, Sequent sub)]
type Match2Type sub = Sequent sub -> Sequent sub -> Maybe [(sub, sub)]
instance Matchable (AbsRule (Sequent sub)) sub where
    match r r' = do
        ininital <- (match :: Match1Type sub) r r'
        concatMatches (map (uncurry (match :: Match2Type sub)) ininital)

--------------------------------------------------------
--5. Define how subtitution works
--------------------------------------------------------

instance Hilbert var schema schema => Hilbert var (Sequent schema) schema where
    ftv (Sequent p c) = ftv (c:p) 
    apply sub (Sequent p c) = Sequent (apply sub p) (apply sub c)

instance Hilbert var schema sub => Hilbert var (AbsRule schema) sub where
    ftv rule = (ftv . premises $ rule) `Set.union` (ftv . conclusion $ rule)
    apply sub (AbsRule p c) = AbsRule (apply sub p) (apply sub c)

instance (Ord schema, Hilbert var schema sub) => Hilbert var (AmbiguousRule schema) sub where
    ftv = ftv . ruleVersions 
    apply sub rule = rule {ruleVersions = apply sub (ruleVersions rule)}
