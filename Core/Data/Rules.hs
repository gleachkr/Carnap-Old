{-#LANGUAGE GADTs, FlexibleInstances, KindSignatures, MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts, UndecidableInstances #-}

module Carnap.Core.Data.Rules (
    Sequent(Sequent), AmbiguousRule(AmbiguousRule), AbsRule(AbsRule), RuleLike,
    ruleVersions, ruleName, premises, conclusion, (⊢) , (∴),
) where

import Carnap.Core.Unification.Unification
import qualified Data.Map as Map
import qualified Data.Set as Set

type Set = Set.Set

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
    deriving(Show, Eq, Ord)

(⊢) = Sequent
    
data AbsRule term = AbsRule {needed :: [term],  given :: term}
    deriving(Show, Eq, Ord)

(∴) = AbsRule

infixl 0 ∴

--when a user uses a rule we do not know which rule is being checked
--for instance bicondtional rules and things like &E
data AmbiguousRule term = AmbiguousRule { ruleVersions :: Set (AbsRule term), ruleName :: String }
    deriving(Show, Eq, Ord)

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
    ftv rule = (ftv . ruleVersions) rule
    apply sub rule = rule {ruleVersions = apply sub (ruleVersions rule)}
