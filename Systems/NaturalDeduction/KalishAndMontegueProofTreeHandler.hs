{-# LANGUAGE FlexibleContexts #-}
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
module Carnap.Systems.NaturalDeduction.KalishAndMontegueProofTreeHandler (handleForestKM) where

import Carnap.Core.Data.AbstractDerivationDataTypes
import Carnap.Core.Data.Rules
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxMultiUnification()
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching
import Carnap.Core.Unification.HigherOrderMatching
import Carnap.Core.Unification.HigherOrderUtil
import Carnap.Languages.Util.LanguageClasses
import Carnap.Systems.NaturalDeduction.ProofTreeDataTypes
import Carnap.Systems.NaturalDeduction.Util.ReportTypes
import Carnap.Systems.NaturalDeduction.JudgementHandler
import Data.Tree
import qualified Data.Set as Set

--The goal of this module is to provide a function that transforms a given
--ProofTree into either an argument that the tree witnesses the validity
--of, or into a line-by-line list of errors

--------------------------------------------------------
--1. Main processing functions
--------------------------------------------------------
--
--The proof forest is first converted into a derivation that reflects the
--actual structure of the argument. We get an errorlist here if the
--ProofForest doesn't actually describe a derivation (because a rule is
--getting the wrong number of premises or something).
--
--The resulting derivation is then checked for correctness. We get an
--errorlist here if there are some steps that aren't correct, for example
--if a rule is applied in such a way that the conclusion does not follow.
--
--XXX: Throughout this code, we systematically pass around a lot of
--information; this kind of suggests that, minimally, we should pack the
--arguments that get carried along the recursion into a single structure,
--and may suggest that, even more radically, we should bring in the reader 
--monad.

handleForestKM :: (S_NextVar sv quant, SchemeVar sv, UniformlyEquaitable sv, UniformlyEquaitable f, UniformlyEquaitable quant, UniformlyEquaitable con, UniformlyEquaitable pred, 
                Matchable (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ()), S_DisplayVar sv quant,
                Matchable (AbsRule (Sequent (SSequentItem pred con quant f sv))) (Var pred con quant f sv ()), 
                Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred)
                => ProofForest (Form pred con quant f sv a) -> RulesAndArity -> Set.Set (AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())) -> 
                Either [ReportLine (Form pred con quant f sv a)] 
                       (Either [MatchError (Var pred con quant f sv () (AbsRule (Sequent (SSequentItem pred con quant f sv)))) (AbsRule (Sequent (SSequentItem pred con quant f sv)))] 
                               (Sequent (SSequentItem pred con quant f sv)), [ReportLine (Form pred con quant f sv a)])
handleForestKM f raa ruleSet = do (j,dr) <- forestToJudgement f raa ruleSet
                                  return $ (derivationProves ruleSet j,dr)
                                
--------------------------------------------------------
--1.1 Tree and Forest to derivation functions
--------------------------------------------------------
--These are functions that are collectively resonsible for turning
--a ProofForest into derivation; the derivation can then be checked.

--This runs a ProofForest through a processing function that returns
--a DerivationReport. It cleans this output, and returns what's needed for
--the Forest-Handler

forestToJudgement :: (S_NextVar sv quant, SchemeVar sv, UniformlyEquaitable sv, UniformlyEquaitable f, UniformlyEquaitable quant, UniformlyEquaitable con, UniformlyEquaitable pred, 
                Matchable (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ()), S_DisplayVar sv quant,
                Matchable (AbsRule (Sequent (SSequentItem pred con quant f sv))) (Var pred con quant f sv ()), 
                Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred)
                => ProofForest (Form pred con quant f sv a) -> RulesAndArity -> Set.Set (AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())) -> 
                    Either [ReportLine (Form pred con quant f sv a)] 
                           (Judgement (Form pred con quant f sv a) (SimpleJustification (Form pred con quant f sv a)),[ReportLine (Form pred con quant f sv a)])
forestToJudgement f raa ruleSet = if all (`checksout` ruleSet) dr 
                                  then conclude $ head $ filter isOpen dr
                                  else Left dr
        where dr = forestProcessor f raa []
              conclude (OpenLine j) = Right (j,dr)
              conclude _ = Left [ErrLine "error 1"] --This case shoud not occur
              isOpen dl = case dl of 
                            OpenLine _ -> True
                            _ -> False

checksout :: (S_NextVar sv quant, SchemeVar sv, Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred, S_DisplayVar sv quant,
             UniformlyEquaitable sv, UniformlyEquaitable f, UniformlyEquaitable quant, UniformlyEquaitable con, UniformlyEquaitable pred, 
             Matchable (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ()), 
             Matchable (AbsRule (Sequent (SSequentItem pred con quant f sv))) (Var pred con quant f sv ())) => 
             ReportLine (Form pred con quant f sv a) -> Set.Set (AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())) -> Bool
checksout dl' ruleSet = case dl' of
                    ErrLine _ -> False
                    OpenLine j -> provesSomething j ruleSet
                    ClosedLine j -> provesSomething j ruleSet
                    _ -> True

provesSomething :: (S_NextVar sv quant, SchemeVar sv, Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred, S_DisplayVar sv quant,
                   UniformlyEquaitable sv, UniformlyEquaitable f, UniformlyEquaitable quant, UniformlyEquaitable con, UniformlyEquaitable pred, 
                   Matchable (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ()), 
                   Matchable (AbsRule (Sequent (SSequentItem pred con quant f sv))) (Var pred con quant f sv ())) => 
                   Judgement (Form pred con quant f sv a) (SimpleJustification (Form pred con quant f sv a)) -> 
                   Set.Set (AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())) -> Bool
provesSomething j ruleSet = case derivationProves ruleSet j of
                                Left _ -> False
                                Right _ -> True
              --this case should not arise

--this processes a ProofTree by building up a DerivationReport
treeProcessor :: ProofTree f -> RulesAndArity -> DerivationReport f 
    -> DerivationReport f 
treeProcessor (Node (Left _) []) _ dr = ErrLine "incomplete line":dr
treeProcessor (Node (Right (fm,':':inf,lns)) f) raa dr = subProofProcessor (fm,inf,lns) raa f dr
treeProcessor (Node (Right (fm,"SHOW", lns)) f) raa dr = subProofProcessor (fm,"SHOW",lns) raa f dr
--I don't think this last case can arise
treeProcessor (Node (Right line) []) raa dr = assertionProcessor line raa dr 
treeProcessor (Node (Left _) _) _ dr = ErrLine "shouldn't happen":dr

--this processes a ProofForest by folding together the DerivationReports
--that arise from its individual trees.
forestProcessor :: [ProofTree f] -> RulesAndArity -> DerivationReport f -> DerivationReport f
forestProcessor forest raa dr = foldl combineWithTree dr forest
    where combineWithTree dr' t =  treeProcessor t raa dr'

--------------------------------------------------------
--1.1.1 Assertion Processing 
--------------------------------------------------------
--These are functions that are responsible for handling single-assertion
--lines

--this processes a line containing a well-formed assertion, in the context of a DerivationReport
assertionProcessor :: WFLine f -> RulesAndArity -> DerivationReport f 
    -> DerivationReport f 
assertionProcessor (f,"PR",[]) _ dr =  OpenLine (Line f Premise):dr
assertionProcessor (f,rule,l) raa dr =
       case raa rule of Nothing -> ErrLine "Unrecognized Inference Rule":dr
                        Just (Right _) -> ErrLine "Not an assertion-justifying rule":dr
                        Just (Left 0) -> nullaryInferenceHandler f rule l dr
                        Just (Left 1) -> unaryInferenceHandler f rule l dr
                        Just (Left 2) -> binaryInferenceHandler f rule l dr
                        _ -> ErrLine "Impossible Error 1":dr
                        --TODO: More cases; ideally make this work for
                        --arbitrary arities of rule
nullaryInferenceHandler :: f -> InferenceRule -> [Int] -> [ReportLine f ] -> [ReportLine f ]
nullaryInferenceHandler f r l dr = case l of 
                                      [] -> nullaryInferFrom f r dr
                                      _  -> ErrLine ("wrong number of premises--you need one, you have " ++ show (length l)) :dr

nullaryInferFrom :: f -> InferenceRule -> [ReportLine f ] -> [ReportLine f ]
nullaryInferFrom f r dr = OpenLine (Line f $ Inference r []):dr 

unaryInferenceHandler :: f -> InferenceRule -> [Int] -> [ReportLine f ] -> [ReportLine f ]
unaryInferenceHandler f r l dr = case l of 
                                      [l1] -> unaryInferFrom f l1 r dr
                                      _    -> ErrLine ("wrong number of premises--you need one, you have " ++ show (length l)) :dr

unaryInferFrom :: f -> Int -> InferenceRule -> [ReportLine f ] -> [ReportLine f ]
unaryInferFrom f l1 r dr = case retrieveOne l1 dr of
                                        Nothing -> ErrLine ("line" ++ show l1 ++ "is unavailable"):dr
                                        Just mj -> 
                                            case mj of 
                                                OpenLine j -> OpenLine (Line f $ Inference r [j]):dr
                                                ErrLine _ -> ErrLine (errLineMsg l1):dr
                                                ClosedLine _ -> ErrLine (closedLineMsg l1):dr
                                                ClosureLine -> ErrLine ("line " ++ show l1 ++ "has nothing on it"):dr

binaryInferenceHandler :: f -> InferenceRule -> [Int] -> [ReportLine f ] -> [ReportLine f ]
binaryInferenceHandler f r l dr = case l of 
                                        [l1,l2] -> binaryInferFrom f l1 l2 r dr
                                        _       -> ErrLine ("wrong number of premises--you need two, you have " ++ show (length l)) :dr

binaryInferFrom :: f -> Int -> Int -> InferenceRule -> [ReportLine f ] -> [ReportLine f ]
binaryInferFrom f l1 l2 r dr = case retrieveTwo l1 l2 dr of
                                        (Nothing,Nothing) -> (ErrLine $ " the lines " ++ show l1 ++ " and " ++ show l2 ++ " are unavailable"):dr
                                        (Nothing,_) -> (ErrLine $ " the line " ++ show l1 ++ " is unavailable"):dr
                                        (_,Nothing) -> (ErrLine $ " the line " ++ show l2 ++ " is unavailable"):dr
                                        (Just mj1, Just mj2) -> handlePair mj1 mj2 f l1 l2 r dr

ternaryInferenceHandler :: f -> InferenceRule -> [Int] -> [ReportLine f] -> [ReportLine f]
ternaryInferenceHandler f r l dr = case l of 
                                        [l1,l2,l3] -> ternaryInferFrom f l1 l2 l3 r dr
                                        _       -> ErrLine ("wrong number of premises--you need three, you have " ++ show (length l)) : dr

ternaryInferFrom :: f -> Int -> Int -> Int -> InferenceRule -> [ReportLine f ] -> [ReportLine f ]
ternaryInferFrom f l1 l2 l3 r dr = case retrieveThree l1 l2 l3 dr of
                                            (Nothing,Nothing,Nothing)      -> (ErrLine $ " the lines " ++ show l1 ++ ", " ++ show l2 ++ "and " ++ show l3 ++ " are unavailable"):dr
                                            (Nothing,Nothing, _)           -> (ErrLine $ " the lines " ++ show l1 ++ " and " ++ show l2 ++ " are unavailable"):dr
                                            (Nothing, _, Nothing)          -> (ErrLine $ " the lines " ++ show l1 ++ " and " ++ show l3 ++ " are unavailable"):dr
                                            (_ , Nothing, Nothing)         -> (ErrLine $ " the lines " ++ show l2 ++ " and " ++ show l3 ++ " are unavailable"):dr
                                            (Nothing,_,_)                  -> (ErrLine $ " the line " ++ show l1 ++ " is unavailable"):dr
                                            (_,Nothing,_)                  -> (ErrLine $ " the line " ++ show l2 ++ " is unavailable"):dr
                                            (_,_,Nothing)                  -> (ErrLine $ " the line " ++ show l3 ++ " is unavailable"):dr
                                            (Just mj1, Just mj2, Just mj3) -> handleTriple mj1 mj2 mj3 f l1 l2 l3 r dr

--------------------------------------------------------
--1.1.2 Subproof processing
--------------------------------------------------------
--These are functions that are responsible for handling subproofs.

--XXX:there are several repeated applications of forestProcessor here. this
--could be a lot less redundant.

--This function takes a line that introduces a ProofForest, and adjusts the
--DerivationReport
subProofProcessor :: WFLine f -> RulesAndArity -> ProofForest f -> DerivationReport f 
    -> DerivationReport f 
subProofProcessor (_, "SHOW", _) raa forest dr = closeFrom (length dr + 1) $ forestProcessor forest raa (ErrLine "Open Subproof":dr)
subProofProcessor (f, rule, l) raa forest dr = 
        case raa rule of Nothing -> ErrLine "Unrecognized Inference Rule":dr
                         Just (Right 1) -> ClosureLine : (closeFrom (length dr + 1) $ unaryTerminationHandler forest raa f rule l dr)
                         Just (Right 2) -> ClosureLine : (closeFrom (length dr + 1) $ binaryTerminationHandler forest raa f rule l dr)
                         Just (Right 3) -> ClosureLine : (closeFrom (length dr + 1) $ ternaryTerminationHandler forest raa f rule l dr)
                        --here the function appends an additional unavailable line, for cases in which
                        --we have a line occupied by the sub-proof closing rule. In a Hardegree
                        --system, rather than a Kalish and Montegue system, this extra line would
                        --be unnecessary.
                         Just (Left _) -> ErrLine "Not a derivation-closing rule":dr
                         _ -> ErrLine "Impossible Error 2":dr
                         --TODO: More cases; ideally allow for arbitrary
                         --arities.

--this is intended to close the lines below line l, not including l, to make their
--contents unavailable. 
closeFrom :: Int -> DerivationReport f -> DerivationReport f 
closeFrom l dr  = close lr
     where close l' = map closeoff (take l' dr) ++ drop l' dr
           lr = length dr - l
           closeoff rl = case rl of
                             ErrLine s    -> ErrLine s
                             OpenLine j   -> ClosedLine j
                             ClosedLine j -> ClosedLine j
                             ClosureLine -> ClosureLine

unaryTerminationHandler :: ProofForest f -> RulesAndArity -> f -> InferenceRule -> [Int] -> DerivationReport f 
    -> DerivationReport f 
unaryTerminationHandler forest raa f r l dr = case l of 
                                                [l1] -> closeWithOne forest raa f l1 r dr
                                                _ -> forestProcessor forest raa (ErrLine "wrong number of lines cited---you need just one":dr)

binaryTerminationHandler :: ProofForest f -> RulesAndArity -> f -> InferenceRule -> [Int] -> DerivationReport f -> DerivationReport f 
binaryTerminationHandler forest raa f r l dr = case l of 
                                                [l1,l2] -> closeWithTwo forest raa f l1 l2 r dr
                                                _ -> forestProcessor forest raa (ErrLine "wrong number of lines cited---you need two":dr)

ternaryTerminationHandler :: ProofForest f -> RulesAndArity -> f -> InferenceRule -> [Int] -> DerivationReport f -> DerivationReport f 
ternaryTerminationHandler forest raa f r l dr = case l of 
                                                [l1,l2,l3] -> closeWithThree forest raa f l1 l2 l3 r dr
                                                _ -> forestProcessor forest raa (ErrLine "wrong number of lines cited---you need three":dr)

closeWithOne :: ProofForest f -> RulesAndArity -> f -> Int -> InferenceRule -> DerivationReport f 
    -> DerivationReport f 
closeWithOne forest raa f l1 r dr = case retrieveOne l1 (preProof forest raa dr) of 
                                    Nothing -> forestProcessor forest raa (ErrLine ("line " ++ show l1 ++ " is unavailable"):dr) 
                                    Just mj  -> case mj of
                                        ErrLine _ -> forestProcessor forest raa (ErrLine (errLineMsg l1):dr)
                                        ClosedLine _ -> forestProcessor forest raa (ErrLine (closedLineMsg l1):dr)
                                        OpenLine j -> forestProcessor forest raa (OpenLine (Line f $ Inference r [j]):dr)
                                        ClosureLine -> forestProcessor forest raa (ErrLine ("line " ++ show l1 ++ " has nothing on it"):dr)

preProof :: ProofForest f -> RulesAndArity -> DerivationReport f -> DerivationReport f 
preProof forest raa dr = forestProcessor forest raa (ClosureLine:dr)

closeWithTwo :: ProofForest f -> RulesAndArity -> f -> Int -> Int -> InferenceRule -> DerivationReport f -> DerivationReport f 
closeWithTwo forest raa f l1 l2 r dr = case retrieveTwo l1 l2 (preProof forest raa dr) of 
                                    (Nothing, Nothing) -> forestProcessor forest raa (ErrLine ("The lines " ++ show l1 ++ " and " ++ show l2 ++ " are unavailable"):dr) 
                                    (Nothing,_) -> forestProcessor forest raa (ErrLine ("The line " ++ show l1 ++ " is unavailable"):dr) 
                                    (_,Nothing) -> forestProcessor forest raa (ErrLine ("The line " ++ show l2 ++ " is unavailable"):dr) 
                                    (Just mj1, Just mj2) -> forestProcessor forest raa (handlePair mj1 mj2 f l1 l2 r dr)

closeWithThree :: ProofForest f -> RulesAndArity -> f -> Int -> Int -> Int -> InferenceRule -> DerivationReport f -> DerivationReport f 
closeWithThree forest raa f l1 l2 l3 r dr = case retrieveThree l1 l2 l3 (preProof forest raa dr) of 
                                    (Nothing, Nothing, Nothing) -> forestProcessor forest raa (ErrLine ("The lines " ++ show l1 ++ ", " ++ show l2 ++ " and " ++ show l3 ++ " are unavailable"):dr) 
                                    (_,Nothing, Nothing) -> forestProcessor forest raa (ErrLine ("The lines " ++ show l2 ++ " and " ++ show l3 ++ " are unavailable"):dr) 
                                    (Nothing,_, Nothing) -> forestProcessor forest raa (ErrLine ("The lines " ++ show l1 ++ " and " ++ show l3 ++ " are unavailable"):dr) 
                                    (Nothing, Nothing,_) -> forestProcessor forest raa (ErrLine ("The lines " ++ show l1 ++ " and " ++ show l2 ++ " are unavailable"):dr) 
                                    (Nothing,_,_) -> forestProcessor forest raa (ErrLine ("The line " ++ show l1 ++ " is unavailable"):dr) 
                                    (_,Nothing,_) -> forestProcessor forest raa (ErrLine ("The line " ++ show l2 ++ " is unavailable"):dr) 
                                    (_,_,Nothing) -> forestProcessor forest raa (ErrLine ("The line " ++ show l3 ++ " is unavailable"):dr) 
                                    (Just mj1, Just mj2, Just mj3) -> forestProcessor forest raa (handleTriple mj1 mj2 mj3 f l1 l2 l3 r dr)
                                    
--------------------------------------------------------
--2. Helper Functions
--------------------------------------------------------

handlePair :: ReportLine f -> ReportLine f -> f -> Int -> Int -> InferenceRule -> DerivationReport f 
    -> DerivationReport f 
handlePair mj1 mj2 f l1 l2 r dr = case (mj1,mj2) of 
                                (OpenLine j1, OpenLine j2) -> OpenLine (Line f $ Inference r [j1,j2]):dr
                                (OpenLine _ , _) -> ErrLine (errorMsg mj2 l2):dr
                                (_, OpenLine _) -> ErrLine (errorMsg mj1 l1):dr
                                _ -> ErrLine (errorMsg mj1 l1 ++ " and " ++ errorMsg mj2 l2):dr

handleTriple :: ReportLine f -> ReportLine f -> ReportLine f -> f -> Int -> Int -> Int -> InferenceRule -> DerivationReport f 
    -> DerivationReport f 
handleTriple mj1 mj2 mj3 f l1 l2 l3 r dr = case (mj1,mj2,mj3) of 
                                (OpenLine j1, OpenLine j2, OpenLine j3) -> OpenLine (Line f $ Inference r [j1,j2,j3]):dr
                                (OpenLine _ , OpenLine _, _) -> ErrLine (errorMsg mj3 l3):dr
                                (OpenLine _ , _, OpenLine _) -> ErrLine (errorMsg mj2 l2):dr
                                (_ , OpenLine _, OpenLine _) -> ErrLine (errorMsg mj1 l1):dr
                                (OpenLine _, _, _) -> ErrLine (errorMsg mj2 l2 ++ " and " ++ errorMsg mj3 l3):dr
                                (_, OpenLine _, _) -> ErrLine (errorMsg mj1 l1 ++ " and " ++ errorMsg mj3 l3):dr
                                (_, _, OpenLine _) -> ErrLine (errorMsg mj1 l1 ++ " and " ++ errorMsg mj2 l2):dr
                                (_, _, OpenLine _) -> ErrLine (errorMsg mj1 l1):dr
                                _ -> ErrLine (errorMsg mj1 l1 ++ ", " ++ errorMsg mj2 l2 ++ " and " ++ errorMsg mj2 l2):dr

closedLineMsg :: Int -> String
closedLineMsg l1 = "The line " ++ show l1 ++ " is closed, and can't be used"

errLineMsg :: Int -> String 
errLineMsg l1 = "The line " ++ show l1 ++ " depends on something not-well-formed, and can't be used"

closureLineMsg :: Int -> String
closureLineMsg l1 = "The line " ++ show l1 ++ " has nothing on it"

errorMsg :: ReportLine f -> Int -> String
errorMsg mj l1 = case mj of
                     ClosedLine _ -> closedLineMsg l1
                     ErrLine _ -> errLineMsg l1
                     ClosureLine -> closureLineMsg l1
                     OpenLine _ -> ""

retrieveOne :: Int -> [t] -> Maybe t
retrieveOne l1 dl = if  l1 > length dl
                           then Nothing 
                           else Just (reverse dl !! (l1 - 1))

retrieveTwo :: Int -> Int -> [t] -> (Maybe t, Maybe t)
retrieveTwo l1 l2 dl = (retrieveOne l1 dl, retrieveOne l2 dl)

retrieveThree :: Int -> Int -> Int-> [t] -> (Maybe t, Maybe t, Maybe t)
retrieveThree l1 l2 l3 dl = (retrieveOne l1 dl, retrieveOne l2 dl, retrieveOne l3 dl)
