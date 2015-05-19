module Carnap.Systems.NaturalDeduction.ProofTreeHandler where
import Carnap.Core.Data.AbstractDerivationDataTypes
import Carnap.Languages.Sentential.PropositionalLanguage
import Carnap.Languages.Sentential.PropositionalDerivations
import Carnap.Systems.NaturalDeduction.ProofTreeDataTypes
import Carnap.Systems.NaturalDeduction.JudgementHandler
import Data.Tree

--The goal of this module is to provide a function that transforms a given
--ProofTree into either an argument that the tree witnesses the validity
--of, or into a line-by-line list of errors

--------------------------------------------------------
--1. Main processing functions
--------------------------------------------------------

--Closed lines are lines for which a judgement can be constructed, but
--which are now in a closed suproof. OpenLines are lines for which
--a judgement can be constructed. ErrorLines are lines for which
--a judgement cannot be constructed. A ClosureLine is a dummy line for
--a proof-closing inference rule, as we find in a Kalish and Montegue
--system.
data ReportLine = ClosedLine PropositionalJudgement 
                | OpenLine PropositionalJudgement 
                | ErrLine String
                | ClosureLine

type DerivationReport = [ReportLine]

type WFLine = (PropositionalFormula, InferenceRule, [Int])

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
--and may suggest that, even more radically, we should bring in the state
--monad.

--TODO: Improve derivationProves to potentially return an errorlist instead
--of Maybe sequent
handleForest f raa ruleSet = do j <- forestToJudgement f raa
                                return $ derivationProves ruleSet j

--------------------------------------------------------
--1.1 Tree and Forest to derivation functions
--------------------------------------------------------
--These are functions that are collectively resonsible for turning
--a ProofForest into PropositionalDerivation; the PropositionalDerivation
--can then be checked.

--This runs a ProofForest through a processing function that returns
--a DerivationReprot . It cleans this output, and returns what's needed for
--the Forest-Handler

forestToJudgement :: ProofForest -> RulesAndArity -> Either DerivationReport PropositionalJudgement
forestToJudgement f raa = if all checksout dr
                          then Right $ conclude $ reverse dr !! (length f - 1) 
                          --length f-1 isn't quite right. It'll go wrong
                          --when there is a subproof between the first line
                          --of the main derivation, and the last line.
                          else Left dr
        where dr = forestProcessor f raa []
              conclude (OpenLine j) = j
              --this case should not arise
              conclude _ = Line (pn 666) Premise
              checksout dl' = case dl' of
                                  ErrLine _ -> False
                                  _ -> True


--this processes a ProofTree by building up a DerivationReport
treeProcessor :: ProofTree -> RulesAndArity -> DerivationReport -> DerivationReport
treeProcessor (Node (Left err) []) raa dr = ErrLine "incomplete line":dr
treeProcessor (Node (Right line) []) raa dr = assertionProcessor line raa dr 
treeProcessor (Node (Right line) f) raa dr = subProofProcessor line raa f dr
--I don't think this last case can arise
treeProcessor (Node (Left err) f) raa dr = ErrLine "shouldn't happen":dr

--this processes a ProofForest by folding together the DerivationReports
--that arise from its individual trees.
forestProcessor :: ProofForest -> RulesAndArity -> DerivationReport -> DerivationReport
forestProcessor forest raa dr = foldl combineWithTree dr forest
    where combineWithTree dr t =  treeProcessor t raa dr


--------------------------------------------------------
--1.1.1 Assertion Processing 
--------------------------------------------------------
--These are functions that are responsible for handling single-assertion
--lines

--this processes a line containing a well-formed assertion, in the context of a DerivationReport
assertionProcessor :: WFLine -> RulesAndArity -> DerivationReport -> DerivationReport
assertionProcessor (f,"PR",[]) raa dr =  OpenLine (Line f Premise):dr
assertionProcessor (f,rule,l) raa dr =
       case raa rule of Nothing -> ErrLine "Unrecognized Inference Rule":dr
                        Just (Right _) -> ErrLine "Not an assertion-justifying rule":dr
                        Just (Left 1) -> unaryInferenceHandler f rule l dr
                        Just (Left 2) -> binaryInferenceHandler f rule l dr
                        _ -> ErrLine "Impossible Error 1":dr
                        --TODO: More cases; ideally make this work for
                        --arbitrary arities of rule

unaryInferenceHandler f r l dr = case l of 
                                      [l1] -> unaryInferFrom f l1 r dr
                                      _       -> ErrLine "wrong number of premises":dr

unaryInferFrom f l1 r dr = case retrieveOne l1 dr of
                                        Nothing -> ErrLine ("line" ++ show l1 ++ "is unavailable"):dr
                                        Just mj -> 
                                            case mj of 
                                                OpenLine j -> OpenLine (Line f $ Inference r [j]):dr
                                                ErrLine _ -> ErrLine (errLineMsg l1):dr
                                                ClosedLine _ -> ErrLine (closedLineMsg l1):dr
                                                ClosureLine -> ErrLine ("line " ++ show l1 ++ "has nothing on it"):dr

binaryInferenceHandler f r l dr = case l of 
                                        [l1,l2] -> binaryInferFrom f l1 l2 r dr
                                        _       -> ErrLine "wrong number of premises":dr

binaryInferFrom f l1 l2 r dr = case retrieveTwo l1 l2 dr of
                                        (Nothing,Nothing) -> (ErrLine $ " the lines " ++ show l1 ++ " and " ++ show l2 ++ " are unavailable"):dr
                                        (Nothing,_) -> (ErrLine $ " the line " ++ show l1 ++ " is unavailable"):dr
                                        (_,Nothing) -> (ErrLine $ " the line " ++ show l2 ++ " is unavailable"):dr
                                        (Just mj1, Just mj2) -> handlePair mj1 mj2 f l1 l2 r dr


--------------------------------------------------------
--1.1.2 Subproof processing
--------------------------------------------------------
--These are functions that are responsible for handling subproofs.

--XXX:there are several repeated applications of forestProcessor here. this
--could be a lot less redundant.

--This function takes a line that introduces a ProofForest, and adjusts the
--DerivationReport
subProofProcessor :: WFLine -> RulesAndArity -> ProofForest -> DerivationReport -> DerivationReport
subProofProcessor (f, "SHOW", _) raa forest dr = closeFrom ((length dr) + 1) $ forestProcessor forest raa (ErrLine "Open Subproof":dr)
subProofProcessor (f, rule, l) raa forest dr = 
        case raa rule of Nothing -> ErrLine "Unrecognized Inference Rule":dr
                         Just (Right 1) -> closeFrom ((length dr) + 1) $ unaryTerminationHandler forest raa f rule l dr
                         Just (Right 2) -> closeFrom ((length dr) + 1) $ binaryTerminationHandler forest raa f rule l dr
                         Just (Left _) -> ErrLine "Not a derivation-closing rule":dr
                         _ -> ErrLine "Impossible Error 2":dr
                         --TODO: More cases; ideally allow for arbitrary
                         --arities.

--this is intended to close the lines below line l, not including l, to make their
--contents unavailable. XXX: It appends an additional unavailable line, on the
--assumption that in addition to the inferences, we have a line occupied by
--the sub-proof closing rule. In a Hardegree system, rather than a Kalish
--and Montegue system, this extra line would be unnecessary.
closeFrom :: Int -> DerivationReport -> DerivationReport 
closeFrom l dr  = ClosureLine:(close lr)
     where close l' = map closeoff (take l' dr) ++ drop l' dr
           lr = length dr - l
           closeoff rl = case rl of
                             ErrLine s    -> ErrLine s
                             OpenLine j   -> ClosedLine j
                             ClosedLine j -> ClosedLine j
                             ClosureLine -> ClosureLine

unaryTerminationHandler :: ProofForest -> RulesAndArity -> PropositionalFormula -> InferenceRule -> [Int] -> DerivationReport -> DerivationReport
unaryTerminationHandler forest raa f r l dr = case l of 
                                                [l1] -> closeWithOne forest raa f l1 r dr
                                                _ -> forestProcessor forest raa (ErrLine "wrong number of lines cited":dr)

binaryTerminationHandler :: ProofForest -> RulesAndArity -> PropositionalFormula -> InferenceRule -> [Int] -> DerivationReport -> DerivationReport
binaryTerminationHandler forest raa f r l dr = case l of 
                                                [l1,l2] -> closeWithTwo forest raa f l1 l2 r dr
                                                _ -> forestProcessor forest raa (ErrLine "wrong number of lines cited":dr)

closeWithOne :: ProofForest -> RulesAndArity -> PropositionalFormula -> Int -> InferenceRule -> DerivationReport -> DerivationReport
closeWithOne forest raa f l1 r dr = case retrieveOne l1 (preProof forest raa dr) of 
                                    Nothing -> forestProcessor forest raa (ErrLine ("line " ++ show l1 ++ " is unavailable"):dr) 
                                    Just mj  -> case mj of
                                        ErrLine _ -> forestProcessor forest raa (ErrLine (errLineMsg l1):dr)
                                        ClosedLine _ -> forestProcessor forest raa (ErrLine (closedLineMsg l1):dr)
                                        OpenLine j -> forestProcessor forest raa (OpenLine (Line f $ Inference r [j]):dr)
                                        ClosureLine -> forestProcessor forest raa (ErrLine ("line " ++ show l1 ++ " has nothing on it"):dr)

preProof :: ProofForest -> RulesAndArity -> DerivationReport -> DerivationReport
preProof forest raa dr = forestProcessor forest raa (ClosureLine:dr)

closeWithTwo :: ProofForest -> RulesAndArity -> PropositionalFormula -> Int -> Int -> InferenceRule -> DerivationReport -> DerivationReport
closeWithTwo forest raa f l1 l2 r dr = case retrieveTwo l1 l2 (preProof forest raa dr) of 
                                    (Nothing, Nothing) -> forestProcessor forest raa (ErrLine ("The lines " ++ show l1 ++ " and " ++ show l2 ++ " are unavailable"):dr) 
                                    (Nothing,_) -> forestProcessor forest raa (ErrLine ("The line " ++ show l1 ++ " is unavailable"):dr) 
                                    (_,Nothing) -> forestProcessor forest raa (ErrLine ("The line " ++ show l2 ++ " is unavailable"):dr) 
                                    (Just mj1, Just mj2) -> forestProcessor forest raa (handlePair mj1 mj2 f l1 l2 r dr)
                                    

--------------------------------------------------------
--2. Helper Functions
--------------------------------------------------------

handlePair :: ReportLine -> ReportLine -> PropositionalFormula -> Int -> Int -> InferenceRule -> DerivationReport -> DerivationReport
handlePair mj1 mj2 f l1 l2 r dr = case (mj1,mj2) of 
                                (OpenLine j1, OpenLine j2) -> OpenLine (Line f $ Inference r [j1,j2]):dr
                                (OpenLine _ , _) -> ErrLine (errorMsg mj2 l2):dr
                                (_, OpenLine _) -> ErrLine (errorMsg mj1 l1):dr
                                _ -> ErrLine (errorMsg mj1 l1 ++ " and " ++ errorMsg mj2 l2):dr

closedLineMsg :: Int -> String
closedLineMsg l1 = "The line " ++ show l1 ++ " is closed, and can't be used"

errLineMsg :: Int -> String 
errLineMsg l1 = "The line " ++ show l1 ++ " depends on something not-well-formed, and can't be used"

closureLineMsg :: Int -> String
closureLineMsg l1 = "The line " ++ show l1 ++ " has nothing on it"

errorMsg :: ReportLine -> Int -> String
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
