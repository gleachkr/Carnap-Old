module ProofTreeHandler where
import Data.Tree
import ProofTreeDataTypes
import PropositionalLanguage
import PropositionalDerivations
import JudgementHandler
import AbstractDerivationDataTypes

--The goal of this module is to provide a function that transforms a given
--ProofTree into either an argument that the tree witnesses the validity
--of, or into a line-by-line list of errors

--------------------------------------------------------
--1. Main processing functions
--------------------------------------------------------

type ErrorList     = [String]
type WFLine        = (PropositionalFormula, InferenceRule, [Int])
type PossibleJList = [Maybe PropositionalJudgement]

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

--TODO: Improve derivationProves to potentially return an errorlist
handleForest f raa ruleSet = do j <- forestToJudgement f raa
                                return $ derivationProves ruleSet j

--------------------------------------------------------
--1.1 Tree and Forest to derivation functions
--------------------------------------------------------
--These are functions that are collectively resonsible for turning
--a ProofForest into PropositionalDerivation; the PropositionalDerivation
--can then be checked.

--This runs a ProofForest through a processing function that returns two
--lists: an errorlist, and a list of what derivations are constructed on
--each line. It cleans this output, and returns what's needed for the
--Forest-Handler
forestToJudgement :: ProofForest -> RulesAndArity -> Either ErrorList PropositionalJudgement
forestToJudgement f raa = if all (== "") el 
                          then Right $ conclude $ reverse dl !! (length f - 1) 
                          --length f-1 isn't quite right. It'll go wrong
                          --when there is a subproof between the first line
                          --of the main derivation, and the last line.
                          else Left el
        where el = fst $ forestProcessor f raa [] []
              dl = snd $ forestProcessor f raa [] []
              conclude (Just j) = j
              --this case should not arise
              conclude (Nothing) = Line (pn 666) Premise

--this processes a ProofTree by building up a list of judgements that have
--been successfully constructed on each line, and of errors in attempted
--judgement construction.
treeProcessor :: ProofTree -> RulesAndArity -> ErrorList -> PossibleJList -> 
                    (ErrorList, PossibleJList)
treeProcessor (Node (Left err) []) raa el dl   = ("formula syntax error":el,Nothing:dl)
treeProcessor (Node (Right line) []) raa el dl = assertionProcessor line raa el dl
treeProcessor (Node (Right line) f) raa el dl  = subProofProcessor line raa f el dl
--I don't think this last case can arise
treeProcessor (Node (Left err) f) raa el dl    = ("shouldn't happen":el,Nothing:dl)

--this processes a ProofForest by folding together the errorlists and
--derivationlists that arise from its individual trees.
forestProcessor :: ProofForest -> RulesAndArity -> ErrorList -> PossibleJList -> 
                    (ErrorList, PossibleJList)
forestProcessor forest raa el dl = foldl combineWithTree (el, dl) forest
    where combineWithTree (el',dl') t =  treeProcessor t raa el' dl'


--------------------------------------------------------
--1.1.1 Assertion Processing 
--------------------------------------------------------
--These are functions that are responsible for handling single-assertion
--lines

--this processes a line containing a well-formed assertion, in the context
--of an errorlist and a list of possibly completed judgments.
assertionProcessor :: WFLine -> RulesAndArity -> ErrorList -> PossibleJList ->
                            (ErrorList, PossibleJList)
assertionProcessor (f,"PR",[]) raa el dl = ("":el, (Just $ Line f Premise):dl)
assertionProcessor (f,rule,l) raa el dl =
       case raa rule of Nothing -> ("Unrecognized Inference Rule":el, Nothing:dl)
                        Just (Right _) -> ("Not an assertion-justifying rule":el, Nothing:dl)
                        Just (Left 1) -> unaryInferenceHandler f rule l el dl
                        Just (Left 2) -> binaryInferenceHandler f rule l el dl
                        _ -> ("Impossible Error 1":el,Nothing:dl)
                        --TODO: More cases; ideally make this work for
                        --arbitrary arities of rule

unaryInferenceHandler f r l el dl = case l of 
                                        [l1] -> unaryInferFrom f l1 r el dl
                                        _       -> ("wrong number of premises":el,Nothing:dl)

unaryInferFrom f l1 r el dl = case retrieveOne l1 dl of
                                        Nothing -> ("unavailable lines":el, Nothing:dl)
                                        Just mj -> 
                                            case mj of 
                                                Just j -> ("":el, (Just $ Line f $ Inference r [j]):dl)
                                                _ -> ("depends on unjustified lines":el, Nothing:dl)

binaryInferenceHandler f r l el dl = case l of 
                                        [l1,l2] -> binaryInferFrom f l1 l2 r el dl
                                        _       -> ("wrong number of premises":el,Nothing:dl)

binaryInferFrom f l1 l2 r el dl = case retrieveTwo l1 l2 dl of
                                        Nothing -> ("unavailable lines":el, Nothing:dl)
                                        Just (mj1, mj2) -> 
                                            case (mj1,mj2) of 
                                                (Just j1, Just j2) -> ("":el, (Just $ Line f $ Inference r [j1,j2]):dl)
                                                _ -> ("depends on unjustified lines":el, Nothing:dl)


--------------------------------------------------------
--1.1.2 Subproof processing
--------------------------------------------------------
--These are functions that are responsible for handling subproofs.

--XXX:there are several repeated applications of forestProcessor here. this
--could be a lot less redundant.

--This function takes a line that introduces a ProofForest, and adjusts the
--ErrorList and the list of subderivations accordingly
subProofProcessor :: WFLine -> RulesAndArity -> ProofForest -> ErrorList -> PossibleJList -> (ErrorList,PossibleJList)
subProofProcessor (f, "SHOW", _) raa forest el dl = closeFrom ((length el) + 1) $ forestProcessor forest raa ("Open Subproof":el) (Nothing:dl) 
subProofProcessor (f, rule, l) raa forest el dl = 
        case raa rule of Nothing -> ("Unrecognized Inference Rule":el, Nothing:dl)
                         Just (Right 1) -> closeFrom ((length el) + 1) $ unaryTerminationHandler forest raa f rule l el dl
                         Just (Right 2) -> closeFrom ((length el) + 1) $ binaryTerminationHandler forest raa f rule l el dl
                         Just (Left _) -> ("Not a derivation-closing rule":el, Nothing:dl)
                         _ -> ("Impossible Error 2":el, Nothing:dl)
                         --TODO: More cases; ideally allow for arbitrary
                         --arities.

--this is intended to close the lines below line l, not including l, to make their
--contents unavailable. XXX: It appends an additional unavailable line, on the
--assumption that in addition to the inferences, we have a line occupied by
--the sub-proof closing rule. In a Hardegree system, rather than a Kalish
--and Montegue system, this extra line would be unnecessary.
closeFrom :: Int -> (ErrorList, PossibleJList) -> (ErrorList, PossibleJList)
closeFrom l (el,dl) = ("":el, Nothing:close lr )
     where close l' = map (\_ -> Nothing) (take l' dl) ++ drop l' dl
           lr = length el - l

unaryTerminationHandler :: ProofForest -> RulesAndArity -> PropositionalFormula -> InferenceRule -> [Int] -> ErrorList -> PossibleJList -> (ErrorList, PossibleJList)
unaryTerminationHandler forest raa f r l el dl = case l of 
                                                [l1] -> closeWithOne forest raa f l1 r el dl
                                                _ -> forestProcessor forest raa ("wrong number of lines cited":el) (Nothing:dl)

binaryTerminationHandler :: ProofForest -> RulesAndArity -> PropositionalFormula -> InferenceRule -> [Int] -> ErrorList -> PossibleJList -> (ErrorList, PossibleJList)
binaryTerminationHandler forest raa f r l el dl = case l of 
                                                [l1,l2] -> closeWithTwo forest raa f l1 l2 r el dl
                                                _ -> forestProcessor forest raa ("wrong number of lines cited":el) (Nothing:dl)

closeWithOne :: ProofForest -> RulesAndArity -> PropositionalFormula -> Int -> InferenceRule -> ErrorList -> PossibleJList -> (ErrorList, PossibleJList)
closeWithOne forest raa f l1 r el dl = case retrieveOne l1 (preProof forest raa el dl) of 
                                    Nothing -> forestProcessor forest raa ("unavailable line":el) (Nothing:dl)
                                    Just mj  -> case mj of
                                        Nothing -> forestProcessor forest raa ("depends on an unjustified line":el) (Nothing:dl)
                                        Just j -> forestProcessor forest raa ("":el) ((Just $ Line f $ Inference r [j]):dl)

preProof :: ProofForest -> RulesAndArity -> ErrorList -> PossibleJList -> PossibleJList
preProof forest raa el dl = snd $ forestProcessor forest raa ("":el) (Nothing:dl)


closeWithTwo :: ProofForest -> RulesAndArity -> PropositionalFormula -> Int -> Int -> InferenceRule -> ErrorList -> PossibleJList -> (ErrorList, PossibleJList)
closeWithTwo forest raa f l1 l2 r el dl = case retrieveTwo l1 l2 (preProof forest raa el dl) of 
                                    Nothing -> forestProcessor forest raa ("unavailable line":el) (Nothing:dl)
                                    Just (mj1,mj2) -> 
                                        case (mj1,mj2) of 
                                            (Just j1, Just j2) -> forestProcessor forest raa ("":el) ((Just $ Line f $ Inference r [j1,j2]):dl)
                                            _ -> forestProcessor forest raa ("depends on an unjustified line":el) (Nothing:dl)

--------------------------------------------------------
--2. Helper Functions
--------------------------------------------------------

retrieveOne :: Int -> [t] -> Maybe t
retrieveOne l1 dl = if  l1 > length dl
                           then Nothing 
                           else Just (reverse dl !! (l1 - 1))

retrieveTwo :: Int -> Int -> [t] -> Maybe (t, t)
retrieveTwo l1 l2 dl = if  max l1 l2 > length dl
                           then Nothing 
                           else Just (reverse dl !! (l1 - 1), reverse dl !! (l2 -1))
