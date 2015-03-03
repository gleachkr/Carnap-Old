module ProofTreeHandler where
import Data.Tree
import ProofTreeDataTypes
import PropositionalLanguage
import PropositionalDerivations
import AbstractDerivationDataTypes

--The goal of this module is to provide a function that transforms a given
--ProofTree into either an argument that the tree witnesses the validity
--of, or into a line-by-line list of errors

--------------------------------------------------------
--1. Main processing functions
--------------------------------------------------------

type ErrorList     = [String]
type WFLine        = (PropositionalFormula, PropRule, [Int])
type PossibleJList = [Maybe PropositionalJudgement]

--The proof forest is first converted into a derivation that reflects the
--actual structure of the argument. We get an errorlist here if the
--ProofForest doesn't actually describe a derivation (because a rule is
--getting the wrong number of premises or something).
--
--The resulting derivation is then checked for correctness. We get an
--errorlist here if there are some steps that aren't correct, for example
--if a rule is applied in such a way that the conclusion does not follow.

--TODO: Improve derivationProves to potentially return an errorlist
handleForest :: ProofForest -> Either ErrorList (Maybe Psequent)
handleForest f = do j <- forestToJudgement f
                    return $ derivationProves j

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
forestToJudgement :: ProofForest -> Either ErrorList PropositionalJudgement
forestToJudgement f = if all (== "") el 
                          then Right $ conclude $ reverse dl !! (length f - 1) 
                          --length f-1 isn't quite right. It'll go wrong
                          --when there is a subproof between the first line
                          --of the main derivation, and the last line.
                          else Left el
        where el = fst $ forestProcessor f [] []
              dl = snd $ forestProcessor f [] []
              conclude (Just j) = j
              --this case should not arise
              conclude (Nothing) = Line (pn 666) Premise

--this processes a ProofTree by building up a list of judgements that have
--been successfully constructed on each line, and of errors in attempted
--judgement construction.
treeProcessor :: ProofTree -> ErrorList -> PossibleJList -> 
                    (ErrorList, PossibleJList)
treeProcessor (Node (Left err) []) el dl = ("formula syntax error":el,Nothing:dl)
treeProcessor (Node (Right line) []) el dl = assertionProcessor line el dl
treeProcessor (Node (Right line) f) el dl = subProofProcessor line f el dl
--I don't think this last case can arise
treeProcessor (Node (Left err) f) el dl = ("shouldn't happen":el,Nothing:dl)

--this processes a ProofForest by folding together the errorlists and
--derivationlists that arise from its individual trees.
forestProcessor :: ProofForest -> ErrorList -> PossibleJList -> 
                    (ErrorList, PossibleJList)
forestProcessor forest el dl = foldl combineWithTree (el, dl) forest
    where combineWithTree (el',dl') t =  treeProcessor t el' dl'


--------------------------------------------------------
--1.1.1 Assertion Processing 
--------------------------------------------------------
--These are functions that are responsible for handling single-assertion
--lines

--this processes a line containing a well-formed assertion, in the context
--of an errorlist and a list of possibly completed judgments.
assertionProcessor :: (PropositionalFormula,PropRule,[Int]) -> ErrorList -> 
                        PossibleJList ->
                            (ErrorList, PossibleJList)
assertionProcessor (f,MP,l) el dl = binaryInferenceHandler f MP l el dl
assertionProcessor (f,ADJ,l) el dl = binaryInferenceHandler f ADJ l el dl
assertionProcessor (f,PR,l) el dl = ("":el, (Just $ Line f Premise):dl)
        
binaryInferenceHandler f r l el dl = case l of 
                                        [l1,l2] -> binaryInferFrom f l1 l2 r el dl
                                        _       -> ("wrong number of premises":el,Nothing:dl)

binaryInferFrom f l1 l2 r el dl = case retrieveTwo l1 l2 dl of
                                        Nothing -> ("unavailable lines":el, Nothing:dl)
                                        Just (mj1, mj2) -> 
                                            case (mj1,mj2) of 
                                                (Just j1, Just j2) ->
                                                    case r of
                                                        MP -> ("":el, (Just $ Line f $ ModusPonens j1 j2):dl)
                                                        ADJ -> ("":el, (Just $ Line f $ Adjunction j1 j2):dl)
                                                _ -> ("depends on unjustified lines":el, Nothing:dl)

retrieveTwo l1 l2 dl = if  max l1 l2 > length dl
                           then Nothing 
                           else Just (reverse dl !! (l1 - 1), reverse dl !! (l2 -1))

--------------------------------------------------------
--1.1.2 Subproof processing
--------------------------------------------------------
--These are functions that are responsible for handling subproofs.

--XXX:there are several repeated applications of forestProcessor here. this
--could be a lot less redundant.

--This function takes a line that introduces a ProofForest, and adjusts the
--ErrorList and the list of subderivations accordingly
subProofProcessor :: WFLine -> ProofForest -> ErrorList -> PossibleJList -> (ErrorList,PossibleJList)
subProofProcessor line forest el dl = case line of
                                          (f, SHOW, _) -> 
                                                closeFrom ((length el) + 1) $ forestProcessor forest ("Open Subproof":el) (Nothing:dl) 
                                          (f, CP, l) -> 
                                                closeFrom ((length el) + 1) $ unaryTerminationHandler forest f CP l el dl

--this is intended to close the lines below line l, not including l, to make their
--contents unavailable.
closeFrom :: Int -> (ErrorList, PossibleJList) -> (ErrorList, PossibleJList)
closeFrom l (el,dl) = (el, close lr dl)
     where close l' dl' = map (\x -> Nothing) (take l' dl) ++ drop l' dl
           lr = length el - l

unaryTerminationHandler forest f r l el dl = case l of 
                                                [l1] -> closeWith forest f l1 r el dl
                                                _ -> forestProcessor forest ("wrong number of lines cited":el) (Nothing:dl)

closeWith forest f l1 r el dl = case retrieveOne l1 forest el dl of 
                                    Nothing -> (forestProcessor forest ("unavailable line":el) (Nothing:dl))
                                    Just j  -> 
                                        case r of
                                            CP -> forestProcessor forest ("":el) ((Just $ Line f $ ConditionalProof j):dl)
                                            --add other cases later

retrieveOne :: Int -> ProofForest -> ErrorList -> PossibleJList -> (Maybe PropositionalJudgement)
retrieveOne l1 forest el dl = if l1 > length preProof 
                                  then Nothing
                                  else reverse preProof !! (l1 - 1)
                            where preProof = snd $ forestProcessor forest ("":el) (Nothing:dl)
