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
--Main processing functions
--------------------------------------------------------

type ErrorList = [String]

--The proof tree is first converted into a derivation that reflects the
--actual structure of the argument. We get an errorlist here if the
--prooftree doesn't actually describe a derivation (because a rule is
--getting the wrong number of premises or something).
--
--The resulting derivation is then checked for correctness. We get an
--errorlist here if there are some steps that aren't correct, for example
--if a rule is applied in such a way that the conclusion does not follow.
handleTree :: ProofTree -> Either ErrorList Argument
handleTree t = do d <- treeToDerivaton t
                  derivationProves d

--this runs a ProofTree through a tree-processing function that returns two
--lists: an errorlist, and a list of what derivations are constructed on
--each line. It cleans this output, and returns what's needed for the
--tree-handler
treeToDerivatonList :: ProofTree -> Either ErrorList PropDerivation

--this processes a ProofTree by building up a list of judgements that have
--been successfully constructed on each line, and of errors in attempted
--judgement construction.
treeProcessor :: ProofTree -> ErrorList -> [Maybe PropositionalJudgement] -> 
                    (ErrorList, [Maybe PropositionalJudgement])
treeProcessor (Node (Left err) []) el dl = ("formula syntax error":el,Nothing:dl)
treeProcessor (Node (Right line) []) el dl = assertionProcessor line el dl
treeProcessor (Node (Right line) f) el dl = subProofProcessor line f el dl
--I don't think this last case can arise
treeProcessor (Node (Left err) f) el dl = undefined

--this processes a line containing a well-formed assertion, in the context
--of an errorlist and a list of possibly completed judgments.
assertionProcessor :: (PropositionalFormula,PropRule,[Int]) -> ErrorList -> 
                        [Maybe PropositionalJudgement] ->
                            (ErrorList, [Maybe PropositionalJudgement])
assertionProcessor (f,MP,l) el dl = binaryInferenceHandler f MP l el dl
assertionProcessor (f,ADJ,l) el dl = binaryInferenceHandler f ADJ l el dl
assertionProcessor (f,PR,l) el dl = ("":el, (Just $ Line f Premise):dl)
        
binaryInferenceHandler f r l el dl = case l of 
                                        [l1,l2] -> binaryInferFrom f l1 l2 r el dl
                                        _       -> ("wrong number of premises":el,Nothing:dl)

binaryInferFrom f l1 l2 r el dl = case retrieveTwo l1 l2 dl of
                                        Nothing -> ("unavailable lines":el, Nothing:dl)
                                        (Just j1 j2) -> 
                                            case r of
                                                MP -> ("":el, (Just $ Line f $ ModusPonens j1 j2):dl)
                                                ADJ -> ("":el, (Just $ Line f $ Adjunction j1 j2):dl)

retrieveTwo l1 l2 dl = if length dl > max l1 l2 
                           then Just (reverse dl !! (l1 - 1), reverse dl !! (l2 -1))
                           else Nothing


