{-# LANGUAGE  DeriveDataTypeable #-}
module Main where
import Haste hiding (style)
import Haste.Foreign
import Haste.HPlay.View as H
import Data.Tree
import ProofTreeDataTypes
import PropositionalLanguage
import PropositionalDerivations
import PropositionalParser
import Text.Parsec as P
import Prelude hiding (div,all,id,print,getChar, putStr, putStrLn,getLine)

betterText = script ! atr "type" "text/javascript" ! src "./textarea-plus.user.js" $ noHtml
betterCss= link ! atr "rel" "stylesheet" ! atr "type" "text/css" ! href "./proofpad.css" 

--the program begins by including some javascript to make the textarea
--easier to work with, and some css. It then inserts into the body of the
--html a textarea and an event that, on each keypress, 
-- 1. attempts to parse the contents of the text area into a (ProofTree,Termination) pair.
-- 2. converts the ProofTree to html, gives the result id "root".
--TODO: Add room for a function that checks a prooftree for correctness,
--and returns the entailment that the tree witnesses, or a line-by-line of errors
--TODO: Add a function that inserts an html element in which the errors or
--witnessed entailement can be viewed

main = do addHeader betterText
          addHeader betterCss
          runBody $ do
                contents <- getMultilineText "" `fire` OnKeyUp
                let possibleParsing = parse blockParser "" ( contents ++ "\n" )
                wraw $ (forestToDom $ fst $ pairHandler possibleParsing) ! id "root"


--------------------------------------------------------
--Functions for converting a ProofTree to an html structure
--------------------------------------------------------
                       
--XXX: this could be clearer if some repetitions were factored out.
treeToDom :: ProofTree -> Perch
treeToDom (Node (Right (f,SHOW,_)) []) = div $ do H.span $ "Show: " ++ show f
treeToDom (Node (Right (f,SHOW,_)) d) = div $ do H.span $ "Show: " ++ show f
                                                 div ! atr "class" "open" $ forestToDom d
treeToDom (Node (Right (f,r,s)) []) = div $ do H.span f 
                                               H.span $ do H.span r 
                                                           H.span s
treeToDom (Node (Right (f,CP,s)) d) = div $ do H.span $ "Show: " ++ show f
                                               div ! atr "class" "closed" $ do forestToDom d
                                                                               div $ do H.span ! atr "class" "termination" $ ""
                                                                                        H.span $ do H.span CP
                                                                                                    H.span s
treeToDom (Node (Left s) _) = div s

forestToDom :: ProofForest -> Perch
forestToDom t = H.span $ mapM_ treeToDom t

--------------------------------------------------------
--Functions for parsing strings into ProofTrees
--------------------------------------------------------

--parses a string into a proof forest, and a termination (returning SHOW
--when no termination is found), by repeatedly grabbing standard and show
--lines, and then checking for a termination line
blockParser:: Parsec String st (ProofForest,Termination)
blockParser = do block <- P.many $ getStandardLine P.<|> getShowLine
                 termination <- try getTerminationLine P.<|> return (SHOW,[])
                 return (block,termination)

--gathers to the end of an intented block
getIndentedBlock :: Parsec String st String 
getIndentedBlock = tab >> (P.manyTill anyChar $ try hiddenEof P.<|> try endOfIndentedBlock)

--strips tabs from an intented block, processes the subproof, and returns
--the results.
--
--XXX:this involves multiple passes, and could probably be streamlined.
processIndentedBlock :: Parsec String st (ProofForest,Termination)
processIndentedBlock = do x <- getIndentedBlock 
                          let y = parse stripTabs "" x
                          let forestAndTerm = parse blockParser "" $ (stringHandler y) ++ ['\n']
                          return $ pairHandler forestAndTerm
 
--Consumes a show line and a subsequent intented block, and returns a tree
--with the contents of the show line at the root (with the SHOW rule to
--indicate an incomplete subproof, and otherwise with the rule used to
--terminate the subproof) , and the contents of the indented subderivation
--below
getShowLine :: Parsec String st ProofTree
getShowLine = do _ <- oneOf "sS"
                 skipMany (alphaNum P.<|> char ':')
                 blanks
                 f <- formulaParser
                 try newline
                 (subder,(rule,lines)) <- try processIndentedBlock P.<|> return ([],(SHOW,[]))
                 return $ Node (Right (f, rule, lines)) subder

--Consumes a standard line, and returns a single node with that assertion
--and its justification
getStandardLine :: Parsec String st ProofTree
getStandardLine   = do f <- formulaParser
                       blanks
                       r <- inferenceRuleParser
                       blanks
                       l <- try lineListParser P.<|> return []
                       let l' = Prelude.map read l :: [Int]
                       try newline
                       return $ Node (Right (f,r,l')) []

--Consumes a termination line, and returns the corresponding termination
getTerminationLine :: Parsec String st Termination
getTerminationLine = do r <- terminationRuleParser
                        blanks
                        l <- try lineListParser P.<|> return []
                        let l' = Prelude.map read l :: [Int]
                        try newline
                        return (r,l')

--------------------------------------------------------
--HELPER FUNCTIONS
--------------------------------------------------------

--Helper functions for dealing with Either
pairHandler   (Left x) = ([Node (Left $ "pair error" ++ show x) []],(SHOW,[]))
pairHandler   (Right x) = x

stringHandler (Left x) = "string error" ++ show x
stringHandler (Right x) = x

--Some minor parsers
stripTabs = P.many (consumeLeadingTab P.<|> anyToken)

hiddenEof = do x <- newline
               eof
               return x
                          
endOfIndentedBlock = do x <- newline
                        notFollowedBy tab
                        return x

blanks = skipMany $ oneOf " \t"

consumeLeadingTab = do x <- newline
                       try tab
                       return x


