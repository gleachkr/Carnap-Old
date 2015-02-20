{-# LANGUAGE  DeriveDataTypeable #-}
module Main where
import Haste hiding (style)
import Haste.Foreign
import Haste.HPlay.View as H
import Data.Tree
import PropositionalLanguage
import PropositionalDerivations
import PropositionalParser
import Text.Parsec as P
import Prelude hiding (div,all,id,print,getChar, putStr, putStrLn,getLine)

betterText = script ! atr "type" "text/javascript" ! src "./textarea-plus.user.js" $ noHtml
betterCss= link ! atr "rel" "stylesheet" ! atr "type" "text/css" ! href "./proofpad.css" 

main = do addHeader betterText
          addHeader betterCss
          runBody $ do
                contents <- getMultilineText "" `fire` OnKeyUp
                let possibleParsing = parse indentBlockParser "" ( contents ++ "\n" )
                wraw $ (forestToDom $ forestHandler possibleParsing) ! id "root"

type ProofTree = Tree PossibleLine

type ProofForest = Forest PossibleLine

type PossibleLine = Either String (PropositionalFormula, PropRule, [Int])

type ParserState = (Int, --the current line number, starts at one, increments with completed lines
                   [(Int, Either String PropositionalJudgement)] --association list of currently available justified assertions/error messages
                   )

forestHandler (Left x) = [Node (Left $ "forest error" ++ show x) []]
forestHandler (Right x) = x

stringHandler (Left x) = "string error" ++ show x
stringHandler (Right x) = x

forestToDom :: ProofForest -> Perch
forestToDom t = H.span $ mapM_ treeToDom t
                       
--transforms a ProofTree into an html structure
treeToDom :: ProofTree -> Perch
treeToDom (Node (Right (f,SHOW,_)) []) = div $ do H.span $ "Show: " ++ show f
treeToDom (Node (Right (f,SHOW,_)) d) = div $ do H.span $ "Show: " ++ show f
                                                 div ! atr "class" "indent" $ forestToDom d
treeToDom (Node (Right (f,r,s)) []) = div $ do H.span f 
                                               H.span $ do H.span r 
                                                           H.span s
treeToDom (Node (Left s) _) = div s

--parses a string into a proof forest, by repeatedly grabbing standard and
--show lines
indentBlockParser:: Parsec String st ProofForest
indentBlockParser = P.many $ getStandardLine P.<|> getShowLine

--takes a string of lines with leading tabs, strips the tabs, and returns
--a tree consisting of their contents (as a forest), with a base labeled
--"indent". This is not optimal, since it involves multiple
--passes over the same thing; first gathering it as a string (in getting
--the block) then the tab-stripping pass, then the reparsing of the block.
--
--This needs to also multiply increment the line number, and feed
--a judgement into any pending show line.
gatherIndentedBlock :: Parsec String st ProofForest
gatherIndentedBlock = do x <- getIndentedBlock 
                         let y = parse stripTabs "" x
                         let f = parse indentBlockParser "" $ (stringHandler y) ++ ['\n']
                         return $ forestHandler f

--gathers to the end of an intented block
getIndentedBlock :: Parsec String st String 
getIndentedBlock = do tab
                      P.manyTill anyChar $ try hiddenEof P.<|> try endOfIndentedBlock

--consumes a show line and a subsequent intented block, and returns a tree
--with the contents of the show line at the root, and the contents of the
--indented subderivation below
getShowLine :: Parsec String st ProofTree
getShowLine = do _ <- oneOf "sS"
                 skipMany (alphaNum P.<|> char ':')
                 blanks
                 f <- formulaParser
                 try newline
                 subder <- try gatherIndentedBlock P.<|> return [] 
                 --need to generalize here to distinguish between closed
                 --and open subproofs. The idea would be to detect these
                 --while gathering the indented block, then to insert the
                 --appropriate justification and line reference in the
                 --return value (the line closing the subproof) when one is available.
                 return $ Node (Right (f, SHOW, [])) subder

--Consumes a standard line, and returns a single node with that assertion
--and its justification
--
--On the stateful parser approach, this needs to increment the line number, and to
--register a new judgement, if one becomes available
getStandardLine :: Parsec String st ProofTree
getStandardLine   = do f <- formulaParser
                       blanks
                       r <- ruleParser
                       blanks
                       l <- try lineListParser P.<|> return []
                       let l' = Prelude.map read l :: [Int]
                       try newline
                       return $ Node (Right (f,r,l')) []

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


