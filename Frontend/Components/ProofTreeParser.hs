module Carnap.Frontend.Components.ProofTreeParser where

import Carnap.Systems.NaturalDeduction.ProofTreeDataTypes
import Carnap.Languages.Sentential.PropositionalParser
import Text.Parsec as P
import Data.Tree

--The goal of this module is to provide a function which transforms a given
--(well-formed) string into a ProofTree
--
--------------------------------------------------------
--1. Functions for parsing strings into ProofTrees
--------------------------------------------------------

parseTheBlock :: String -> Either ParseError (ProofForest, Termination)
parseTheBlock b = parse blockParser "" b
--parses a string into a proof forest, and a termination (returning SHOW
--when no termination is found), by repeatedly grabbing standard and show
--lines, and then checking for a termination line
blockParser:: Parsec String st (ProofForest,Termination)
blockParser = do block <- P.many1 $ getStandardLine P.<|> getShowLine
                 termination <- try getTerminationLine P.<|> return ("SHOW",[])
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
                 _ <- try newline
                 (subder,(rule,lns)) <- try processIndentedBlock P.<|> return ([],("SHOW",[]))
                 return $ Node (Right (f, rule, lns)) subder

--Consumes a standard line, and returns a single node with that assertion
--and its justification
getStandardLine :: Parsec String st ProofTree
getStandardLine   = do f <- formulaParser
                       blanks
                       r <- inferenceRuleParser
                       blanks
                       l <- try lineListParser P.<|> return []
                       let l' = Prelude.map read l :: [Int]
                       _ <- try newline
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
--2. HELPER FUNCTIONS
--------------------------------------------------------

--Helper functions for dealing with Either
pairHandler   (Left x) = ([Node (Left $ "pair error" ++ show x) []],("SHOW",[]))
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
