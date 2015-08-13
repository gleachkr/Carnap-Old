module Carnap.Frontend.Components.ProofTreeParser where

import Carnap.Systems.NaturalDeduction.ProofTreeDataTypes
import Carnap.Core.Data.AbstractDerivationDataTypes
import Text.Parsec as P
import Data.Tree

--The goal of this module is to provide a function which transforms a given
--(well-formed) string into a ProofTree. We're going to be passing around
--a formula parser.

--------------------------------------------------------
--1. Functions for parsing strings into ProofTrees
--------------------------------------------------------

type FParser f = Parsec String () f 

parseTheBlock :: Show f => FParser f -> String -> Either ParseError (ProofForest f, Termination)
parseTheBlock fParser = parse (blockParser fParser) ""
--parses a string into a proof forest, and a termination (returning SHOW
--when no termination is found), by repeatedly grabbing standard and show
--lines, and then checking for a termination line
blockParser:: Show f => FParser f -> Parsec String () (ProofForest f,Termination)
blockParser fParser = do reglines    <- many (try (getShowLine fParser) <|> try (getStandardLine fParser) <|> getErrLine fParser)
                         _ <- try newline <|> return '\n'
                         termination <- try getTerminationLine <|> return ("SHOW",[]) <?> "terminating inference"
                         if termination == ("SHOW",[]) then return () else eof <?> "end of subproof"
                         return (reglines,termination)

--gathers to the end of an intented block
getIndentedBlock :: Parsec String st String 
getIndentedBlock = tabOrFour >> P.manyTill anyChar (try hiddenEof P.<|> try endOfIndentedBlock) 

--strips tabs from an intented block, processes the subproof, and returns
--the results.
--
--XXX:this involves multiple passes, and could probably be streamlined.
processIndentedBlock :: Show f => FParser f -> Parsec String st (ProofForest f,Termination)
processIndentedBlock fParser = do x <- getIndentedBlock 
                                  let y = parse stripTabs "" x
                                  let forestAndTerm = parse (blockParser fParser) "" $ stringHandler y
                                  return $ pairHandler forestAndTerm

getErrLine :: Show f => FParser f -> Parsec String st (ProofTree f)
getErrLine fParser = do notFollowedBy getTerminationLine
                        l <- P.many1 (noneOf ['\n','\t'])
                        _ <- try newline <|> return '\n'
                        case parse fParser "" l of
                            Left e -> return $ Node (Left $ show e) []
                            Right f -> return $ Node (Left $ show f) []

--Consumes a show line and a subsequent intented block, and returns a tree
--with the contents of the show line at the root (with the SHOW rule to
--indicate an incomplete subproof, and otherwise with the rule used to
--terminate the subproof) , and the contents of the indented subderivation
--below
getShowLine :: Show f=> FParser f -> Parsec String () (ProofTree f)
getShowLine fParser = do _ <- oneOf "sS"
                         skipMany (alphaNum P.<|> char ':')
                         blanks
                         f <- fParser
                         blanks
                         _ <- newline <|> return '\n'
                         (subder,(rule,lns)) <- try (processIndentedBlock fParser)
                                                <|> return ([],("SHOW",[]))
                         return $ Node (Right (f, rule, lns)) subder

--Consumes a standard line, and returns a single node with that assertion
--and its justification
getStandardLine :: FParser f -> Parsec String () (ProofTree f)
getStandardLine fParser = do blanks
                             f <- fParser
                             blanks
                             r <- inferenceRuleParser
                             blanks
                             l <- try lineListParser <|> return []
                             let l' = Prelude.map read l :: [Int]
                             blanks
                             _ <- try newline <|> return '\n'
                             return $ Node (Right (f,r,l')) []

--Consumes a termination line, and returns the corresponding termination
getTerminationLine :: Parsec String st Termination
getTerminationLine = do blanks
                        _ <- try (string "/") <|> try (string "closed") <|> manyTill letter (char ':') 
                        blanks
                        r <- terminationRuleParser
                        blanks
                        l <- try lineListParser <|> return []
                        let l' = Prelude.map read l :: [Int]
                        blanks
                        return (':':r,l')

--------------------------------------------------------
--2. HELPER FUNCTIONS
--------------------------------------------------------

ruleParser :: Parsec String st InferenceRule
ruleParser = many1 alphaNum

inferenceRuleParser :: Parsec String st InferenceRule
inferenceRuleParser = try ruleParser

terminationRuleParser :: Parsec String st InferenceRule
terminationRuleParser = try ruleParser

intParser :: Parsec String st String
intParser = P.many1 digit

lineListParser :: Parsec String st [String]
lineListParser = intParser `sepEndBy1` many1 (char ' ' <|> char ',')

--Helper functions for dealing with Either
pairHandler :: Show a => Either a ([Tree (Either String b)], (String, [t])) -> ([Tree (Either String b)], (String, [t]))
pairHandler   (Left x) = ([Node (Left $ "pair error" ++ show x) []],("SHOW",[]))
pairHandler   (Right x) = x

stringHandler :: Show a => Either a String -> String
stringHandler (Left x) = "string error" ++ show x
stringHandler (Right x) = x

--Some minor parsers
stripTabs :: Parsec String st String
stripTabs = P.many (consumeLeadingTab <|> anyToken)

hiddenEof :: Parsec String st ()
hiddenEof = do _ <- P.many newline
               eof
                          
endOfIndentedBlock:: Parsec String st ()
endOfIndentedBlock = do _ <- newline
                        notFollowedBy tabOrFour
                        return ()

blanks :: Parsec String st ()
blanks = skipMany $ oneOf " \t"

tabOrFour :: Parsec String st String
tabOrFour = try (string "    ") <|> string "\t"

consumeLeadingTab :: Parsec String st Char
consumeLeadingTab = do x <- newline
                       try tabOrFour
                       return x
