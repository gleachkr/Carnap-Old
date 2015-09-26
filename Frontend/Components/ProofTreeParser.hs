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

module Carnap.Frontend.Components.ProofTreeParser where

import Carnap.Systems.NaturalDeduction.ProofTreeDataTypes
import Carnap.Core.Data.AbstractDerivationDataTypes
import Carnap.Languages.Util.ParserTypes
import Text.Parsec as P
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Pos
import Control.Monad (unless)
import Data.Tree
import Data.Functor.Identity

--The goal of this module is to provide a function which transforms a given
--(well-formed) string into a ProofTree. We're going to be passing around
--a formula parser.

--------------------------------------------------------
--1. Functions for parsing strings into ProofTrees
--------------------------------------------------------

parseTheBlock :: Show f => FParser f UserState -> String -> Either ParseError (ProofForest f, Termination)
parseTheBlock fParser = runParser (blockParser fParser) (initState fParser) ""

--parses a string into a proof forest, and a termination (returning SHOW
--when no termination is found), by repeatedly grabbing standard and show
--lines, and then checking for a termination line
blockParser:: Show f => FParser f UserState -> Parsec String UserState (ProofForest f,Termination)
blockParser fParser = do reglines <- mainPartParser fParser
                         hiddenEof <?> "end of proof"
                         return (reglines,("SHOW", []))

subBlockParser:: Show f => FParser f UserState -> Parsec String UserState (ProofForest f,Termination)
subBlockParser fParser = do reglines <- mainPartParser fParser
                            termination <- try getTerminationLine <|> return ("SHOW",[]) 
                            unless (termination == ("SHOW",[])) hiddenEof <?> "end of subproof"
                            return (reglines,termination)

--gathers to the end of an intented block
getIndentedBlock :: Parsec String UserState String 
getIndentedBlock = tabOrFour >> P.manyTill anyChar (try hiddenEof P.<|> try endOfIndentedBlock) 

--strips tabs from an intented block, processes the subproof, and returns
--the results.
--
--XXX:this involves multiple passes, and could probably be streamlined.
processIndentedBlock :: Show f => FParser f UserState -> Parsec String UserState (ProofForest f,Termination)
processIndentedBlock fParser = do x <- getIndentedBlock 
                                  s <- getState
                                  let y = runParser stripIndent s "" x
                                  let forestAndTerm = runParser (subBlockParser fParser) s "" $ stringHandler y
                                  return $ pairHandler forestAndTerm

getErrLine :: Show f => FParser f UserState -> Parsec String UserState (ProofTree f)
getErrLine fParser = do blanks
                        notFollowedBy getTerminationLine <?> "an open line or end of proof"
                        l <- P.many1 (noneOf "\n\t")
                        _ <- try newline <|> return '\n'
                        case stateParse fParser l of
                            Left e -> return $ Node (Left $ show e) []
                            Right f -> return $ Node (Left $ show f) []

--Consumes a show line and a subsequent intented block, and returns a tree
--with the contents of the show line at the root (with the SHOW rule to
--indicate an incomplete subproof, and otherwise with the rule used to
--terminate the subproof) , and the contents of the indented subderivation
--below
getShowLine :: Show f=> FParser f UserState -> Parsec String UserState (ProofTree f)
getShowLine fParser = do blanks
                         _ <- try (string "Show") <|> try (string "SHOW") <|> string "show"
                         _ <- try (do char ':'; return ()) <|> return ()
                         blanks
                         f <- (parser fParser)
                         blanks
                         _ <- newline <|> return '\n'
                         (subder,(rule,lns)) <- try (processIndentedBlock fParser)
                                                <|> return ([],("SHOW",[]))
                         return $ Node (Right (f, rule, lns)) subder

--Consumes a standard line, and returns a single node with that assertion
--and its justification
getStandardLine :: FParser f UserState -> Parsec String UserState (ProofTree f)
getStandardLine fParser = do blanks
                             f <- parser fParser
                             blanks
                             r <- inferenceRuleParser
                             blanks
                             l <- try lineListParser <|> return []
                             let l' = Prelude.map read l :: [Int]
                             blanks
                             _ <- try newline <|> return '\n'
                             return $ Node (Right (f,r,l')) []

--Consumes a termination line, and returns the corresponding termination
getTerminationLine :: Parsec String UserState Termination
getTerminationLine = do blanks
                        _ <- try (string "/") <|> try (string "closed") <|> manyTill letter (char ':') 
                        blanks
                        r <- terminationRuleParser
                        blanks
                        l <- try lineListParser <|> return []
                        let l' = Prelude.map read l :: [Int]
                        many $ oneOf " \t\n"
                        return (':':r,l')

--------------------------------------------------------
--2. HELPER FUNCTIONS
--------------------------------------------------------

mainPartParser:: Show f => FParser f UserState -> Parsec String UserState (ProofForest f)
mainPartParser fParser =  many (try (getShowLine fParser) <|> 
                                try (getStandardLine fParser) <|> 
                                try (getErrLine fParser))

ruleParser :: Parsec String UserState InferenceRule
ruleParser = many1 alphaNum

inferenceRuleParser :: Parsec String UserState InferenceRule
inferenceRuleParser = try ruleParser

terminationRuleParser :: Parsec String UserState InferenceRule
terminationRuleParser = try ruleParser

intParser :: Parsec String UserState String
intParser = P.many1 digit

lineListParser :: Parsec String UserState [String]
lineListParser = intParser `sepEndBy1` many1 (char ' ' <|> char ',')

--Helper functions for dealing with Either
pairHandler :: Show a => Either a ([Tree (Either String b)], (String, [t])) -> ([Tree (Either String b)], (String, [t]))
pairHandler   (Left x) = ([Node (Left $ "pair error" ++ show x) []],("SHOW",[]))
pairHandler   (Right x) = x

stringHandler :: Show a => Either a String -> String
stringHandler (Left x) = "string error" ++ show x
stringHandler (Right x) = x

termHandler :: Show a => Either a (String,[Int]) -> (String,[Int])
termHandler   (Left x) = ("Term Err",[])
termHandler   (Right x) = x

--Some minor parsers
stripIndent :: Parsec String UserState String
stripIndent = P.many (consumeLeadingIndent <|> anyToken)

hiddenEof :: Parsec String UserState ()
hiddenEof = do _ <- P.many (newline <|> char ' ' <|> char '\t')
               eof
                          
endOfIndentedBlock:: Parsec String UserState ()
endOfIndentedBlock = do _ <- newline
                        notFollowedBy tabOrFour 
                        return ()

blanks :: Parsec String UserState ()
blanks = skipMany $ oneOf " \t"

blanks' :: Parsec String () ()
blanks' = skipMany $ oneOf " \t"

tabOrFour :: Parsec String UserState String
tabOrFour = try (string "    ") <|> string "\t"

consumeLeadingIndent :: Parsec String UserState Char
consumeLeadingIndent = do x <- newline
                          try tabOrFour 
                          return x

--------------------------------------------------------
--Experimental stateful parser
--------------------------------------------------------

parseTheBlock' :: Show f => FParser f UserState -> String -> ProofForest f
parseTheBlock' fParser s = case mppf of
                             Right ppf -> toForest fParser ppf
                             Left  ppf -> [Node (Left $ "ptb error:"++ show ppf) []]
        where mppf = runParser toPreForest 0 "" s

toPreForest :: Parsec String Int PreProofForest
toPreForest = do l <- lookAhead line 
                 indent <- getState
                 if (indent > indentOf l) || null l 
                     then return []
                     else do line
                             r <- if isShowLine l then subProof l else return $ Node l []
                             setState indent
                             rest <- toPreForest
                             return $ r:rest
        where line = manyTill anyChar newLineOrEof

subProof l = do setState $ indentOf l + 1
                sp <- toPreForest
                return $ Node l sp

toForest fParser = map (toTree fParser) 

toTree :: Show f => FParser f UserState -> PreProofTree -> ProofTree f
toTree fParser ppt@(Node line rest) = if isShowLine line
                                          then treeFromSubproof fParser ppt
                                          else treeFromloneLine fParser line

treeFromSubproof :: Show f => FParser f UserState -> PreProofTree -> ProofTree f
treeFromSubproof fParser ppf@(Node showline rest) = 
        case rest of 
            [] -> fromShow fParser showline "SHOW" []
                                        (toForest fParser rest)
            _ -> if isTermination lastLine
                         then (fromShow fParser showline
                                   (fst $ terminationData lastLine)
                                   (snd $ terminationData lastLine)
                                   ) (toForest fParser $ init rest)
                         else fromShow fParser showline "SHOW" []
                                        (toForest fParser rest)
                where lastLine = case last rest of Node s _ -> s

treeFromloneLine fParser line = clean $ runParser (loneLine fParser) (initState fParser) "" line
    where clean (Left x) =  Node (Left $ "tfl error:" ++ show x) []
          clean (Right x) = x


fromShow fParser line = clean $ runParser (showLine' fParser) (initState fParser) "" line
    where clean (Left x) = \_ _ -> Node (Left $ "fs error:" ++ show x) 
          clean (Right x) = \a b -> Node (Right (x, a, b)) 

showLine' :: FParser b UserState -> Parsec String UserState b
showLine' fParser = do blanks
                       _ <- try (string "Show") <|> try (string "SHOW") <|> string "show"
                       _ <- try (do char ':'; return ()) <|> return ()
                       blanks
                       f <- (parser fParser)
                       blanks
                       return f

terminationLine' :: Parsec String () Termination
terminationLine' = do blanks'
                      _ <- try (string "/") <|> try (string "closed") <|> manyTill letter (char ':') 
                      blanks'
                      r <- many1 alphaNum
                      blanks'
                      l <- try lineListParser' <|> return []
                      let l' = Prelude.map read l :: [Int]
                      many $ oneOf " \t\n"
                      return (':':r,l')

terminationData :: PrePossibleLine -> (String, [Int])
terminationData l = termHandler $ parse terminationLine' "" l

loneLine fParser = (try (getStandardLine fParser) <|> try (getErrLine fParser))

isShowLine l = take 4 (dropWhile isIndent l) `elem` ["S","show","Show"]

isTermination l = take 1 (dropWhile isIndent l) == ":" --XXX:more flexibility
        -- case parse (try (string "/") <|> 
        --                       try (string "closed") <|> 
        --                       manyTill letter (char ':')) "" l of 
        --               Right _ -> True
        --               Left _ -> False
    
indentOf l = sum (map toVal (indent l))
        where indent     = takeWhile isIndent 
              toVal ' '  = 1
              toVal '\t' = 4
              toVal _    = 0

isIndent x = x `elem` " \t"

intParser' :: Parsec String () String
intParser' = P.many1 digit

lineListParser' :: Parsec String () [String]
lineListParser' = intParser' `sepEndBy1` many1 (char ' ' <|> char ',')

newLineOrEof = (do try newline ; return ()) <|> eof
