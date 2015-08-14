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
module Carnap.Languages.FirstOrder.QuantifiedParser where

import Carnap.Languages.FirstOrder.QuantifiedLanguage
import Carnap.Languages.Util.LanguageClasses as L
import Carnap.Core.Data.AbstractDerivationDataTypes
import Text.Parsec as P
import Text.Parsec.Expr

----operator parsers. Might be cleaner to just make these into local
--functions within the opTable, and to abstract the repeated pattern here.

parseAnd :: Parsec String st (FirstOrderFormula -> FirstOrderFormula -> FirstOrderFormula)
parseAnd = do spaces
              _ <- string "/\\" <|> string "∧"
              spaces
              return land
              
parseOr :: Parsec String st (FirstOrderFormula -> FirstOrderFormula -> FirstOrderFormula)
parseOr = do spaces
             _ <- string "\\/" <|> string "∨"
             spaces
             return lor

parseIf :: Parsec String st (FirstOrderFormula -> FirstOrderFormula -> FirstOrderFormula)
parseIf = do spaces
             _ <- string "=>" <|> string "→"
             spaces
             return lif

parseIff :: Parsec String st (FirstOrderFormula -> FirstOrderFormula -> FirstOrderFormula)
parseIff = do spaces
              _ <- string "<=>" <|> string "↔"
              spaces
              return liff

parseNeg :: Parsec String st (FirstOrderFormula -> FirstOrderFormula)
parseNeg = do spaces
              _ <- string "-" <|> string "¬"
              return lneg

subFormulaParser :: Parsec String st FirstOrderFormula
subFormulaParser = do { char '(' ; x <- formulaParser; char ')' ; return x }
            <|> try quantifierParser
            <|> atomParser

atomParser :: Parsec String st FirstOrderFormula
atomParser = choice [try relationParser, try predicateParser, try equalsParser, sentenceParser]

quantifierParser :: Parsec String st FirstOrderFormula
quantifierParser = do s <- char 'A' <|> char 'E'
                      (v,c) <- parseFreeVarName
                      f <- subFormulaParser
                      let bf = substitute f v --partially applied, returning a function
                      return $ if s == 'A' then ub c bf else eb c bf --which we bind

sentenceParser :: Parsec String st FirstOrderFormula
sentenceParser = do s <- many1 $ alphaNum <|> char '_'
                    return $ prop s

predicateParser :: Parsec String st FirstOrderFormula
predicateParser = do c <- upper
                     s <- many $ alphaNum <|> char '_'
                     _ <- char '('
                     t <- parseTerm
                     _ <- char ')'
                     return $ L.pred (c:s) t

relationParser :: Parsec String st FirstOrderFormula
relationParser =  do c <- upper
                     s <- many $ alphaNum <|> char '_'
                     _ <- char '('
                     t1 <- parseTerm
                     _ <- char ','
                     t2 <- parseTerm
                     _ <- char ')'
                     return $ rel (c:s) t1 t2

equalsParser :: Parsec String st FirstOrderFormula
equalsParser =  do t1 <- parseTerm
                   spaces
                   _ <- char '='
                   spaces
                   t2 <- parseTerm
                   return $ equals t1 t2

parseTerm :: Parsec String st FirstOrderTerm
parseTerm = choice [try parseBFunc, try parseUFunc, try parseConstant, parseFreeVar]

parseConstant :: Parsec String st FirstOrderTerm
parseConstant = do c <- alphaNum
                   if c `elem` ['x','y','z'] then lookAhead alphaNum else return '*'
                   s <- many $ alphaNum <|> char '_'
                   return $ cn $ c : s

parseUFunc :: Parsec String st FirstOrderTerm
parseUFunc = do c <- lower
                s <- many $ alphaNum <|> char '_'
                _ <- char '('
                t <- parseTerm
                _ <- char ')'
                return $ fn (c:s) t

parseBFunc :: Parsec String st FirstOrderTerm
parseBFunc = do c <- upper
                s <- many $ alphaNum <|> char '_'
                _ <- char '('
                t1 <- parseTerm
                _ <- char ','
                t2 <- parseTerm
                _ <- char ')'
                return $ fn2 (c:s) t1 t2

parseFreeVar :: Parsec String st FirstOrderTerm
parseFreeVar = choice [try $ do _ <- string "x_"
                                n <- number
                                return $ freeVarn n,
                             do c <- oneOf "xyzw"
                                case c of
                                    'x' -> return $ freeVarn 0
                                    'y' -> return $ freeVarn 1
                                    'z' -> return $ freeVarn 2
                                    'w' -> return $ freeVarn 3
                      ]

parseFreeVarName :: Parsec String st (FirstOrderTerm, String)
parseFreeVarName = choice [try $ do s <- string "x_"
                                    n <- number
                                    return (freeVarn n,"x_" ++ s),
                             do c <- oneOf "xyzw"
                                case c of
                                    'x' -> return (freeVarn 0,[c])
                                    'y' -> return (freeVarn 1,[c])
                                    'z' -> return (freeVarn 2,[c])
                                    'w' -> return (freeVarn 3,[c])
                      ]

formulaParser :: Parsec String st FirstOrderFormula
formulaParser = buildExpressionParser opTable subFormulaParser

--Operators for parsec

opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

ruleParser :: Parsec String st InferenceRule
ruleParser = many1 alphaNum

inferenceRuleParser :: Parsec String st InferenceRule
inferenceRuleParser = try ruleParser

terminationRuleParser :: Parsec String st InferenceRule
terminationRuleParser = try ruleParser

intParser :: Parsec String st String
intParser = P.many1 digit

number :: Parsec String st Int
number = do { ds <- many1 digit; return (read ds) } <?> "number"

lineListParser = intParser `sepEndBy1` char ',' 
