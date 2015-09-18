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
import Control.Applicative ((<*),(*>))
import Text.Parsec as P
import Text.Parsec.Expr


--------------------------------------------------------
--1. Generic Parsers
--------------------------------------------------------
--These are parsers that are shared by different syntaxes for FOL.

--------------------------------------------------------
--1.1 Operator Parsers
--------------------------------------------------------
--operator parsers. Might be cleaner to just make these into local
--functions within the opTable, and to abstract the repeated pattern here.

parseAnd :: Parsec String st (FirstOrderFormula -> FirstOrderFormula -> FirstOrderFormula)
parseAnd = do spaces
              _ <- string "/\\" <|> string "∧" <|> string "^" <|> string "&" <|> string "and"
              spaces
              return land
              
parseOr :: Parsec String st (FirstOrderFormula -> FirstOrderFormula -> FirstOrderFormula)
parseOr = do spaces
             _ <- string "\\/" <|> string "∨" <|> string "v" <|> string "|" <|> string "or"
             spaces
             return lor

parseIf :: Parsec String st (FirstOrderFormula -> FirstOrderFormula -> FirstOrderFormula)
parseIf = do spaces
             _ <- string "=>" <|> string "->" <|> string ">" <|> string "→" <|> string "only if"
             spaces
             return lif

parseIff :: Parsec String st (FirstOrderFormula -> FirstOrderFormula -> FirstOrderFormula)
parseIff = do spaces
              _ <- try (string "<=>") <|> try (string "<->") <|> string "<>" <|> string "↔" <|> string "if and only if"
              spaces
              return liff

parseNeg :: Parsec String st (FirstOrderFormula -> FirstOrderFormula)
parseNeg = do spaces
              _ <- string "-" <|> string "~" <|> string "¬" <|> string "not "
              return lneg

--------------------------------------------------------
--1.2 Variable parsers
--------------------------------------------------------

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
parseFreeVarName = choice [try $ do _ <- string "x_"
                                    n <- number
                                    return (freeVarn n,"x_" ++ show n),
                             do c <- oneOf "xyzw"
                                case c of
                                    'x' -> return (freeVarn 0,[c])
                                    'y' -> return (freeVarn 1,[c])
                                    'z' -> return (freeVarn 2,[c])
                                    'w' -> return (freeVarn 3,[c])
                      ]
--------------------------------------------------------
--2. Lax Parsers
--------------------------------------------------------
--These are parsers for a syntax where predicates and sentences can be
--almost arbitrary strings. This means sacrificing some concision, but it
--makes it possible to formalize argumetnts in a way that may be easier to
--follow.

subFormulaParser :: Parsec String st FirstOrderFormula
subFormulaParser = do wrapped formulaParser
            <|> negParser
            <|> try quantifierParser
            <|> atomParser

atomParser :: Parsec String st FirstOrderFormula
atomParser = choice [try relationParser, try predicateParser, try equalsParser, sentenceParser]

negParser :: Parsec String st FirstOrderFormula
negParser = do _ <- try parseNeg
               f <- subFormulaParser
               return $ lneg f

quantifierParser :: Parsec String st FirstOrderFormula
quantifierParser = do s <- oneOf "AE∀∃"
                      (v,c) <- parseFreeVarName
                      f <- subFormulaParser
                      let bf = substitute f v --partially applied, returning a function
                      return $ if s `elem` "A∀" then ub c bf else eb c bf --which we bind

sentenceParser :: Parsec String st FirstOrderFormula
sentenceParser = do s <- many1 $ alphaNum <|> char '_'
                    return $ prop s


predicateParser :: Parsec String st FirstOrderFormula
predicateParser = do c <- upper
                     s <- many $ alphaNum <|> char '_'
                     t <- wrapped parseTerm
                     return $ L.pred (c:s) t

relationParser :: Parsec String st FirstOrderFormula
relationParser =  do c <- upper
                     s <- many $ alphaNum <|> char '_'
                     (t1,t2) <- wrappedPair parseTerm parseTerm
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
                   if c `elem` ['x','y','z','w'] then lookAhead alphaNum else return '*'
                   s <- many $ alphaNum <|> char '_'
                   return $ cn $ c : s

parseUFunc :: Parsec String st FirstOrderTerm
parseUFunc = do c <- lower
                s <- many $ alphaNum <|> char '_'
                t <- wrapped parseTerm
                return $ fn (c:s) t

parseBFunc :: Parsec String st FirstOrderTerm
parseBFunc = do c <- lower
                s <- many $ alphaNum <|> char '_'
                (t1,t2) <- wrappedPair parseTerm parseTerm
                return $ fn2 (c:s) t1 t2

opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

formulaParser :: Parsec String st FirstOrderFormula
formulaParser = buildExpressionParser opTable subFormulaParser

--------------------------------------------------------
--3. Strict Parsers
--------------------------------------------------------
--These are parsers for an FOL syntax in which each predicate, relation,
--constant and setence letter is a single symbol. This lets us avoid a lot
--of ambiguity.

strictAtomParser :: Parsec String st FirstOrderFormula
strictAtomParser = choice [try strictRelationParser, try strictPredicateParser, try strictEqualsParser, strictSentenceParser]

strictSentenceParser :: Parsec String st FirstOrderFormula
strictSentenceParser = do s <- upper
                          return $ prop [s]

strictRelationParser :: Parsec String st FirstOrderFormula
strictRelationParser =  do c <- upper
                           (t1,t2) <- optionallyWrappedPair strictParseTerm strictParseTerm
                           return $ rel [c] t1 t2

strictPredicateParser :: Parsec String st FirstOrderFormula
strictPredicateParser = do c <- upper
                           t <- optionallyWrapped strictParseTerm
                           return $ L.pred [c] t

strictEqualsParser :: Parsec String st FirstOrderFormula
strictEqualsParser =  do t1 <- strictParseTerm
                         spaces
                         _ <- char '='
                         spaces
                         t2 <- strictParseTerm
                         return $ equals t1 t2

strictParseTerm :: Parsec String st FirstOrderTerm
strictParseTerm = choice [try strictParseBFunc, try strictParseUFunc, try strictParseConstant, parseFreeVar]

strictParseConstant :: Parsec String st FirstOrderTerm
strictParseConstant = do c <- lower
                         if c `elem` ['x','y','z','w'] then unexpected "variable" else return ()
                         return $ cn [c] 

strictParseUFunc :: Parsec String st FirstOrderTerm
strictParseUFunc = do c <- lower
                      t <- strictParseTerm
                      return $ fn [c] t

strictParseBFunc :: Parsec String st FirstOrderTerm
strictParseBFunc = do c <- upper
                      (t1, t2) <- wrappedPair strictParseTerm strictParseTerm
                      return $ fn2 [c] t1 t2

strictSubFormulaParser :: Parsec String st FirstOrderFormula
strictSubFormulaParser = wrapped strictFormulaParser
            <|> strictNegParser
            <|> try strictQuantifierParser
            <|> strictAtomParser

strictNegParser :: Parsec String st FirstOrderFormula
strictNegParser = do _ <- try parseNeg
                     f <- strictSubFormulaParser
                     return $ lneg f

strictQuantifierParser :: Parsec String st FirstOrderFormula
strictQuantifierParser = do s <- oneOf "AE∀∃"
                            (v,c) <- parseFreeVarName
                            f <- strictSubFormulaParser
                            let bf = substitute f v --partially applied, returning a function
                            return $ if s `elem` "A∀" then ub c bf else eb c bf --which we bind

strictOpTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

strictFormulaParser :: Parsec String st FirstOrderFormula
strictFormulaParser = buildExpressionParser opTable strictSubFormulaParser

--------------------------------------------------------
--Helper Parsers
--------------------------------------------------------

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

wrapped p = char '(' *> p <* char ')'

wrappedPair p1 p2 = do _ <- char '('
                       v1 <- p1
                       _ <- char ','
                       v2 <- p2
                       _ <- char ')'
                       return (v1,v2)

optionallyWrapped p =  try (wrapped p) <|> p

optionallyWrappedPair p1 p2 =  try (wrappedPair p1 p2) <|> do v1 <- p1
                                                              v2 <- p2
                                                              return (v1,v2)
