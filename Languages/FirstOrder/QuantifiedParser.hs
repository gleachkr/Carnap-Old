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
import Carnap.Languages.Util.ParserTypes
import Carnap.Core.Data.AbstractDerivationDataTypes
import Control.Applicative ((<*),(*>))
import Text.Parsec as P
import Text.Parsec.Expr



--------------------------------------------------------
--2. Generic Parsers
--------------------------------------------------------
--These are parsers that are shared by different syntaxes for FOL.

--------------------------------------------------------
--2.1 Operator Parsers
--------------------------------------------------------
--operator parsers. Might be cleaner to just make these into local
--functions within the opTable, and to abstract the repeated pattern here.

parseAnd :: Parsec String UserState (FirstOrderFormula -> FirstOrderFormula -> FirstOrderFormula)
parseAnd = do spaces
              _ <- string "/\\" <|> string "∧" <|> string "^" <|> string "&" <|> string "and"
              spaces
              return land
              
parseOr :: Parsec String UserState (FirstOrderFormula -> FirstOrderFormula -> FirstOrderFormula)
parseOr = do spaces
             _ <- string "\\/" <|> string "∨" <|> string "v" <|> string "|" <|> string "or"
             spaces
             return lor

parseIf :: Parsec String UserState (FirstOrderFormula -> FirstOrderFormula -> FirstOrderFormula)
parseIf = do spaces
             _ <- string "=>" <|> string "->" <|> string ">" <|> string "→" <|> string "only if"
             spaces
             return lif

parseIff :: Parsec String UserState (FirstOrderFormula -> FirstOrderFormula -> FirstOrderFormula)
parseIff = do spaces
              _ <- try (string "<=>") <|> try (string "<->") <|> string "<>" <|> string "↔" <|> string "if and only if"
              spaces
              return liff

parseNeg :: Parsec String UserState (FirstOrderFormula -> FirstOrderFormula)
parseNeg = do spaces
              _ <- string "-" <|> string "~" <|> string "¬" <|> string "not "
              return lneg

--------------------------------------------------------
--1.2 Variable parsers
--------------------------------------------------------

parseFreeVar :: Parsec String UserState FirstOrderTerm
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

parseFreeVarName :: Parsec String UserState (FirstOrderTerm, String)
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
--1.3 Formula Parsers
--------------------------------------------------------

subFormulaParser :: Parsec String UserState FirstOrderFormula
subFormulaParser = wrapped (parser formulaParser)
            <|> try quantifierParser
            <|> negParser
            <|> atomParser

atomParser :: Parsec String UserState FirstOrderFormula
atomParser = do s <- getState
                if strict s 
                    then choice [try equalsParser, try strictRelationParser, try strictPredicateParser, strictSentenceParser]
                    else choice [try equalsParser, try relationParser, try predicateParser, sentenceParser]


negParser :: Parsec String UserState FirstOrderFormula
negParser = do _ <- try parseNeg
               f <- subFormulaParser
               return $ lneg f

quantifierParser :: Parsec String UserState FirstOrderFormula
quantifierParser = do s <- oneOf "AE∀∃"
                      (v,c) <- parseFreeVarName
                      f <- subFormulaParser
                      let bf = substitute f v --partially applied, returning a function
                      return $ if s `elem` "A∀" then ub c bf else eb c bf --which we bind

equalsParser :: Parsec String UserState FirstOrderFormula
equalsParser =  do t1 <- parseTerm
                   spaces
                   _ <- char '='
                   spaces
                   t2 <- parseTerm
                   return $ equals t1 t2

parseTerm :: Parsec String UserState FirstOrderTerm
parseTerm = do s <- getState
               if strict s 
                   then choice [try strictParseBFunc, try strictParseUFunc, try strictParseConstant, parseFreeVar]
                   else choice [try parseBFunc, try parseUFunc, try parseConstant, parseFreeVar]

opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

strictFormulaParser :: FParser FirstOrderFormula UserState
strictFormulaParser = FParser{ parser = buildExpressionParser opTable subFormulaParser,
                         initState = UserState {strict = True}
                         }

--------------------------------------------------------
--3. Lax Parsers
--------------------------------------------------------
--These are parsers for a syntax where predicates and sentences can be
--almost arbitrary strings. This means sacrificing some concision, but it
--makes it possible to formalize argumetnts in a way that may be easier to
--follow.

formulaParser :: FParser FirstOrderFormula UserState
formulaParser = FParser{ parser = buildExpressionParser opTable subFormulaParser,
                         initState = UserState {strict = False}
                         }
                         
sentenceParser :: Parsec String UserState FirstOrderFormula
sentenceParser = do s <- many1 $ alphaNum <|> char '_'
                    return $ prop s


predicateParser :: Parsec String UserState FirstOrderFormula
predicateParser = do c <- letter
                     s <- many $ alphaNum <|> char '_'
                     t <- wrapped parseTerm
                     return $ L.pred (c:s) t

relationParser :: Parsec String UserState FirstOrderFormula
relationParser =  do c <- letter
                     s <- many $ alphaNum <|> char '_'
                     (t1,t2) <- wrappedPair parseTerm parseTerm
                     return $ rel (c:s) t1 t2


parseConstant :: Parsec String UserState FirstOrderTerm
parseConstant = do c <- alphaNum
                   if c `elem` ['x','y','z','w'] then lookAhead alphaNum else return '*'
                   s <- many $ alphaNum <|> char '_'
                   return $ cn $ c : s

parseUFunc :: Parsec String UserState FirstOrderTerm
parseUFunc = do c <- letter
                s <- many $ alphaNum <|> char '_'
                t <- wrapped parseTerm
                return $ fn (c:s) t

parseBFunc :: Parsec String UserState FirstOrderTerm
parseBFunc = do c <- letter
                s <- many $ alphaNum <|> char '_'
                (t1,t2) <- wrappedPair parseTerm parseTerm
                return $ fn2 (c:s) t1 t2

--------------------------------------------------------
--3. Strict Parsers
--------------------------------------------------------
--These are parsers for an FOL syntax in which each predicate, relation,
--constant and setence letter is a single symbol. This lets us avoid a lot
--of ambiguity.


strictSentenceParser :: Parsec String UserState FirstOrderFormula
strictSentenceParser = do s <- letter
                          return $ prop [s]

strictRelationParser :: Parsec String UserState FirstOrderFormula
strictRelationParser =  do c <- letter
                           (t1,t2) <- optionallyWrappedPair parseTerm parseTerm
                           return $ rel [c] t1 t2

strictPredicateParser :: Parsec String UserState FirstOrderFormula
strictPredicateParser = do c <- letter
                           t <- optionallyWrapped parseTerm
                           return $ L.pred [c] t

strictParseConstant :: Parsec String UserState FirstOrderTerm
strictParseConstant = do c <- alphaNum
                         if c `elem` ['x','y','z','w'] then unexpected "variable" else return ()
                         return $ cn [c] 

strictParseUFunc :: Parsec String UserState FirstOrderTerm
strictParseUFunc = do c <- letter
                      t <- parseTerm
                      return $ fn [c] t

strictParseBFunc :: Parsec String UserState FirstOrderTerm
strictParseBFunc = do c <- letter
                      (t1, t2) <- wrappedPair parseTerm parseTerm
                      return $ fn2 [c] t1 t2

--------------------------------------------------------
--Helper Parsers
--------------------------------------------------------

ruleParser :: Parsec String UserState InferenceRule
ruleParser = many1 alphaNum

inferenceRuleParser :: Parsec String UserState InferenceRule
inferenceRuleParser = try ruleParser

terminationRuleParser :: Parsec String UserState InferenceRule
terminationRuleParser = try ruleParser

intParser :: Parsec String UserState String
intParser = P.many1 digit

number :: Parsec String UserState Int
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
