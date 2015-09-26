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
module Carnap.Languages.Sentential.PropositionalParser where

import Carnap.Languages.Sentential.PropositionalLanguage
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.ParserTypes
import Text.Parsec as P
import Text.Parsec.Expr

----operator parsers. Might be cleaner to just make these into local
--functions within the opTable, and to abstract the repeated pattern here.

parseAnd :: Parsec String st (PropositionalFormula -> PropositionalFormula -> PropositionalFormula)
parseAnd = do spaces
              _ <- string "/\\" <|> string "∧" <|> string "^" <|> string "&"
              spaces
              return land
              
parseOr :: Parsec String st (PropositionalFormula -> PropositionalFormula -> PropositionalFormula)
parseOr = do spaces
             _ <- string "\\/" <|> string "∨" <|> string "v" <|> string "|"
             spaces
             return lor

parseIf :: Parsec String st (PropositionalFormula -> PropositionalFormula -> PropositionalFormula)
parseIf = do spaces
             _ <- string "=>" <|> string "->" <|> string ">" <|> string "→"
             spaces
             return lif

parseIff :: Parsec String st (PropositionalFormula -> PropositionalFormula -> PropositionalFormula)
parseIff = do spaces
              _ <- try (string "<=>") <|> try (string "<->") <|> string "<>" <|> string "↔"
              spaces
              return liff

parseNeg :: Parsec String st (PropositionalFormula -> PropositionalFormula)
parseNeg = do spaces
              _ <- string "-" <|> string "~" <|> string "¬"
              return lneg

subFormulaParser :: Parsec String st PropositionalFormula
subFormulaParser = parenParser <|> negParser <|> atomParser

number :: Parsec String st Int
number = do { ds <- many1 digit; return (read ds) } <?> "number"

parenParser :: Parsec String st PropositionalFormula
parenParser = do _ <- char '(' 
                 x <- formulaParser
                 _ <-char ')' 
                 return x

atomParser :: Parsec String st PropositionalFormula
atomParser = do s <- many1 $ alphaNum <|> char '_'
                return $ prop s

negParser :: Parsec String st PropositionalFormula
negParser = do _ <- try parseNeg
               f <- subFormulaParser
               return $ lneg f

formulaParser :: Parsec String st PropositionalFormula
formulaParser = buildExpressionParser opTable subFormulaParser

formulaParserSL :: FParser PropositionalFormula UserState
formulaParserSL = FParser{ parser = buildExpressionParser opTable subFormulaParser,
                         initState = UserState {strict = False}
                         }

opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]


