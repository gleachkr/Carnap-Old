module Carnap.Languages.Sentential.PropositionalParser where

import Carnap.Languages.Sentential.PropositionalLanguage
import Carnap.Languages.Util.LanguageClasses
import Text.Parsec as P
import Text.Parsec.Expr

----operator parsers. Might be cleaner to just make these into local
--functions within the opTable, and to abstract the repeated pattern here.

parseAnd :: Parsec String st (PropositionalFormula -> PropositionalFormula -> PropositionalFormula)
parseAnd = do spaces
              _ <- string "/\\" <|> string "∧"
              spaces
              return land
              
parseOr :: Parsec String st (PropositionalFormula -> PropositionalFormula -> PropositionalFormula)
parseOr = do spaces
             _ <- string "\\/" <|> string "∨"
             spaces
             return lor

parseIf :: Parsec String st (PropositionalFormula -> PropositionalFormula -> PropositionalFormula)
parseIf = do spaces
             _ <- string "=>" <|> string "→"
             spaces
             return lif

parseIff :: Parsec String st (PropositionalFormula -> PropositionalFormula -> PropositionalFormula)
parseIff = do spaces
              _ <- string "<=>" <|> string "↔"
              spaces
              return liff

parseNeg :: Parsec String st (PropositionalFormula -> PropositionalFormula)
parseNeg = do spaces
              _ <- string "-" <|> string "¬"
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

--Operators for parsec

opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

