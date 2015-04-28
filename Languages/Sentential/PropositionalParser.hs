module Carnap.Languages.Sentential.PropositionalParser where

import Carnap.Languages.Sentential.PropositionalLanguage
import Carnap.Languages.Util.LanguageClasses
import Carnap.Core.Data.AbstractDerivationDataTypes
import Text.Parsec as P
import Text.Parsec.Expr

----operator parsers. Might be cleaner to just make these into local
--functions within the opTable, and to abstract the repeated pattern here.

parseAnd :: Parsec String st (PropositionalFormula -> PropositionalFormula -> PropositionalFormula)
parseAnd = do _ <- string "/\\"
              return land
              
parseOr :: Parsec String st (PropositionalFormula -> PropositionalFormula -> PropositionalFormula)
parseOr = do _ <- string "\\/"
             return lor

parseIf :: Parsec String st (PropositionalFormula -> PropositionalFormula -> PropositionalFormula)
parseIf = do _ <- string "=>"
             return lif

parseNeg :: Parsec String st (PropositionalFormula -> PropositionalFormula)
parseNeg = do _ <- string "-"
              return lneg

subFormulaParser :: Parsec String st PropositionalFormula
subFormulaParser = do { char '(' ; x <- formulaParser; char ')' ; return x }
            <|> atomParser

number :: Parsec String st Int
number = do { ds <- many1 digit; return (read ds) } <?> "number"

atomParser = do _ <- string "P_"
                n <- number
                return $ pn n

formulaParser = buildExpressionParser opTable subFormulaParser

--Operators for parsec

opTable = [[ Prefix parseNeg], 
          [Infix parseOr AssocLeft, Infix parseAnd AssocLeft],
          [Infix parseIf AssocNone]]

ruleParser :: Parsec String st InferenceRule
ruleParser = many1 alphaNum

inferenceRuleParser :: Parsec String st InferenceRule
inferenceRuleParser = try ruleParser

terminationRuleParser :: Parsec String st InferenceRule
terminationRuleParser = try ruleParser

intParser :: Parsec String st String
intParser = P.many1 digit

lineListParser = intParser `sepEndBy1` char ',' 
