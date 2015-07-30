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
atomParser = try relationParser <|> try predicateParser <|> try equalsParser <|> sentenceParser 

quantifierParser :: Parsec String st FirstOrderFormula
quantifierParser = do s <- string "A" <|> string "E"
                      v <- parseFreeVar
                      f <- subFormulaParser
                      let bf = substitute f v --partially applied, returning a function
                      return $ if s == "A" then ub bf else eb bf --which we bind

sentenceParser :: Parsec String st FirstOrderFormula
sentenceParser = do s <- many1 $ alphaNum <|> char '_'
                    return $ prop s

predicateParser :: Parsec String st FirstOrderFormula
predicateParser = do s <- many1 $ alphaNum <|> char '_'
                     _ <- char '('
                     t <- parseTerm
                     _ <- char ')'
                     return $ L.pred s t

relationParser :: Parsec String st FirstOrderFormula
relationParser =  do s <- many1 $ alphaNum <|> char '_'
                     _ <- char '('
                     t1 <- parseTerm
                     _ <- char ','
                     t2 <- parseTerm
                     _ <- char ')'
                     return $ rel s t1 t2

equalsParser :: Parsec String st FirstOrderFormula
equalsParser =  do t1 <- parseTerm
                   spaces
                   _ <- char '='
                   spaces
                   t2 <- parseTerm
                   return $ equals t1 t2

parseTerm :: Parsec String st FirstOrderTerm
parseTerm = try parseFreeVar <|> parseConstant

parseConstant :: Parsec String st FirstOrderTerm
parseConstant = do s <- many1 $ alphaNum <|> char '_'
                   return $ cn s

parseFreeVar :: Parsec String st FirstOrderTerm
parseFreeVar = do _ <- string "x_"
                  n <- number
                  return $ freeVarn n

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
