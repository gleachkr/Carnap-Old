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
module Main (
    main
) where

import Options.Applicative as O
import Data.List 
import Data.Maybe (catMaybes)
import Data.Map as M (lookup, fromList, Map(..), member, foldrWithKey) 
import Data.Tree
import System.IO
import Text.Parsec as P
import Control.Monad
import Carnap.Frontend.Util.HelperFunctions (toPremConcPair, matchesSequent, cleanGoalPair)
import Carnap.Frontend.Ghcjs.Components.BoxSettings --FIXME:Should be independent of GHCJS. 

data Command = GradeCommand GradeOptions

data GradeOptions = GradeOptions { targets :: [FilePath]
                                 , writeToFile :: Bool}

type Problem = [String]

type Modifiers = [String]

type Goal = String

flagParser = subparser $ command "Grade" (info (helper <*> gradeOptions) 
                                            (progDesc "Grade Submitted Work"
                                            ))

gradeOptions :: Parser Command
gradeOptions = GradeCommand <$> (GradeOptions <$> O.many (argument str $ metavar "FILES"
                                                   <> help "Files to grade")
                                                <*> switch ( short 'w'
                                                          <> long "write"
                                                          <> help "Write grades to metadata block in FILES"))

main :: IO ()
main = execParser opts >>= dispatch
    where opts = ( info (helper <*> flagParser) 
                   (fullDesc 
                    <> header "carnap - a command line interface for the Carnap proof assistant"
                   )
                 )

dispatch :: Command -> IO ()
dispatch c = case c of GradeCommand go -> gradeRoutine go

gradeRoutine :: GradeOptions -> IO ()
gradeRoutine go = do when (writeToFile go) $ mapM_ gradeFile (targets go)
                     mapM_ echoGrade (targets go)

echoGrade f = do s <- readFile f
                 let mheader = getHeader s f
                 let mprobs = getProblems s f
                 case mheader of Right header -> putStr $ formatMetaDataCSV header
                                 Left e -> hPutStrLn stderr $ show e
                 case mprobs of Right probs -> putStr $ toPercent $ probResults probs
                                Left e -> hPutStrLn stderr $ show e
                 putStr "\n"

gradeFile f = do s <- readFile f
                 let mheader = getHeader s f
                 let mrest = getBody s f
                 case (mheader,mrest) of (Right header, Right rest) -> 
                                            if member "Grade" header then return () else addGrade f s header rest
                                         _ -> return ()

addGrade f s header rest = do let mprobs = getProblems s f
                              case mprobs of Left e -> return ()
                                             Right probs -> writeFile f (graded probs)
    where graded probs = "---\n" ++ 
                         metaDatatoString header ++ 
                         "Grade: " ++ toPercent (probResults probs) ++ "\n" ++ 
                         "---\n" ++ 
                         rest

probResults probs = zipWith matches probs theArgs
    where theArgs = map (\(m,g,l) -> collapseMaybe $ checksOut (unlines l) $ applyMods m initSettingsFOL) probs
          matches (m,g,_) marg = case (parseGoal g (applyMods m initSettingsFOL), marg) of 
                                            (Just gseq, Just arg) -> matchesSequent gseq arg
                                            _ -> False
          collapseMaybe mb = case mb of Just a -> a
                                        Nothing -> Nothing
          modifications m = catMaybes $ map (`M.lookup` modTableFOL) m
          applyMods m init = foldr ($) init (modifications m)
              


parseGoal g settings = theGoal
    where (premstring,_:concstring) = break (\x -> x == ';' || x == '⊢' ) g
          goalpair = toPremConcPair (concstring) (premstring) settings
          theGoal = cleanGoalPair goalpair

getProblems :: String -> SourceName -> Either P.ParseError [(Modifiers, Goal, Problem)]
getProblems s f = parse problemsParser f s
    where problemsParser = many1 (try problemParser)
          problemParser = do skipMany nonTick
                             mods <- openingLine <?> "Problem Opening Line"
                             goal <- nonTick
                             plines <- P.many nonTick
                             (replicateM 3 $ char '`') <?> "Problem Closing Line"
                             return $ (mods, goal, plines)
          nonTick = do notFollowedBy $ string "```"
                       manyTill anyChar newline
          openingLine = do string "```"
                           mods <- char '{' *> mod `sepBy1` space <* char '}'
                           newline
                           return mods
          mod = do char '.'
                   many1 alphaNum

getHeader :: String -> SourceName -> Either P.ParseError (Map String String)
getHeader s f = parse headerParser f s 
    where headerParser = do (replicateM 3 $ char '-') >> newline <?> "Header Opening Line"
                            hlines <- P.many nonDash
                            (replicateM 3 $ char '-') >> newline <?> "Header Closing Line"
                            return $ fromList hlines

getBody :: String -> SourceName -> Either P.ParseError String
getBody s f = parse headerParser f s 
    where headerParser = do (replicateM 3 $ char '-') >> newline <?> "Header Opening Line"
                            P.many nonDash
                            (replicateM 3 $ char '-') >> newline <?> "Header Closing Line"
                            body <- P.many lines 
                            return $ unlines body
          lines = manyTill anyChar newline 
                       
nonDash = do notFollowedBy $ string "---"
             k <- manyTill (noneOf ":") (char ':') <?> "Header Key"
             skipMany $ space
             v <- manyTill anyChar newline <?> "Header Value"
             return (k,v)

checksOut s settings = if null theForest
                                  then return Nothing
                                  else case theForestHandler theForest theRules theRuleSet of 
                                                 (Left derRept) -> return Nothing
                                                 (Right (Left _,derRept)) -> return Nothing
                                                 (Right (Right arg, derRept)) -> return $ Just arg
                where theRules = rules settings
                      theRuleSet = ruleset settings
                      theForestHandler = fhandler settings
                      theParParser = pparser settings
                      theFormulaParser = fparser settings
                      theParser = theParParser theFormulaParser
                      theForest = theParser ( s ++ "\n" )

toPercent l = show $ (fromIntegral $ length (filter (== True) l)) / (fromIntegral $ length l)

metaDatatoString = foldrWithKey (\k v acc -> acc ++ k ++ ": " ++ v ++ "\n" ) ""

formatMetaDataCSV = foldrWithKey (\k v acc -> acc ++ if k /= "Grade" then v ++ ", " else "") "" 
