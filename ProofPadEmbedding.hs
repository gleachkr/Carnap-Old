--{-# LANGUAGE  OverloadedStrings, DeriveDataTypeable #-} 
module Main where

import Haste hiding (style)
import Haste.Foreign
import Haste.Prim
import Haste.HPlay.View as H
import Data.Tree
import Data.List (intercalate)
import Rules (Sequent(Sequent))
import ProofTreeDataTypes
import ProofTreeHandler
import ProofTreeParser
import ClassicalSententialLogic (classicalRules, classicalSLruleSet)
import PropositionalLanguage
import PropositionalDerivations
import Prelude hiding (div,all,id,print,getChar, putStr, putStrLn,getLine)

--the program begins by including some javascript to make the textarea
--easier to work with, and some css. It then inserts into the body of the
--html a textarea and an event that, on each keypress, 
-- 1. attempts to parse the contents of the text area into a (ProofTree,Termination) pair.
-- 2. converts the ProofTree to html, gives the result id "root".
--TODO: Add room for a function that checks a prooftree for correctness,
--and returns the entailment that the tree witnesses, or a line-by-line of errors
--TODO: Add a function that inserts an html element in which the errors or
--witnessed entailement can be viewed

main = do pboxes <- elemsByClass "proofbox"
          mapM_ activateCarnap pboxes
          setTimeout 60 $ do _ <- eval $ toJSStr"$(\".lined\").linedtextarea({selectedLine:1});"
                             return ()

activateCarnap pbox = do originalContents <- getProp pbox "innerHTML"
                         setProp pbox "innerHTML" ""
                         runWidget (carnapWith originalContents) pbox
                
carnapWith text = do contents <- getMultilineText text `fire` OnKeyUp ! atr "class" "lined"
                     let possibleParsing = parseTheBlock ( contents ++ "\n" )
                     let theForest = fst $ pairHandler possibleParsing
                     wraw $ div "" ! id "rslt"
                     wraw $ (forestToDom theForest ) ! id "root"
                     case handleForest theForest classicalRules classicalSLruleSet of 
                         (Left errlist)     -> wraw $ toDomList (reverse errlist) ! id "analysis"
                         (Right (Just arg)) -> at "rslt" Insert $ wraw $ H.span $ display arg
                         (Right Nothing)    -> at "rslt" Insert $ wraw $ H.span "invalid"

analyzeForest f = case (handleForest f classicalRules classicalSLruleSet) of 
                            (Left errlist)     -> reverse errlist
                            (Right (Just arg)) -> [show arg]
                            (Right Nothing)    -> ["invalid"]

display (Sequent ps c) = intercalate " . " (Prelude.map show ps) ++ " ∴ " ++ show c


--------------------------------------------------------
--Functions for converting html structures
--------------------------------------------------------
                       
--XXX: this could be clearer if some repetitions were factored out.
treeToDom :: ProofTree -> Perch
treeToDom (Node (Right (f,"SHOW",_)) []) = div $ do H.span $ "Show: " ++ show f
treeToDom (Node (Right (f,"SHOW",_)) d) = div $ do H.span $ "Show: " ++ show f
                                                   div ! atr "class" "open" $ forestToDom d
treeToDom (Node (Right (f,r,s)) []) = div $ do H.span f 
                                               H.span $ do H.span r 
                                                           H.span s
treeToDom (Node (Right (f,r,s)) d) = div $ do H.span $ "Show: " ++ show f
                                              div ! atr "class" "closed" $ do forestToDom d
                                                                              div $ do H.span ! atr "class" "termination" $ ""
                                                                                       H.span $ do H.span r
                                                                                                   H.span s
treeToDom (Node (Left s) _) = div s

forestToDom :: ProofForest -> Perch
forestToDom t = H.span $ mapM_ treeToDom t

toDomList :: [String] -> Perch
toDomList = div . mapM_ div

