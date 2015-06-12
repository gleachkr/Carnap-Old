{-# LANGUAGE GADTs, FlexibleContexts #-} 
module Carnap.Frontend.Haste.Components.ProofPadEmbedding where

import Carnap.Core.Data.Rules
import Carnap.Core.Unification.MultiUnification
import Carnap.Systems.NaturalDeduction.ProofTreeDataTypes
import Carnap.Systems.NaturalDeduction.ProofTreeHandler
import Carnap.Systems.NaturalDeduction.JudgementHandler
import Carnap.Frontend.Components.ProofTreeParser
import Carnap.Languages.Sentential.PropositionalLanguage
import Carnap.Languages.Sentential.PropositionalDerivations
import Haste hiding (style)
import Haste.Foreign
import Haste.Prim
import Haste.HPlay.View as H
import Data.Tree
import Data.Monoid (mconcat, (<>))
import Data.List (intercalate, intersperse, nub)
import Prelude hiding (div,all,id,print,getChar, putStr, putStrLn,getLine)

--------------------------------------------------------
--1. Main Function: embedWith
--------------------------------------------------------

--the program begins by including some javascript to make the textarea
--easier to work with, and some css. It then inserts into the body of the
--html a textarea and an event that, on each keypress, 1. attempts to parse
--the contents of the text area into a (ProofTree,Termination) pair. 2.
--converts the ProofTree to html, gives the result id "root".
--
--TODO: factor into subprogams: Add room for a function that checks
--a prooftree for correctness, and returns the entailment that the tree
--witnesses, or a line-by-line of errors, Add a function that inserts an
--html element in which the errors or witnessed entailement can be viewed

embedWith thisLogic = do pboxes <- elemsByClass "proofbox"
                         mapM_ (activateCarnap thisLogic) pboxes
                         writeLog "embedding complete"
                         setTimeout 60 $ do _ <- eval $ toJSStr "$(\".lined\").linedtextarea({selectedLine:1});"
                                            return ()

activateCarnap thisLogic pbox = do originalContents <- getProp pbox "textContent"
                                   setProp pbox "innerHTML" ""
                                   let newContents = carnapWith thisLogic originalContents
                                   runWidget newContents pbox
                
carnapWith thisLogic text = do contents <- getMultilineText text `fire` OnKeyUp `fire` OnFocus ! atr "class" "lined"
                               let possibleParsing = parseTheBlock ( contents ++ "\n" )
                               let theForest = fst $ pairHandler possibleParsing
                               rslt <- getNextId
                               root <- getNextId
                               analysis <- getNextId
                               wraw $ div "" ! id rslt ! atr "class" "rslt"
                               wraw $ (forestToDom theForest ) ! id root ! atr "class" "root"
                               case handleForest theForest (fst thisLogic) (snd thisLogic) of 
                                   (Left derRept) -> wraw $ toDomList thisLogic (reverse derRept) ! id analysis ! atr "class" "analysis"
                                   (Right (Right arg)) -> at rslt Insert $ wraw $ H.span $ display arg
                                   (Right (Left _)) -> at rslt Insert $ wraw $ H.span "invalid"

display (Sequent ps c) = intercalate " . " (Prelude.map show (nub ps)) ++ " ∴ " ++ show c


--------------------------------------------------------
--2. Helper Functions for converting html structures
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

toDomList thisLogic = div . mapM_ handle
        where view j = case derivationProves (snd thisLogic) j of 
                                Right arg -> div $ do div "✓"
                                                      div (display arg) ! atr "class" "errormsg"
                                Left e -> div $ do div "✖"
                                                   let l = intersperse hr $ Prelude.map (\x -> div (toElem x)) e
                                                   div (mconcat l) ! atr "class" "errormsg"
              handle dl = case dl of
                             ClosureLine -> div ""
                             OpenLine j -> view j
                             ClosedLine j -> view j
                             ErrLine e -> div $ do div "✖"
                                                   div e ! atr "class" "errormsg"

instance (ToElem term) => ToElem (AbsRule term) where
        toElem (AbsRule ps c) = (mconcat $ intersperse br $ Prelude.map toElem ps) <> br <> toElem " ∴ " <> toElem c

instance (ToElem term) => ToElem (Sequent term) where
        toElem (Sequent ps c) = (mconcat $ intersperse (toElem ", ") $ Prelude.map toElem ps) <> toElem " ⊢ " <> toElem c

instance (ToElem var, ToElem t) => ToElem (UnificationError var t) where
        toElem (UnableToUnify a b) = toElem "I need to match " <> toElem a 
                                                               <> toElem " with " <> toElem b <> toElem "." <> br 
                                                               <> toElem "But that's impossible."
        toElem (ErrWrapper e)      = toElem e
        toElem (SubError err a b)  = toElem "I need to match " <> div (toElem a) ! atr "class" "uniblock" 
                                                               <> toElem " with " <> div (toElem b) ! atr "class" "uniblock" 
                                                               <> toElem "so " <> toElem err
        toElem (OccursCheck v t)   = toElem "Cannot construct infinite type " <> toElem v <> toElem " = " <> toElem t
