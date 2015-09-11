{-#LANGUAGE OverlappingInstances #-}
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

import Data.Map as M
import Data.Monoid ((<>))
import Data.List (intercalate)
import Carnap.Calculi.ClassicalFirstOrderLogic1 (classicalRules, classicalQLruleSet, prettyClassicalQLruleSet)
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (SSequentItem(SeqList))
import Carnap.Core.Data.AbstractSyntaxDataTypes (liftToScheme)
import Carnap.Frontend.Ghcjs.Components.UpdateBox 
    (BoxSettings(BoxSettings,fparser,pparser,manalysis,mproofpane,mresult,rules,ruleset,clearAnalysisOnComplete))
import Carnap.Frontend.Components.ProofTreeParser (parseTheBlock)
import Carnap.Frontend.Ghcjs.Components.KeyCatcher
import Carnap.Frontend.Ghcjs.Components.GenShowBox (genShowBox)
import Carnap.Frontend.Ghcjs.Components.GenHelp (inferenceTable, terminationTable)
import Carnap.Frontend.Ghcjs.Components.GenPopup (genPopup)
import Carnap.Core.Data.Rules (Sequent(Sequent))
import Text.Parsec (parse)
import Text.Parsec.Char (oneOf)
import Text.Parsec.Combinator (many1,sepBy)
import Carnap.Languages.FirstOrder.QuantifiedParser (formulaParser)
import Control.Applicative ((<$>))
import Control.Monad.Trans (liftIO)
import Text.Blaze.Html5 as B
import GHCJS.DOM.Element (elementSetAttribute, elementOnclick, elementFocus)
import GHCJS.DOM.HTMLInputElement 
import GHCJS.DOM.Node (nodeGetFirstChild,nodeAppendChild,nodeInsertBefore)
import GHCJS.DOM.NodeList (nodeListGetLength,nodeListItem)
import GHCJS.DOM.Types (HTMLDivElement, HTMLElement)
import GHCJS.DOM (WebView, enableInspector, webViewGetDomDocument, runWebGUI)
import GHCJS.DOM.Document (documentGetBody, documentGetElementById, documentGetElementsByClassName, documentCreateElement, documentGetDefaultView )
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementGetInnerHTML, htmlElementSetInnerHTML)
import GHCJS.DOM.DOMWindow (domWindowAlert)
import GHCJS.DOM.Attr (attrSetValue)
import Language.Javascript.JSaddle (eval,runJSaddle)

main = runWebGUI $ \webView -> do  
    enableInspector webView
    Just doc <- webViewGetDomDocument webView
    Just body <- documentGetBody doc
    Just proofDiv <- documentGetElementById doc "proofDiv"
    Just premInput <- documentGetElementById doc "premForm"
    Just concInput <- documentGetElementById doc "concForm"
    Just shareURL <- documentGetElementById doc "shareURL"
    Just shareButton <- documentGetElementById doc "shareButton"
    elementOnclick shareButton (updateFromGoals doc (castToHTMLElement shareURL))
    let pi = castToHTMLInputElement premInput
    let ci = castToHTMLInputElement concInput
    dv@(Just win) <- documentGetDefaultView doc 
    help <- genPopup proofDiv doc helpPopup "help"
    mapM_ (\x -> keyCatcher x $ \kbf k -> if k == 13 then do pv <- htmlInputElementGetValue pi
                                                             cv <- htmlInputElementGetValue ci
                                                             let conc = parse formulaParser "" cv
                                                             let prem = parse formList "" pv
                                                             case (conc,prem) of 
                                                                 (Right concForm, Right premForms) -> 
                                                                     do mcontainer@(Just cont) <- documentCreateElement doc "div"
                                                                        mfc <-nodeGetFirstChild proofDiv
                                                                        case mfc of Nothing -> nodeAppendChild proofDiv mcontainer
                                                                                    Just fc -> nodeInsertBefore proofDiv mcontainer mfc
                                                                        genShowBox cont doc initSettings 
                                                                                (Sequent [SeqList $ Prelude.map liftToScheme premForms] 
                                                                                        (SeqList [liftToScheme concForm]))
                                                                        mgrip@(Just grip) <- documentCreateElement doc "div"
                                                                        htmlElementSetInnerHTML (castToHTMLElement grip) "☰"
                                                                        elementSetAttribute grip "class" "gripper"
                                                                        nodeAppendChild cont mgrip
                                                                        htmlInputElementSetValue pi ""
                                                                        htmlInputElementSetValue ci ""
                                                                 _ -> domWindowAlert win "Sorry, the conclusion or one of the premises was not well-formed"
                                                             runJSaddle webView $ eval "setTimeout(function(){$(\"#proofDiv > div > .lined\").linedtextarea({selectedLine:1});}, 30);"
                                                             return False
                                                     else return False) [premInput, concInput]
    keyCatcher proofDiv $ \kbf k -> do if k == 63 then do elementSetAttribute help "style" "display:block" 
                                                          elementFocus help
                                                else return ()
                                       return (k == 63) --the handler returning true means that the keypress is intercepted
    return ()

updateFromGoals doc surl = liftIO $ do (Just goalsNL) <- documentGetElementsByClassName doc "goal"
                                       goals <- nodelistToList goalsNL
                                       goalContents <- mapM fromMaybeNode goals
                                       htmlElementSetInnerHTML surl (toURL goalContents)
                                where fromMaybeNode (Just n) =  htmlElementGetInnerHTML $ castToHTMLElement n
                                      fromMaybeNode Nothing =  return ""

toURL glist =  case glist 
                  of [[]] -> "<span>You need to generate some problems first</span>"
                     l -> "<a href=\"http://gleachkr.github.io/Carnap/Frontend/Ghcjs/Implementations/FromURL/dist/build/FromURL/FromURL.jsexe/index.html?" ++ 
                            (Prelude.filter (/= ' ') $ intercalate "." $ Prelude.map (Prelude.map punct) l) ++ "\">" ++
                            "gleachkr.github.io/Carnap/Frontend/Ghcjs/Implementations/FromURL/dist/build/FromURL/FromURL.jsexe/index.html?" ++
                            (Prelude.filter (/= ' ') $ intercalate "." $ Prelude.map (Prelude.map punct) l) ++
                            "</a>"
    where punct c = case c of 
                    '⊢' -> ';'
                    '.' -> ','
                    _ -> c

nodelistToList nl = do len <- nodeListGetLength nl
                       mapM (\n -> do i <- nodeListItem nl n; return i) [0 .. len]

initSettings = BoxSettings {fparser = formulaParser,
                            pparser = parseTheBlock,
                            ruleset = classicalQLruleSet,
                            rules = classicalRules,
                            clearAnalysisOnComplete = False,
                            manalysis = Nothing,
                            mproofpane = Nothing,
                            mresult = Nothing}

helpPopup = B.div (toHtml infMessage) <>
            inferenceTable prettyClassicalQLruleSet classicalRules comments <>
            B.div (toHtml termMessage) <>
            terminationTable prettyClassicalQLruleSet classicalRules comments

infMessage :: String
infMessage = "The following are inference rules. They can be used to directly justify the assertion on a given line, by referring to previous open lines."
     <> " An inference rule can justify a statement matching the form that appears on the right side of the sequent that concludes the rule."
     <> " (I.e. on the right side of the \"⊢\" following the \"∴\".)"
     <> " It needs to refer back to previous lines which match all of the forms that appear on the right side of the sequents in the premises of the rule."
     <> " The symbols on the left sides of the sequents tell you how the dependencies of the justified line relate to the dependencies of the lines that justify it."

termMessage :: String
termMessage = "The following are termination rules. They can be used to close a subproof, by referring to previous open lines (including lines that belong to the subproof)."
      <> " A termination rule can close a subproof that begins with a show line followed by something matching the form that appears on the right side of the sequent that concludes the rule."
      <> " It needs to refer back to previous lines which match all of the forms that appear on the right side of the sequents in the premises of the rule."
      <> " The symbols on the left sides of the sequents tell you how the dependencies of the statement established by the subproof relate to the dependencies of the lines that close the subproof."

comments = M.fromList [
                      ("R","Reflexivity"),
                      ("BC", "Biconditional to conditional"),
                      ("DS", "Disjunctive Syllogism"),
                      ("IE", "Interchange of Equivalents"),
                      ("S", "Simplification"),
                      ("CB", "Conditional to Biconditional"),
                      ("MTP", "Modus Tollendo Ponens"),
                      ("DN", "Double Negation"),
                      ("MT", "Modus Tollens"),
                      ("LL", "Leibniz's Law"),
                      ("EG", "Existential Generalization"),
                      ("ADD", "Addition"),
                      ("MP", "Modus Ponens"),
                      ("ADJ", "Adjunction"),
                      ("UI", "Universal Instantiation"),
                      ("UD", "Universal Derivation. <br> Note: τ_1 must be a new variable"),
                      ("ED", "Existential Derivation. <br> Note: τ_1 must a new variable"),
                      ("ID", "Indirect Derivation"),
                      ("CD", "Conditional Derivation"),
                      ("DD", "Direct Derivation")
                      ]

formList = formulaParser `sepBy` (many1 $ oneOf " ,")
