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
import Data.IORef
import Data.Maybe
import Carnap.Calculi.ClassicalFirstOrderLogic1 (classicalRules, classicalQLruleSet, prettyClassicalQLruleSet, logicBookSDruleSetQL )
import Carnap.Calculi.ClassicalSententialLogic1 (logicBookSDrules,logicBookSDruleSet)
import Carnap.Languages.FirstOrder.QuantifiedParser (formulaParser)
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (SSequentItem(SeqList))
import Carnap.Core.Data.AbstractSyntaxDataTypes (liftToScheme)
import Carnap.Core.Data.Rules (Sequent(Sequent))
import Carnap.Frontend.Ghcjs.Components.UpdateBox 
    (BoxSettings(BoxSettings,helpMessage, fhandler,fparser,pparser,manalysis,mproofpane,mresult,rules,ruleset,clearAnalysisOnComplete))
import Carnap.Frontend.Components.ProofTreeParser (parseTheBlockKM,parseTheBlockFitch)
import Carnap.Frontend.Ghcjs.Components.KeyCatcher
import Carnap.Systems.NaturalDeduction.FitchProofTreeHandler
import Carnap.Systems.NaturalDeduction.KalishAndMontegueProofTreeHandler
import Carnap.Frontend.Ghcjs.Components.GenShowBox (genShowBox)
import Carnap.Frontend.Ghcjs.Components.GenHelp (inferenceTable, terminationTable)
import Carnap.Frontend.Ghcjs.Components.GenPopup (genPopup)
import Carnap.Languages.Util.ParserTypes
import Text.Parsec (runParser)
import Text.Parsec.Char (oneOf)
import Text.Parsec.Combinator (many1,sepBy)
import Text.Blaze.Html5 as B
import Text.Blaze.Html.Renderer.Text (renderHtml)
import Control.Applicative ((<$>))
import Control.Monad.Trans (liftIO)
import Control.Monad (when,zipWithM_)
import GHCJS.DOM.Element (elementOnchange,elementSetAttribute, elementOnclick, elementFocus)
import GHCJS.DOM.HTMLInputElement 
import GHCJS.DOM.Node (castToNode, nodeGetFirstChild,nodeAppendChild,nodeInsertBefore)
import GHCJS.DOM.NodeList (nodeListGetLength,nodeListItem)
import GHCJS.DOM.Types (HTMLDivElement, HTMLElement, castToHTMLOptionElement,castToHTMLSelectElement)
import GHCJS.DOM.HTMLOptionElement (htmlOptionElementSetValue)
import GHCJS.DOM.HTMLSelectElement (htmlSelectElementGetValue)
import GHCJS.DOM (WebView, enableInspector, webViewGetDomDocument, runWebGUI)
import GHCJS.DOM.Document (documentGetBody, documentGetElementById, documentGetElementsByClassName, documentCreateElement, documentGetDefaultView )
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementGetInnerHTML, htmlElementSetInnerHTML, htmlElementGetChildren)
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
    Just ssel <- documentGetElementById doc "sselector"
    setref <- newIORef initSettings
    elementOnclick shareButton (updateFromGoals doc ssel (castToHTMLElement shareURL))
    let pi = castToHTMLInputElement premInput
    let ci = castToHTMLInputElement concInput
    dv@(Just win) <- documentGetDefaultView doc 
    help <- genPopup proofDiv doc helpPopupQL "help"
    hookSettingsInit doc ssel setref modTable
    mapM_ (\x -> keyCatcher x $ \kbf k -> if k == 13 then do pv <- htmlInputElementGetValue pi
                                                             cv <- htmlInputElementGetValue ci
                                                             theseSettings <- readIORef setref
                                                             let conc = stateParse (fparser theseSettings) cv
                                                             let prem = runParser formList (initState (fparser theseSettings)) "" pv
                                                             case (conc,prem) of 
                                                                 (Right concForm, Right premForms) -> 
                                                                     do mcontainer@(Just cont) <- documentCreateElement doc "div"
                                                                        mfc <-nodeGetFirstChild proofDiv
                                                                        case mfc of Nothing -> nodeAppendChild proofDiv mcontainer
                                                                                    Just fc -> nodeInsertBefore proofDiv mcontainer mfc
                                                                        (sref, _) <- genShowBox cont doc theseSettings
                                                                                        (Sequent [SeqList $ Prelude.map liftToScheme premForms] 
                                                                                        (SeqList [liftToScheme concForm]))
                                                                        hookSettingsLink doc ssel sref modTable
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
    keyCatcher proofDiv $ \kbf k -> do when (k == 63) $ do theseSettings <- readIORef setref
                                                           case helpMessage theseSettings of 
                                                              Just msg -> htmlElementSetInnerHTML help (renderHtml msg)
                                                              Nothing -> return ()
                                                           elementSetAttribute help "style" "display:block" 
                                                           elementFocus help
                                       return (k == 63) --the handler returning true means that the keypress is intercepted
    return ()

hookSettingsGen doc sl' ref mt mt' = do let modkeys = keys mt
                                        let sel = castToHTMLSelectElement sl'
                                        opList <- optsFrom doc modkeys --want to convert a list of strings into a list of option elements with appropriate values
                                        let mopList = Prelude.map Just opList 
                                        mapM (nodeAppendChild $ castToNode sel) mopList
                                        elementOnchange sel $ liftIO $ do v <- htmlSelectElementGetValue sel
                                                                          case M.lookup v mt' of
                                                                              Nothing -> return ()
                                                                              Just f -> modifyIORef ref f

hookSettingsInit doc sl' ref mt = hookSettingsGen doc sl' ref mt mt

hookSettingsLink doc sl' ref mt = hookSettingsGen doc sl' ref (Prelude.foldr delete mt (keys mt)) mt

optsFrom doc list = do mopts <- mapM (const $ newOpt doc) list
                       let opts = catMaybes mopts
                       zipWithM_ htmlElementSetInnerHTML opts list
                       zipWithM_ htmlOptionElementSetValue opts list
                       return opts

newOpt doc = fmap castToHTMLOptionElement <$> documentCreateElement doc "option"

updateFromGoals doc ssel surl = liftIO $ do (Just goalsNL) <- documentGetElementsByClassName doc "goal"
                                            let sel = castToHTMLSelectElement ssel
                                            v <- htmlSelectElementGetValue sel
                                            goals <- nodelistToList goalsNL
                                            goalContents <- mapM fromMaybeNode goals
                                            htmlElementSetInnerHTML surl (toURL v goalContents )
                                where fromMaybeNode (Just n) =  htmlElementGetInnerHTML $ castToHTMLElement n
                                      fromMaybeNode Nothing =  return ""

toURL v glist =  case glist 
                  of [[]] -> "<span>You need to generate some problems first</span>"
                     l -> "<a href=\"http://gleachkr.github.io/Carnap/Frontend/Ghcjs/Implementations/FromURL/dist/build/FromURL/FromURL.jsexe/index.html?" ++ 
                          theUrl ++ "\">" ++
                          "gleachkr.github.io/Carnap/Frontend/Ghcjs/Implementations/FromURL/dist/build/FromURL/FromURL.jsexe/index.html?" ++
                          theUrl ++ "</a>"
                        where theUrl = Prelude.head v : (Prelude.filter (/= ' ') $ intercalate "." $ Prelude.map (Prelude.map punct) l)
    where punct c = case c of 
                    '⊢' -> ';'
                    '.' -> ','
                    _ -> c

nodelistToList nl = do len <- nodeListGetLength nl
                       mapM (\n -> do i <- nodeListItem nl n; return i) [0 .. len]

initSettings = BoxSettings {fparser = formulaParser,
                            pparser = parseTheBlockKM,
                            fhandler = handleForestKM,
                            ruleset = classicalQLruleSet,
                            rules = classicalRules,
                            clearAnalysisOnComplete = False,
                            manalysis = Nothing,
                            mproofpane = Nothing,
                            mresult = Nothing,
                            helpMessage = Just helpPopupQL}

formList = parser formulaParser `sepBy` many1 (oneOf " ,")

modTable = M.fromList [ ("-", id)
                      , ("Fitch Mode", fitchOn)
                      , ("Default Mode", kmOn)
                      , ("Logic Book Mode", logicBookModeOn)
                      ]

fitchOn settings = settings { fhandler = handleForestFitch
                            , pparser = parseTheBlockFitch
                            , rules = classicalRules
                            , ruleset = classicalQLruleSet
                            , helpMessage = Just helpPopupQL
                            }

kmOn settings = settings { fhandler = handleForestKM
                         , pparser = parseTheBlockKM
                         , rules = classicalRules
                         , ruleset = classicalQLruleSet
                         , helpMessage = Just helpPopupQL
                         }

logicBookModeOn settings = settings { fhandler = handleForestFitch
                                    , pparser = parseTheBlockFitch
                                    , rules = logicBookSDrules
                                    , ruleset = logicBookSDruleSetQL
                                    , helpMessage = Just helpPopupLogicBookSD
                                    }

--------------------------------------------------------
--Help messages
--------------------------------------------------------

helpPopupQL :: Html
helpPopupQL = B.div (toHtml infMessage) <>
            inferenceTable prettyClassicalQLruleSet classicalRules comments <>
            B.div (toHtml termMessage) <>
            terminationTable prettyClassicalQLruleSet classicalRules comments

helpPopupLogicBookSD :: Html
helpPopupLogicBookSD = B.div (toHtml infMessage) <>
            inferenceTable logicBookSDruleSet logicBookSDrules comments <>
            B.div (toHtml spMessage) <>
            terminationTable logicBookSDruleSet logicBookSDrules comments

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

spMessage :: String
spMessage = "The following are subproof rules. They can be used to justify the assertion on a given line by referring back to previous subproofs."
      <> " An suproof rule can justify a statement matching the form that appears on the right side of the sequent that concludes the rule."
      <> " It needs to refer back to one or more subproofs whose final lines match the forms that appear on the right side of the sequents in the premises of the rule."
      <> " The symbols on the left sides of the sequents tell you how the dependencies of the statement established by the subproof rule relate to the dependencies of the lines used to justify it."

comments = M.fromList [ ("RF","Reflexivity")
                      , ("R" ,"Reiteration")
                      , ("BC", "Biconditional to conditional")
                      , ("IE", "Interchange of Equivalents")
                      , ("S", "Simplification")
                      , ("CB", "Conditional to Biconditional")
                      , ("MTP", "Modus Tollendo Ponens")
                      , ("DN", "Double Negation")
                      , ("MT", "Modus Tollens")
                      , ("LL", "Leibniz's Law")
                      , ("EG", "Existential Generalization")
                      , ("ADD", "Addition")
                      , ("MP", "Modus Ponens")
                      , ("ADJ", "Adjunction")
                      , ("UI", "Universal Instantiation")
                      , ("UD", "Universal Derivation")
                      , ("ED", "Existential Derivation")
                      , ("ID", "Indirect Derivation")
                      , ("CD", "Conditional Derivation")
                      , ("DD", "Direct Derivation")
                      , ("AI", "Conjunction Introduction")
                      , ("AE", "Conjunction Eliminiation")
                      , ("CI", "Conditional Introduction")
                      , ("CE", "Conditional Eliminiation")
                      , ("DI", "Disjunction Introduction")
                      , ("DE", "Disjunction Elimination")
                      , ("BI", "Biconditional Introduction")
                      , ("BE", "Biconditional Elimination")
                      , ("NI", "Negation Introduction")
                      , ("NE", "Negation Elimination")
                      ]

