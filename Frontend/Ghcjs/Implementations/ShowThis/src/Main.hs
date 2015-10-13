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
import Data.List (intercalate)
import Data.IORef
import Carnap.Languages.FirstOrder.QuantifiedParser (formulaParser)
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (SSequentItem(SeqList))
import Carnap.Core.Data.AbstractSyntaxDataTypes (liftToScheme)
import Carnap.Core.Data.Rules (Sequent(Sequent))
import Carnap.Frontend.Ghcjs.Components.BoxSettings (BoxSettings(..),initSettingsFOL, longModTable)
import Carnap.Frontend.Ghcjs.Components.KeyCatcher
import Carnap.Frontend.Ghcjs.Components.HelperFunctions (nodelistToList)
import Carnap.Frontend.Ghcjs.Components.HookSettingsTo (hookSettingsInit,hookSettingsLink)
import Carnap.Frontend.Ghcjs.Components.GenShowBox (genShowBox)
import Carnap.Frontend.Ghcjs.Components.GenHelp (helpPopupQL,helpPopupLogicBookSD)
import Carnap.Frontend.Ghcjs.Components.GenPopup (genPopup)
import Carnap.Languages.Util.ParserTypes
import Text.Parsec (runParser)
import Text.Parsec.Char (oneOf)
import Text.Parsec.Combinator (many1,sepBy)
import Text.Blaze.Html.Renderer.Text (renderHtml)
import Control.Monad.Trans (liftIO)
import Control.Monad (when)
import GHCJS.DOM.Element (elementSetAttribute, elementOnclick, elementFocus)
import GHCJS.DOM.HTMLInputElement (castToHTMLInputElement,htmlInputElementSetValue,htmlInputElementGetValue)
import GHCJS.DOM.Node (nodeGetFirstChild,nodeAppendChild,nodeInsertBefore)
import GHCJS.DOM.Types (HTMLDivElement, HTMLElement, castToHTMLOptionElement,castToHTMLSelectElement)
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
    hookSettingsInit doc ssel setref longModTable
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
                                                                        hookSettingsLink doc ssel sref longModTable
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

initSettings = initSettingsFOL{clearAnalysisOnComplete=False}

formList = parser formulaParser `sepBy` many1 (oneOf " ,")
