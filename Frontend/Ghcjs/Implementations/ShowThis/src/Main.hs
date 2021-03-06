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
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (SSequentItem(SeqList))
import Carnap.Core.Data.AbstractSyntaxDataTypes (liftToScheme)
import Carnap.Core.Data.Rules (Sequent(Sequent))
import Carnap.Frontend.Ghcjs.Components.BoxSettings (BoxSettings(..),initSettingsFOL, longModTable)
import Carnap.Frontend.Ghcjs.Components.KeyCatcher (keyCatcher)
import Carnap.Frontend.Ghcjs.Components.HelperFunctions (nodelistToList,lineWithDelay)
import Carnap.Frontend.Util.HelperFunctions (toPremConcPair)
import Carnap.Frontend.Ghcjs.Components.HookSettingsTo (hookSettingsInit,hookSettingsLink)
import Carnap.Frontend.Ghcjs.Components.GenShowBox (genShowBox)
import Carnap.Frontend.Ghcjs.Components.GenHelp (helpPopupQL,helpPopupLogicBookSD)
import Carnap.Frontend.Ghcjs.Components.GenPopup (genPopup)
import Text.Blaze.Html.Renderer.Text (renderHtml)
import Control.Monad.Trans (liftIO)
import Control.Monad (when)
import GHCJS.DOM.Element (elementSetAttribute, elementOnclick, elementFocus)
import GHCJS.DOM.HTMLInputElement (castToHTMLInputElement,htmlInputElementSetValue,htmlInputElementGetValue,htmlInputElementGetChecked)
import GHCJS.DOM.Node (nodeGetFirstChild,nodeAppendChild,nodeInsertBefore)
import GHCJS.DOM.Types (HTMLDivElement, HTMLElement, castToHTMLOptionElement,castToHTMLSelectElement)
import GHCJS.DOM.HTMLSelectElement (htmlSelectElementGetValue)
import GHCJS.DOM (WebView, enableInspector, webViewGetDomDocument, runWebGUI)
import GHCJS.DOM.Document (documentGetBody, documentGetElementById, documentGetElementsByClassName, documentCreateElement, documentGetDefaultView )
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementGetInnerHTML, htmlElementSetInnerHTML, htmlElementGetChildren)
import GHCJS.DOM.DOMWindow (domWindowAlert)
import GHCJS.DOM.Attr (attrSetValue)

main = runWebGUI $ \webView -> do  
    enableInspector webView
    Just doc <- webViewGetDomDocument webView
    Just body <- documentGetBody doc
    Just proofDiv <- documentGetElementById doc "proofDiv"
    Just premInput <- documentGetElementById doc "premForm"
    Just concInput <- documentGetElementById doc "concForm"
    Just wdlInput <- documentGetElementById doc "withDownloadBox"
    Just shareURL <- documentGetElementById doc "shareURL"
    Just shareButton <- documentGetElementById doc "shareButton"
    Just ssel <- documentGetElementById doc "sselector"
    setref <- newIORef initSettings
    elementOnclick shareButton (updateFromGoals doc ssel wdlInput (castToHTMLElement shareURL))
    let pi = castToHTMLInputElement premInput
    let ci = castToHTMLInputElement concInput
    dv@(Just win) <- documentGetDefaultView doc 
    help <- genPopup proofDiv doc helpPopupQL "help"
    hookSettingsInit doc ssel setref longModTable
    mapM_ (\x -> keyCatcher x $   \_ k -> if k == 13 then do pv <- htmlInputElementGetValue pi
                                                             cv <- htmlInputElementGetValue ci
                                                             theseSettings <- readIORef setref
                                                             case toPremConcPair cv pv theseSettings of 
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
                                                             lineWithDelay 
                                                             return False
                                                     else return False) [premInput, concInput]
    keyCatcher proofDiv $   \_ k -> do when (k == 63) $ do theseSettings <- readIORef setref
                                                           case helpMessage theseSettings of 
                                                              Just msg -> htmlElementSetInnerHTML help (renderHtml msg)
                                                              Nothing -> return ()
                                                           elementSetAttribute help "style" "display:block" 
                                                           elementFocus help
                                       return (k == 63) --the handler returning true means that the keypress is intercepted
    return ()

updateFromGoals doc ssel wdl surl = liftIO $ do (Just goalsNL) <- documentGetElementsByClassName doc "goal"
                                                let sel = castToHTMLSelectElement ssel
                                                let box = castToHTMLInputElement wdl
                                                v <- htmlSelectElementGetValue sel
                                                checked <- htmlInputElementGetChecked box
                                                goals <- nodelistToList goalsNL
                                                goalContents <- mapM fromMaybeNode goals
                                                htmlElementSetInnerHTML surl (toURL (if checked then '1':v else '0':v) goalContents)
                                    where fromMaybeNode (Just n) =  htmlElementGetInnerHTML $ castToHTMLElement n
                                          fromMaybeNode Nothing =  return ""

toURL v glist = case glist 
                  of [[]] -> "<span>You need to generate some problems first</span>"
                     l -> "<a href=\"http://gleachkr.github.io/Carnap/Frontend/Ghcjs/Implementations/FromURL/dist/build/FromURL/FromURL.jsexe/index.html?" ++ 
                          theUrl ++ "\">" ++
                          "gleachkr.github.io/Carnap/Frontend/Ghcjs/Implementations/FromURL/dist/build/FromURL/FromURL.jsexe/index.html?" ++
                          theUrl ++ "</a>"
                        where theUrl = take 2 v ++ (Prelude.filter (/= ' ') $ intercalate "." $ Prelude.map (Prelude.map punct) l)
                              punct c = case c of 
                                        '⊢' -> ';'
                                        '.' -> ','
                                        _ -> c

initSettings = initSettingsFOL{clearAnalysisOnComplete=False}
