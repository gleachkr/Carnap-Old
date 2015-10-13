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
--{-# LANGUAGE GADTs, FlexibleInstances, UndecidableInstances, OverlappingInstances #-}
module Main (
    main
) where

import Data.Maybe (catMaybes)
import Data.IORef
import Data.Map as Map
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (SSequentItem(SeqList))
import Carnap.Core.Data.AbstractSyntaxDataTypes (liftToScheme)
import Carnap.Core.Data.Rules (Sequent(Sequent), AmbiguousRulePlus)
import Carnap.Frontend.Ghcjs.Components.LazyLister
import Carnap.Frontend.Ghcjs.Components.GenShowBox (genShowBox)
import Carnap.Frontend.Ghcjs.Components.BoxSettings (BoxSettings(..),initSettingsSL,modeTableSL)
import Carnap.Languages.Sentential.PropositionalLanguage (tautologyWithNconnectives)
import Carnap.Languages.Util.LanguageClasses
import Control.Applicative ((<$>))
import Control.Monad.Trans (liftIO)
import Control.Monad (when,zipWithM_)
import GHCJS.DOM.Node (nodeAppendChild, nodeInsertBefore, nodeSetNodeValue)
import GHCJS.DOM.Element (elementSetAttribute, elementOnclick, elementOnchange)
import GHCJS.DOM.Types (HTMLDivElement, HTMLElement, castToNode, castToHTMLSelectElement, castToHTMLTextAreaElement, castToHTMLOptionElement)
import GHCJS.DOM (WebView, enableInspector, webViewGetDomDocument, runWebGUI)
import GHCJS.DOM.DOMWindow (domWindowConfirm) 
import GHCJS.DOM.Document (documentGetBody, documentGetElementById, documentCreateElement, documentGetDefaultView, documentGetElementsByClassName)
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementSetInnerHTML, htmlElementSetInnerText)
import GHCJS.DOM.NodeList
import GHCJS.DOM.HTMLSelectElement (htmlSelectElementGetValue)
import GHCJS.DOM.HTMLOptionElement (htmlOptionElementSetValue)
import GHCJS.DOM.HTMLTextAreaElement (htmlTextAreaElementSetValue)
import GHCJS.DOM.Attr (attrSetValue)
import Language.Javascript.JSaddle (eval,runJSaddle) 

main = runWebGUI $ \ webView -> do
    enableInspector webView
    Just doc  <- webViewGetDomDocument webView
    Just body <- documentGetBody doc
    Just pb   <- documentGetElementById doc "proofbox"
    Just opts <- documentGetElementById doc "optionDiv"
    Just ssel <- documentGetElementById doc "sselector"
    mtautologies@(Just tautologies) <- fmap castToHTMLElement <$> documentCreateElement doc "div"
    elementSetAttribute tautologies "id" "tautologies"
    (sref,gref) <- genShowBox pb doc settings (Sequent [SeqList []] $ SeqList [prop "P" .=>. prop "P"])
    nodeAppendChild (castToNode opts) mtautologies
    runJSaddle webView $ eval "setTimeout(function(){$(\".lined\").linedtextarea({selectedLine:1});}, 30);"
    activateLazyList (Prelude.map (toTautElem doc gref) (concatMap (tautologyWithNconnectives) [1..])) tautologies
    hookSettingsTo doc ssel sref modeTableSL
    return ()
    where settings = initSettingsSL{clearAnalysisOnComplete=False}

--------------------------------------------------------
--Helper Functions
--------------------------------------------------------

toTautElem doc gref f = do mdiv@(Just div) <- fmap castToHTMLElement <$> documentCreateElement doc "div"
                           htmlElementSetInnerHTML div (show f)
                           elementOnclick div $ liftIO $ do writeIORef gref (Sequent [SeqList []] $ SeqList [liftToScheme f])
                                                            Just nodes <- documentGetElementsByClassName doc "goal"
                                                            nlist <- nodelistToNumberedList nodes
                                                            let (Just g,_) = head nlist
                                                            let ge = castToHTMLElement g
                                                            elementSetAttribute ge "class" "goal"
                                                            htmlElementSetInnerHTML ge ("⊢ " ++ show f)

                           return div

nodelistToNumberedList nl = do len <- nodeListGetLength nl
                               mapM (\n -> do i <- nodeListItem nl n; return (i,n)) [0 .. len]

setMainBox doc f  = do mwin <- documentGetDefaultView doc
                       case mwin of 
                        Nothing -> return ()
                        Just win -> do ok  <- domWindowConfirm win $ "Try to prove " ++ show f ++ "? \n\n (Warning: this will clear the solution window)"
                                       when ok $ do mmb <- documentGetElementById doc "proofbox"
                                                    case mmb of 
                                                        Nothing -> return ()
                                                        Just mb -> htmlTextAreaElementSetValue (castToHTMLTextAreaElement mb) ("Show: " ++ show f)

hookSettingsTo doc sl' ref mt = do let modkeys = keys mt
                                   let sel = castToHTMLSelectElement sl'
                                   opList <- optsFrom doc modkeys --want to convert a list of strings into a list of option elements with appropriate values
                                   let mopList = Prelude.map Just opList 
                                   mopH@(Just opHead) <- newOpt doc
                                   htmlElementSetInnerHTML opHead "-"
                                   mapM (nodeAppendChild $ castToNode sel) (mopH:mopList)
                                   elementOnchange sel $ liftIO $ do v <- htmlSelectElementGetValue sel
                                                                     case Map.lookup v mt of
                                                                         Nothing -> return ()
                                                                         Just f -> modifyIORef ref f

optsFrom doc list = do mopts <- mapM (const $ newOpt doc) list
                       let opts = catMaybes mopts
                       zipWithM_ htmlElementSetInnerHTML opts list
                       zipWithM_ htmlOptionElementSetValue opts list
                       return opts

newOpt doc = fmap castToHTMLOptionElement <$> documentCreateElement doc "option"
