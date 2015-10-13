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

import Data.IORef
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (SSequentItem(SeqList))
import Carnap.Core.Data.AbstractSyntaxDataTypes (liftToScheme)
import Carnap.Core.Data.Rules (Sequent(Sequent), AmbiguousRulePlus)
import Carnap.Frontend.Ghcjs.Components.LazyLister
import Carnap.Frontend.Ghcjs.Components.HookSettingsTo (hookSettingsTo)
import Carnap.Frontend.Ghcjs.Components.GenShowBox (genShowBox)
import Carnap.Frontend.Ghcjs.Components.BoxSettings (BoxSettings(..),initSettingsSL,modeTableSL)
import Carnap.Frontend.Ghcjs.Components.HelperFunctions (nodelistToNumberedList)
import Carnap.Languages.Sentential.PropositionalLanguage (tautologyWithNconnectives)
import Carnap.Languages.Util.LanguageClasses
import Control.Monad.Trans (liftIO)
import Control.Monad (when)
import Control.Applicative ((<$>))
import GHCJS.DOM.Node (nodeAppendChild)
import GHCJS.DOM.Element (elementSetAttribute, elementOnclick)
import GHCJS.DOM.Types (HTMLDivElement, HTMLElement, castToNode, castToHTMLTextAreaElement)
import GHCJS.DOM (WebView, enableInspector, webViewGetDomDocument, runWebGUI)
import GHCJS.DOM.DOMWindow (domWindowConfirm) 
import GHCJS.DOM.Document (documentGetBody, documentGetElementById, documentCreateElement, documentGetDefaultView, documentGetElementsByClassName)
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementSetInnerHTML)
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

setMainBox doc f  = do mwin <- documentGetDefaultView doc
                       case mwin of 
                        Nothing -> return ()
                        Just win -> do ok  <- domWindowConfirm win $ "Try to prove " ++ show f ++ "? \n\n (Warning: this will clear the solution window)"
                                       when ok $ do mmb <- documentGetElementById doc "proofbox"
                                                    case mmb of 
                                                        Nothing -> return ()
                                                        Just mb -> htmlTextAreaElementSetValue (castToHTMLTextAreaElement mb) ("Show: " ++ show f)
