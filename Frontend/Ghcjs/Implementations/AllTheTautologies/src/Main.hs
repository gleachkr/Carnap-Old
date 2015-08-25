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

import Carnap.Calculi.ClassicalSententialLogic1 (classicalRules, classicalSLruleSet)
import Carnap.Frontend.Ghcjs.Components.LazyLister
import Carnap.Frontend.Ghcjs.Components.ActivateProofBox
import Carnap.Languages.Sentential.PropositionalLanguage (tautologyWithNconnectives)
import Carnap.Languages.Sentential.PropositionalParser (formulaParser)
import Control.Applicative ((<$>))
import Control.Monad.Trans (liftIO)
import GHCJS.DOM.Node (nodeInsertBefore, nodeSetNodeValue)
import GHCJS.DOM.Element (elementSetAttribute, elementOnclick)
import GHCJS.DOM.Types (HTMLDivElement, HTMLElement, castToHTMLTextAreaElement)
import GHCJS.DOM (WebView, enableInspector, webViewGetDomDocument, runWebGUI)
import GHCJS.DOM.DOMWindow (domWindowConfirm) 
import GHCJS.DOM.Document (documentGetBody, documentGetElementById, documentCreateElement, documentGetDefaultView)
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementSetInnerHTML, htmlElementSetInnerText)
import GHCJS.DOM.HTMLTextAreaElement (htmlTextAreaElementSetValue)
import GHCJS.DOM.Attr (attrSetValue)
import Language.Javascript.JSaddle (eval,runJSaddle) 

main = runWebGUI $ \ webView -> do
    enableInspector webView
    Just doc <- webViewGetDomDocument webView
    Just body <- documentGetBody doc
    Just pb <- documentGetElementById doc "proofbox"
    mtautologies@(Just tautologies) <- fmap castToHTMLElement <$> documentCreateElement doc "div"
    elementSetAttribute tautologies "id" "tautologies"
    runJSaddle webView $ eval "setTimeout(function(){$(\".lined\").linedtextarea({selectedLine:1});}, 30);"
    nodeInsertBefore body mtautologies (Just pb)
    activateLazyList (Prelude.map (toTautElem doc) (concatMap tautologyWithNconnectives [1..])) tautologies
    activateProofBox pb doc classicalRules classicalSLruleSet formulaParser
    return ()

--------------------------------------------------------
--Helper Functions
--------------------------------------------------------

toTautElem doc f = do mdiv@(Just div) <- fmap castToHTMLElement <$> documentCreateElement doc "div"
                      htmlElementSetInnerHTML div (show f)
                      elementOnclick div $ liftIO $ setMainBox doc f
                      return div

setMainBox doc f  = do mwin <- documentGetDefaultView doc
                       case mwin of 
                        Nothing -> return ()
                        Just win -> do ok  <- domWindowConfirm win $ "Try to prove " ++ show f ++ "? \n\n (Warning: this will clear the solution window)"
                                       if ok then do mmb <- documentGetElementById doc "proofbox"
                                                     case mmb of 
                                                        Nothing -> return ()
                                                        Just mb -> htmlTextAreaElementSetValue (castToHTMLTextAreaElement mb) ("Show: " ++ show f)
                                             else return ()
