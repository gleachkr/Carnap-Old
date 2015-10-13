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

import Control.Monad (when)
import Data.Map as M (lookup)
import Data.Maybe (catMaybes)
import Carnap.Frontend.Ghcjs.Components.ActivateProofBox (activateProofBox)
import Carnap.Frontend.Ghcjs.Components.BoxSettings (BoxSettings(..), initSettingsFOL, initSettingsSL,modTableSL,modTableFOL)
import Carnap.Frontend.Ghcjs.Components.GenPopup (genPopup)
import Carnap.Frontend.Ghcjs.Components.Slider (slider)
import Carnap.Frontend.Ghcjs.Components.KeyCatcher
import Carnap.Frontend.Ghcjs.Components.HelperFunctions (nodelistToNumberedList,htmlColltoList)
import GHCJS.DOM.Node (nodeAppendChild,nodeGetChildNodes)
import GHCJS.DOM.Element (castToElement, elementSetAttribute, elementOnclick, elementFocus, elementGetClassName)
import GHCJS.DOM (WebView, enableInspector, webViewGetDomDocument, runWebGUI)
import GHCJS.DOM.Document (documentGetBody, documentGetElementsByClassName)
import GHCJS.DOM.HTMLElement (htmlElementGetChildren,castToHTMLElement)
import Language.Javascript.JSaddle (eval,runJSaddle)

--------------------------------------------------------
--1. Main functions
--------------------------------------------------------

main = runWebGUI $ \webView -> do  
    enableInspector webView
    Just doc <- webViewGetDomDocument webView
    Just body <- documentGetBody doc
    Just folpbs <- documentGetElementsByClassName doc "FOLproofbox"
    Just slpbs <- documentGetElementsByClassName doc "SLproofbox"
    mfolnodes <- nodelistToNumberedList folpbs
    mslnodes <- nodelistToNumberedList slpbs
    mapM_ (byCase doc initSettingsFOL modTableFOL) mfolnodes
    mapM_ (byCase doc initSettingsSL modTableSL) mslnodes
    Just slidernodelist <- documentGetElementsByClassName doc "slider"
    msliders <- nodelistToNumberedList slidernodelist
    mapM_ (toSlider doc) msliders
    runJSaddle webView $ eval "setTimeout(function(){$(\".lined\").linedtextarea({selectedLine:1});}, 30);"
    return ()

--turns a numbered node into a proofbox
--XXX:Might want to automate adding an id
byCase doc init mt (n,l) = case n of 
        Just node -> do settings <- readSettings init mt node
                        activateProofBox node doc settings
                        case helpMessage settings of 
                            Nothing -> return ()
                            Just msg -> do help <- genPopup node doc msg ("help" ++ show l)
                                           keyCatcher node $ \kbf k -> do when (k == 63 ) $ do elementSetAttribute help "style" "display:block" 
                                                                                               elementFocus help
                                                                          return (k == 63) --the handler returning true means that the keypress is intercepted
        Nothing -> return ()

--turns a numbered node into a slider.
toSlider doc (n,l) = case n of
            Just node -> do let nodeAsElt = castToHTMLElement node
                            mcc@(Just childcollection) <- htmlElementGetChildren nodeAsElt 
                            childms <- htmlColltoList childcollection
                            let children = catMaybes childms
                            sdiv <- slider doc (Prelude.map castToElement children)
                            nodeAppendChild node (Just sdiv)
                            return ()
            Nothing -> return ()

--reads settings off of a node when activating it, to determine any special
--behavior.
readSettings init mt node = do classname <- elementGetClassName $ castToElement node :: IO String
                               print classname
                               let classes = words classname
                               let modifications = catMaybes $ Prelude.map (`M.lookup` mt) classes
                               return $ Prelude.foldr ($) init modifications

--------------------------------------------------------
--2. Utility Functions
--------------------------------------------------------

