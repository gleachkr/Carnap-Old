{-#LANGUAGE JavaScriptFFI #-}
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

module Carnap.Frontend.Ghcjs.Components.HelperFunctions (nodelistToNumberedList,nodelistToList, htmlColltoList, saveAs, lineWithDelay)

where 

import GHCJS.DOM.HTMLCollection (htmlCollectionGetLength, htmlCollectionItem)
import GHCJS.DOM.NodeList (nodeListGetLength, nodeListItem)
import GHCJS.Foreign (toJSString)
import GHCJS.Types (JSString)

--This module houses some helper functions which are useful for dealing with GHCJS data structures

--------------------------------------------------------
--1. DOM manipulation
--------------------------------------------------------
nodelistToNumberedList nl = do len <- nodeListGetLength nl
                               mapM (\n -> do i <- nodeListItem nl n; return (i,n)) [0 .. len]

nodelistToList nl = do len <- nodeListGetLength nl
                       mapM (\n -> do i <- nodeListItem nl n; return i) [0 .. len]

htmlColltoList hc = do len <- htmlCollectionGetLength hc
                       mapM (htmlCollectionItem hc) [0 .. len]

--------------------------------------------------------
--2. Javascript Interaction
--------------------------------------------------------
--these functions do depend on some external javascript libraries, so you
--need to remember to import those if you want to use these.

foreign import javascript unsafe  "setTimeout(function(){$(\"#proofDiv > div > .lined\").linedtextarea({selectedLine:1});}, 30);" lineWithDelay :: IO ()

foreign import javascript unsafe "var blob = new Blob([$1], {type: \"text/plain;charset=utf-8\"}); saveAs(blob, $2);" saveAsJS :: JSString -> JSString -> IO ()

saveAs string title = saveAsJS (toJSString string) (toJSString title)

