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

module Carnap.Frontend.Ghcjs.Components.HelperFunctions (nodelistToNumberedList,nodelistToList, htmlColltoList, toPremConcPair)

where 

import GHCJS.DOM.HTMLCollection (htmlCollectionGetLength, htmlCollectionItem)
import GHCJS.DOM.NodeList (nodeListGetLength, nodeListItem)
import Carnap.Languages.Util.ParserTypes
import Carnap.Frontend.Ghcjs.Components.BoxSettings (BoxSettings(..))
import Text.Parsec (runParser)
import Text.Parsec.Char (oneOf)
import Text.Parsec.Combinator (many1,sepBy)

--This module houses some helper functions which are useful for dealing
--with GHCJS data structures

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
--1. Common parsing tasks
--------------------------------------------------------

formList s = parser (fparser s) `sepBy` many1 (oneOf " ,")

toPremConcPair cv pv s = (stateParse (fparser s) cv, runParser (formList s) (initState (fparser s)) "" pv)
