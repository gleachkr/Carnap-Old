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
-}
module Carnap.Frontend.Ghcjs.Components.Slider (slider) where

import GHCJS.DOM.Types (IsNode,IsDocument,IsHTMLTextAreaElement, HTMLElement, Element, Node)
import GHCJS.DOM.Element (elementSetAttribute, elementGetClassName, elementOnclick)
import GHCJS.DOM.HTMLElement (htmlElementSetInnerHTML,castToHTMLElement)
import GHCJS.DOM.Node (nodeAppendChild)
import GHCJS.DOM.Document (documentCreateElement)
import Control.Monad.IO.Class (liftIO)

slider :: GHCJS.DOM.Types.IsDocument self => self -> [Element] -> IO Element
slider doc els = do
           msliderDiv@(Just sliderDiv) <- documentCreateElement doc "div"
           mnext@(Just next) <- documentCreateElement doc "button"
           mprev@(Just prev) <- documentCreateElement doc "button"
           elementSetAttribute sliderDiv "class" "sliderDiv"
           elementSetAttribute next "class" "nextA"
           elementSetAttribute prev "class" "prevA"
           htmlElementSetInnerHTML (castToHTMLElement next) "next"
           htmlElementSetInnerHTML (castToHTMLElement prev) "prev"
           elementSetAttribute (head els) "class" "sliderVisible"
           mapM_ (\x -> elementSetAttribute x "class" "sliderHidden") $ tail els
           elementOnclick next $ advance els
           elementOnclick prev $ regress els
           mapM_ (nodeAppendChild sliderDiv . Just) els
           nodeAppendChild sliderDiv mprev
           nodeAppendChild sliderDiv mnext
           return sliderDiv
    where
        advance ls = liftIO $ do bv <- breakAtVis ls
                                 case bv of
                                     (last, vis:next:post) -> resetVis vis next "sliderViewed"
                                     _ -> return ()
        regress ls = liftIO $ do bv <- breakAtVis ls
                                 case bv of
                                     (last:pre, vis:post) -> resetVis vis last "sliderHidden"
                                     _ -> return ()
        breakAtVis ls = do classes <- mapM (\x -> do name <- elementGetClassName x; print name; return name)ls 
                           let m = length $ takeWhile (/= "sliderVisible") classes
                           let (pre, post) = splitAt m ls
                           return (reverse pre, post)
        resetVis oldvis newvis s = do elementSetAttribute oldvis "class" s
                                      elementSetAttribute newvis "class" "sliderVisible" 
