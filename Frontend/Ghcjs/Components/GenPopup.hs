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
module Carnap.Frontend.Ghcjs.Components.GenPopup (genPopup) where

import Text.Blaze.Html.Renderer.Text (renderHtml)
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementSetInnerHTML,htmlElementSetTabIndex)
import GHCJS.DOM.HTMLDivElement (castToHTMLDivElement)
import GHCJS.DOM.Node (nodeAppendChild, nodeGetParentElement)
import GHCJS.DOM.Document (documentGetBody, documentCreateElement)
import GHCJS.DOM.Element (elementGetAttribute, elementSetAttribute, elementSetId, elementOnkeydown, elementOnclick)
import GHCJS.DOM.EventM (event, preventDefault)
import GHCJS.DOM.Event (eventStopPropagation)
import Control.Monad.Trans (liftIO)
import Control.Applicative ((<$>))

genPopup target doc html id = do let el = castToHTMLElement target
                                 Just parent <- nodeGetParentElement target
                                 Just body <- documentGetBody doc
                                 mpopup@(Just popup) <- fmap castToHTMLDivElement <$> documentCreateElement doc "div"
                                 elementSetAttribute popup "class" "popup"
                                 elementSetId popup id
                                 mcloser@(Just closer) <- fmap castToHTMLDivElement <$> documentCreateElement doc "div"
                                 elementSetAttribute closer "class" "closer"
                                 htmlElementSetTabIndex popup 1
                                 htmlElementSetInnerHTML popup $ renderHtml html
                                 htmlElementSetInnerHTML closer "✕"
                                 nodeAppendChild parent mpopup
                                 nodeAppendChild popup mcloser
                                 elementOnclick popup $ do e <- event
                                                           liftIO $ eventStopPropagation e
                                 elementOnkeydown popup $ hide popup
                                 elementOnclick body $ hide popup
                                 elementOnclick closer $ hide popup
                                 return popup
                                where hide popup = liftIO $ do style <- elementGetAttribute popup "style" 
                                                               if style /= "display:none" 
                                                                    then elementSetAttribute popup "style" "display:none" 
                                                                    else return ()
                                                               return ()

