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
module Carnap.Frontend.Ghcjs.Components.GenHelp (genHelp) where

import Carnap.Core.Data.AbstractDerivationDataTypes (RulesAndArity)
import Carnap.Core.Data.Rules (Sequent(Sequent), AbsRulePlus(rule), AbsRule(AbsRule),AmbiguousRulePlus(ruleVersionsPlus,ruleNamePlus))
import Data.Monoid (mconcat, (<>))
import Data.Set (toList)
import Text.Blaze.Html5 as B
--import Text.Blaze.Html5.Attributes
import Text.Blaze.Internal (stringValue, MarkupM)
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

genHelp target doc rules ruleset id = do let el = castToHTMLElement target
                                         Just parent <- nodeGetParentElement target
                                         Just body <- documentGetBody doc
                                         mhelp@(Just help) <- fmap castToHTMLDivElement <$> documentCreateElement doc "div"
                                         elementSetAttribute help "class" "help"
                                         elementSetId help id
                                         mcloser@(Just closer) <- fmap castToHTMLDivElement <$> documentCreateElement doc "div"
                                         elementSetAttribute closer "class" "closer"
                                         htmlElementSetTabIndex help 1
                                         htmlElementSetInnerHTML help $ renderHtml $ ruleTable ruleset
                                         htmlElementSetInnerHTML closer "✕"
                                         nodeAppendChild parent mhelp
                                         nodeAppendChild help mcloser
                                         elementOnclick help $ do e <- event
                                                                  liftIO $ eventStopPropagation e
                                         elementOnkeydown help $ hide help
                                         elementOnclick body $ hide help
                                         elementOnclick closer $ hide help
                                         return help
                                where hide help = liftIO $ do
                                                    style <- elementGetAttribute help "style" 
                                                    if style /= "display:none" 
                                                        then elementSetAttribute help "style" "display:none" 
                                                        else return ()
                                                    return ()

ruleTable rs = table $ mconcat $ Prelude.map ruleRow $ toList rs

ruleRow ambrp = tr $ td (toHtml $ ruleNamePlus ambrp) <> mconcat (ruleCols ambrp) 

ruleCols ambrp = Prelude.map (td . toMarkup . rule) (ruleVersionsPlus ambrp)
