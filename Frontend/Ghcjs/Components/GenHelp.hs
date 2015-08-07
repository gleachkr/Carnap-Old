module Carnap.Frontend.Ghcjs.Components.GenHelp (genHelp) where

import Carnap.Core.Data.AbstractDerivationDataTypes (RulesAndArity)
import Carnap.Core.Data.Rules (Sequent(Sequent), AbsRulePlus(rule), AbsRule(AbsRule),AmbiguousRulePlus(ruleVersionsPlus,ruleNamePlus))
import Data.Monoid (mconcat, (<>))
import Data.Set (toList)
import Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Text.Blaze.Internal (stringValue, MarkupM)
import Text.Blaze.Html.Renderer.Text (renderHtml)
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementSetInnerHTML,htmlElementSetTabIndex)
import GHCJS.DOM.HTMLDivElement (castToHTMLDivElement)
import GHCJS.DOM.Node (nodeAppendChild, nodeGetParentElement)
import GHCJS.DOM.Document (documentCreateElement)
import GHCJS.DOM.Element (elementSetAttribute, elementSetId, elementOnkeypress)
import Control.Monad.Trans (liftIO)
import Control.Applicative ((<$>))

genHelp target doc rules ruleset id = do let el = castToHTMLElement target
                                         Just parent <- nodeGetParentElement target
                                         mhelp@(Just help) <- fmap castToHTMLDivElement <$> documentCreateElement doc "div"
                                         elementSetAttribute help "class" "help"
                                         elementSetId help id
                                         htmlElementSetTabIndex help 1
                                         htmlElementSetInnerHTML help $ renderHtml $ ruleTable ruleset
                                         nodeAppendChild parent mhelp
                                         elementOnkeypress help $ 
                                             liftIO $ do
                                                 elementSetAttribute help "style" "display:none"
                                                 return ()
                                         return help

ruleTable rs = table $ mconcat $ Prelude.map ruleRow $ toList rs

ruleRow ambrp = tr $ td (toHtml $ ruleNamePlus ambrp) <> mconcat (ruleCols ambrp) 

ruleCols ambrp = Prelude.map (td . toMarkup . rule) (ruleVersionsPlus ambrp)
