{-# LANGUAGE GADTs, FlexibleInstances, UndecidableInstances, OverlappingInstances #-}
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
module Carnap.Frontend.Ghcjs.Components.ActivateProofBox (activateProofBox) where

import Carnap.Frontend.Components.ProofTreeParser (parseTheBlock, pairHandler, FParser)
import Carnap.Core.Unification.HigherOrderMatching
import Carnap.Core.Data.AbstractSyntaxDataTypes (DisplayVar,NextVar,Schematizable, Form)
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (S_NextVar, SchemeVar,SSequentItem, Var)
import Carnap.Core.Data.AbstractDerivationDataTypes (RulesAndArity)
import Carnap.Core.Data.AbstractDerivationSecondOrderMatching
import Carnap.Core.Data.Rules (Sequent(Sequent), AbsRule(AbsRule),AmbiguousRulePlus)
import Carnap.Systems.NaturalDeduction.ProofTreeHandler
import Carnap.Systems.NaturalDeduction.JudgementHandler (derivationProves)
import Carnap.Systems.NaturalDeduction.ProofTreeDataTypes
import Data.IORef
import Data.Tree (Tree(Node))
import qualified Data.Set as Set
import Data.List (intercalate, intersperse, nub)
import Data.Monoid (mconcat, (<>))
import Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Text.Blaze.Internal (stringValue, MarkupM)
import Text.Blaze.Html.Renderer.Text (renderHtml)
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementSetInnerHTML, htmlElementSetInnerText)
import GHCJS.DOM.HTMLTextAreaElement (castToHTMLTextAreaElement, htmlTextAreaElementGetValue)
import GHCJS.DOM.HTMLDivElement (castToHTMLDivElement, HTMLDivElement)
import GHCJS.DOM.Node (nodeInsertBefore, nodeAppendChild, nodeGetParentElement)
import GHCJS.DOM.Document (documentCreateElement)
import GHCJS.DOM.Element (elementSetAttribute, elementOnkeyup)
import GHCJS.DOM.Types (IsNode,IsDocument,IsHTMLTextAreaElement, IsHTMLElement)
import Control.Monad.Trans (liftIO)
import Control.Applicative ((<$>))
import Control.Concurrent

activateProofBox :: (GHCJS.DOM.Types.IsNode newChild, GHCJS.DOM.Types.IsDocument self, S_NextVar sv quant, SchemeVar sv, 
                    UniformlyEquaitable sv, UniformlyEquaitable f, UniformlyEquaitable quant, UniformlyEquaitable con, UniformlyEquaitable pred, 
                    DisplayVar sv quant, NextVar sv quant, Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred) => 
                    newChild -> self -> RulesAndArity -> Set.Set (AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())) -> 
                        FParser (Form pred con quant f sv a) -> IO HTMLDivElement
activateProofBox pb doc rules ruleset fParser = do let field = castToHTMLTextAreaElement pb
                                                   Just parent <- nodeGetParentElement pb
                                                   mnewDiv1@(Just newDiv) <- fmap castToHTMLDivElement <$> documentCreateElement doc "div"
                                                   manalysis@(Just analysis) <- fmap castToHTMLDivElement <$> documentCreateElement doc "div"
                                                   mnewSpan2@(Just newSpan2) <- fmap castToHTMLElement <$> documentCreateElement doc "span"
                                                   mnewSpan3@(Just newSpan3) <- fmap castToHTMLElement <$> documentCreateElement doc "span"
                                                   updateBox field rules ruleset fParser newSpan2 newSpan3 analysis
                                                   mref <- newIORef Nothing
                                                   elementOnkeyup field $ 
                                                       liftIO $ do mthr <- readIORef mref
                                                                   case mthr of
                                                                       Nothing -> return ()
                                                                       Just t -> killThread t
                                                                   elementSetAttribute newSpan3 "class" "loading"
                                                                   nthr <- forkIO $ do threadDelay 1000000
                                                                                       _ <- updateBox field rules ruleset fParser newSpan2 newSpan3 analysis 
                                                                                       elementSetAttribute newSpan3 "class" ""
                                                                                       return ()
                                                                   writeIORef mref $ Just nthr
                                                                   nnthr <- readIORef mref
                                                                   return ()
                                                   elementSetAttribute analysis "class" "analysis"
                                                   elementSetAttribute newSpan2 "class" "rslt"
                                                   nodeAppendChild parent mnewDiv1
                                                   nodeAppendChild newDiv (Just pb)
                                                   nodeAppendChild newDiv manalysis
                                                   nodeAppendChild newDiv mnewSpan2
                                                   nodeAppendChild newDiv mnewSpan3
                                                   return newDiv

updateBox :: (GHCJS.DOM.Types.IsHTMLTextAreaElement self, GHCJS.DOM.Types.IsHTMLElement self1, GHCJS.DOM.Types.IsHTMLElement self2,GHCJS.DOM.Types.IsHTMLElement self3,
             S_NextVar sv quant, SchemeVar sv, UniformlyEquaitable sv, UniformlyEquaitable f, UniformlyEquaitable quant, UniformlyEquaitable con, UniformlyEquaitable pred, 
                DisplayVar sv quant, NextVar sv quant, Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred) =>
                    self -> RulesAndArity -> Set.Set (AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())) 
                    -> FParser (Form pred con quant f sv b) -> self2 -> self1 -> self3 -> IO ()
updateBox box rules ruleset fParser newSpan2 newSpan3 analysis =  do contents <- htmlTextAreaElementGetValue box :: IO String
                                                                     let possibleParsing = parseTheBlock fParser ( contents ++ "\n" )
                                                                     let theForest = fst $ pairHandler possibleParsing
                                                                     if null theForest
                                                                         then do htmlElementSetInnerHTML newSpan2 ""
                                                                                 htmlElementSetInnerHTML newSpan3 ""
                                                                                 htmlElementSetInnerHTML analysis ""
                                                                                 return ()
                                                                         else do htmlElementSetInnerHTML newSpan3 $ renderHtml (forestToDom theForest ! class_ (stringValue "root"))
                                                                                 case handleForest theForest rules ruleset of 
                                                                                     (Left derRept) -> do htmlElementSetInnerHTML analysis (renderHtml $ toDomList (rules,ruleset) (reverse derRept))
                                                                                                          htmlElementSetInnerHTML newSpan2 ("" :: String)
                                                                                     (Right (Left _)) -> do htmlElementSetInnerText analysis ("invalid" :: String)
                                                                                                            htmlElementSetInnerHTML newSpan2 ("" :: String)
                                                                                     (Right (Right arg)) -> do htmlElementSetInnerText newSpan2 (display arg)
                                                                                                               htmlElementSetInnerHTML analysis ("" :: String)
                                                                                 return ()

display (Sequent ps c) = intercalate " . " (Prelude.map show (nub ps)) ++ " ∴ " ++ show c

forestToDom :: Show f => ProofForest f -> Html 
forestToDom t = B.span $ mapM_ treeToDom t

treeToDom :: Show f => ProofTree f -> Html
treeToDom (Node (Right (f,"SHOW",_)) []) = B.div . B.span . toHtml $ "Show: " ++ show f
treeToDom (Node (Right (f,"SHOW",_)) d) = B.div $ do B.span . toHtml $ "Show: " ++ show f
                                                     B.div ! class_ (stringValue "open") $ forestToDom d
treeToDom (Node (Right (f,':':r,s)) d) = B.div $ do B.span $ toHtml $ "Show: " ++ show f
                                                    B.div ! class_ (stringValue "closed") $ do forestToDom d
                                                                                               B.div $ do B.span ! class_ (stringValue "termination") $ toHtml ""
                                                                                                          B.span $ do B.span $ toHtml r
                                                                                                                      if s /= [] then B.span . toHtml . init . tail $ show s 
                                                                                                                                 else return ()
treeToDom (Node (Right (f,r,s)) []) = B.div $ do B.span . toHtml . show $ f 
                                                 B.span $ do B.span $ toHtml r 
                                                             if s /= [] then B.span . toHtml . init . tail $ show s 
                                                                        else return ()
treeToDom (Node (Left s) _) = B.div $ toHtml s

toDomList :: (S_NextVar sv quant, SchemeVar sv, UniformlyEquaitable sv,
             UniformlyEquaitable f, UniformlyEquaitable quant,
             UniformlyEquaitable con, UniformlyEquaitable pred, 
             NextVar sv quant, Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred) => 
             (a, Set.Set (AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ()))) -> 
                [ReportLine (Form pred con quant f sv b)] -> Text.Blaze.Internal.MarkupM ()
toDomList thisLogic = mapM_ handle
        where view j = case derivationProves (snd thisLogic) j of 
                                Right arg -> B.div $ do B.div $ toHtml "✓"
                                                        B.div (toHtml $ display arg) ! class_ (stringValue "errormsg")
                                Left e -> B.div $ do B.div $ toHtml "✖"
                                                     let ers = Prelude.map (B.div . toHtml) e
                                                     let l = intersperse hr ers 
                                                     B.div (B.div (toMarkup $ "This rule didn't match. I tried " ++ (show $ length ers) ++ " possibilities") 
                                                            <> br <> mconcat l) ! class_ (stringValue "errormsg")
              handle dl = case dl of
                             ClosureLine -> B.div $ toHtml ""
                             OpenLine j -> view j
                             ClosedLine j -> view j
                             ErrLine e -> B.div $ do B.div $ toHtml "✖"
                                                     B.div (toHtml e) ! class_ (stringValue "errormsg")

instance (Show a) => ToMarkup a where
        toMarkup x = toMarkup (show x)

instance (ToMarkup term) => ToMarkup (AbsRule term) where
        toMarkup (AbsRule ps c) = mconcat (intersperse br $ Prelude.map toMarkup ps) <> br <> toMarkup " ∴ " <> toMarkup c

instance (ToMarkup term) => ToMarkup (Sequent term) where
        toMarkup (Sequent ps c) = mconcat (intersperse (toMarkup ", ") $ Prelude.map toMarkup ps) <> toMarkup " ⊢ " <> toMarkup c

instance (ToMarkup var, ToMarkup t) => ToMarkup (MatchError var t) where
        toMarkup (UnableToMatch a b) = toMarkup "I need to match " <> br <> B.div (toMarkup a) ! class_ (stringValue "uniblock")
                                                               <> toMarkup " with " <> B.div (toMarkup b) ! class_ (stringValue "uniblock") <> toMarkup "." <> br 
                                                               <> toMarkup "But that's impossible."
        toMarkup (ErrWrapper e)      = toMarkup e
        toMarkup (SubError err a b)  = toMarkup "I need to match " <> br <> B.div (toMarkup a) ! class_ (stringValue "uniblock" )
                                                               <> toMarkup " with " <> B.div (toMarkup b) ! class_ (stringValue "uniblock")
                                                               <> B.div (toMarkup "so..." <> (B.div ! class_ (stringValue "suberr") $  toMarkup err))
        toMarkup (OccursCheck v t)   = toMarkup "Cannot construct infinite type " <> toMarkup v <> toMarkup " = " <> toMarkup t
        toMarkup (SpecialErr s)      = toMarkup s


