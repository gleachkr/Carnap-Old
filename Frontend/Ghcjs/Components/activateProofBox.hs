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

import Carnap.Frontend.Ghcjs.Components.UpdateBox (updateBox)
import Carnap.Frontend.Ghcjs.Components.BoxSettings (BoxSettings(..))
import Carnap.Frontend.Ghcjs.Components.SyncScroll (syncScroll)
import Carnap.Core.Unification.HigherOrderMatching (UniformlyEquaitable)
import Carnap.Core.Data.AbstractSyntaxDataTypes (DisplayVar,NextVar,Schematizable, Form)
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (S_NextVar, S_DisplayVar, SchemeVar,SSequentItem, Var)
import Data.IORef
import Data.Tree (Tree(Node))
import qualified Data.Set as Set
import Data.List (intercalate, intersperse, nub)
import Data.Monoid (mconcat, (<>))
import Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Text.Blaze.Internal (stringValue, MarkupM)
import Text.Blaze.Html.Renderer.Text (renderHtml)
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementSetInnerHTML)
import GHCJS.DOM.HTMLTextAreaElement (castToHTMLTextAreaElement, htmlTextAreaElementGetValue)
import GHCJS.DOM.Node (nodeInsertBefore, nodeAppendChild, nodeGetParentElement)
import GHCJS.DOM.Document (documentCreateElement)
import GHCJS.DOM.Element (elementSetAttribute, elementOnkeyup)
import GHCJS.DOM.Types (IsNode,IsDocument,IsHTMLTextAreaElement, HTMLElement)
import GHCJS.DOM.EventM(uiKeyCode)
import Control.Monad.Trans (liftIO)
import Control.Applicative ((<$>))
import Control.Monad (unless)
import Control.Concurrent

activateProofBox :: (GHCJS.DOM.Types.IsNode newChild, GHCJS.DOM.Types.IsDocument self, S_NextVar sv quant, SchemeVar sv, 
                    UniformlyEquaitable sv, UniformlyEquaitable f, UniformlyEquaitable quant, UniformlyEquaitable con, UniformlyEquaitable pred, 
                    DisplayVar sv quant, S_DisplayVar sv quant, NextVar sv quant, Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred) => 
                    newChild -> self -> BoxSettings pred con quant f sv a st -> IO (HTMLElement, IORef (BoxSettings pred con quant f sv a st))
activateProofBox pb doc settings' = do let field = castToHTMLTextAreaElement pb
                                       Just parent <- nodeGetParentElement pb
                                       mnewDiv1@(Just newDiv) <- fmap castToHTMLElement <$> documentCreateElement doc "div"
                                       mnewDiv2@(Just newDiv2) <- fmap castToHTMLElement <$> documentCreateElement doc "div"
                                       mnewSpan2@(Just newSpan2) <- fmap castToHTMLElement <$> documentCreateElement doc "span"
                                       manalysis'@(Just analysis) <- fmap castToHTMLElement <$> documentCreateElement doc "div"
                                       syncScroll analysis newDiv2
                                       settings <- newIORef settings' { manalysis = manalysis', mresult = mnewSpan2, mproofpane = mnewDiv2}
                                       cursettings <- readIORef settings
                                       updateBox field cursettings
                                       mref <- newIORef Nothing
                                       elementOnkeyup field $ do
                                           k <- uiKeyCode
                                           unless (k `elem` [16 .. 20] ++ [33 .. 40] ++ [91 .. 93]) --don't redrawn on modifiers and arrows
                                             $ liftIO $ do mthr <- readIORef mref
                                                           cursettings' <- readIORef settings
                                                           case mthr of
                                                               Nothing -> return ()
                                                               Just t -> killThread t
                                                           elementSetAttribute newDiv2 "class" "loading root"
                                                           nthr <- forkIO $ do threadDelay 500000
                                                                               _ <- updateBox field cursettings'
                                                                               elementSetAttribute newDiv2 "class" "root"
                                                                               return ()
                                                           writeIORef mref $ Just nthr
                                                           nnthr <- readIORef mref
                                                           return ()
                                       elementSetAttribute analysis "class" "analysis"
                                       elementSetAttribute newSpan2 "class" "rslt"
                                       nodeAppendChild parent mnewDiv1
                                       nodeAppendChild newDiv (Just pb)
                                       nodeAppendChild newDiv manalysis'
                                       nodeAppendChild newDiv mnewSpan2
                                       nodeAppendChild newDiv mnewDiv2
                                       return (newDiv,settings)
