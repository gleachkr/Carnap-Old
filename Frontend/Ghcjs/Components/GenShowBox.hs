{-# LANGUAGE AllowAmbiguousTypes #-}
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
module Carnap.Frontend.Ghcjs.Components.GenShowBox (genShowBox) where

-- import Carnap.Frontend.Ghcjs.Components.ActivateProofBox (activateProofBox)
import Carnap.Frontend.Ghcjs.Components.UpdateBox (updateBox)
import Carnap.Frontend.Ghcjs.Components.BoxSettings (BoxSettings(..))
import Carnap.Core.Data.AbstractSyntaxDataTypes (DisplayVar,NextVar,Schematizable, Form)
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (S_DisplayVar, S_NextVar, SchemeVar,SSequentItem(SeqList), Var)
import Carnap.Core.Data.AbstractDerivationDataTypes (RulesAndArity)
import Carnap.Core.Unification.HigherOrderMatching
import Carnap.Languages.Util.ParserTypes
import Carnap.Languages.Util.LanguageClasses
import Carnap.Core.Data.Rules (Sequent(Sequent), AmbiguousRulePlus)
import Data.IORef
import Data.List (intercalate)
import GHCJS.DOM.HTMLDivElement (HTMLDivElement)
import qualified Data.Set as Set
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementSetInnerHTML)
import GHCJS.DOM.HTMLTextAreaElement (castToHTMLTextAreaElement, htmlTextAreaElementSetValue, htmlTextAreaElementGetValue)
import GHCJS.DOM.Node (nodeInsertBefore, nodeAppendChild, nodeGetParentElement)
import GHCJS.DOM.Document (documentCreateElement)
import GHCJS.DOM.Element (elementSetAttribute, elementOnkeyup)
import GHCJS.DOM.Types (IsNode,IsDocument,IsHTMLTextAreaElement, HTMLElement, Element)
import GHCJS.DOM.EventM(uiKeyCode)
import Control.Monad.Trans (liftIO)
import Control.Concurrent
import Control.Applicative ((<$>))

genShowBox :: (GHCJS.DOM.Types.IsDocument self, S_DisplayVar sv quant, S_NextVar sv quant, SchemeVar sv, 
                    UniformlyEquaitable sv, UniformlyEquaitable f, UniformlyEquaitable quant, UniformlyEquaitable con, UniformlyEquaitable pred, 
                    DisplayVar sv quant, NextVar sv quant, Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred) => 
                    Element -> self -> BoxSettings pred con quant f sv a st -> Sequent (SSequentItem pred con quant f sv) -> 
                    IO (IORef (BoxSettings pred con quant f sv a st), IORef (Sequent (SSequentItem pred con quant f sv)))
genShowBox parent doc initSettings goal@(Sequent [SeqList prems] conc) = do
           mpb@(Just pb) <- documentCreateElement doc "textarea"
           let field = castToHTMLTextAreaElement pb
           mgoalDiv@(Just goalDiv) <- fmap castToHTMLElement <$> documentCreateElement doc "div"
           manalysis'@(Just analysis') <- fmap castToHTMLElement <$> documentCreateElement doc "div"
           mproofpane'@(Just proofpane') <- fmap castToHTMLElement <$> documentCreateElement doc "div"
           elementSetAttribute pb "class" "lined"
           elementSetAttribute goalDiv "class" "goal"
           elementSetAttribute analysis' "class" "analysis"
           elementSetAttribute proofpane' "class" "root"
           htmlElementSetInnerHTML goalDiv (show goal)
           htmlTextAreaElementSetValue field $ intercalate "\n" $ Prelude.map (\x -> show x ++ "\tPR") prems 
           settings <- newIORef initSettings {manalysis  = manalysis', mproofpane = mproofpane'}
           cursettings <- readIORef settings
           updateBox field cursettings
           mref <- newIORef Nothing
           gref <- newIORef goal
           elementOnkeyup field $ do
               k <- uiKeyCode
               if k `elem` [16 .. 20] ++ [33 .. 40] ++ [91 .. 93] --don't redrawn on modifiers and arrows
                   then return ()
                   else liftIO $ do mthr <- readIORef mref
                                    goal' <- readIORef gref
                                    cursettings' <- readIORef settings
                                    case mthr of
                                        Nothing -> return ()
                                        Just t -> killThread t
                                    elementSetAttribute proofpane' "class" "loading root"
                                    nthr <- forkIO $ do threadDelay 500000
                                                        shown <- updateBox field cursettings'
                                                        case shown of
                                                            Just sequent ->  if goal' `matchesSequent` sequent 
                                                                                    then elementSetAttribute goalDiv "class" "goal achieved"
                                                                                    else elementSetAttribute goalDiv "class" "goal"
                                                            _ -> do elementSetAttribute goalDiv "class" "goal"
                                                                    return ()
                                                        elementSetAttribute proofpane' "class" "root"
                                                        return ()
                                    writeIORef mref $ Just nthr
                                    nnthr <- readIORef mref
                                    return ()
           nodeAppendChild parent (Just pb)
           nodeAppendChild parent (Just goalDiv)
           nodeAppendChild parent $! mproofpane'
           nodeAppendChild parent $! manalysis'
           return (settings,gref)

matchesSequent :: (S_DisplayVar sv quant, S_NextVar sv quant, SchemeVar sv, 
                    UniformlyEquaitable sv, UniformlyEquaitable f, UniformlyEquaitable quant, UniformlyEquaitable con, UniformlyEquaitable pred, 
                    DisplayVar sv quant, NextVar sv quant, Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred) => 
                    Sequent (SSequentItem pred con quant f sv) -> Sequent (SSequentItem pred con quant f sv) -> Bool
matchesSequent (Sequent [SeqList ps] c) (Sequent [SeqList ps'] c') = c == c' && all (`elem` ps) ps'
matchesSequent _ _ = False

