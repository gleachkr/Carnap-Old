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

module Carnap.Frontend.Ghcjs.Components.SyncScroll (syncScroll) where

import GHCJS.DOM.Element (elementOnscroll, elementGetScrollTop,elementSetScrollTop)
import Control.Monad.Trans (liftIO)

syncScroll e1 e2 = do elementOnscroll e1 $ liftIO $ do st <- elementGetScrollTop e1
                                                       elementSetScrollTop e2 st
                      elementOnscroll e2 $ liftIO $ do st <- elementGetScrollTop e2
                                                       elementSetScrollTop e1 st
                        
