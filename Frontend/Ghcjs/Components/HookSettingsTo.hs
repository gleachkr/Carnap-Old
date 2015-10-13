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

module Carnap.Frontend.Ghcjs.Components.HookSettingsTo (hookSettingsInit, hookSettingsLink)

where

import Data.Map as M
import Data.Maybe (catMaybes)
import Data.IORef
import GHCJS.DOM.HTMLSelectElement (htmlSelectElementGetValue)
import GHCJS.DOM.HTMLOptionElement (htmlOptionElementSetValue)
import GHCJS.DOM.Types (castToNode, castToHTMLSelectElement, castToHTMLOptionElement)
import Control.Applicative ((<$>))
import Control.Monad (zipWithM_)
import Control.Monad.Trans (liftIO)
import GHCJS.DOM.HTMLElement (htmlElementSetInnerHTML)
import GHCJS.DOM.Element (elementOnchange)
import GHCJS.DOM.Node (nodeAppendChild)
import GHCJS.DOM.Document (documentCreateElement)

hookSettingsInit doc sl' ref mt = hookSettingsGen doc sl' ref mt mt

hookSettingsLink doc sl' ref mt = hookSettingsGen doc sl' ref (Prelude.foldr delete mt (keys mt)) mt

hookSettingsGen doc sl' ref mt mt' = do let modkeys = keys mt
                                        let sel = castToHTMLSelectElement sl'
                                        opList <- optsFrom doc modkeys --want to convert a list of strings into a list of option elements with appropriate values
                                        let mopList = Prelude.map Just opList 
                                        mapM (nodeAppendChild $ castToNode sel) mopList
                                        elementOnchange sel $ liftIO $ do v <- htmlSelectElementGetValue sel
                                                                          case M.lookup v mt' of
                                                                              Nothing -> return ()
                                                                              Just f -> modifyIORef ref f

optsFrom doc list = do mopts <- mapM (const $ newOpt doc) list
                       let opts = catMaybes mopts
                       zipWithM_ htmlElementSetInnerHTML opts list
                       zipWithM_ htmlOptionElementSetValue opts list
                       return opts

newOpt doc = fmap castToHTMLOptionElement <$> documentCreateElement doc "option"
