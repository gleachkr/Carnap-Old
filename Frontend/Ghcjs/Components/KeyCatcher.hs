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
module Carnap.Frontend.Ghcjs.Components.KeyCatcher where

import Control.Monad.Reader
import Data.IORef
import GHCJS.DOM.Element (elementOnkeypress)
import GHCJS.DOM.HTMLElement (castToHTMLElement)
import GHCJS.DOM.EventM(uiCharCode,uiKeyCode, preventDefault)

--keyCatcher :: System.Glib.Types.GObjectClass obj => obj -> (IORef [t] -> Int -> IO ()) -> IO ()
keyCatcher target handler = do let el = castToHTMLElement target
                               kbuffer <- newIORef [] 
                               elementOnkeypress el $ do k <- uiCharCode
                                                         k' <- uiKeyCode --we also get the keycode to handle some FireFox irregularities
                                                         catch <- liftIO $ handler kbuffer (if k > 0 then k else k') 
                                                         when catch preventDefault
                               return ()
