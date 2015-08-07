
module Carnap.Frontend.Ghcjs.Components.KeyCatcher where

import Control.Monad.Reader
import Data.IORef
import GHCJS.DOM.Element (elementOnkeyup)
import GHCJS.DOM.HTMLElement (castToHTMLElement)
import GHCJS.DOM.EventM(uiKeyCode)

keyCatcher :: System.Glib.Types.GObjectClass obj => obj -> (IORef [t] -> Int -> IO ()) -> IO ()
keyCatcher target handler = do let el = castToHTMLElement target
                               kbuffer <- newIORef [] 
                               elementOnkeyup el $ do k <- uiKeyCode
                                                      liftIO $ handler kbuffer k
                               return ()
