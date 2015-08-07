
module Carnap.Frontend.Ghcjs.Components.KeyCatcher where

import Control.Monad.Reader
import Data.IORef
import GHCJS.DOM.Element (elementOnkeypress)
import GHCJS.DOM.HTMLElement (castToHTMLElement)
import GHCJS.DOM.EventM(uiCharCode, preventDefault)

--keyCatcher :: System.Glib.Types.GObjectClass obj => obj -> (IORef [t] -> Int -> IO ()) -> IO ()
keyCatcher target handler = do let el = castToHTMLElement target
                               kbuffer <- newIORef [] 
                               elementOnkeypress el $ do k <- uiCharCode
                                                         catch <- liftIO $ handler kbuffer k
                                                         if catch then preventDefault else return ()
                               return ()
