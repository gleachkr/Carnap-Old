module Carnap.Frontend.Ghcjs.Components.LazyLister (activateLazyList) where 

import Control.Monad
import Control.Monad.IO.Class
import Data.IORef
import GHCJS.DOM.Types (HTMLElement)
import GHCJS.DOM.Element
import GHCJS.DOM.Node

lazyList :: IORef Int-> [IO HTMLElement] -> HTMLElement -> IO ()
lazyList ref l el =  do st <- elementGetScrollTop el
                        sh <- elementGetScrollHeight el
                        ch <- elementGetClientHeight el
                        if fromIntegral sh - fromIntegral st < ch + 1
                            then do updateBot ref l el
                                    elementSetScrollTop el (st - 5)
                            else if st < 1 
                            then do updateTop ref l el
                                    elementSetScrollTop el 1
                            else return ()

updateBot :: IORef Int -> [IO HTMLElement] -> HTMLElement -> IO ()
updateBot ref l el =  do n <- readIORef ref
                         if n > 100 then do mc <- elementGetFirstElementChild el
                                            nodeRemoveChild el mc
                                            return ()
                                 else return ()
                         writeIORef ref (n+1)
                         lc <- l !! n
                         nodeAppendChild el (Just lc)
                         return ()

updateTop :: IORef Int -> [IO HTMLElement] -> HTMLElement -> IO ()
updateTop ref l el = liftIO $ do n <- readIORef ref
                                 if n > 99 then 
                                    do mc <- elementGetLastElementChild el
                                       nodeRemoveChild el mc
                                       writeIORef ref (n-1)
                                       mc2 <- elementGetFirstElementChild el
                                       lc <- l !! (n-100)
                                       nodeInsertBefore el (Just lc) mc2
                                       return ()
                                 else return ()

activateLazyList :: [IO HTMLElement] -> HTMLElement -> IO (IO ())
activateLazyList l el = do ref <- newIORef 0 
                           replicateM_ 50 $ updateBot ref l el
                           elementOnscroll el $ liftIO $ lazyList ref l el
