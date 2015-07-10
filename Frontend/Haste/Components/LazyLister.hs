module Carnap.Frontend.Haste.Components.LazyLister where

import Haste hiding (style)
import Data.IORef
import Control.Monad.IO.Class
import Carnap.Languages.Sentential.PropositionalLanguage

lazyList :: IORef Int -> [IO Elem] -> Elem -> IO ()
lazyList ref l el = do st <- getProp el "scrollTop" 
                       sh <- getProp el "scrollHeight"
                       ch <- getProp el "clientHeight" 
                       if (read sh::Int) - (read st::Int) == (read ch::Int)
                       then updateBot ref l el
                       else if (read st::Int) == 0 
                       then updateTop ref l el
                       else return ()

updateBot :: IORef Int -> [IO Elem] -> Elem -> IO ()
updateBot ref l el = do n <- readIORef ref
                        if n > 100 then do mc <- getFirstChild el
                                           case mc of 
                                                Just c1 -> removeChild c1 el
                                                Nothing -> return ()
                                   else return ()
                        writeIORef ref (n+1)
                        lc <- l !! n
                        addChild lc el

updateTop :: IORef Int -> [IO Elem] -> Elem -> IO ()
updateTop ref l el = do n <- readIORef ref
                        if n > 100 then do mc <- getLastChild el
                                           case mc of 
                                                Just c1 -> removeChild c1 el
                                                Nothing -> return ()
                                           writeIORef ref (n-1)
                                           do mc2 <- getFirstChild el
                                              lc <- (l !! (n-100))
                                              case mc2 of
                                                Just c2 -> addChildBefore lc el c2
                                                Nothing -> return ()
                                   else return ()

activateLazyList :: Control.Monad.IO.Class.MonadIO m => IORef Int -> [IO Elem] -> Elem -> m Bool
activateLazyList ref l el = onEvent el OnWheel (\_ _ -> lazyList ref l el)
