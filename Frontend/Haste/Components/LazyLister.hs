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
