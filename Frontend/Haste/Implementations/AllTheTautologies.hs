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
module Main where

import Haste hiding (style)
import Data.IORef
import Carnap.Languages.Sentential.PropositionalLanguage
import Carnap.Calculi.ClassicalSententialLogic1 (classicalRules, classicalSLruleSet)
import Carnap.Frontend.Haste.Components.LazyLister (activateLazyList)
import Carnap.Frontend.Haste.Components.ProofPadEmbedding (embedWith)

main :: IO ()
main = do scrollboxes <- elemsByClass "scrollbox"
          ref <- newIORef 0
          let el = Prelude.map toTautElem $ concatMap tautologyWithNconnectives [1..]
          mapM_ (activateLazyList ref el) scrollboxes
          embedWith (classicalRules, classicalSLruleSet)

toTautElem f = do e <- newElem "div"
                  setProp e "innerHTML" (show f)
                  onEvent e OnClick $ setMainBox f
                  return e

setMainBox f _ _ = do mmb <- elemById "mainBox"
                      case mmb of 
                        Nothing -> return ()
                        Just mb -> 
                            do tas <- elemsByQS mb "textarea"
                               mapM_ (\e -> 
                                      setProp e "value" ("Show: " ++ show f)) tas
