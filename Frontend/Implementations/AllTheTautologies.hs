module Main where

import Haste hiding (style)
import Data.IORef
import Carnap.Languages.Sentential.PropositionalLanguage
import Carnap.Frontend.Components.LazyLister

main :: IO ()
main = do scrollboxes <- elemsByClass "scrollbox"
          ref <- newIORef 0
          let el = Prelude.map (\f -> do e <- newElem "div"
                                         setProp e "innerHTML" (show f)
                                         return e) (concat $ map tautologyWithNconnectives [1..])
          mapM_ (activateLazyList ref el) scrollboxes
