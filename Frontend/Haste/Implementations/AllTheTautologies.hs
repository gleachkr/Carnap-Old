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
