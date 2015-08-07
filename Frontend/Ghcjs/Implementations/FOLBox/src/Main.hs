{-#LANGUAGE OverlappingInstances #-}
module Main (
    main
) where

import Carnap.Calculi.ClassicalFirstOrderLogic1 (classicalRules, classicalQLruleSet)
import Carnap.Frontend.Ghcjs.Components.ActivateProofBox
import Carnap.Frontend.Ghcjs.Components.KeyCatcher
import Carnap.Frontend.Ghcjs.Components.GenHelp
import Carnap.Languages.FirstOrder.QuantifiedParser (formulaParser)
import Control.Applicative ((<$>))
import Control.Monad.Trans (liftIO)
import GHCJS.DOM.Node (nodeInsertBefore)
import GHCJS.DOM.Element (elementSetAttribute, elementOnclick, elementFocus)
import GHCJS.DOM.Types (HTMLDivElement, HTMLElement)
import GHCJS.DOM (WebView, enableInspector, webViewGetDomDocument, runWebGUI)
import GHCJS.DOM.Document (documentGetBody, documentGetElementsByClassName, documentCreateElement)
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementSetInnerText)
import GHCJS.DOM.NodeList
import GHCJS.DOM.Attr (attrSetValue)
import Language.Javascript.JSaddle (eval,runJSaddle)

main = runWebGUI $ \webView -> do  
    enableInspector webView
    Just doc <- webViewGetDomDocument webView
    Just body <- documentGetBody doc
    Just pbs <- documentGetElementsByClassName doc "proofbox"
    mnodes <- nodelistToNumberedList pbs
    mapM_ (byCase doc) mnodes
    runJSaddle webView $ eval "setTimeout(function(){$(\".lined\").linedtextarea({selectedLine:1});}, 30);"
    return ()
    where byCase doc (n,l) = case n of 
            Just node -> do activateProofBox node doc classicalRules classicalQLruleSet formulaParser
                            help <- genHelp node doc classicalRules classicalQLruleSet ("help" ++ show l)
                            keyCatcher node $ \kbf k -> do if k == 63 then do elementSetAttribute help "style" "display:block" 
                                                                              elementFocus help
                                                                      else return ()
                                                           return (k == 63) --the handler returning true means that the keypress is intercepted
                            return ()
            Nothing -> return ()


nodelistToNumberedList nl = do len <- nodeListGetLength nl
                               mapM (\n -> do i <- nodeListItem nl n; return (i,n)) [0 .. len]
