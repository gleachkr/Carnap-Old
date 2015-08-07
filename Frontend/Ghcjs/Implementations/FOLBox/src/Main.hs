{-#LANGUAGE OverlappingInstances #-}
module Main (
    main
) where

import Carnap.Calculi.ClassicalFirstOrderLogic1 (classicalRules, classicalQLruleSet)
import Carnap.Frontend.Ghcjs.Components.LazyLister
import Carnap.Frontend.Ghcjs.Components.ActivateProofBox
import Carnap.Languages.FirstOrder.QuantifiedParser (formulaParser)
import Control.Applicative ((<$>))
import Control.Monad.Trans (liftIO)
import GHCJS.DOM.Node (nodeInsertBefore)
import GHCJS.DOM.Element (elementSetAttribute, elementOnclick)
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
    mnodes <- nodelistToList pbs
    mapM_ (byCase doc) mnodes
    runJSaddle webView $ eval "setTimeout(function(){$(\".lined\").linedtextarea({selectedLine:1});}, 30);"
    return ()
    where byCase doc n = case n of 
            Just node -> do activateProofBox node doc classicalRules classicalQLruleSet formulaParser
                            return ()
            Nothing -> return ()


nodelistToList nl = do len <- nodeListGetLength nl
                       mapM (nodeListItem nl) [0 .. len]
                       
