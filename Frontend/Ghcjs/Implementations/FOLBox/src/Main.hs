{-#LANGUAGE OverlappingInstances #-}
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
module Main (
    main
) where

import Data.Map as M
import Data.Monoid ((<>))
import Carnap.Calculi.ClassicalFirstOrderLogic1 (classicalRules, classicalQLruleSet, prettyClassicalQLruleSet)
import Carnap.Frontend.Ghcjs.Components.ActivateProofBox
import Carnap.Frontend.Ghcjs.Components.KeyCatcher
import Carnap.Frontend.Ghcjs.Components.GenHelp (inferenceTable, terminationTable)
import Carnap.Frontend.Ghcjs.Components.GenPopup (genPopup)
import Carnap.Languages.FirstOrder.QuantifiedParser (formulaParser)
import Control.Applicative ((<$>))
import Control.Monad.Trans (liftIO)
import Text.Blaze.Html5 as B
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
                            help <- genPopup node doc helpPopup ("help" ++ show l)
                            keyCatcher node $ \kbf k -> do if k == 63 then do elementSetAttribute help "style" "display:block" 
                                                                              elementFocus help
                                                                      else return ()
                                                           return (k == 63) --the handler returning true means that the keypress is intercepted
                            return ()
            Nothing -> return ()

nodelistToNumberedList nl = do len <- nodeListGetLength nl
                               mapM (\n -> do i <- nodeListItem nl n; return (i,n)) [0 .. len]

helpPopup = B.div (toHtml infMessage) <>
            inferenceTable prettyClassicalQLruleSet classicalRules comments <>
            B.div (toHtml termMessage) <>
            terminationTable prettyClassicalQLruleSet classicalRules comments

infMessage :: String
infMessage = "The following are inference rules. They can be used to directly justify the assertion on a given line, by referring to previous open lines."
     <> " An inference rule can justify a statement matching the form that appears on the right side of the sequent that concludes the rule."
     <> " (I.e. on the right side of the \"⊢\" following the \"∴\".)"
     <> " It needs to refer back to previous lines which match all of the forms that appear on the right side of the sequents in the premises of the rule."
     <> " The symbols on the left sides of the sequents tell you how the dependencies of the justified line relate to the dependencies of the lines that justify it."

termMessage :: String
termMessage = "The following are termination rules. They can be used to close a subproof, by referring to previous open lines (including lines that belong to the subproof)."
      <> " A termination rule can close a subproof that begins with a show line followed by something matching the form that appears on the right side of the sequent that concludes the rule."
      <> " It needs to refer back to previous lines which match all of the forms that appear on the right side of the sequents in the premises of the rule."
      <> " The symbols on the left sides of the sequents tell you how the dependencies of the statement established by the subproof relate to the dependencies of the lines that close the subproof."

comments = M.fromList [
                      ("R","Reflexivity"),
                      ("BC", "Biconditional to conditional"),
                      ("IE", "Interchange of Equivalents"),
                      ("S", "Simplification"),
                      ("CB", "Conditional to Biconditional"),
                      ("MTP", "Modus Tollendo Ponens"),
                      ("DN", "Double Negation"),
                      ("MT", "Modus Tollens"),
                      ("LL", "Leibniz's Law"),
                      ("EG", "Existential Generalization"),
                      ("ADD", "Addition"),
                      ("MP", "Modus Ponens"),
                      ("ADJ", "Adjunction"),
                      ("UI", "Universal Instantiation"),
                      ("UD", "Universal Derivation"),
                      ("ED", "Existential Derivation"),
                      ("ID", "Indirect Derivation"),
                      ("CD", "Conditional Derivation"),
                      ("DD", "Direct Derivation")
                      ]

