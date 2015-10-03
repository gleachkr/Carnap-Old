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
import Data.Maybe (catMaybes)
import Data.Monoid ((<>))
import Carnap.Calculi.ClassicalFirstOrderLogic1 (classicalRules, classicalQLruleSet, prettyClassicalQLruleSet)
import Carnap.Calculi.ClassicalSententialLogic1 (classicalSLRules, classicalSLruleSet, logicBookSDrules,logicBookSDruleSet)
import Carnap.Frontend.Components.ProofTreeParser (parseTheBlockKM,parseTheBlockFitch)
import Carnap.Frontend.Ghcjs.Components.ActivateProofBox (activateProofBox)
import Carnap.Frontend.Ghcjs.Components.UpdateBox (BoxSettings(BoxSettings,fhandler,fparser,pparser,manalysis,mproofpane,mresult,rules,ruleset,clearAnalysisOnComplete))
import Carnap.Frontend.Ghcjs.Components.KeyCatcher
import Carnap.Frontend.Ghcjs.Components.GenHelp (inferenceTable, terminationTable)
import Carnap.Frontend.Ghcjs.Components.GenPopup (genPopup)
import Carnap.Frontend.Ghcjs.Components.Slider (slider)
import Carnap.Languages.FirstOrder.QuantifiedParser (formulaParser, strictFormulaParser)
import Carnap.Languages.Sentential.PropositionalParser (formulaParserSL)
import Carnap.Languages.Util.ParserTypes
import Carnap.Systems.NaturalDeduction.KalishAndMontegueProofTreeHandler
import Carnap.Systems.NaturalDeduction.FitchProofTreeHandler
import Control.Applicative ((<$>))
import Control.Monad.Trans (liftIO)
import Control.Monad (when)
import Text.Blaze.Html5 as B
import GHCJS.DOM.Node (nodeAppendChild,nodeGetChildNodes)
import GHCJS.DOM.Element (castToElement, elementSetAttribute, elementOnclick, elementFocus, elementGetClassName)
import GHCJS.DOM.Types (HTMLDivElement, HTMLElement)
import GHCJS.DOM (WebView, enableInspector, webViewGetDomDocument, runWebGUI)
import GHCJS.DOM.Document (documentGetBody, documentGetElementsByClassName, documentCreateElement)
import GHCJS.DOM.HTMLElement (htmlElementGetChildren,castToHTMLElement, htmlElementSetInnerText)
import GHCJS.DOM.HTMLCollection (htmlCollectionGetLength, htmlCollectionItem)
import GHCJS.DOM.NodeList
import GHCJS.DOM.Attr (attrSetValue)
import Language.Javascript.JSaddle (eval,runJSaddle)

--------------------------------------------------------
--1. Main functions
--------------------------------------------------------

main = runWebGUI $ \webView -> do  
    enableInspector webView
    Just doc <- webViewGetDomDocument webView
    Just body <- documentGetBody doc
    Just folpbs <- documentGetElementsByClassName doc "FOLproofbox"
    Just slpbs <- documentGetElementsByClassName doc "SLproofbox"
    mfolnodes <- nodelistToNumberedList folpbs
    mslnodes <- nodelistToNumberedList slpbs
    mapM_ (byCase doc initSettingsFOL modTableFOL) mfolnodes
    mapM_ (byCase doc initSettingsSL modTableSL) mslnodes
    Just slidernodelist <- documentGetElementsByClassName doc "slider"
    msliders <- nodelistToNumberedList slidernodelist
    mapM_ (toSlider doc) msliders
    runJSaddle webView $ eval "setTimeout(function(){$(\".lined\").linedtextarea({selectedLine:1});}, 30);"
    return ()

--turns a numbered node into a proofbox
--XXX:Might want to automate adding an id
byCase doc init mt (n,l) = case n of 
        Just node -> do settings <- readSettings init mt node
                        activateProofBox node doc settings
                        help <- genPopup node doc helpPopup ("help" ++ show l)
                        keyCatcher node $ \kbf k -> do when (k == 63 ) $ do elementSetAttribute help "style" "display:block" 
                                                                            elementFocus help
                                                       return (k == 63) --the handler returning true means that the keypress is intercepted
                        return ()
        Nothing -> return ()

--turns a numbered node into a slider.
toSlider doc (n,l) = case n of
            Just node -> do let nodeAsElt = castToHTMLElement node
                            mcc@(Just childcollection) <- htmlElementGetChildren nodeAsElt 
                            childms <- htmlColltoList childcollection
                            let children = catMaybes childms
                            sdiv <- slider doc (Prelude.map castToElement children)
                            nodeAppendChild node (Just sdiv)
                            return ()
            Nothing -> return ()

--reads settings off of a node when activating it, to determine any special
--behavior.
readSettings init mt node = do classname <- elementGetClassName $ castToElement node :: IO String
                               print classname
                               let classes = words classname
                               let modifications = catMaybes $ Prelude.map (`M.lookup` mt) classes
                               return $ Prelude.foldr ($) init modifications

--------------------------------------------------------
--2. Help Popup
--------------------------------------------------------

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

comments = M.fromList [ ("RF","Reflexivity")
                      , ("RP","Repetition")
                      , ("BC", "Biconditional to conditional")
                      , ("IE", "Interchange of Equivalents")
                      , ("S", "Simplification")
                      , ("CB", "Conditional to Biconditional")
                      , ("MTP", "Modus Tollendo Ponens")
                      , ("DN", "Double Negation")
                      , ("MT", "Modus Tollens")
                      , ("LL", "Leibniz's Law")
                      , ("EG", "Existential Generalization")
                      , ("ADD", "Addition")
                      , ("MP", "Modus Ponens")
                      , ("ADJ", "Adjunction")
                      , ("UI", "Universal Instantiation")
                      , ("UD", "Universal Derivation")
                      , ("ED", "Existential Derivation")
                      , ("ID", "Indirect Derivation")
                      , ("CD", "Conditional Derivation")
                      , ("DD", "Direct Derivation")
                      ]

--------------------------------------------------------
--3. Settings, and Settings Modifiers
--------------------------------------------------------

initSettingsFOL = BoxSettings { fparser = formulaParser,
                             pparser = parseTheBlockKM,
                             fhandler = handleForestKM,
                             manalysis = Nothing, 
                             mproofpane = Nothing,
                             mresult = Nothing,
                             rules = classicalRules,
                             ruleset = classicalQLruleSet,
                             clearAnalysisOnComplete = True}

initSettingsSL = BoxSettings { fparser = formulaParserSL
                             , pparser = parseTheBlockKM
                             , fhandler = handleForestKM
                             , manalysis = Nothing
                             , mproofpane = Nothing
                             , mresult = Nothing
                             , rules = classicalSLRules
                             , ruleset = classicalSLruleSet
                             , clearAnalysisOnComplete = True
                             }

visOn settings = settings {clearAnalysisOnComplete = False}

strictOn settings = settings {fparser = strictFormulaParser}

fitchOn settings = settings { fhandler = handleForestFitch
                            , pparser = parseTheBlockFitch
                            }

logicBookSDOn settings = settings { rules = logicBookSDrules
                                  , ruleset = logicBookSDruleSet
                                  }


--list of keywords that activate settings modifiers
modTableFOL = fromList [ ("visible",visOn)
                       , ("strict", strictOn)
                       , ("fitch", fitchOn)
                       ]

modTableSL = fromList [ ("visible", visOn)
                      , ("fitch", fitchOn)
                      , ("logicBookSD",logicBookSDOn)
                      ]


--------------------------------------------------------
--4. Utility Functions
--------------------------------------------------------

nodelistToNumberedList nl = do len <- nodeListGetLength nl
                               mapM (\n -> do i <- nodeListItem nl n; return (i,n)) [0 .. len]

htmlColltoList hc = do len <- htmlCollectionGetLength hc
                       mapM (htmlCollectionItem hc) [0 .. len]
