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
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (SSequentItem(SeqList))
import Carnap.Core.Data.AbstractSyntaxDataTypes (liftToScheme)
import Carnap.Frontend.Components.ProofTreeParser (parseTheBlock')
import Carnap.Frontend.Ghcjs.Components.UpdateBox 
    (BoxSettings(BoxSettings,fparser,pparser, manalysis,mproofpane,mresult,rules,ruleset,clearAnalysisOnComplete))
import Carnap.Frontend.Ghcjs.Components.GenShowBox (genShowBox)
import Carnap.Frontend.Ghcjs.Components.KeyCatcher
import Carnap.Frontend.Ghcjs.Components.GenHelp (inferenceTable, terminationTable)
import Carnap.Frontend.Ghcjs.Components.GenPopup (genPopup)
import Carnap.Core.Data.Rules (Sequent(Sequent))
import Carnap.Languages.Util.ParserTypes
import Text.Parsec (runParser)
import Text.Parsec.Char (char) 
import Text.Parsec.Combinator (many1,sepBy,sepEndBy1)
import Carnap.Languages.FirstOrder.QuantifiedParser (formulaParser)
import Control.Applicative ((<$>))
import Control.Monad.Trans (liftIO)
import Text.Blaze.Html5 as B
import GHCJS.DOM.Element (elementSetAttribute, elementFocus)
import GHCJS.DOM.Node (nodeGetFirstChild,nodeAppendChild,nodeInsertBefore)
import GHCJS.DOM (WebView, enableInspector, webViewGetDomDocument, runWebGUI)
import GHCJS.DOM.Document (documentGetBody, documentGetElementById, documentCreateElement, documentGetDefaultView, documentGetDocumentURI)
import GHCJS.DOM.DOMWindow (domWindowAlert)
import Network.URI (unEscapeString)
import Language.Javascript.JSaddle (eval,runJSaddle)

main = runWebGUI $ \webView -> do  
    enableInspector webView
    Just doc <- webViewGetDomDocument webView
    Just body <- documentGetBody doc
    Just proofDiv <- documentGetElementById doc "proofDiv"
    dv@(Just win) <- documentGetDefaultView doc 
    url <- documentGetDocumentURI doc :: IO String
    help <- genPopup proofDiv doc helpPopup "help"
    let qs = dropWhile (/= '?') url
    let qs' = unEscapeString qs
    print qs'
    case qs' of
        "" -> domWindowAlert win "Sorry, there doesn't appear to be a problem set in the supplied url"
        "?" -> domWindowAlert win "Sorry, there doesn't appear to be a problem set in the supplied url"
        _ -> case runParser goalList (initState formulaParser) "" (tail qs') of
                 Left _ -> domWindowAlert win "Sorry, the url supplied is not well-formed"
                 Right ls@((p,c):xs) -> mapM_ (goalDiv doc proofDiv) ls 
                 k -> domWindowAlert win $ "Unexpected error on query" ++ qs ++ " parsed as " ++ show k
    runJSaddle webView $ eval "setTimeout(function(){$(\"#proofDiv > div > .lined\").linedtextarea({selectedLine:1});}, 30);"
    keyCatcher proofDiv $ \kbf k -> do if k == 63 then do elementSetAttribute help "style" "display:block" 
                                                          elementFocus help
                                                    else return ()
                                       return (k == 63) --the handler returning true means that the keypress is intercepted
    return ()

goalDiv doc pd (a,b) = do let a' = Prelude.map liftToScheme a
                          let b' = liftToScheme b
                          mcontainer@(Just cont) <- documentCreateElement doc "div"
                          mfc@(Just fc) <- nodeGetFirstChild pd
                          case mfc of Nothing -> nodeAppendChild pd mcontainer
                                      Just fc -> nodeInsertBefore pd mcontainer mfc
                          genShowBox cont doc initSettings (Sequent [SeqList a'] (SeqList [b']))

initSettings = BoxSettings {fparser = formulaParser,
                            pparser = parseTheBlock',
                            ruleset = classicalQLruleSet,
                            rules = classicalRules,
                            clearAnalysisOnComplete = False,
                            manalysis = Nothing,
                            mproofpane = Nothing,
                            mresult = Nothing}

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

goalList = goalParser `sepEndBy1` char '.'

goalParser = do prems <- parser formulaParser `sepBy` char ','
                _ <- char ';'
                conc <- parser formulaParser
                return (prems,conc)
