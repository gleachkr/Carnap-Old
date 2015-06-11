{-# LANGUAGE OverloadedStrings #-}
module Main (
    main
) where

import Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Text.Blaze.Html.Renderer.Text
import Data.Tree
import Data.Monoid (mconcat, (<>))
import Data.List (intercalate, intersperse, nub)
import Carnap.Core.Data.Rules
import Carnap.Core.Unification.MultiUnification
import Carnap.Systems.NaturalDeduction.ProofTreeDataTypes
import Carnap.Systems.NaturalDeduction.ProofTreeHandler
import Carnap.Systems.NaturalDeduction.JudgementHandler
import Carnap.Calculi.ClassicalSententialLogic1 (classicalRules, classicalSLruleSet)
import Carnap.Frontend.Components.ProofTreeParser
import Carnap.Languages.Sentential.PropositionalLanguage
import Carnap.Languages.Sentential.PropositionalDerivations
import Control.Applicative ((<$>))
import Control.Monad.Trans (liftIO)
import GHCJS.DOM (enableInspector, webViewGetDomDocument, runWebGUI)
import GHCJS.DOM.Document (documentGetBody, documentGetElementById, documentCreateElement)
import GHCJS.DOM.HTMLElement (htmlElementSetInnerHTML, htmlElementSetInnerText)
import GHCJS.DOM.Element (elementOnkeypress, elementSetAttribute, IsElement)
import GHCJS.DOM.HTMLParagraphElement (castToHTMLParagraphElement)
import GHCJS.DOM.HTMLTextAreaElement (castToHTMLTextAreaElement, htmlTextAreaElementGetValue)
import GHCJS.DOM.Node (nodeAppendChild)
import GHCJS.DOM.Attr (attrSetValue)

main = runWebGUI $ \ webView -> do
    enableInspector webView
    Just doc <- webViewGetDomDocument webView
    Just body <- documentGetBody doc
    Just field <- fmap castToHTMLTextAreaElement <$> documentGetElementById doc ("proofbox" ::String)
    mnewParagraph1@(Just newParagraph1) <- fmap castToHTMLParagraphElement <$> documentCreateElement doc ("p"::String)
    mnewParagraph2@(Just newParagraph2) <- fmap castToHTMLParagraphElement <$> documentCreateElement doc ("p"::String)
    mnewParagraph3@(Just newParagraph3) <- fmap castToHTMLParagraphElement <$> documentCreateElement doc ("p"::String)
    nodeAppendChild body mnewParagraph1
    nodeAppendChild body mnewParagraph2
    nodeAppendChild body mnewParagraph3
    elementOnkeypress field $ 
        liftIO $ do
            contents <- htmlTextAreaElementGetValue field :: IO String
            let possibleParsing = parseTheBlock ( contents ++ "\n" )
            let theForest = fst $ pairHandler possibleParsing
            htmlElementSetInnerHTML newParagraph3 $ renderHtml (forestToDom theForest ! class_ "root")
            case handleForest theForest classicalRules classicalSLruleSet of 
                (Left derRept) -> do htmlElementSetInnerHTML newParagraph1 
                                        (renderHtml $ toDomList (classicalRules,classicalSLruleSet) (reverse derRept))
                                     htmlElementSetInnerHTML newParagraph2 ("" :: String)
                (Right (Left _)) -> do htmlElementSetInnerText newParagraph1 ("invalid" :: String)
                                       htmlElementSetInnerHTML newParagraph2 ("" :: String)
                (Right (Right arg)) -> do htmlElementSetInnerText newParagraph2 (display arg)
                                          htmlElementSetInnerHTML newParagraph1 ("" :: String)
            return ()
    return ()

--------------------------------------------------------
--Main Helpers, for construction HTML
--------------------------------------------------------
forestToDom :: ProofForest -> Html 
forestToDom t = B.span $ mapM_ treeToDom t

treeToDom :: ProofTree -> Html
treeToDom (Node (Right (f,"SHOW",_)) []) = B.div . B.span . toHtml $ "Show: " ++ show f
treeToDom (Node (Right (f,"SHOW",_)) d) = B.div $ do B.span . toHtml $ "Show: " ++ show f
                                                     B.div ! class_ "open" $ forestToDom d
treeToDom (Node (Right (f,r,s)) []) = B.div $ do B.span . toHtml . show $ f 
                                                 B.span $ do B.span $ toHtml r 
                                                             B.span . toHtml . show $ s 
treeToDom (Node (Right (f,r,s)) d) = B.div $ do B.span $ toHtml $ "Show: " ++ show f
                                                B.div ! class_ "closed" $ do forestToDom d
                                                                             B.div $ do B.span ! class_ "termination" $ ""
                                                                                        B.span $ do B.span $ toHtml r
                                                                                                    B.span . toHtml . show $ s
treeToDom (Node (Left s) _) = B.div $ toHtml s

toDomList thisLogic = B.div . mapM_ handle
        where view j = case derivationProves (snd thisLogic) j of 
                                Right arg -> B.div $ do B.div "✓"
                                                        B.div (toHtml $ display arg) ! class_ "errormsg"
                                Left e -> B.div $ do B.div "✖"
                                                     let l = intersperse hr $ Prelude.map (\x -> B.div $ toHtml . show $ x) e
                                                     B.div (mconcat l) ! class_ "errormsg"
              handle dl = case dl of
                             ClosureLine -> B.div ""
                             OpenLine j -> view j
                             ClosedLine j -> view j
                             ErrLine e -> B.div $ do B.div "✖"
                                                     B.div (toHtml e) ! class_ "errormsg"

display (Sequent ps c) = intercalate " . " (Prelude.map show (nub ps)) ++ " ∴ " ++ show c
