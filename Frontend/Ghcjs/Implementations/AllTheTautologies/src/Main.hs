{-# LANGUAGE GADTs, FlexibleInstances, UndecidableInstances, OverlappingInstances #-}
module Main (
    main
) where

import Control.Monad
import Control.Monad.IO.Class
import Text.Blaze
import Text.Blaze.Html
import Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Text.Blaze.Html.Renderer.Text
import Data.Tree
import Data.Monoid (mconcat, (<>))
import Data.List (intercalate, intersperse, nub)
import Data.IORef
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
import GHCJS.DOM.Node
import GHCJS.DOM.Element
import GHCJS.DOM.Types (HTMLDivElement, HTMLElement)
import GHCJS.DOM (WebView, enableInspector, webViewGetDomDocument, runWebGUI)
import GHCJS.DOM.Document (documentGetBody, documentGetElementById, documentCreateElement)
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementSetInnerHTML, htmlElementSetInnerText)
import GHCJS.DOM.HTMLTextAreaElement (castToHTMLTextAreaElement, htmlTextAreaElementGetValue)
import GHCJS.DOM.HTMLDivElement (castToHTMLDivElement, HTMLDivElement)
import GHCJS.DOM.Attr (attrSetValue)
import qualified Language.Javascript.JSaddle as JS

main = runWebGUI $ \ webView -> do
    enableInspector webView
    Just doc <- webViewGetDomDocument webView
    Just body <- documentGetBody doc
    Just pb <- documentGetElementById doc "proofbox"
    let field = castToHTMLTextAreaElement pb
    mnewDiv1@(Just newDiv) <- fmap castToHTMLDivElement <$> documentCreateElement doc "div"
    manalysis@(Just analysis) <- fmap castToHTMLDivElement <$> documentCreateElement doc "div"
    mtautologies@(Just tautologies) <- fmap castToHTMLElement <$> documentCreateElement doc "div"
    mnewSpan2@(Just newSpan2) <- fmap castToHTMLElement <$> documentCreateElement doc "span"
    mnewSpan3@(Just newSpan3) <- fmap castToHTMLElement <$> documentCreateElement doc "span"
    elementSetAttribute tautologies "id" "tautologies"
    elementSetAttribute analysis "class" "analysis"
    elementSetAttribute newSpan2 "class" "rslt"
    nodeAppendChild body mnewDiv1
    nodeAppendChild newDiv mtautologies
    nodeAppendChild newDiv (Just field)
    nodeAppendChild newDiv manalysis
    nodeAppendChild newDiv mnewSpan2
    nodeAppendChild newDiv mnewSpan3
    activateLazyList (Prelude.map (toTautElem doc) (concat $ Prelude.map tautologyWithNconnectives [1..])) tautologies
    elementOnkeyup field $ 
        liftIO $ do
            contents <- htmlTextAreaElementGetValue field :: IO String
            let possibleParsing = parseTheBlock ( contents ++ "\n" )
            let theForest = fst $ pairHandler possibleParsing
            htmlElementSetInnerHTML newSpan3 $ renderHtml (forestToDom theForest ! class_ (stringValue "root"))
            case handleForest theForest classicalRules classicalSLruleSet of 
                (Left derRept) -> do htmlElementSetInnerHTML analysis 
                                        (renderHtml $ toDomList (classicalRules,classicalSLruleSet) (reverse derRept))
                                     htmlElementSetInnerHTML newSpan2 ("" :: String)
                (Right (Left _)) -> do htmlElementSetInnerText analysis ("invalid" :: String)
                                       htmlElementSetInnerHTML newSpan2 ("" :: String)
                (Right (Right arg)) -> do htmlElementSetInnerText newSpan2 (display arg)
                                          htmlElementSetInnerHTML analysis ("" :: String)
            return ()
    JS.runJSaddle webView $ JS.eval "setTimeout(function(){$(\".lined\").linedtextarea({selectedLine:1});}, 30);"
    return ()

--------------------------------------------------------
--Main Helpers, for construction HTML
--------------------------------------------------------
forestToDom :: ProofForest -> Html 
forestToDom t = B.span $ mapM_ treeToDom t

treeToDom :: ProofTree -> Html
treeToDom (Node (Right (f,"SHOW",_)) []) = B.div . B.span . toHtml $ "Show: " ++ show f
treeToDom (Node (Right (f,"SHOW",_)) d) = B.div $ do B.span . toHtml $ "Show: " ++ show f
                                                     B.div ! class_ (stringValue "open") $ forestToDom d
treeToDom (Node (Right (f,r,s)) []) = B.div $ do B.span . toHtml . show $ f 
                                                 B.span $ do B.span $ toHtml r 
                                                             B.span . toHtml . show $ s 
treeToDom (Node (Right (f,r,s)) d) = B.div $ do B.span $ toHtml $ "Show: " ++ show f
                                                B.div ! class_ (stringValue "closed") $ do forestToDom d
                                                                                           B.div $ do B.span ! class_ (stringValue "termination") $ toHtml ""
                                                                                                      B.span $ do B.span $ toHtml r
                                                                                                                  B.span . toHtml . show $ s
treeToDom (Node (Left s) _) = B.div $ toHtml s

toDomList thisLogic = mapM_ handle
        where view j = case derivationProves (snd thisLogic) j of 
                                Right arg -> B.div $ do B.div $ toHtml "✓"
                                                        B.div (toHtml $ display arg) ! class_ (stringValue "errormsg")
                                Left e -> B.div $ do B.div $ toHtml "✖"
                                                     let l = intersperse hr $ Prelude.map (B.div . toHtml) e
                                                     B.div (mconcat l) ! class_ (stringValue "errormsg")
              handle dl = case dl of
                             ClosureLine -> B.div $ toHtml ""
                             OpenLine j -> view j
                             ClosedLine j -> view j
                             ErrLine e -> B.div $ do B.div $ toHtml "✖"
                                                     B.div (toHtml e) ! class_ (stringValue "errormsg")

display (Sequent ps c) = intercalate " . " (Prelude.map show (nub ps)) ++ " ∴ " ++ show c


lazyList :: IORef Int-> [IO HTMLElement] -> HTMLElement -> IO ()
lazyList ref l el =  do st <- elementGetScrollTop el
                        sh <- elementGetScrollHeight el
                        ch <- elementGetClientHeight el
                        if (fromIntegral sh) - (fromIntegral st) < ch + 1
                            then do updateBot ref l el
                                    elementSetScrollTop el (st - 1)
                            else if st < 1 
                            then do updateTop ref l el
                                    elementSetScrollTop el 1
                            else return ()

updateBot :: IORef Int -> [IO HTMLElement] -> HTMLElement -> IO ()
updateBot ref l el =  do n <- readIORef ref
                         if n > 100 then do mc <- elementGetFirstElementChild el
                                            nodeRemoveChild el mc
                                            return ()
                                 else return ()
                         writeIORef ref (n+1)
                         lc <- l !! n
                         nodeAppendChild el (Just lc)
                         return ()

updateTop :: IORef Int -> [IO HTMLElement] -> HTMLElement -> IO ()
updateTop ref l el = liftIO $ do n <- readIORef ref
                                 if n > 99 then 
                                    do mc <- elementGetLastElementChild el
                                       nodeRemoveChild el mc
                                       writeIORef ref (n-1)
                                       mc2 <- elementGetFirstElementChild el
                                       lc <- (l !! (n-100))
                                       nodeInsertBefore el (Just lc) mc2
                                       return ()
                                 else return ()

activateLazyList :: [IO HTMLElement] -> HTMLElement -> IO (IO ())
activateLazyList l el = do ref <- newIORef 0 
                           replicateM_ 50 $ updateBot ref l el
                           elementOnscroll el $ liftIO $ lazyList ref l el

toTautElem doc f = do mdiv@(Just div) <- fmap castToHTMLElement <$> documentCreateElement doc "div"
                      htmlElementSetInnerText div (show f)
                      elementOnclick div $ liftIO $ setMainBox doc f
                      return div

setMainBox doc f  = do mmb <- documentGetElementById doc "proofbox"
                       case mmb of 
                          Nothing -> return ()
                          Just mb -> htmlElementSetInnerText (castToHTMLElement mb) ("Show: " ++ show f)

instance (Show a) => ToMarkup a where
        toMarkup x = toMarkup (show x)

instance (ToMarkup term) => ToMarkup (AbsRule term) where
        toMarkup (AbsRule ps c) = (mconcat $ intersperse br $ Prelude.map toMarkup ps) <> br <> toMarkup " ∴ " <> toMarkup c

instance (ToMarkup term) => ToMarkup (Sequent term) where
        toMarkup (Sequent ps c) = (mconcat $ intersperse (toMarkup ", ") $ Prelude.map toMarkup ps) <> toMarkup " ⊢ " <> toMarkup c

instance (ToMarkup var, ToMarkup t) => ToMarkup (UnificationError var t) where
        toMarkup (UnableToUnify a b) = toMarkup "I need to match " <> toMarkup a 
                                                               <> toMarkup " with " <> toMarkup b <> toMarkup "." <> br 
                                                               <> toMarkup "But that's impossible."
        toMarkup (ErrWrapper e)      = toMarkup e
        toMarkup (SubError err a b)  = toMarkup "I need to match " <> B.div (toMarkup a) ! class_ (stringValue "uniblock" )
                                                               <> toMarkup " with " <> B.div (toMarkup b) ! class_ (stringValue "uniblock")
                                                               <> toMarkup "so " <> toMarkup err
        toMarkup (OccursCheck v t)   = toMarkup "Cannot construct infinite type " <> toMarkup v <> toMarkup " = " <> toMarkup t
