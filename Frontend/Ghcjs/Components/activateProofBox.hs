{-# LANGUAGE GADTs, FlexibleInstances, UndecidableInstances, OverlappingInstances #-}
module Carnap.Frontend.Ghcjs.Components.ActivateProofBox (activateProofBox) where

import Carnap.Frontend.Components.ProofTreeParser (parseTheBlock, pairHandler)
import Carnap.Core.Unification.MultiUnification
import Carnap.Core.Data.Rules (Sequent(Sequent), AbsRule(AbsRule))
import Carnap.Systems.NaturalDeduction.ProofTreeHandler
import Carnap.Systems.NaturalDeduction.JudgementHandler (derivationProves)
import Carnap.Systems.NaturalDeduction.ProofTreeDataTypes
import Data.Tree (Tree(Node))
import Data.List (intercalate, intersperse, nub)
import Data.Monoid (mconcat, (<>))
import Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Text.Blaze.Html.Renderer.Text (renderHtml)
import GHCJS.DOM.HTMLElement (castToHTMLElement, htmlElementSetInnerHTML, htmlElementSetInnerText)
import GHCJS.DOM.HTMLTextAreaElement (castToHTMLTextAreaElement, htmlTextAreaElementGetValue)
import GHCJS.DOM.HTMLDivElement (castToHTMLDivElement, HTMLDivElement)
import GHCJS.DOM.Node (nodeInsertBefore, nodeAppendChild, nodeGetParentElement)
import GHCJS.DOM.Document (documentCreateElement)
import GHCJS.DOM.Element (elementSetAttribute, elementOnkeyup)
import Control.Monad.Trans (liftIO)
import Control.Applicative ((<$>))

activateProofBox pb doc rules ruleset = do let field = castToHTMLTextAreaElement pb
                                           Just parent <- nodeGetParentElement pb
                                           mnewDiv1@(Just newDiv) <- fmap castToHTMLDivElement <$> documentCreateElement doc "div"
                                           manalysis@(Just analysis) <- fmap castToHTMLDivElement <$> documentCreateElement doc "div"
                                           mnewSpan2@(Just newSpan2) <- fmap castToHTMLElement <$> documentCreateElement doc "span"
                                           mnewSpan3@(Just newSpan3) <- fmap castToHTMLElement <$> documentCreateElement doc "span"
                                           elementSetAttribute analysis "class" "analysis"
                                           elementSetAttribute newSpan2 "class" "rslt"
                                           nodeAppendChild parent mnewDiv1
                                           nodeAppendChild newDiv (Just pb)
                                           nodeAppendChild newDiv manalysis
                                           nodeAppendChild newDiv mnewSpan2
                                           nodeAppendChild newDiv mnewSpan3
                                           elementOnkeyup field $ 
                                               liftIO $ do
                                                   contents <- htmlTextAreaElementGetValue field :: IO String
                                                   let possibleParsing = parseTheBlock ( contents ++ "\n" )
                                                   let theForest = fst $ pairHandler possibleParsing
                                                   htmlElementSetInnerHTML newSpan3 $ renderHtml (forestToDom theForest ! class_ (stringValue "root"))
                                                   case handleForest theForest rules ruleset of 
                                                       (Left derRept) -> do htmlElementSetInnerHTML analysis 
                                                                               (renderHtml $ toDomList (rules,ruleset) (reverse derRept))
                                                                            htmlElementSetInnerHTML newSpan2 ("" :: String)
                                                       (Right (Left _)) -> do htmlElementSetInnerText analysis ("invalid" :: String)
                                                                              htmlElementSetInnerHTML newSpan2 ("" :: String)
                                                       (Right (Right arg)) -> do htmlElementSetInnerText newSpan2 (display arg)
                                                                                 htmlElementSetInnerHTML analysis ("" :: String)
                                                   return ()
                                           return newDiv

display (Sequent ps c) = intercalate " . " (Prelude.map show (nub ps)) ++ " ∴ " ++ show c

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

instance (Show a) => ToMarkup a where
        toMarkup x = toMarkup (show x)

instance (ToMarkup term) => ToMarkup (AbsRule term) where
        toMarkup (AbsRule ps c) = mconcat (intersperse br $ Prelude.map toMarkup ps) <> br <> toMarkup " ∴ " <> toMarkup c

instance (ToMarkup term) => ToMarkup (Sequent term) where
        toMarkup (Sequent ps c) = mconcat (intersperse (toMarkup ", ") $ Prelude.map toMarkup ps) <> toMarkup " ⊢ " <> toMarkup c

instance (ToMarkup var, ToMarkup t) => ToMarkup (UnificationError var t) where
        toMarkup (UnableToUnify a b) = toMarkup "I need to match " <> toMarkup a 
                                                               <> toMarkup " with " <> toMarkup b <> toMarkup "." <> br 
                                                               <> toMarkup "But that's impossible."
        toMarkup (ErrWrapper e)      = toMarkup e
        toMarkup (SubError err a b)  = toMarkup "I need to match " <> B.div (toMarkup a) ! class_ (stringValue "uniblock" )
                                                               <> toMarkup " with " <> B.div (toMarkup b) ! class_ (stringValue "uniblock")
                                                               <> toMarkup "so " <> toMarkup err
        toMarkup (OccursCheck v t)   = toMarkup "Cannot construct infinite type " <> toMarkup v <> toMarkup " = " <> toMarkup t
