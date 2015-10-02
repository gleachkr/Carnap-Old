{-# LANGUAGE GADTs, FlexibleInstances, UndecidableInstances, OverlappingInstances #-}
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
-}
module Carnap.Frontend.Ghcjs.Components.UpdateBox (updateBox, 
        BoxSettings(BoxSettings,fhandler,fparser,pparser,rules,ruleset,manalysis,mproofpane,mresult,clearAnalysisOnComplete)) 
where

import Carnap.Frontend.Components.ProofTreeParser (pairHandler)
import Carnap.Languages.Util.ParserTypes
import Text.ParserCombinators.Parsec.Error (ParseError)
import Carnap.Core.Unification.HigherOrderMatching
import Carnap.Core.Data.AbstractSyntaxDataTypes (DisplayVar,NextVar,Schematizable, Form)
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (S_NextVar, S_DisplayVar, SchemeVar,SSequentItem, Var)
import Carnap.Core.Data.AbstractDerivationDataTypes (RulesAndArity)
import Carnap.Core.Data.AbstractDerivationSecondOrderMatching
import Carnap.Core.Data.Rules (Sequent(Sequent), AbsRule(AbsRule),AmbiguousRulePlus)
import Carnap.Systems.NaturalDeduction.JudgementHandler (derivationProves)
import Carnap.Systems.NaturalDeduction.ProofTreeDataTypes
import Carnap.Systems.NaturalDeduction.Util.ReportTypes
import Data.Tree (Tree(Node))
import Data.Set
import Data.List (intercalate, intersperse, nub)
import Data.Monoid (mconcat, (<>))
import Data.Maybe (fromMaybe)
import Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Text.Blaze.Internal (stringValue, MarkupM)
import Text.Blaze.Html.Renderer.Text (renderHtml)
import GHCJS.DOM.HTMLElement (htmlElementSetInnerHTML)
import GHCJS.DOM.HTMLTextAreaElement (htmlTextAreaElementGetValue)
import GHCJS.DOM.Element (elementSetAttribute)
import GHCJS.DOM.Types (IsNode,IsDocument,IsHTMLTextAreaElement, IsHTMLElement, HTMLElement)
import Control.Monad (when)

data BoxSettings pred con quant f sv a st = BoxSettings {
                    fparser :: FParser (Form pred con quant f sv a) st,
                    fhandler:: ProofForest (Form pred con quant f sv a) -> RulesAndArity -> Set (AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())) -> 
                        Either (DerivationReport (Form pred con quant f sv a))
                            (Either [MatchError (Var pred con quant f sv () (AbsRule (Sequent (SSequentItem pred con quant f sv)))) (AbsRule (Sequent (SSequentItem pred con quant f sv)))] 
                                    (Sequent (SSequentItem pred con quant f sv)), DerivationReport (Form pred con quant f sv a)),
                    pparser :: FParser (Form pred con quant f sv a) st -> String -> ProofForest (Form pred con quant f sv a),
                    rules :: RulesAndArity,
                    ruleset :: Set (AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ())),
                    manalysis :: Maybe HTMLElement,
                    mresult :: Maybe HTMLElement,
                    mproofpane :: Maybe HTMLElement,
                    clearAnalysisOnComplete :: Bool --should we clear the analysis div when the proof is complete?
                    }

updateBox :: (GHCJS.DOM.Types.IsHTMLTextAreaElement self, S_DisplayVar sv quant, S_NextVar sv quant, SchemeVar sv, 
             UniformlyEquaitable sv, UniformlyEquaitable f, UniformlyEquaitable quant, UniformlyEquaitable con, UniformlyEquaitable pred, 
                DisplayVar sv quant, NextVar sv quant, Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred) =>
                    self -> BoxSettings pred con quant f sv a st -> IO (Maybe (Sequent (SSequentItem pred con quant f sv)))
updateBox box settings =  do contents <- htmlTextAreaElementGetValue box :: IO String
                             let theForest = pparser settings (fparser settings) ( contents ++ "\n" )
                             if Prelude.null theForest
                                 then do when (has manalysis) $ htmlElementSetInnerHTML analysis ""
                                         when (has mresult) $ htmlElementSetInnerHTML result ""
                                         when (has mproofpane) $ htmlElementSetInnerHTML proofpane ""
                                         return Nothing
                                 else do when (has mproofpane) $ do htmlElementSetInnerHTML proofpane $ renderHtml $ forestToDom theForest
                                                                    elementSetAttribute proofpane "class" "root"
                                         case fhandler settings theForest theRules theRuleSet of 
                                             (Left derRept) -> do when (has manalysis) $ htmlElementSetInnerHTML analysis (renderHtml $ toDomList (theRules,theRuleSet) (reverse derRept))
                                                                  when (has mresult)   $ do htmlElementSetInnerHTML result ""
                                                                                            elementSetAttribute result "class" "rslt"
                                                                  return Nothing
                                             (Right (Left _,derRept)) -> do 
                                                                    when (has manalysis) $ htmlElementSetInnerHTML analysis "invalid" 
                                                                    when (has mresult) $ do elementSetAttribute result "class" "rslt"
                                                                                            htmlElementSetInnerHTML result ""
                                                                    return Nothing
                                             (Right (Right arg, derRept)) -> do 
                                                                       when (has mresult) $ do htmlElementSetInnerHTML result (display arg)
                                                                                               elementSetAttribute result "class" "rslt complete"
                                                                       when (has manalysis) $ if clearAnalysis 
                                                                                                  then htmlElementSetInnerHTML analysis ""
                                                                                                  else htmlElementSetInnerHTML analysis (renderHtml $ toDomList (theRules,theRuleSet) (reverse derRept))
                                                                       return $ Just arg
                            where has f = case f settings of 
                                            Nothing -> False
                                            Just _ -> True
                                  unmaybe f = fromMaybe undefined (f settings)
                                  proofpane = unmaybe mproofpane
                                  analysis = unmaybe manalysis
                                  result = unmaybe mresult
                                  theRules = rules settings
                                  theRuleSet = ruleset settings
                                  clearAnalysis = clearAnalysisOnComplete settings


display (Sequent ps c) = intercalate " . " (Prelude.map show (nub ps)) ++ " ∴ " ++ show c

preorderListSmear (t1@(Node v etc):ts) l = Node (v,Prelude.head l) (preorderListSmear etc $ take (length etc) (tail l)) : preorderListSmear ts (drop (length etc + 1) l)
preorderListSmear _ _ = undefined

--XXX:Eventually break this up into two functions, for different formattings of the ProofForest

forestToDom :: Show f => ProofForest f -> Html 
forestToDom = mapM_ treeToDom
    where
    treeToDom :: Show f => ProofTree f -> Html
    treeToDom (Node (Right (f,"SHOW",_)) []) = B.div . B.span . toHtml $ "Show: " ++ show f
    treeToDom (Node (Right (f,"SHOW",_)) d) = B.div $ do B.span . toHtml $ "Show: " ++ show f
                                                         B.div ! class_ (stringValue "open") $ forestToDom d
    treeToDom (Node (Right (f,"AS",_)) d) = B.div ! class_ (stringValue "fitchSP") $ do B.div $ do B.span . toHtml $ show f
                                                                                                   B.span . toHtml $ "Assumption"
                                                                                        forestToDom d
    treeToDom (Node (Right (f,':':r,s)) d) = B.div $ do B.span $ toHtml $ "Show: " ++ show f
                                                        B.div ! class_ (stringValue "closed") $ do forestToDom d
                                                                                                   B.div $ do B.span ! class_ (stringValue "termination") $ toHtml ""
                                                                                                              B.span $ do B.span $ toHtml r
                                                                                                                          when (s /= []) $ B.span . toHtml . init . tail $ show s 
    treeToDom (Node (Right (f,'-':r,s)) []) = B.div $ do B.span . toHtml . show $ f 
                                                         B.span $ do B.span $ toHtml r 
                                                                     B.span $ toHtml (fromRange s)
                                            where fromRange (a:b:l) = if a == b 
                                                                          then show a ++ " " ++ fromRange l
                                                                          else show b ++ "-" ++ show a ++ " " ++ fromRange l
                                                  fromRange _ = ""
    treeToDom (Node (Right (f,r,s)) []) = B.div $ do B.span . toHtml . show $ f 
                                                     B.span $ do B.span $ toHtml r 
                                                                 when (s /= []) $ B.span . toHtml . init . tail $ show s 
    treeToDom (Node (Left s) _) = B.div $ if ':' `elem` s --XXX:ugly hack. Detect error messages by scanning for colon 
                                            then do B.span $ toHtml "⚠" 
                                                    anchored $ errorDiv $ toHtml s
                                            else B.span $ toHtml s 

toDomList :: (S_DisplayVar sv quant, S_NextVar sv quant, SchemeVar sv, UniformlyEquaitable sv,
             UniformlyEquaitable f, UniformlyEquaitable quant,
             UniformlyEquaitable con, UniformlyEquaitable pred, 
             NextVar sv quant, Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred) => 
             (a, Set (AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ()))) -> 
                [ReportLine (Form pred con quant f sv b)] -> Text.Blaze.Internal.MarkupM ()
toDomList thisLogic = mapM_ handle
        where view j = case derivationProves (snd thisLogic) j of 
                                Right arg -> B.div $ do B.div $ toHtml "✓"
                                                        anchored $ errorDiv $ toHtml $ display arg
                                Left e -> B.div $ do B.div $ toHtml "✖"
                                                     let ers = Prelude.map (B.div . toHtml) e
                                                     let l = intersperse hr ers 
                                                     anchored $ errorDiv $ B.div (toMarkup $ "This rule didn't match. I tried " ++ show (length ers) ++ " possibilities") 
                                                            <> br <> mconcat l
              handle dl = case dl of
                             ClosureLine -> B.div $ toHtml ""
                             OpenLine j -> view j
                             ClosedLine j -> view j
                             DeepClosedLine _ j -> view j
                             ErrLine e -> B.div $ do B.div $ toHtml "✖"
                                                     anchored $ errorDiv $ toHtml e

anchored html = B.div html ! class_ (stringValue "anchor")

errorDiv html = B.div html ! class_ (stringValue "errormsg")

instance (Show a) => ToMarkup a where
        toMarkup x = toMarkup (show x)

instance (ToMarkup term) => ToMarkup (AbsRule term) where
        toMarkup (AbsRule ps c) = mconcat (intersperse br $ Prelude.map toMarkup ps) <> br <> toMarkup " ∴ " <> toMarkup c

instance (ToMarkup term) => ToMarkup (Sequent term) where
        toMarkup (Sequent ps c) = mconcat (intersperse (toMarkup ", ") $ Prelude.map toMarkup ps) <> toMarkup " ⊢ " <> toMarkup c

instance (ToMarkup var, ToMarkup t) => ToMarkup (MatchError var t) where
        toMarkup (UnableToMatch a b) = toMarkup "I need to match " <> br <> B.div (toMarkup a) ! class_ (stringValue "uniblock")
                                                               <> toMarkup " with " <> B.div (toMarkup b) ! class_ (stringValue "uniblock") <> toMarkup "." <> br 
                                                               <> toMarkup "But that's impossible."
        toMarkup (ErrWrapper e)      = toMarkup e
        toMarkup (SubError err a b)  = toMarkup "I need to match " <> br <> B.div (toMarkup a) ! class_ (stringValue "uniblock" )
                                                               <> toMarkup " with " <> B.div (toMarkup b) ! class_ (stringValue "uniblock")
                                                               <> B.div (toMarkup "so..." <> (B.div ! class_ (stringValue "suberr") $  toMarkup err))
        toMarkup (OccursCheck v t)   = toMarkup "Cannot construct infinite type " <> toMarkup v <> toMarkup " = " <> toMarkup t
        toMarkup (SpecialErr s)      = toMarkup s
