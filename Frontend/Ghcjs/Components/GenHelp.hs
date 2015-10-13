{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, UndecidableInstances, OverlappingInstances #-}
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

module Carnap.Frontend.Ghcjs.Components.GenHelp (helpPopupQL,helpPopupSL,helpPopupLogicBookSD) where

import Carnap.Core.Data.AbstractDerivationDataTypes (RulesAndArity)
import Carnap.Core.Data.Rules (AbsRulePlus(rule), AbsRule(),AmbiguousRulePlus(ruleVersionsPlus,ruleNamePlus))
import Carnap.Calculi.ClassicalFirstOrderLogic1 (classicalRules, classicalQLruleSet, prettyClassicalQLruleSet)
import Carnap.Calculi.ClassicalSententialLogic1 (classicalSLRules, prettyClassicalSLruleSet, classicalSLruleSet, logicBookSDrules,logicBookSDruleSet)
import Carnap.Frontend.Ghcjs.Components.MarkupClasses ()
import Data.Set as S (Set(Set), toList, filter) 
import Text.Blaze.Html5 as B
--import Text.Blaze.Html5.Attributes
import Text.Blaze.Internal ()
import Data.Monoid (mconcat, (<>))
import Data.Map.Strict as M (lookup)
import Data.Map (Map,fromList)

ruleTable :: ToMarkup (AbsRule a) => Map String String -> Set (AmbiguousRulePlus a v) -> Html
ruleTable comments rs = table $ mconcat $ Prelude.map (ruleRow comments) $ toList rs

ruleRow :: ToMarkup (AbsRule a) => Map String String -> AmbiguousRulePlus a v -> Html
ruleRow comments ambrp = case M.lookup name comments of
                             Just comment -> tr $ td (toHtml name <> preEscapedString (": " ++ comment)) <> ruleCols ambrp
                             Nothing -> tr $ td (toHtml name) <> ruleCols ambrp 
                        where name = ruleNamePlus ambrp

ruleCols :: ToMarkup (AbsRule a) => AmbiguousRulePlus a v -> Html
ruleCols ambrp = do mconcat $ Prelude.map (td . toMarkup . rule) $ Prelude.head chunks
                    mapM_ (\x -> tr $ td (toHtml "ctd.") <> 
                           mconcat (Prelude.map (td . toMarkup . rule) x)) 
                           (tail chunks)
            where chunks = chunksOf 3 (ruleVersionsPlus ambrp)

chunksOf :: Int -> [e] -> [[e]]
chunksOf i ls = Prelude.map (take i) (build (splitter ls)) where
  splitter :: [e] -> ([e] -> a -> a) -> a -> a
  splitter [] _ n = n
  splitter l c n  = l `c` splitter (drop i l) c n
  build g = g (:) []

terminationRules :: Set (AmbiguousRulePlus a b) -> RulesAndArity -> Set (AmbiguousRulePlus a b)
terminationRules rs raa = S.filter (\x -> case raa (ruleNamePlus x) of 
                                        Just (Right _) -> True 
                                        _ -> False) rs

inferenceRules :: Set (AmbiguousRulePlus a b) -> RulesAndArity -> Set (AmbiguousRulePlus a b)
inferenceRules rs raa = S.filter (\x -> case raa (ruleNamePlus x) of 
                                        Just (Left _) -> True 
                                        _ -> False) rs

inferenceTable :: ToMarkup (AbsRule a) => Set (AmbiguousRulePlus a b) -> RulesAndArity -> Map String String -> Html
inferenceTable rs raa comments = ruleTable comments $ inferenceRules rs raa

terminationTable :: ToMarkup (AbsRule a) => Set (AmbiguousRulePlus a b) -> RulesAndArity -> Map String String -> Html
terminationTable rs raa comments = ruleTable comments $ terminationRules rs raa

helpPopupQL :: Html
helpPopupQL = B.div (toHtml infMessage) <>
            inferenceTable prettyClassicalQLruleSet classicalRules comments <>
            B.div (toHtml termMessage) <>
            terminationTable prettyClassicalQLruleSet classicalRules comments

helpPopupSL :: Html
helpPopupSL = B.div (toHtml infMessage) <>
            inferenceTable prettyClassicalSLruleSet classicalSLRules comments <>
            B.div (toHtml termMessage) <>
            terminationTable prettyClassicalSLruleSet classicalSLRules comments

helpPopupLogicBookSD :: Html
helpPopupLogicBookSD = B.div (toHtml infMessage) <>
            inferenceTable logicBookSDruleSet logicBookSDrules comments <>
            B.div (toHtml spMessage) <>
            terminationTable logicBookSDruleSet logicBookSDrules comments

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

spMessage :: String
spMessage = "The following are subproof rules. They can be used to justify the assertion on a given line by referring back to previous subproofs."
      <> " An suproof rule can justify a statement matching the form that appears on the right side of the sequent that concludes the rule."
      <> " It needs to refer back to one or more subproofs whose final lines match the forms that appear on the right side of the sequents in the premises of the rule."
      <> " The symbols on the left sides of the sequents tell you how the dependencies of the statement established by the subproof rule relate to the dependencies of the lines used to justify it."

comments =   fromList [ ("RF","Reflexivity")
                      , ("R" ,"Reiteration")
                      , ("BC", "Biconditional to Conditional")
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
                      , ("AI", "Conjunction Introduction")
                      , ("AE", "Conjunction Eliminiation")
                      , ("CI", "Conditional Introduction")
                      , ("CE", "Conditional Eliminiation")
                      , ("DI", "Disjunction Introduction")
                      , ("DE", "Disjunction Elimination")
                      , ("BI", "Biconditional Introduction")
                      , ("BE", "Biconditional Elimination")
                      , ("NI", "Negation Introduction")
                      , ("NE", "Negation Elimination")
                      ]
