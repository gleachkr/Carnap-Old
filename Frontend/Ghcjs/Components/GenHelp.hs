{-# LANGUAGE FlexibleContexts #-}
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

module Carnap.Frontend.Ghcjs.Components.GenHelp (ruleTable, inferenceTable, terminationTable) where

import Carnap.Core.Data.AbstractDerivationDataTypes (RulesAndArity)
import Carnap.Core.Data.Rules (AbsRulePlus(rule), AbsRule(),AmbiguousRulePlus(ruleVersionsPlus,ruleNamePlus))
import Data.Set as S (Set(Set), toList, filter) 
import Text.Blaze.Html5 as B
--import Text.Blaze.Html5.Attributes
import Text.Blaze.Internal ()
import Data.Monoid (mconcat, (<>))
import Data.Map.Strict as M (lookup)
import Data.Map (Map)

ruleTable comments rs = table $ mconcat $ Prelude.map (ruleRow comments) $ toList rs

ruleRow comments ambrp = case M.lookup name comments of
                             Just comment -> tr $ td (toHtml name <> preEscapedString (": " ++ comment)) <> ruleCols ambrp
                             Nothing -> tr $ td (toHtml name) <> ruleCols ambrp 
                        where name = ruleNamePlus ambrp

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
