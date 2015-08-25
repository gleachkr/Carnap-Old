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

module Carnap.Frontend.Ghcjs.Components.GenHelp (ruleTable) where

import Carnap.Core.Data.AbstractDerivationDataTypes (RulesAndArity)
import Carnap.Core.Data.Rules (Sequent(Sequent), AbsRulePlus(rule), AbsRule(AbsRule),AmbiguousRulePlus(ruleVersionsPlus,ruleNamePlus))
import Data.Set (toList)
import Text.Blaze.Html5 as B
--import Text.Blaze.Html5.Attributes
import Text.Blaze.Internal (stringValue, MarkupM)
import Data.Monoid (mconcat, (<>))

ruleTable rs = table $ mconcat $ Prelude.map ruleRow $ toList rs

ruleRow ambrp = tr $ td (toHtml $ ruleNamePlus ambrp) <> mconcat (ruleCols ambrp) 

ruleCols ambrp = Prelude.map (td . toMarkup . rule) (ruleVersionsPlus ambrp)
