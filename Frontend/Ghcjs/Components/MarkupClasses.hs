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
module Carnap.Frontend.Ghcjs.Components.MarkupClasses

where

import Carnap.Core.Data.Rules (Sequent(Sequent), AbsRule(AbsRule))
import Carnap.Core.Unification.HigherOrderMatching (MatchError(..))
import Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes (class_)
import Data.Monoid (mconcat, (<>))
import Data.List (intersperse)

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
