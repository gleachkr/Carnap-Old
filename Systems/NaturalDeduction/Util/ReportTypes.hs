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
module Carnap.Systems.NaturalDeduction.Util.ReportTypes where

import Carnap.Core.Data.AbstractDerivationDataTypes

--Closed lines are lines for which a judgement can be constructed, but
--which are now in a closed suproof. OpenLines are lines for which
--a judgement can be constructed. ErrorLines are lines for which
--a judgement cannot be constructed. A ClosureLine is a dummy line for
--a proof-closing inference rule, as we find in a Kalish and Montegue
--system.

data ReportLine form = ClosedLine (Judgement form (SimpleJustification form))
                     | OpenLine (Judgement form (SimpleJustification form))
                     | ErrLine String
                     | ClosureLine
                     | DeepClosedLine Int (Judgement form (SimpleJustification form))

type DerivationReport form = [ReportLine form]

type WFLine form = (form, InferenceRule, [Int])

