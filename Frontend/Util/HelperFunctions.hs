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

module Carnap.Frontend.Util.HelperFunctions (formList, matchesSequent, toPremConcPair, cleanGoalPair)

where 

import Text.Parsec (runParser)
import Text.Parsec.Char (oneOf)
import Text.Parsec.Combinator (many1,sepBy)
import Carnap.Core.Data.Rules (Sequent(Sequent), AmbiguousRulePlus)
import Carnap.Core.Data.AbstractSyntaxDataTypes (liftToScheme, DisplayVar,NextVar,Schematizable, Form)
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching (S_DisplayVar, S_NextVar, SchemeVar,SSequentItem(SeqList), Var)
import Carnap.Frontend.Ghcjs.Components.BoxSettings (BoxSettings(..))
import Carnap.Core.Unification.HigherOrderMatching (UniformlyEquaitable)
import Carnap.Languages.Util.ParserTypes

--------------------------------------------------------
--1. Common parsing tasks
--------------------------------------------------------

formList s = parser (fparser s) `sepBy` many1 (oneOf " ,")

toPremConcPair concstring premstring s = (stateParse (fparser s) concstring', runParser (formList s) (initState (fparser s)) "" premstring')
    where premstring' = trim premstring
          concstring' = trim concstring 
          trim = f . f
          f = reverse . dropWhile (== ' ') --XXX: more efficient solutions are possible
 

matchesSequent :: (S_DisplayVar sv quant, S_NextVar sv quant, SchemeVar sv, 
                    UniformlyEquaitable sv, UniformlyEquaitable f, UniformlyEquaitable quant, UniformlyEquaitable con, UniformlyEquaitable pred, 
                    DisplayVar sv quant, NextVar sv quant, Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred) => 
                    Sequent (SSequentItem pred con quant f sv) -> Sequent (SSequentItem pred con quant f sv) -> Bool
matchesSequent (Sequent [SeqList ps] c) (Sequent [SeqList ps'] c') = c == c' && all (`elem` ps) ps'
matchesSequent _ _ = False

--turns a goal presented as a list of formulas and a conclusion into a goal presented as a sequent of schemes
cleanGoalPair gp = case gp of (Right conc, Right prems) -> Just (Sequent [SeqList (Prelude.map liftToScheme prems)] 
                                                                                        (SeqList [liftToScheme conc]))
                              _ -> Nothing
