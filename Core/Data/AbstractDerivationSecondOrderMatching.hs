{-#LANGUAGE GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-Copyright 2015 (C) Jake Ehrlich and Graham Leach-Krouse

This file is part of Carnap. 

Carnap is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Carnap is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Carnap If not, see <http://www.gnu.org/licenses/>.
-}

module Carnap.Core.Data.AbstractDerivationSecondOrderMatching where 

import Carnap.Core.Data.AbstractDerivationDataTypes()
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching
import Carnap.Core.Data.Rules
import Carnap.Core.Unification.HigherOrderMatching
import Carnap.Core.Unification.HigherOrderUtil()
import Data.List()

type SSequent pred con quant f sv = Sequent (SSequentItem pred con quant f sv)
                                  
--TODO: We'd like a unification instance for schematic sequents, so that
--Abs rules can be unified with inferences via compositeUnify

--------------------------------------------------------
--2. Multi-Unification Instances
--------------------------------------------------------

instance (UniformlyEquaitable f, UniformlyEquaitable pred, UniformlyEquaitable sv, UniformlyEquaitable con, UniformlyEquaitable quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
        S_NextVar sv quant, SchemeVar sv) => 
        Matchable (SSequentItem pred con quant f sv) (Var pred con quant f sv ()) where

        freeVars (SeqVar c) = [FreeVar c]
        freeVars (SeqList fs) = concat $ map freeVars fs

        apply sub (SeqVar c) = case fvLookup c sub of 
            Just (SeqList fs) -> SeqList (map (apply sub) fs)
            Just (SeqVar c') -> SeqVar c'
            Nothing -> SeqVar c
        apply sub (SeqList fs) = SeqList (map (apply sub) fs)

        match (SeqVar _) _ = Just []
        match _ (SeqVar _) = Just []
        match (SeqList fs) (SeqList fs')
            | length fs == length fs' = Just $ zipWith (:=:) fs fs'
        match _ _ = Nothing

        matchVar (SeqVar c) fs = [LambdaMapping c [] fs]
        matchVar _          _  = []

        makeTerm v@(SideForms _) = SeqVar v 

instance (UniformlyEquaitable f, UniformlyEquaitable pred, UniformlyEquaitable sv, UniformlyEquaitable con, UniformlyEquaitable quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
        S_NextVar sv quant, SchemeVar sv) => 
        Matchable (SSequent pred con quant f sv) (Var pred con quant f sv ()) where

        freeVars (Sequent fs cs) = concat [concat $ map freeVars fs, freeVars cs]

        apply sub (Sequent fs cs) = Sequent (map (apply sub) fs) (apply sub cs)

        match (Sequent fs cs) (Sequent fs' cs')  
            | length fs == length fs' = Just $ (cs :=: cs') : zipWith (:=:) fs fs'
        match _ _ = Nothing

        matchVar _ _ = [] --We don't have schematic variables ranging over sequents

        makeTerm = undefined

instance (UniformlyEquaitable f, UniformlyEquaitable pred, UniformlyEquaitable sv, UniformlyEquaitable con, UniformlyEquaitable quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
        S_NextVar sv quant, SchemeVar sv) =>
        Matchable (AbsRule (SSequent pred con quant f sv)) (Var pred con quant f sv ()) where

        freeVars (AbsRule p c) = concat [concat $ map freeVars p, freeVars c] 

        apply sub (AbsRule p c) = AbsRule (map (apply sub) p) (apply sub c)

        matchVar _ _ = []

        makeTerm = undefined

        match (AbsRule ps c) (AbsRule ps' c')  
            | length ps == length ps' = Just $ (c :=: c') : zipWith (:=:) ps ps'
        match _ _ = Nothing


