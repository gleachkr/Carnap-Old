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

module Carnap.Core.Data.AbstractDerivationMultiUnification where 

import Carnap.Core.Data.AbstractDerivationDataTypes
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxMultiUnification
import Carnap.Core.Data.Rules
import Carnap.Core.Unification.MultiUnification
import Data.List

--------------------------------------------------------
--1. Multi-Unifiable Derivation Data
--------------------------------------------------------

--A Schematic multiple concusion sequent, which is of the form "[prems], Δ |- [conclusions]",
--with schematic variables ranging over lists of side-formulas. In initial
--applications, we'll force this to stick to the single-conclusion case.
--
--Note that sequents need to be presented for matching with the
--main-formulas and side-formulas of a given inference in separate lists.
--E.g. when we're presenting some sequents to check if they are an instance
--of conditional proof, we need [phi] [etc] |- [psi] and [etc] |-
--[phi->psi]; we can't have [phi][etc1][etc2] |- [psi], for example.
--I suspect this will be avoidable once we get second-order pattern
--matching going.
 
type SSequent pred con quant f sv = Sequent (SSequentItem pred con quant f sv)
                                  
--TODO: Infix constructors for sequents would be nice...
--TODO: We'd like a unification instance for schematic sequents, so that
--Abs rules can be unified with inferences via compositeUnify

--------------------------------------------------------
--2. Multi-Unification Instances
--------------------------------------------------------

instance (Schematizable pred, Schematizable con, Schematizable quant, Schematizable f, Schematizable sv, 
        S_NextVar sv quant, SchemeVar sv) => 
            MultiHilbert (SSequentItem pred con quant f sv) (Var pred con quant f sv ()) where

        multiFreeVars (SeqVar c) = [FreeVar c]
        multiFreeVars (SeqList fs) = concat $ map multiFreeVars fs

        multiApply sub (SeqVar c) = case fvLookup c sub of 
            Just (SeqList fs) -> SeqList (map (multiApply sub) fs)
            Nothing -> SeqVar c
        multiApply sub (SeqList fs) = SeqList (map (multiApply sub) fs)

instance (UniformlyEq f, UniformlyEq pred, UniformlyEq sv, UniformlyEq con, UniformlyEq quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
        S_NextVar sv quant, SchemeVar sv) => 
        MultiMatchable (SSequentItem pred con quant f sv) (Var pred con quant f sv ()) where

        multiMatch (SeqVar _) _ = Just []
        multiMatch _ (SeqVar _) = Just []
        multiMatch (SeqList fs) (SeqList fs')
            | length fs == length fs' = Just $ zipWith (|+|) fs fs'
        multiMatch _ _ = Nothing

instance (UniformlyEq f, UniformlyEq pred, UniformlyEq sv, UniformlyEq con, UniformlyEq quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
        S_NextVar sv quant, SchemeVar sv) =>
        MultiUnifiable (SSequentItem pred con quant f sv) (Var pred con quant f sv ()) where

        multiMatchVar (SeqVar c) fs = Just (Mapping c fs)
        multiMatchVar _ _ = Nothing

        multiMakeTerm v@(SideForms _) = SeqVar v

instance (Schematizable pred, Schematizable con, Schematizable quant, Schematizable f, Schematizable sv, 
        S_NextVar sv quant, SchemeVar sv) => 
            MultiHilbert (SSequent pred con quant f sv) (Var pred con quant f sv ()) where

            multiFreeVars (Sequent fs cs) = concat [concat $ map multiFreeVars fs, multiFreeVars cs]

            multiApply sub (Sequent fs cs) = Sequent (map (multiApply sub) fs) (multiApply sub cs)

instance (UniformlyEq f, UniformlyEq pred, UniformlyEq sv, UniformlyEq con, UniformlyEq quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
        S_NextVar sv quant, SchemeVar sv) => 
        MultiMatchable (SSequent pred con quant f sv) (Var pred con quant f sv ()) where

        multiMatch (Sequent fs cs) (Sequent fs' cs')  
            | length fs == length fs' = Just $ (UnifiablePairing cs cs') : (zipWith UnifiablePairing fs fs')
        multiMatch _ _ = Nothing

instance (UniformlyEq f, UniformlyEq pred, UniformlyEq sv, UniformlyEq con, UniformlyEq quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
        S_NextVar sv quant, SchemeVar sv) =>
        MultiUnifiable (SSequent pred con quant f sv) (Var pred con quant f sv ()) where

        multiMatchVar _ _ = Nothing --We don't have schematic variables ranging over sequents

        multiMakeTerm = undefined

instance (Schematizable pred, Schematizable con, Schematizable quant, Schematizable f, Schematizable sv, 
        S_NextVar sv quant, SchemeVar sv) => 
        MultiHilbert (AbsRule (SSequent pred con quant f sv)) (Var pred con quant f sv ()) where

        multiFreeVars (AbsRule p c) = concat [concat $ map multiFreeVars p, multiFreeVars c] 

        multiApply sub (AbsRule p c) = AbsRule (map (multiApply sub) p) (multiApply sub c)

instance (UniformlyEq f, UniformlyEq pred, UniformlyEq sv, UniformlyEq con, UniformlyEq quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
        S_NextVar sv quant, SchemeVar sv) =>
        MultiUnifiable (AbsRule (SSequent pred con quant f sv)) (Var pred con quant f sv ()) where

        multiMatchVar _ _ = Nothing

        multiMakeTerm = undefined

instance (UniformlyEq f, UniformlyEq pred, UniformlyEq sv, UniformlyEq con, UniformlyEq quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
        S_NextVar sv quant, SchemeVar sv) => 
        MultiMatchable (AbsRule (SSequent pred con quant f sv)) (Var pred con quant f sv ()) where

        multiMatch (AbsRule ps c) (AbsRule ps' c')  
            | length ps == length ps' = Just $ (UnifiablePairing c c') : (zipWith UnifiablePairing ps ps')
        multiMatch _ _ = Nothing
