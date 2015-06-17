{-#LANGUAGE MultiParamTypeClasses, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module Carnap.Languages.Sentential.TemporalPropositionalLanguage where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxMultiUnification
import Carnap.Languages.Util.LanguageClasses
import Data.Tree

--------------------------------------------------------
--1. Data types for a temporal propositional language
--------------------------------------------------------
--These are datatypes for a temporal propositional language, of the kind
--used in LTL and other temporal languages
--XXX: The semantics presuppose linear time. It would make sense to
--generalize these.

--------------------------------------------------------
--1.1 Boolean Sentences
--------------------------------------------------------

--temporal intensions are functions from times to truth values
type TemporalIntension = (Int -> Bool)

--atomic sentences carry temporal intensions (relative to an assignment)
data TemporalSentence a where
        TSentence :: {index :: Int} -> TemporalSentence TemporalIntension

--where temporal intensions are nothing but functions from (indicies of
--the) the apprpriate BooleanSentences to functions from times to truth
--values.
type TAssignment = Int -> TemporalIntension

--The truth value of an atomic sentence at a time is the value assigned by
--its intension to that time
instance Modelable TemporalSentence TAssignment where
        satisfies a (TSentence n) = a n

instance Eq (TemporalSentence a) where
        TSentence x == TSentence y = x == y

instance UniformlyEq (TemporalSentence) where
        TSentence x =* TSentence y = x == y

instance Schematizable TemporalSentence where
        schematize (TSentence n) _ = "P_" ++ show n
        
instance SchemeVar TemporalSentence where
        appropriateSchematicVariable _ = undefined

--------------------------------------------------------
--1.2 Boolean connectives
--------------------------------------------------------

--connectives carry functions from boolean values to boolean values.
data TemporalConnectives a where
        Not   :: TemporalConnectives (TemporalIntension -> TemporalIntension)
        Next  :: TemporalConnectives (TemporalIntension -> TemporalIntension)
        Hence :: TemporalConnectives (TemporalIntension -> TemporalIntension)
        And   :: TemporalConnectives (TemporalIntension -> TemporalIntension -> TemporalIntension)
        Or    :: TemporalConnectives (TemporalIntension -> TemporalIntension -> TemporalIntension)
        If    :: TemporalConnectives (TemporalIntension -> TemporalIntension -> TemporalIntension)
        Iff   :: TemporalConnectives (TemporalIntension -> TemporalIntension -> TemporalIntension)
        
--the functions they carry are invariant across assingments. XXX: Unfortunately,
--this will be undecidable in many cases involving Hence. 
instance Modelable TemporalConnectives (TAssignment,Int) where
        satisfies _ Hence = undefined
        satisfies _ Next = \i t -> i (t + 1)
        satisfies _ Not = \i -> not . i
        satisfies _ And = \i1 i2 t -> i1 t && i2 t
        satisfies _ Or  = \i1 i2 t -> i1 t || i2 t
        satisfies _ If  = \i1 i2 t -> (not . i1) t || i2 t
        satisfies _ Iff = \i1 i2 t -> i1 t == i2 t

instance Evaluable TemporalConnectives where
        eval = satisfies ((\_ -> const False) :: TAssignment,0::Int)

instance Eq (TemporalConnectives a) where
        Not == Not = True
        And == And = True
        Or  == Or  = True
        If  == If  = True
        Iff == Iff = True
        Hence == Hence = True
        Next == Next = True
        _   == _   = False

instance UniformlyEq TemporalConnectives where
        Not =* Not = True
        And =* And = True
        Or  =* Or  = True
        If  =* If  = True
        Iff =* Iff = True
        Hence =* Hence = True
        Next =* Next = True
        _   =* _   = False
        
instance Schematizable TemporalConnectives where
        schematize Not = \x -> case x of [y] -> "¬" ++ y 
                                         _   -> undefined
        schematize Next = \x -> case x of [y] -> "◎" ++ y 
                                          _   -> undefined
        schematize Hence = \x -> case x of [y] -> "▢" ++ y 
                                           _   -> undefined
        schematize And = \x -> case x of [y,z] -> "(" ++ y ++ " ∧ " ++ z ++ ")"
                                         _   -> undefined
        schematize Or  = \x -> case x of [y,z] -> "(" ++ y ++ " ∨ " ++ z ++ ")"
                                         _   -> undefined
        schematize If  = \x -> case x of [y,z] -> "(" ++ y ++ " → " ++ z ++ ")"
                                         _   -> undefined
        schematize Iff = \x -> case x of [y,z] -> "(" ++ y ++ " ↔ " ++ z ++ ")"
                                         _   -> undefined

--------------------------------------------------------
--1.3 Temporal Formulas
--------------------------------------------------------
--a Temporal formula is built from:
type TemporalFormula = Form Nothing --no predicates
                            TemporalConnectives --temporal connectives
                            Nothing --no quantifiers
                            Nothing --no function symbols
                            TemporalSentence
                                --semantic values are BooleanSentences
                                --(intuitively, intensions or fregean
                                --senses: things that let you compute
                                --the reference of something in a given
                                --model.)
                            TemporalIntension --only types are temporal intensions

instance Eq TemporalFormula where
        ConstantFormBuilder x == ConstantFormBuilder y = x == y
        UnaryConnect Not x    == UnaryConnect Not z = x == z
        UnaryConnect Hence x  == UnaryConnect Hence z = x == z
        UnaryConnect Next x   == UnaryConnect Next z = x == z
        BinaryConnect And x y == BinaryConnect And z w = x == z && y == w
        BinaryConnect  Or x y == BinaryConnect  Or z w = x == z && y == w
        BinaryConnect  If x y == BinaryConnect  If z w = x == z && y == w
        BinaryConnect Iff x y == BinaryConnect Iff z w = x == z && y == w
        _ == _ = False

instance BooleanLanguage TemporalFormula where
        lneg = UnaryConnect Not
        land = BinaryConnect And
        lor = BinaryConnect Or
        lif = BinaryConnect If
        liff = BinaryConnect Iff

--------------------------------------------------------
--1.4 Propositional Schemata
--------------------------------------------------------

type TemporalScheme = SchematicForm Nothing --no predicates
                                    TemporalConnectives--boolean connectives
                                    Nothing --no quantifiers
                                    Nothing --no function symbols
                                    TemporalSentence
                                        --semantic values are BooleanSentences
                                        --(intuitively, intensions or fregean
                                        --senses: things that let you compute
                                        --the reference of something in a given
                                        --model.)
                                    ()  --sentences aren't meaningful

instance BooleanLanguage TemporalScheme where
        lneg = S_UnaryConnect Not
        land = S_BinaryConnect And
        lor = S_BinaryConnect Or
        lif = S_BinaryConnect If
        liff = S_BinaryConnect Iff

type Tvar = Var Nothing --no predicates
                TemporalConnectives --temporal connectives
                Nothing --no quantifiers
                Nothing --no function symbols
                TemporalSentence
                    --semantic values are temporal sentences
                ()  --sentences aren't meaningful
                ()

type TItem = SSequentItem Nothing --no predicates
                          TemporalConnectives --Temporal connectives
                          Nothing --no quantifiers
                          Nothing --no function symbols
                          TemporalSentence --semantic values are temporal Sentences


--------------------------------------------------------
--2. Wrapper functions for constructors
--------------------------------------------------------

pn :: Int -> TemporalFormula
pn n = ConstantFormBuilder (TSentence n)

phi :: Int -> TemporalScheme
phi n = S_ConstantSchematicFormBuilder (ConstantFormVar $ "φ_" ++ show n) 

delta :: Int -> TItem
delta n = SeqVar (SideForms $ "Δ_" ++ show n)

phi_ :: Int -> TItem
phi_ n = SeqList [phi n]

--------------------------------------------------------
--3. Language Utilities
--------------------------------------------------------

--TODO: An algorithm for validity of temporal sentences.
