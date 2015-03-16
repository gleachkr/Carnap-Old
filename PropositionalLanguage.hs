{-#LANGUAGE MultiParamTypeClasses, EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module PropositionalLanguage where

import AbstractSyntaxDataTypes
import AbstractSyntaxUnification
import Unification

--------------------------------------------------------
--1. Data types for a simple propositional language
--------------------------------------------------------
--These are datatypes for a propositional language

--------------------------------------------------------
--1.1 Boolean Sentences
--------------------------------------------------------

--atomic sentences carry boolean values (relative to an assignment)
data BooleanSentence a where
        Sentence :: {index :: Int} -> BooleanSentence Bool

--where assignments are nothing but functions from (indicies of the) the
--apprpriate BooleanSentences to truth values.
type Assignment = Int -> Bool

--an atomic sentence is true in a valuation iff that valuation assigns it
--"True".
instance Modelable BooleanSentence Assignment where
        satisfies v (Sentence n) = v n

instance Eq (BooleanSentence a) where
        Sentence x == Sentence y = x == y

instance UniformlyEq BooleanSentence where
        Sentence x =* Sentence y = x == y
        _ =* _ = False

instance Schematizable BooleanSentence where
        schematize (Sentence n) _ = "P_" ++ show n
        
instance SchemeVar BooleanSentence where
        appropriateSchematicVariable _ = undefined

--------------------------------------------------------
--1.2 Boolean connectives
--------------------------------------------------------

--connectives carry functions from boolean values to boolean values.
data BooleanConnectives a where
        Not :: BooleanConnectives (Bool -> Bool)
        And :: BooleanConnectives (Bool -> Bool -> Bool)
        Or  :: BooleanConnectives (Bool -> Bool -> Bool)
        If  :: BooleanConnectives (Bool -> Bool -> Bool)
        Iff :: BooleanConnectives (Bool -> Bool -> Bool)
        
--the functions they carry are invariant across assingments.
instance Modelable BooleanConnectives Assignment where
        satisfies _ Not = not
        satisfies _ And = (&&)
        satisfies _ Or  = (||)
        satisfies _ If  = \x y -> not x || y
        satisfies _ Iff = \x y -> x == y

instance Evaluable BooleanConnectives where
        eval x = satisfies ((\_-> False) :: Assignment) x

instance Eq (BooleanConnectives a) where
        Not == Not = True
        And == And = True
        Or  == Or  = True
        If  == If  = True
        Iff == Iff = True
        _   == _   = False

instance UniformlyEq BooleanConnectives where
        Not =* Not = True
        And =* And = True
        Or  =* Or  = True
        If  =* If  = True
        Iff =* Iff = True
        _   =* _   = False
        
instance Schematizable BooleanConnectives where
        schematize Not = \x -> case x of [y] -> "not" ++ y 
                                         _   -> undefined
        schematize And = \x -> case x of [y,z] -> "(" ++ y ++ " and " ++ z ++ ")"
                                         _   -> undefined
        schematize Or  = \x -> case x of [y,z] -> "(" ++ y ++ " or " ++ z ++ ")"
                                         _   -> undefined
        schematize If  = \x -> case x of [y,z] -> "( if " ++ y ++ " then " ++ z ++ ")"
                                         _   -> undefined
        schematize Iff = \x -> case x of [y,z] -> "(" ++ y ++ " iff " ++ z ++ ")"
                                         _   -> undefined

--------------------------------------------------------
--1.3 Propositional Formulas
--------------------------------------------------------
--a propositional formula is built from:
type PropositionalFormula = Form Nothing --no predicates
                                BooleanConnectives --boolean connectives
                                Nothing --no quantifiers
                                Nothing --no function symbols
                                BooleanSentence 
                                    --semantic values are BooleanSentences
                                    --(intuitively, intensions or fregean
                                    --senses: things that let you compute
                                    --the reference of something in a given
                                    --model.)
                                Bool --only types are booleans

--XXX: for some reason it's happy to use the instance of Eq with
--BooleanSentence, but not with BooleanConnectives. I think it may be that
--the pattern match on the left gives it enough information to sign off on
--the equality definition on the right. 
instance Eq PropositionalFormula where
        ConstantFormBuilder x == ConstantFormBuilder y = x == y
        BinaryConnect And x y == BinaryConnect And z w = x == z && y == w
        BinaryConnect  Or x y == BinaryConnect  Or z w = x == z && y == w
        BinaryConnect  If x y == BinaryConnect  If z w = x == z && y == w
        BinaryConnect Iff x y == BinaryConnect Iff z w = x == z && y == w
        _ == _ = False

--------------------------------------------------------
--1.4 Propositional Schemata
--------------------------------------------------------

type PropositionalScheme = SchematicForm Nothing --no predicates
                                    BooleanConnectives --boolean connectives
                                    Nothing --no quantifiers
                                    Nothing --no function symbols
                                    BooleanSentence 
                                        --semantic values are BooleanSentences
                                        --(intuitively, intensions or fregean
                                        --senses: things that let you compute
                                        --the reference of something in a given
                                        --model.)
                                    ()  --sentences aren't meaningful

type PSubst = Subst SSymbol PropositionalScheme

--------------------------------------------------------
--2. Wrapper functions for constructors
--------------------------------------------------------

lneg :: PropositionalFormula -> PropositionalFormula
lneg = UnaryConnect Not

land :: PropositionalFormula -> PropositionalFormula -> PropositionalFormula
land = BinaryConnect And

lor :: PropositionalFormula -> PropositionalFormula -> PropositionalFormula
lor = BinaryConnect Or

lif :: PropositionalFormula -> PropositionalFormula -> PropositionalFormula
lif = BinaryConnect If

(.→.) :: PropositionalFormula -> PropositionalFormula -> PropositionalFormula
(.→.) = lif 

--TODO: Some additional infix wrappers would be nice.

pn :: Int -> PropositionalFormula
pn n = ConstantFormBuilder (Sentence n)

phi :: Int -> PropositionalScheme
phi n = S_ConstantSchematicFormBuilder (S,"phi_" ++ show n) 

s_land :: PropositionalScheme -> PropositionalScheme -> PropositionalScheme
s_land = S_BinaryConnect And 

evens :: Assignment
evens = even
