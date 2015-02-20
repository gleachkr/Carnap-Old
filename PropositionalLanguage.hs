{-#LANGUAGE MultiParamTypeClasses, EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module PropositionalLanguage where

import AbstractSyntaxDataTypes

type Assignment = Int -> Bool

data BooleanConnectives a where
        Not :: BooleanConnectives (Bool -> Bool)
        And :: BooleanConnectives (Bool -> Bool -> Bool)
        Or  :: BooleanConnectives (Bool -> Bool -> Bool)
        If  :: BooleanConnectives (Bool -> Bool -> Bool)
        Iff :: BooleanConnectives (Bool -> Bool -> Bool)

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

data BooleanSentence a where
        Sentence :: {index :: Int} -> BooleanSentence Bool

instance Eq (BooleanSentence a) where
        Sentence x == Sentence y = x == y

instance Schematizable BooleanSentence where
        schematize (Sentence n) = \_ -> "P_" ++ show n

instance Modelable BooleanSentence Assignment where
        satisfies v (Sentence n) = v n

type PropositionalFormula = Form Nothing --no predicates
                                BooleanConnectives --boolean connectives
                                Nothing --no quantifiers
                                Nothing --no function symbols
                                BooleanSentence --semantic values are boolean sentences
                                Bool --only types are booleans

--for some reason it's happy to use the instance of Eq with
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

pn :: Int -> PropositionalFormula
pn n = ConstantFormBuilder (Sentence n)

evens :: Assignment
evens = even
