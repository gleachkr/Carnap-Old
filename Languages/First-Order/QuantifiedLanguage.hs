{-#LANGUAGE MultiParamTypeClasses, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module Carnap.Languages.Sentential.PropositionalLanguage where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxMultiUnification
import Carnap.Languages.Util.LanguageClasses

--------------------------------------------------------
--1. Data types for the language of First Order Logic, with equality
--------------------------------------------------------
--These are datatypes for a propositional language

--------------------------------------------------------
--1.1 The Domain
--------------------------------------------------------

--This data type plays the role of a domain of objects. Right now, we just
--use integers.

type Domain = Int

--------------------------------------------------------
--1.1 Semantic Values
--------------------------------------------------------

--The semantic values that our atomic terms will carry are arbitrary entities
--in the domain; the semantic values of atomic sentences are truth values
data Referent a where
    SentenceVal :: {s_index :: Int} -> Referent Bool
    Entity :: {e_index :: Int} -> Referent Domain

--XXX:No modelable instance for now. We don't know how (or if) we want to
--represent models.

instance Eq (Referent a) where
        SentenceVal x == SentenceVal y = x == y
        Entity x == Entity y = x == y
        _ == _ = False

instance UniformlyEq Referent where
        SentenceVal x =* SentenceVal y = x == y
        Entity x =* Entity y = x == y
        _ =* _   = False

instance Schematizable Referent where
        schematize (SentenceVal n) _ = "S_" ++ show n
        schematize (Entity n) _ = "c_" ++ show n
        
instance SchemeVar Referent where
        appropriateSchematicVariable _ = undefined

--------------------------------------------------------
--1.2 Boolean connectives
--------------------------------------------------------

--connectives carry functions from boolean values to boolean values.
data FirstOrderConnectives a where
        Not :: FirstOrderConnectives (Bool -> Bool)
        And :: FirstOrderConnectives (Bool -> Bool -> Bool)
        Or  :: FirstOrderConnectives (Bool -> Bool -> Bool)
        If  :: FirstOrderConnectives (Bool -> Bool -> Bool)
        Iff :: FirstOrderConnectives (Bool -> Bool -> Bool)
        
--XXX:No modealable/evaluable instances for now.

instance Eq (FirstOrderConnectives a) where
        Not == Not = True
        And == And = True
        Or  == Or  = True
        If  == If  = True
        Iff == Iff = True
        _   == _   = False

instance UniformlyEq FirstOrderConnectives where
        Not =* Not = True
        And =* And = True
        Or  =* Or  = True
        If  =* If  = True
        Iff =* Iff = True
        _   =* _   = False
        
instance Schematizable FirstOrderConnectives where
        schematize Not = \x -> case x of [y] -> "¬" ++ y 
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
--1.3 Predicates and relations
--------------------------------------------------------

data AtomicPredicate a where
        AtomicUnary  :: {u_index :: Int} -> AtomicPredicate (Domain -> Bool)
        AtomicBinary :: {b_index :: Int} -> AtomicPredicate (Domain -> Domain -> Bool)
        Equality :: AtomicPredicate (Domain -> Domain -> Bool)

instance Eq (AtomicPredicate a) where
        AtomicUnary x == AtomicUnary y = x == y
        AtomicBinary x == AtomicBinary y = x == y
        Equality == Equality = True
        _ == _ = False

instance UniformlyEq AtomicPredicate where
        AtomicUnary x =* AtomicUnary y  = x == y
        AtomicBinary x =* AtomicBinary y  = x == y
        Equality =* Equality = True
        _ =* _  = False

instance Schematizable AtomicPredicate where
        schematize (AtomicUnary n) [x] = "P_" ++ show n ++ "(" ++ x ++ ")"
        schematize (AtomicBinary n) [x,y] = "R_" ++ show n ++ "(" ++ x ++ "," ++ y ++ ")"
        schematize (Equality) [x,y] = x ++ "=" ++ y
        schematize _ _ = undefined
        
instance SchemeVar AtomicPredicate where
        appropriateSchematicVariable _ = undefined

--------------------------------------------------------
--1.4 Quantifiers
--------------------------------------------------------

data FirstOrderQuantifiers a where 
        Universal   :: FirstOrderQuantifiers ((Referent Domain -> Bool) -> Bool)
        Existential :: FirstOrderQuantifiers ((Referent Domain -> Bool) -> Bool)

instance Eq (FirstOrderQuantifiers a) where
        Universal == Universal = True
        Existential == Existential = True
        _ == _ = False

instance UniformlyEq FirstOrderQuantifiers where
        Universal =* Universal = True
        Existential =* Existential = True
        _ =* _ = False

instance Schematizable FirstOrderQuantifiers where
        schematize (Universal) [x,y] = "∀" ++ x ++ y
        schematize (Existential) [x,y] = "∃" ++ x ++ y
        schematize _ _ = "error in schematizing quantifier"

--placeholder while we work out other bugs
instance NextVar Referent FirstOrderQuantifiers where
        appropriateVariable f _ = "x_" ++ show (quantifierCount f)

--------------------------------------------------------
--1.4 Quantified Formulas and Terms
--------------------------------------------------------
--a Quantified formula is built from:
type FirstOrderFormula =   Form AtomicPredicate --atomic predicates
                                FirstOrderConnectives --boolean connectives
                                FirstOrderQuantifiers --first-order quantifiers
                                Nothing --no function symbols (XXX:yet)
                                Referent --semantic values are referents 
                                Bool -- we should be able to evaluate to boolean values

type FirstOrderTerm =      Term Nothing --no function symbols (XXX: yet)
                                Referent --semantic values are referents 
                                Domain -- we should be able to evaluate to entities in the domain

instance Eq FirstOrderFormula where
        ConstantFormBuilder x == ConstantFormBuilder y = x == y
        UnaryPredicate (AtomicUnary n) t == UnaryPredicate (AtomicUnary n') t' = 
            n == n' && t == t'
        BinaryPredicate (AtomicBinary n) t s == BinaryPredicate (AtomicBinary n') t' s' = 
            n == n' && t == t' && s == s'
        BinaryPredicate Equality t s == BinaryPredicate Equality t' s' = 
            t == t' && s == s'
        UnaryConnect Not x == UnaryConnect Not z = x == z 
        BinaryConnect And x y == BinaryConnect And z w = x == z && y == w
        BinaryConnect  Or x y == BinaryConnect  Or z w = x == z && y == w
        BinaryConnect  If x y == BinaryConnect  If z w = x == z && y == w
        BinaryConnect Iff x y == BinaryConnect Iff z w = x == z && y == w
        _ == _ = False

instance Eq FirstOrderTerm where
        BlankTerm _ == BlankTerm _ = True
        ConstantTermBuilder x == ConstantTermBuilder y = x == y
        _ == _ = False

instance BooleanLanguage FirstOrderFormula where
        lneg = UnaryConnect Not
        land = BinaryConnect And
        lor = BinaryConnect Or
        lif = BinaryConnect If
        liff = BinaryConnect Iff

--------------------------------------------------------
--1.4 First-Order Schemata
--------------------------------------------------------

type FirstOrderScheme = SchematicForm AtomicPredicate
                                      FirstOrderConnectives --boolean connectives
                                      FirstOrderQuantifiers --no quantifiers
                                      Nothing --no function symbols (XXX:yet)
                                      Referent --semantic values are referents
                                      ()  --sentences aren't meaningful

instance BooleanLanguage FirstOrderScheme where
        lneg = S_UnaryConnect Not
        land = S_BinaryConnect And
        lor = S_BinaryConnect Or
        lif = S_BinaryConnect If
        liff = S_BinaryConnect Iff

type Qvar = Var AtomicPredicate
                FirstOrderConnectives 
                FirstOrderQuantifiers 
                Nothing --no function symbols (XXX:yet)
                Referent --semantic values are referents
                ()  --sentences aren't meaningful
                ()

type QItem = SSequentItem AtomicPredicate
                          FirstOrderConnectives
                          FirstOrderQuantifiers 
                          Nothing --no function symbols
                          Referent

instance S_NextVar Referent FirstOrderQuantifiers where
        s_appropriateVariable f _ = "x_" ++ show (s_quantifierCount f)

--------------------------------------------------------
--2. Wrapper functions for constructors
--------------------------------------------------------

--
pn :: Int -> FirstOrderFormula 
pn n = ConstantFormBuilder (SentenceVal n)

--constant n
cn :: Int -> FirstOrderTerm
cn n = ConstantTermBuilder (Entity n)

--predicate n
predn :: Int -> FirstOrderTerm -> FirstOrderFormula
predn n = UnaryPredicate (AtomicUnary n)

--equality symbol
eq :: FirstOrderTerm -> FirstOrderTerm -> FirstOrderFormula
eq = BinaryPredicate Equality

--relation symbol n
reln :: Int -> FirstOrderTerm -> FirstOrderTerm -> FirstOrderFormula
reln n = BinaryPredicate (AtomicBinary n) 

--universal Bind
ub :: (FirstOrderTerm -> FirstOrderFormula) -> FirstOrderFormula
ub = Bind Universal

--existential Bind
eb :: (FirstOrderTerm -> FirstOrderFormula) -> FirstOrderFormula
eb = Bind Existential

phi :: Int -> FirstOrderScheme
phi n = S_ConstantSchematicFormBuilder (ConstantFormVar $ "φ_" ++ show n) 

delta :: Int -> QItem
delta n = SeqVar (SideForms $ "Δ_" ++ show n)

phi_ :: Int -> QItem
phi_ n = SeqList [phi n]

--------------------------------------------------------
--3. Helper Functions
--------------------------------------------------------

quantifierCount :: Form pred con quant f sv a -> Int
quantifierCount (Bind _ f) = quantifierCount (f $ BlankTerm "*") + 1
quantifierCount (UnaryConnect _ f) = quantifierCount f
quantifierCount (BinaryConnect _ f g) = quantifierCount f + quantifierCount g
quantifierCount _ = 0

s_quantifierCount :: SchematicForm pred con quant f sv a -> Int
s_quantifierCount (S_Bind _ f) = s_quantifierCount (f $ BlankTerm "*") + 1
s_quantifierCount (S_SchematicBind _ f) = s_quantifierCount (f $ BlankTerm "*") + 1
s_quantifierCount (S_UnaryConnect _ f) = s_quantifierCount f
s_quantifierCount (S_UnarySchematicConnect _ f) = s_quantifierCount f
s_quantifierCount (S_BinaryConnect _ f g) = s_quantifierCount f + s_quantifierCount g
s_quantifierCount (S_BinarySchematicConnect _ f g) = s_quantifierCount f + s_quantifierCount g
s_quantifierCount _ = 0
