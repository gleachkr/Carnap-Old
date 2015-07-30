{-#LANGUAGE FunctionalDependencies #-}
module Carnap.Languages.Util.LanguageClasses where

--------------------------------------------------------
--1. Connectives
--------------------------------------------------------
--------------------------------------------------------
--1.1 Boolean Languages
--------------------------------------------------------
--these are classes and datatypes for languages and schematic languages
--with boolean connectives

class BooleanLanguage l where
            lneg :: l -> l
            land :: l -> l -> l
            lor  :: l -> l -> l
            lif  :: l -> l -> l
            liff :: l -> l -> l
            (.¬.) :: l -> l 
            (.¬.) = lneg
            (.-.) :: l -> l 
            (.-.) = lneg
            (.→.) :: l -> l -> l
            (.→.) = lif
            (.=>.) :: l -> l -> l
            (.=>.) = lif
            (.∧.) :: l -> l -> l
            (.∧.) = land
            (./\.) :: l -> l -> l
            (./\.) = land
            (.∨.) :: l -> l -> l
            (.∨.) = lor
            (.\/.) :: l -> l -> l
            (.\/.) = lor
            (.↔.) :: l -> l -> l
            (.↔.) = liff
            (.<=>.) :: l -> l -> l
            (.<=>.) = liff

--------------------------------------------------------
--2. Relations
--------------------------------------------------------
--------------------------------------------------------
--2.1 Relation Constants
--------------------------------------------------------
--these are classes and datatypes for formula and schematic formula types
--with an infinity of 0-ary, 1-ary or 2-ary constant relation symbols

class PropositionalConstants l where
        prop :: String -> l

class UnaryPredicateConstants l t | l -> t where
        pred :: String -> t -> l

class BinaryPredicateConstants l t | l -> t where
        rel :: String -> t -> t -> l

--------------------------------------------------------
--2.2 Schematic Relations 
--------------------------------------------------------
--these are classes and datatypes for schematic formula and sequent item types
--with an infinity of 0-ary, 1-ary or 2-ary schematic relation symbols,

class S_PropositionalConstants l where
        phi :: Int -> l

class S_UnaryPredicateConstants l t | l -> t where
        phi1 :: Int -> t -> l

class S_BinaryPredicateConstants l t | l -> t where
        phi2 :: Int -> t -> t -> l

class SItemConstants l where
        delta :: Int -> l

--------------------------------------------------------
--2.3 Logical Constants
--------------------------------------------------------
--these are classes and datatypes for languages and schematic langauges
--with distinguished logical relations

class EqualityConstant l t | l -> t where
        equals :: t -> t -> l

--------------------------------------------------------
--3. Quantifiers
--------------------------------------------------------
--------------------------------------------------------
--3.1 Quantifier Constants
--------------------------------------------------------
--these are classes and datatypes for formula and schematic formula types
--with quantifier constants

class ExistentialQuantifiers l t | l -> t where
        eb :: (t -> l) -> l

class UniversaQuantifiers l t | l -> t where
        ub :: (t -> l) -> l

--------------------------------------------------------
--4. Terms 
--------------------------------------------------------
--------------------------------------------------------
--4.1 Variables
--------------------------------------------------------
--these are classes and datatypes for term types which include an infinity
--of free variables

class FreeVariables t where
        freeVarn :: Int -> t

--------------------------------------------------------
--4.2 Constant Symbols 
--------------------------------------------------------
--these are classes and datatypes for term types which include an infinity
--of individual constant symbols.

class IndividualConstants t where
        cn :: String -> t

--------------------------------------------------------
--5. Connectives
--------------------------------------------------------
--------------------------------------------------------
--5.1 Schematic Connectives
--------------------------------------------------------

--this class is for languages that allow for (unary) schematic propositional contexts
class PropositionalContexts t where
            propContext :: Int -> t -> t

