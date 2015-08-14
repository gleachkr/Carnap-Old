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
{-#LANGUAGE MultiParamTypeClasses, GADTs, TypeSynonymInstances, OverlappingInstances, FlexibleInstances, FlexibleContexts #-}

module Carnap.Languages.Sentential.PropositionalLanguage where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.Rules()
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching
import Carnap.Core.Unification.HigherOrderMatching
import Carnap.Languages.Util.LanguageClasses
import Data.Tree

--------------------------------------------------------
--1. Data types for a simple propositional language
--------------------------------------------------------
--These are datatypes for a propositional language

--------------------------------------------------------
--1.1 Boolean Sentences
--------------------------------------------------------

--atomic sentences carry boolean values (relative to an assignment)
data BooleanSentence a where
        Sentence :: {index :: String} -> BooleanSentence Bool

--where assignments are nothing but functions from (indicies of the) the
--apprpriate BooleanSentences to truth values.
type Assignment = Int -> Bool

--an atomic sentence is true in a valuation iff that valuation assigns it
--"True". Only applicable to sentences of the form "[PQRS]_n"
instance Modelable BooleanSentence Assignment where
        satisfies v (Sentence s) = v $ getpos s

instance Eq (BooleanSentence a) where
        Sentence x == Sentence y = x == y

instance UniformlyEq BooleanSentence where
        Sentence x =* Sentence y = x == y

instance UniformlyEquaitable BooleanSentence where
        eq = (=*)

instance Schematizable BooleanSentence where
        schematize (Sentence s) _ = s
        
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
        satisfies _ Iff = (==)

instance Evaluable BooleanConnectives where
        eval = satisfies (const False :: Assignment)

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
        
instance UniformlyEquaitable BooleanConnectives where
        eq = (=*)

instance Schematizable BooleanConnectives where
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

instance BooleanLanguage PropositionalFormula where
        lneg = UnaryConnect Not
        land = BinaryConnect And
        lor = BinaryConnect Or
        lif = BinaryConnect If
        liff = BinaryConnect Iff

instance PropositionalConstants PropositionalFormula where
        prop s = ConstantFormBuilder (Sentence s)
        
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

instance BooleanLanguage PropositionalScheme where
        lneg = S_UnaryConnect Not
        land = S_BinaryConnect And
        lor = S_BinaryConnect Or
        lif = S_BinaryConnect If
        liff = S_BinaryConnect Iff

instance PropositionalConstants PropositionalScheme where
        prop s = S_ConstantFormBuilder (Sentence s)

instance S_PropositionalConstants PropositionalScheme where
        phi n = S_ConstantSchematicFormBuilder (ConstantFormVar $ "φ_" ++ show n) 

instance PropositionalContexts PropositionalScheme where
    propContext n = S_UnarySchematicConnect $ UnaryConnectVar $ "Φ_" ++ show n

type Pvar = Var Nothing --no predicates
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
                ()

type PItem = SSequentItem Nothing --no predicates
                          BooleanConnectives --boolean connectives
                          Nothing --no quantifiers
                          Nothing --no function symbols
                          BooleanSentence --semantic values are BooleanSentences
                                        --(intuitively, intensions or fregean
                                        --senses: things that let you compute
                                        --the reference of something in a given
                                        --model.)

instance S_PropositionalConstants PItem where
        phi n = SeqList [phi n]

instance SItemConstants PItem where
        delta n = SeqVar (SideForms $ "Δ_" ++ show n)

--------------------------------------------------------
--2. Language Utilities
--------------------------------------------------------

letters :: [String]
letters = cycle ["P","Q","R","S"]

indexNumbers :: [Integer]
indexNumbers = zipWith (+) [1,1 ..] ([0,0,0,0] ++ indexNumbers)

indicies = ["","","",""] ++ map (\x -> '_' : show x) indexNumbers

plist :: [String]
plist = zipWith (++) letters indicies

getpos :: String -> Int
getpos s = case s of 
                "P" -> 1
                "Q" -> 2
                "R" -> 3
                "S" -> 4
                _   -> case head s of 
                        'P' -> read (tail $ tail s)  * 4 + 1
                        'Q' -> read (tail $ tail s)  * 4 + 2
                        'R' -> read (tail $ tail s)  * 4 + 3
                        'S' -> read (tail $ tail s)  * 4 + 4
                        _ -> undefined

instance UniformlyEquaitable Nothing where 
        eq = (=*)

formsWithNconnectives :: Int -> [Tree String]
formsWithNconnectives 0 = [Node "*" []]
formsWithNconnectives n = do x <- [0..n-1]
                             let y = (n-1) - x 
                             con <- if x == n-1 
                                        then ["land","lor", "lif", "liff", "lneg"] 
                                        else ["land","lor", "lif", "liff"]
                             form1 <- formsWithNconnectives x
                             form2 <- formsWithNconnectives y
                             case con of "lneg" -> return (Node con [form1])
                                         _      -> return (Node con [form1, form2])

irredundentAtoms :: Int -> [[Int]]
irredundentAtoms 1 = [[1]]
irredundentAtoms n = do l <- irredundentAtoms (n-1)
                        let m = maximum l
                        x <- [1..m+1]
                        return (x : l)

numberOfLeaves :: Num a => Tree t -> a
numberOfLeaves (Node _ []) = 1
numberOfLeaves (Node _ s) = sum (map numberOfLeaves s)

distributeAtoms :: [Int] -> Tree [Char] -> PropositionalFormula
distributeAtoms atoms (Node _ []) = prop (plist !! (head atoms - 1))
distributeAtoms atoms (Node conn [t1, t2]) = tf conn (distributeAtoms (take (numberOfLeaves t1) atoms) t1)
                                                     (distributeAtoms (drop (numberOfLeaves t1) atoms) t2)
    where tf s = case s of "land" -> land
                           "lor" -> lor
                           "liff" -> liff
                           "lif" -> lif
                           _ -> land
distributeAtoms atoms (Node _ l) = lneg (distributeAtoms atoms (head l))

assignments :: Int -> [Int -> Bool]
assignments 0 = [const False]
assignments n = do new <- [True,False]
                   extendee <- assignments (n - 1)
                   return (\m -> if m < n then extendee m else new)

validIn :: Int -> PropositionalFormula -> Bool
validIn n f = and $ do a <- assignments n
                       return (satisfies a f)

formulasWithNconnectives :: Int -> [PropositionalFormula]
formulasWithNconnectives n = do f <- formsWithNconnectives n
                                let m = numberOfLeaves f
                                atoms <- irredundentAtoms m
                                return (distributeAtoms atoms f)

--not as efficient as possible, since some of these will have fewer than
--n atoms.
tautologyWithNconnectives :: Int -> [PropositionalFormula]
tautologyWithNconnectives n = filter (validIn (n+1)) (formulasWithNconnectives n)
