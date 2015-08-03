{-#LANGUAGE MultiParamTypeClasses, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, OverlappingInstances #-}

module Carnap.Languages.FirstOrder.QuantifiedLanguage where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxMultiUnification()
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching
import Carnap.Core.Unification.HigherOrderMatching
import Carnap.Core.Unification.HigherOrderUtil
import Carnap.Languages.Util.LanguageClasses

import Control.Lens

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
    SentenceVal :: {s_index :: String} -> Referent Bool
    Entity :: {e_index :: String} -> Referent Domain

--XXX:No modelable instance for now. We don't know how (or if) we want to
--represent models.

-- instance Eq (Referent a) where
--         SentenceVal x == SentenceVal y = x == y
--         Entity x == Entity y = x == y
--         _ == _ = False

instance UniformlyEq Referent where
        SentenceVal x =* SentenceVal y = x == y
        Entity x =* Entity y = x == y
        _ =* _   = False

instance UniformlyEquaitable Referent where 
        eq = (=*)

instance Schematizable Referent where
        schematize (SentenceVal s) _ = s
        schematize (Entity s) _ = s
        
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
        
instance UniformlyEquaitable FirstOrderConnectives where 
        eq = (=*)

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
        AtomicUnary  :: {u_index :: String} -> AtomicPredicate (Domain -> Bool)
        AtomicBinary :: {b_index :: String} -> AtomicPredicate (Domain -> Domain -> Bool)
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

instance UniformlyEquaitable AtomicPredicate where 
        eq = (=*)

instance Schematizable AtomicPredicate where
        schematize (AtomicUnary s) [x] = s ++ "(" ++ x ++ ")"
        schematize (AtomicBinary s) [x,y] = s ++ "(" ++ x ++ "," ++ y ++ ")"
        schematize (Equality) [x,y] = x ++ "=" ++ y
        schematize _ _ = undefined
        
instance SchemeVar AtomicPredicate where
        appropriateSchematicVariable _ = undefined

--------------------------------------------------------
--1.4 Function Symbols
--------------------------------------------------------

data FunctionSymbol a where
        UnaryFS :: {u_findex :: String} -> FunctionSymbol (Domain -> Domain)
        BinaryFS :: {b_findex :: String} -> FunctionSymbol (Domain -> Domain -> Domain)

instance Eq (FunctionSymbol a) where
        UnaryFS x == UnaryFS y = x == y
        BinaryFS x == BinaryFS y = x == y
        _ == _ = False

instance UniformlyEq FunctionSymbol where
        UnaryFS x =* UnaryFS y  = x == y
        BinaryFS x =* BinaryFS y  = x == y
        _ =* _  = False

instance UniformlyEquaitable FunctionSymbol where 
        eq = (=*)

instance Schematizable FunctionSymbol where
        schematize (UnaryFS s) [x] = s ++ "(" ++ x ++ ")"
        schematize (BinaryFS s) [x,y] = s ++ "(" ++ x ++ "," ++ y ++ ")"
        schematize _ _ = undefined
        
instance SchemeVar FunctionSymbol where
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

instance UniformlyEquaitable FirstOrderQuantifiers where 
        eq = (=*)

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
                                FunctionSymbol --basic function symbols
                                Referent --semantic values are referents 
                                Bool -- we should be able to evaluate to boolean values

instance PropositionalConstants FirstOrderFormula where
        prop s = ConstantFormBuilder (SentenceVal s)

instance UnaryPredicateConstants FirstOrderFormula FirstOrderTerm where 
        pred s = UnaryPredicate (AtomicUnary s)

instance BinaryPredicateConstants FirstOrderFormula FirstOrderTerm where
        rel s = BinaryPredicate (AtomicBinary s) 

instance EqualityConstant FirstOrderFormula FirstOrderTerm where
        equals = BinaryPredicate Equality

instance ExistentialQuantifiers FirstOrderFormula FirstOrderTerm where
        eb = Bind Existential

instance UniversalQuantifiers FirstOrderFormula FirstOrderTerm where
        ub = Bind Universal
        
instance BooleanLanguage FirstOrderFormula where
        lneg = UnaryConnect Not
        land = BinaryConnect And
        lor = BinaryConnect Or
        lif = BinaryConnect If
        liff = BinaryConnect Iff

type FirstOrderTerm = Term FunctionSymbol --Basic Function Symbols
                           Referent --semantic values are referents 
                           Domain -- we should be able to evaluate to entities in the domain

instance IndividualConstants FirstOrderTerm where
        cn s = ConstantTermBuilder (Entity s)

instance UnaryFunctionConstants FirstOrderTerm where
        fn s = UnaryFuncApp (UnaryFS s)

instance BinaryFunctionConstants FirstOrderTerm where
        fn2 s = BinaryFuncApp (BinaryFS s)

instance FreeVariables FirstOrderTerm where
        freeVarn n = BlankTerm $ "*_" ++ show n

-- instance Eq FirstOrderFormula where
--         ConstantFormBuilder x == ConstantFormBuilder y = x == y
--         UnaryPredicate (AtomicUnary n) t == UnaryPredicate (AtomicUnary n') t' = 
--             n == n' && t == t'
--         BinaryPredicate (AtomicBinary n) t s == BinaryPredicate (AtomicBinary n') t' s' = 
--             n == n' && t == t' && s == s'
--         BinaryPredicate Equality t s == BinaryPredicate Equality t' s' = 
--             t == t' && s == s'
--         UnaryConnect Not x == UnaryConnect Not z = x == z 
--         BinaryConnect And x y == BinaryConnect And z w = x == z && y == w
--         BinaryConnect  Or x y == BinaryConnect  Or z w = x == z && y == w
--         BinaryConnect  If x y == BinaryConnect  If z w = x == z && y == w
--         BinaryConnect Iff x y == BinaryConnect Iff z w = x == z && y == w
--         _ == _ = False

-- instance Eq FirstOrderTerm where
--         BlankTerm s == BlankTerm s' = s == s'
--         ConstantTermBuilder x == ConstantTermBuilder y = x == y
--         _ == _ = False


--------------------------------------------------------
--1.4 First-Order Schemata
--------------------------------------------------------

type FirstOrderScheme = SchematicForm AtomicPredicate
                                      FirstOrderConnectives --boolean connectives
                                      FirstOrderQuantifiers --no quantifiers
                                      FunctionSymbol --basic function symbols
                                      Referent --semantic values are referents
                                      ()  --schematic sentences aren't meaningful

instance PropositionalConstants FirstOrderScheme where
        prop s = S_ConstantFormBuilder (SentenceVal s)

instance UnaryPredicateConstants FirstOrderScheme FirstOrderTermScheme where 
        pred s = S_UnaryPredicate (AtomicUnary s)

instance BinaryPredicateConstants FirstOrderScheme FirstOrderTermScheme where
        rel s = S_BinaryPredicate (AtomicBinary s) 

instance EqualityConstant FirstOrderScheme FirstOrderTermScheme where
        equals = S_BinaryPredicate Equality

instance ExistentialQuantifiers FirstOrderScheme FirstOrderTerm where
        eb = S_Bind Existential

instance UniversalQuantifiers FirstOrderScheme FirstOrderTerm where
        ub = S_Bind Universal

instance S_PropositionalConstants FirstOrderScheme where
        phi n = S_ConstantSchematicFormBuilder (ConstantFormVar $ "φ_" ++ show n) 

instance S_UnaryPredicateConstants FirstOrderScheme FirstOrderTermScheme where
        phi1 n = S_UnarySchematicPredicate (UnaryPredVar $ "φ^1_" ++ show n) 

instance S_BinaryPredicateConstants FirstOrderScheme FirstOrderTermScheme where
        phi2 n = S_BinarySchematicPredicate (BinaryPredVar $ "φ^2_" ++ show n) 

instance PropositionalContexts FirstOrderScheme where
    propContext n = S_UnarySchematicConnect $ UnaryConnectVar $ "Φ_" ++ show n

instance BooleanLanguage FirstOrderScheme where
        lneg = S_UnaryConnect Not
        land = S_BinaryConnect And
        lor = S_BinaryConnect Or
        lif = S_BinaryConnect If
        liff = S_BinaryConnect Iff

type FirstOrderTermScheme = SchematicTerm AtomicPredicate                               
                                          FirstOrderConnectives --boolean connectives   
                                          FirstOrderQuantifiers --no quantifiers        
                                          FunctionSymbol --Basic Function Symbols
                                          Referent --semantic values are referents      
                                          () ---schematic terms aren't meaningful

instance IndividualConstants FirstOrderTermScheme where
        cn s = S_ConstantTermBuilder (Entity s)

instance S_IndividualConstants FirstOrderTermScheme where
        tau n = S_ConstantSchematicTermBuilder (ConstantTermVar $ "τ_" ++ show n)

instance FreeVariables FirstOrderTermScheme where
        freeVarn n = S_BlankTerm $ "*_" ++ show n

type Qvar = Var AtomicPredicate
                FirstOrderConnectives 
                FirstOrderQuantifiers 
                FunctionSymbol 
                Referent --semantic values are referents
                ()  --sentences aren't meaningful

type QItem = SSequentItem AtomicPredicate
                          FirstOrderConnectives
                          FirstOrderQuantifiers 
                          FunctionSymbol 
                          Referent

instance S_PropositionalConstants QItem where
    phi n = SeqList [phi n]

instance SItemConstants QItem where
    delta n = SeqVar (SideForms $ "Δ_" ++ show n)

instance S_NextVar Referent FirstOrderQuantifiers where
        s_appropriateVariable f _ = "x_" ++ show (1 + s_maxBlankForm f)

folMatch :: FirstOrderScheme -> FirstOrderScheme -> Either (MatchError (Qvar FirstOrderScheme) FirstOrderScheme) [Subst Qvar] 
folMatch = patternMatch

--------------------------------------------------------
--3. Helper Functions and Instances
--------------------------------------------------------

class GatherConstants a where 
        constants :: a -> [FirstOrderTermScheme]

--XXX:this is pretty obviously prime for some kind of composOp simplification.
instance GatherConstants FirstOrderScheme where
        constants (S_ConstantFormBuilder _) = []
        constants (S_ConstantSchematicFormBuilder _) = []
        constants (S_BlankForm) = []
        constants (S_UnaryConnect _ f) = constants f
        constants (S_UnarySchematicConnect _ f) = constants f
        constants (S_BinaryConnect _ f1 f2) = constants f1 ++ constants f2
        constants (S_BinarySchematicConnect _ f1 f2) = constants f1 ++ constants f2
        constants (S_UnaryPredicate _ t) = constants t
        constants (S_UnarySchematicPredicate _ t) = constants t
        constants (S_BinaryPredicate _ t1 t2) = constants t1 ++ constants t2
        constants (S_BinarySchematicPredicate _ t1 t2) = constants t1 ++ constants t2
        constants (S_Bind _ f) = constants (f $ BlankTerm "*")
        constants (S_SchematicBind _ f) = constants (f $ BlankTerm "*")

instance GatherConstants FirstOrderTermScheme where
        constants (S_UnaryFuncApp _ t) = constants t
        constants (S_UnarySchematicFuncApp _ t) = constants t
        constants (S_BinaryFuncApp _ t1 t2) = constants t1 ++ constants t2
        constants (S_BinarySchematicFuncApp _ t1 t2) = constants t1 ++ constants t2
        constants (S_BlankTerm _) = []
        constants t@(S_ConstantTermBuilder _) = [t]
        constants (S_ConstantSchematicTermBuilder _) = []

instance GatherConstants QItem where
        constants (SeqList l) = concatMap constants l
        constants (SeqVar _) = []

instance GatherConstants a => GatherConstants [a] where
        constants = concatMap constants 

instance UniformlyEquaitable Nothing where 
        eq = (=*)

s_maxBlankTerm :: SchematicTerm pred con FirstOrderQuantifiers f Referent () -> Int
s_maxBlankTerm (S_BlankTerm (_:_:n)) = read n
s_maxBlankTerm (S_UnaryFuncApp _ t)  = s_maxBlankTerm t
s_maxBlankTerm (S_BinaryFuncApp _ t1 t2)  = s_maxBlankTerm t1 `max` s_maxBlankTerm t2
s_maxBlankTerm node                  = composOpFold 0 max s_maxBlankTerm node

--this one is, for some reason, hard to implement with composOpFold or other lens-tech
s_maxBlankForm :: SchematicForm pred con FirstOrderQuantifiers f Referent a -> Int
s_maxBlankForm (S_Bind _ f) = s_maxBlankForm (f $ BlankTerm "*")
s_maxBlankForm (S_SchematicBind _ f) = s_maxBlankForm (f $ BlankTerm "*")
s_maxBlankForm (S_UnaryConnect _ f) = s_maxBlankForm f
s_maxBlankForm (S_UnarySchematicConnect _ f) = s_maxBlankForm f
s_maxBlankForm (S_BinaryConnect _ f g) = s_maxBlankForm f `max` s_maxBlankForm g
s_maxBlankForm (S_BinarySchematicConnect _ f g) = s_maxBlankForm f `max` s_maxBlankForm g
s_maxBlankForm (S_UnaryPredicate _ f) = s_maxBlankTerm f
s_maxBlankForm (S_UnarySchematicPredicate _ f) = s_maxBlankTerm f
s_maxBlankForm (S_BinaryPredicate _ f g) = s_maxBlankTerm f `max` s_maxBlankTerm g
s_maxBlankForm (S_BinarySchematicPredicate _ f g) = s_maxBlankTerm f `max` s_maxBlankTerm g
s_maxBlankForm _ = 0

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

--XXX: This is a lens-like operation, and it would be more elegant to
--replace this use with an appropriate instance of multiplated, or with
--some kind of type-spanning lens
substitute :: FirstOrderFormula -> FirstOrderTerm -> FirstOrderTerm -> FirstOrderFormula
substitute (BlankForm s) _ _ = BlankForm s
substitute (ConstantFormBuilder s) _ _ = ConstantFormBuilder s
substitute s@(UnaryPredicate p@(AtomicUnary _) t) t1 t2 = UnaryPredicate p (substitute_t t t1 t2) 
substitute s@(BinaryPredicate p@(AtomicBinary _) t t') t1 t2 = BinaryPredicate p (substitute_t t t1 t2) (substitute_t t' t1 t2)
substitute (UnaryConnect Not f) t1 t2 = UnaryConnect Not (substitute f t1 t2) 
substitute (BinaryConnect Or f1 f2) t1 t2 = BinaryConnect Or (substitute f1 t1 t2) (substitute f2 t1 t2)
substitute (BinaryConnect And f1 f2) t1 t2 = BinaryConnect And (substitute f1 t1 t2) (substitute f2 t1 t2)
substitute (BinaryConnect If f1 f2) t1 t2 = BinaryConnect If (substitute f1 t1 t2) (substitute f2 t1 t2)
substitute (BinaryConnect Iff f1 f2) t1 t2 = BinaryConnect Iff (substitute f1 t1 t2) (substitute f2 t1 t2)
substitute (Bind Universal f) t1 t2 = Bind Universal (\x -> substitute (f x) t1 t2)
substitute (Bind Existential f) t1 t2 = Bind Existential (\x -> substitute (f x) t1 t2)

substitute_t :: FirstOrderTerm -> FirstOrderTerm -> FirstOrderTerm -> FirstOrderTerm
substitute_t t@(UnaryFuncApp f@(UnaryFS _) t') t1 t2 = if t == t1 then t2 else UnaryFuncApp f (substitute_t t' t1 t2)
substitute_t t@(BinaryFuncApp f@(BinaryFS _) t' t'') t1 t2 = if t == t1 then t2 else BinaryFuncApp f (substitute_t t' t1 t2) (substitute_t t'' t1 t2)
substitute_t t t1 t2 = if t == t1 then t2 else t

-- instance MultiPlated FirstOrderFormula FirstOrderTerm where
--     multiplate = undefined

--this should work assuming the above are implemented
--also I think this is a generic function over any multiplated thing where the child type implements Eq!!
--so like everything basically
-- substitute' :: FirstOrderFormula -> FirstOrderTerm -> FirstOrderTerm -> FirstOrderFormula
-- substitute' node t1 t2 = rewriteOnOf multiplate id replace node
--     where replace c | c == t1   = Just t2
--                     | otherwise = Nothing
