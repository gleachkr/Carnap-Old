{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes #-}

import Carnap.Core.Unification.HigherOrderPatternMatching
import Carnap.Core.Unification.HigherOrderUtilLens
--for automatic testing
import Test.QuickCheck
import Test.QuickCheck.Property
--for some list things
import Data.List

--------------------------------------------------------
--1. Define the types involved
--------------------------------------------------------

data SchemaTerm = SConstant String
                | SFunction String [SchemaTerm]
                | HConstant String
                | HFunction String [SchemaTerm]
                | Choice [SchemaTerm]
    deriving(Eq)

trim1 = init . tail

instance Show SchemaTerm where
    show (SConstant s)       = s
    show (SFunction s terms) = s ++ "(" ++ (trim1 $ show terms) ++ ")"
    show (HConstant s)       = s
    show (HFunction s terms) = s ++ "(" ++ (trim1 $ show terms) ++ ")"   

data Term = Constant String
          | Function String [Term]
    deriving(Eq)

instance Show Term where
    show (Constant s)       = s
    show (Function s terms) = s ++ "(" ++ (trim1 $ show terms) ++ ")"

data Var a where
    Var :: String -> Var SchemaTerm

instance Show (Var a) where
    show (Var s) = s

instance EquaitableVar Var where
  --turns the schema' into a schema if the varibles are equal
  getLikeSchema (Var v) (Var v') s' = if v == v' then Just s' else Nothing

--------------------------------------------------------
--2.1 Define some helpers
--------------------------------------------------------

bigUnion l f = foldl union [] (map f l)

coerceUnknown :: Var unknown -> Var SchemaTerm
coerceUnknown (Var v) = Var v

coerceUnknown' :: Var unknown -> unknown -> SchemaTerm
coerceUnknown' (Var v) s = s 

--pre-condition: lists are of same length and all free vars can be coerced
--zipLamMapping :: [FreeVar Var] -> [SchemaTerm] -> [Mapping Var]
zipLamMapping ((FreeVar v):vs) (s:ss) = (LambdaMapping (coerceUnknown v) [] s) : zipLamMapping vs ss
zipLamMapping []               []     = []

--------------------------------------------------------
--2.2 Define the type classes
--------------------------------------------------------

--we are going to need this so that we can use HigherOrderUtil
instance Plated Expr where
   plate f (Neg e) = Neg <$> f e
   plate f (Add a b) = Add <$> f a <*> f b
   plate _ a = pure a

--defines how to get free varibles and how to perform substiutions
instance Hilbert SchemaTerm Var where
    freeVars (SConstant s)       = [FreeVar (Var s)]
    freeVars (SFunction s terms) = [FreeVar (Var s)] `union` (bigUnion terms freeVars)
    freeVars (HConstant _)       = []
    freeVars (HFunction s terms) = bigUnion terms freeVars
    freeVars (Choice terms)      = bigUnion terms freeVars

    apply sub (SConstant s)       = case fvMapLookup (Var s) sub of
        Just (LambdaMapping s' [] subst) -> coerceUnknown' s' subst
        Nothing -> SConstant s
    apply sub (SFunction v terms) = case fvMapLookup (Var v) sub of
        Just (LambdaMapping v' fvs subst) -> apply (zipLamMapping fvs terms) (coerceUnknown' v' subst)
        Nothing -> SFunction v terms
    apply sub (HConstant s)       = HConstant s
    apply sub (HFunction s terms) = HFunction s (map (apply sub) terms)
    apply sub (Choice terms)      = Choice (map (apply sub) terms)

--in real cases you would generate unique names
--here I reserve these names for use in lambdas
cheatVars = ["A", "B", "C", "D", "X", "Y", "Z"]

--finally we need a few more helper terms to define how pattern matching works
instance Matchable Term SchemaTerm Var where
    match (SConstant _) _   = Just []
    match (SFunction _ _) _ = Just []
    match (HConstant a) (Constant b) | a == b = Just []
    match (HFunction f t1) (Function g t2) | f == g = Just $ (map convertPair $ zip t1 t2)
        where convertPair (s, c) = Pairing s c

    matchVar (SConstant v) c       = Just $ LambdaMapping (Var v) [] (toSchema c)
    matchVar (SFunction f terms) c = 

    makeTerm = undefined
    toSchema = undefined
    makeChoice = undefined




