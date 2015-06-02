{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes #-}

import Carnap.Core.Unification.HigherOrderPatternMatching
import Carnap.Core.Unification.HigherOrderUtilLens
--for automatic testing
import Test.QuickCheck
import Test.QuickCheck.Property
--for some list things
import Data.List
--needed for HigherOrderUtil
import Control.Lens
import Control.Applicative

--------------------------------------------------------
--1. Define the types involved
--------------------------------------------------------

data SchemaTerm = SConstant String
                | SFunction String [SchemaTerm]
                | HConstant String
                | HFunction String [SchemaTerm]
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
instance Plated Term where
   plate f (Constant c)       = (const $ Constant c) <$> traverse f []
   plate f (Function g terms) = (Function g) <$> traverse f terms

--we are going to need this so that we can use HigherOrderUtil
instance Plated SchemaTerm where
   plate f (SConstant c)       = (const $ SConstant c) <$> traverse f []
   plate f (SFunction g terms) = (SFunction g) <$> traverse f terms
   plate f (HConstant c)       = (const $ HConstant c) <$> traverse f []
   plate f (HFunction g terms) = (HFunction g) <$> traverse f terms

--defines how to get free varibles and how to perform substiutions
instance Hilbert SchemaTerm Var where
    freeVars (SConstant s)       = [FreeVar (Var s)]
    freeVars (SFunction s terms) = [FreeVar (Var s)] `union` (bigUnion terms freeVars)
    freeVars (HConstant _)       = []
    freeVars (HFunction s terms) = bigUnion terms freeVars
    apply sub (SConstant s)       = case fvMapLookup (Var s) sub of
        Just (LambdaMapping s' [] subst) -> coerceUnknown' s' subst
        Nothing -> SConstant s
    apply sub (SFunction v terms) = case fvMapLookup (Var v) sub of
        Just (LambdaMapping v' fvs subst) -> apply (zipLamMapping fvs newTerms) (coerceUnknown' v' subst)
        Nothing -> SFunction v newTerms
        where newTerms = map (apply sub) terms
    apply sub (HConstant s)       = HConstant s
    apply sub (HFunction s terms) = HFunction s (map (apply sub) terms)

--in real cases you would generate unique names
--here I reserve these names for use in lambdas
cheatVars = map Var ["alpha", "beta", "delta", "gamma", "eta"]

--finally we need a few more helper terms to define how pattern matching works
instance Matchable Term SchemaTerm Var where
    match (SConstant _) _   = Just []
    match (SFunction _ _) _ = Just []
    match (HConstant a) (Constant b) | a == b = Just []
    match (HFunction f t1) (Function g t2) | f == g = Just $ (map convertPair $ zip t1 t2)
        where convertPair (s, c) = Pairing s c
    match _ _ = Nothing
    matchVar (SConstant v)       c = [LambdaMapping (Var v) [] (toSchema c)]
    matchVar (SFunction f terms) c = makeSub (Var f) (zip cheatVars terms) c --I love this, it is typed perfectly
    matchVar _                   _ = []
    makeTerm (Var v) = SConstant v
    toSchema (Constant c)       = HConstant c
    toSchema (Function f terms) = HFunction f (map toSchema terms)


--------------------------------------------------------
--3 Helpers for manual testing
--------------------------------------------------------
ff = SFunction "F"
gg = SFunction "G"
hh = SFunction "H"
kk = SFunction "K"
aa = SConstant "A"
bb = SConstant "B"
cc = SConstant "C"
dd = SConstant "D"
f = Function "f"
g = Function "g"
h = Function "h"
k = Function "k"
a = Constant "a"
b = Constant "b"
c = Constant "c"
x = Constant "x"
y = Constant "y"
z = Constant "z"
fs = HFunction "f"
gs = HFunction "g"
hs = HFunction "h"
as = HConstant "a"
bs = HConstant "b"
cs = HConstant "c"

instance Show (Pairing Var) where
    show (Pairing s c) = show (s, c)

--------------------------------------------------------
--4 Quick check stuff
--------------------------------------------------------

instance Arbitrary Term where
    arbitrary = do
        arg1 <- arbitrary
        arg2 <- arbitrary
        f <- oneof $ map return [f[arg1], g[arg1, arg2], h[arg2], k[arg2, arg1]]
        a <- oneof $ map return [a, b, c, x, y, z]
        oneof $ map return [f, f, a, a]

    shrink (Function f terms) = terms ++ (concatMap shrink terms)
    shrink (Constant c)       = []

instance Arbitrary SchemaTerm where
    arbitrary = do
        arg1 <- arbitrary
        arg2 <- arbitrary
        f <- oneof $ map return [fs[arg1], gs[arg1, arg2], hs[arg2], ff[arg1], gg[arg1, arg2], hh[arg2], kk[arg2, arg1]]
        a <- oneof $ map return [aa, bb, cc, dd, as, bs, cs]
        oneof $ map return [f, f, f, a, a]

    shrink (SFunction f terms) = terms ++ (concatMap shrink terms)
    shrink (HFunction f terms) = terms ++ (concatMap shrink terms)
    shrink (SConstant c)       = []
    shrink (HConstant c)       = []

--------------------------------------------------------
--5 Testing
--------------------------------------------------------

checkError :: Matchable concrete schema var => MatchError (var schema) schema -> Bool
checkError (UnableToMatch s c) = case match s c of
    Nothing -> True
    Just _  -> False
checkError (ErrWrapper sub) = checkError sub
checkError (SubError sub s c) = case match s c of
    Nothing -> False
    Just _  -> checkError sub
checkError _ = False

unifyProp :: (Int, SchemaTerm, Term) -> Bool
unifyProp (idx, a, b) = case patternMatch a b of
  Left []  -> a == (toSchema b)
  Left subs -> (apply (subs !! ((abs idx) `mod` length subs)) a) == (toSchema b)
  Right err -> checkError err

args = Args {replay = Nothing, chatty = True, maxSuccess = 1000, maxDiscardRatio = 3, maxSize = 5}
--veryify both of the properties
testUnifyProp = quickCheckWith args (within 10000000 unifyProp)

