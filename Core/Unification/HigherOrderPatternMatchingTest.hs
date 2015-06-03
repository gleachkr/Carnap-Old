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

data SchemaFormula = HConnective String [SchemaFormula]
                   | SPredicate String [SchemaTerm]
                   | HPredicate String [SchemaTerm]
    deriving(Eq)

trim1 = init . tail

instance Show SchemaTerm where
    show (SConstant s)       = s
    show (SFunction s terms) = s ++ "(" ++ (trim1 $ show terms) ++ ")"
    show (HConstant s)       = s
    show (HFunction s terms) = s ++ "(" ++ (trim1 $ show terms) ++ ")"   

instance Show SchemaFormula where
    show (HConnective s [t]) = s ++ show t
    show (HConnective s [t1, t2]) = "(" ++ show t1 ++ s ++ show t2 ++ ")"
    show (HConnective s terms) = s ++ "(" ++ (trim1 $ show terms) ++ ")"
    show (SPredicate s terms) = s ++ "(" ++ (trim1 $ show terms) ++ ")"
    show (HPredicate s terms) = s ++ "(" ++ (trim1 $ show terms) ++ ")" 

data Term = Constant String
          | Function String [Term]
    deriving(Eq)

data Formula = Connective String [Formula]
             | Predicate String [Term]
    deriving(Eq)

instance Show Term where
    show (Constant s)       = s
    show (Function s terms) = s ++ "(" ++ (trim1 $ show terms) ++ ")"

instance Show Formula where
    show (Connective s [t])  = s ++ show t
    show (Connective s [t1, t2])  = "(" ++ show t1 ++ s ++ show t2 ++ ")"
    show (Connective s terms)  = s ++ "(" ++ (trim1 $ show terms) ++ ")"
    show (Predicate s terms) = s ++ "(" ++ (trim1 $ show terms) ++ ")"

data Var a where
    Var :: String -> Var SchemaTerm
    FVar :: String -> Var SchemaFormula

instance Show (Var a) where
    show (Var s) = s
    show (FVar s) = s

instance EquaitableVar Var where
  --turns the schema' into a schema if the varibles are equal
  getLikeSchema (Var v)  (Var v')  s' = if v == v' then Just s' else Nothing
  getLikeSchema (FVar v) (FVar v') s' = if v == v' then Just s' else Nothing
  getLikeSchema _        _         _  = Nothing

--------------------------------------------------------
--2.1 Define some helpers
--------------------------------------------------------

bigUnion l f = foldl union [] (map f l)

--unsafe cast but it seems like I need it
coerceUnknown :: Var unknown -> Var SchemaTerm
coerceUnknown (Var v) = Var v

--unsafe cast but it seems like I need it
coerceFormula :: Var unknown -> Var SchemaFormula
coerceFormula (FVar v) = FVar v

coerceUnknown' :: Var unknown -> unknown -> SchemaTerm
coerceUnknown' (Var v) s = s

--pre-condition: lists are of same length and all free vars can be coerced
--zipLamMapping :: [FreeVar Var] -> [SchemaTerm] -> [Mapping Var]
--note that the use of this explicitllay limits us to second order matching
--third order matching would require substitutions with varibles here
zipTermLamMapping ((FreeVar v):vs) (s:ss) = (LambdaMapping (coerceUnknown v) [] s) : zipTermLamMapping vs ss
zipTermLamMapping []               []     = []

--zipFormulaLamMapping ((FreeVar v):vs) (s:ss) = (LambdaMapping (coerceFormula v) [] s) : zipLamMapping vs ss
--zipFormulaLamMapping []               []     = []

--------------------------------------------------------
--2.2 Define the type classes for plating
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

--we are going to need this so that we can use HigherOrderUtil
instance Plated Formula where
   plate f (Connective c terms) = (Connective c) <$> traverse f terms
   plate f (Predicate g terms)  = (const $ Predicate g terms) <$> traverse f []

--we are going to need this so that we can use HigherOrderUtil
instance Plated SchemaFormula where
   plate f (HConnective c terms) = (HConnective c) <$> traverse f terms
   plate f (HPredicate c terms)  = (const $ HPredicate c terms) <$> traverse f []
   plate f (SPredicate c terms)  = (const $ SPredicate c terms) <$> traverse f []

instance MultiPlated Formula Term where
   multiplate f (Connective c terms) = (Connective c) <$> (traverse . multiplate) f terms
   multiplate f (Predicate c terms) = (Predicate c) <$> traverse f terms

instance MultiPlated SchemaFormula SchemaTerm where
   multiplate f (HConnective c terms) = (HConnective c) <$> (traverse . multiplate) f terms
   multiplate f (SPredicate c terms) = (SPredicate c) <$> traverse f terms
   multiplate f (HPredicate c terms) = (HPredicate c) <$> traverse f terms

--------------------------------------------------------
--2.3 Define the type classes for matching
--------------------------------------------------------

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
        Just (LambdaMapping v' fvs subst') -> case getLikeSchema (Var v) v' subst' of
            Just subst -> apply (zipTermLamMapping fvs newTerms) subst
            Nothing -> SFunction v newTerms
        Nothing -> SFunction v newTerms
        where newTerms = map (apply sub) terms
    apply sub (HConstant s)       = HConstant s
    apply sub (HFunction s terms) = HFunction s (map (apply sub) terms)

instance Hilbert SchemaFormula Var where
    freeVars (HConnective s terms) = bigUnion terms freeVars
    freeVars (SPredicate s terms) = bigUnion terms freeVars
    freeVars (HPredicate s terms) = bigUnion terms freeVars

    apply sub (HConnective s terms) = HConnective s (map (apply sub) terms)
    apply sub (SPredicate v terms) = case fvMapLookup (FVar v) sub of
        Just (LambdaMapping v' fvs subst') -> case getLikeSchema (FVar v) v' subst' of
            Just subst -> apply (zipTermLamMapping fvs newTerms) subst
            Nothing -> SPredicate v newTerms
        Nothing -> SPredicate v newTerms
        where newTerms = map (apply sub) terms
    apply sub (HPredicate s terms) = HPredicate s (map (apply sub) terms)

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

--finally we need a few more helper terms to define how pattern matching works
instance Matchable Formula SchemaFormula Var where
    match (HConnective s t1) (Connective s' t2) | s == s' = Just $ (map convertPair $ zip t1 t2)
        where convertPair (s, c) = Pairing s c
    match (SPredicate _ _)    _                           = Just []
    match (HPredicate s t1) (Predicate s' t2) | s == s'   = Just $ (map convertPair $ zip t1 t2)
        where convertPair (s, c) = Pairing s c
    match _                 _                             = Nothing
    
    matchVar (SPredicate p terms) c = makeSub (FVar p) (zip cheatVars terms) c
    matchVar _                    _ = []

    --this is awkward for this case. it makes a tiny degree of sense elsewhere but not here
    --in fact this may make no sense elsewhere. I might factor this out
    --it *does* need to be used for makeSub in the sub-types but not on this type
    makeTerm (FVar v) = SPredicate v []

    toSchema (Connective c terms) = HConnective c (map toSchema terms)
    toSchema (Predicate p terms)  = HPredicate p (map toSchema terms)

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
pp = SPredicate "P"
qq = SPredicate "Q"
rr = SPredicate "R"
ps = HPredicate "p"
qs = HPredicate "q"
r = Predicate "r"
p = Predicate "p"
q = Predicate "q"
rs = HPredicate "r"
x .-> y = Connective "->" [x, y]
x .->. y = HConnective "->" [x, y]
x .^ y = Connective "&" [x, y]
x .^. y = HConnective "&" [x, y]
x `v` y = Connective "v" [x, y]
x `sv` y = HConnective "v" [x, y]
neg x = Connective "~" [x]
sneg x = HConnective "~" [x]

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
        oneof $ map return [f, f, a, a, a]

    shrink (Function f terms) = terms ++ (concatMap shrink terms)
    shrink (Constant c)       = []

instance Arbitrary SchemaTerm where
    arbitrary = do
        arg1 <- arbitrary
        arg2 <- arbitrary
        f <- oneof $ map return [fs[arg1], gs[arg1, arg2], hs[arg2], ff[arg1], gg[arg1, arg2], hh[arg2], kk[arg2, arg1]]
        a <- oneof $ map return [aa, bb, cc, dd, as, bs, cs]
        oneof $ map return [f, a, a, a]

    shrink (SFunction f terms) = terms ++ (concatMap shrink terms)
    shrink (HFunction f terms) = terms ++ (concatMap shrink terms)
    shrink (SConstant c)       = []
    shrink (HConstant c)       = []

instance Arbitrary SchemaFormula where
    arbitrary = do
        arg1 <- arbitrary
        arg2 <- arbitrary
        f1 <- arbitrary
        f2 <- arbitrary
        f <- oneof $ map return [pp[arg1], qq[arg2], rr[arg1, arg2]]
        c <- oneof $ map return [f1 .^. f2, f1 `sv` f2, sneg f1]
        a <- oneof $ map return [ps[arg1], qs[arg2], rs[arg1, arg2]]
        oneof $ map return [f, f, c, a, a]

    shrink (HConnective f terms) = terms ++ (concatMap shrink terms)
    shrink (SPredicate p terms) = map (SPredicate p) (transpose $ map shrink terms)
    shrink (HPredicate p terms) = map (HPredicate p) (transpose $ map shrink terms)

instance Arbitrary Formula where
    arbitrary = do
        arg1 <- arbitrary
        arg2 <- arbitrary
        f1 <- arbitrary
        f2 <- arbitrary
        f <- oneof $ map return [p[arg1], q[arg2], r[arg1, arg2]]
        c <- oneof $ map return [f1 .^ f2, f1 `v` f2, neg f1]
        oneof $ map return [f, c, f]

    shrink (Connective f terms) = terms ++ (concatMap shrink terms)
    shrink (Predicate p terms) = map (Predicate p) (transpose $ map shrink terms)

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

--ensures that all returned substitutions are valid
--and that if there is an error there is some evidence of it
--granted match errors are kinda broken
unifyProp :: (Int, SchemaFormula, Formula) -> Bool
unifyProp (idx, a, b) = case patternMatch a b of
  Left []  -> a == (toSchema b)
  Left subs -> (apply (subs !! ((abs idx) `mod` length subs)) a) == (toSchema b)
  Right err -> checkError err

args = Args {replay = Nothing, chatty = True, maxSuccess = 1000, maxDiscardRatio = 3, maxSize = 3}
--veryify both of the properties
testUnifyProp = quickCheckWith args (within 1000000 unifyProp)

main = do
    print $ patternMatch (rr[bb]) (r[b])