{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes #-}

import MultiUnification
--for automatic testing
import Test.QuickCheck
import Test.QuickCheck.Property
--for union
import Data.List

--------------------------------------------------------
--6. Define an example
--------------------------------------------------------

--define a data type for simply typed lambda calculus
--eventully we will perform multi unification
data Var t where
    TermVar :: String -> Var Term
    TypeVar :: String -> Var Type

--define some instances real quick for varibles
instance Show (Var a) where
    show (TermVar s) = s
    show (TypeVar s) = s

instance EquaitableVar Var where
    getLikeSchema (TermVar s) (TermVar s') t | s == s' = Just t
    getLikeSchema (TypeVar s) (TypeVar s') t | s == s' = Just t
    getLikeSchema _           _            _           = Nothing

instance Eq (Var schmea) where
	v1 == v2 = eq v1 v2

--instance Eq (Var a) where
  --  (TermVar s) == (TermVar s') = s == s'
   -- (TypeVar s) == (TypeVar s') = s == s'
    --_           == _            = False

--instance UniformlyEquaitable Var where
  --  eq (TermVar s) (TermVar s') = s == s'
    --eq (TypeVar s) (TypeVar s') = s == s'
    --eq _           _            = False

--now define the actual language terms

--these are simple types
data Type = Type :-> Type
          | BasicType String
          | TyVar (Var Type)
    deriving(Eq, Show)

--and these are simply typed lambda terms
data Term = Lam String Type Term
          | Term :$: Term
          | BasicTerm String
          | TmVar (Var Term)
    deriving(Eq, Show)

--------------------------------------------------------
--6.1 Define instances for the lambda terms
--------------------------------------------------------

--first lets do types 
instance MultiMatchable Type Var where
    multiMatch (t1 :-> t1')  (t2 :-> t2') = Just [UnifiablePairing t1 t2, UnifiablePairing t1' t2']
    multiMatch (BasicType a) (BasicType b)
        | a == b = Just []
    multiMatch (TyVar _) _ = Just []
    multiMatch _ (TyVar _) = Just []
    multiMatch _ _         = Nothing

instance MultiHilbert Type Var where
    multiFreeVars (t :-> t')    = (multiFreeVars t) `union` (multiFreeVars t')
    multiFreeVars (BasicType a) = []
    multiFreeVars (TyVar v)     = [FreeVar v]  

    multiApply subst (t :-> t') = (multiApply subst t) :-> (multiApply subst t')
    multiApply subst (TyVar v)  = case fvLookup v subst of
        Just tm -> tm
        Nothing -> TyVar v
    multiApply _     x          = x

instance MultiUnifiable Type Var where
    multiMatchVar (TyVar v) tm = Just $ Mapping v tm
    multiMatchVar tm (TyVar v) = Just $ Mapping v tm
    multiMatchVar _  _         = Nothing

    multiMakeTerm = TyVar

--now lets do terms

instance MultiMatchable Term Var where
    multiMatch (Lam v tau tm) (Lam v' tau' tm') | v == v' = Just [UnifiablePairing tau tau', UnifiablePairing tm tm']
    multiMatch (BasicTerm a)  (BasicTerm b)     | a == b  = Just []
    multiMatch (t1 :$: t1')   (t2 :$: t2')                = Just [UnifiablePairing t1 t2, UnifiablePairing t1' t2']
    multiMatch (TmVar v)      _                           = Just []
    multiMatch _              (TmVar v)                   = Just []
    multiMatch _              _                           = Nothing

instance MultiHilbert Term Var where
    multiFreeVars (t :$: t')    = (multiFreeVars t) `union` (multiFreeVars t')
    multiFreeVars (BasicTerm a) = []
    multiFreeVars (TmVar v)     = [FreeVar v]
    multiFreeVars (Lam _ ty tm) = (multiFreeVars ty) `union` (multiFreeVars tm)

    multiApply subst (Lam v tau tm) = Lam v (multiApply subst tau) (multiApply subst tm)
    multiApply subst (t :$: t')     = (multiApply subst t) :$: (multiApply subst t')
    multiApply subst (TmVar v)      = case fvLookup v subst of
        Just tm -> tm
        Nothing -> TmVar v
    multiApply _     x              = x

--------------------------------------------------------
--7. Testing
--------------------------------------------------------

instance MultiUnifiable Term Var where
    multiMatchVar (TmVar v) tm = Just $ Mapping v tm
    multiMatchVar tm (TmVar v) = Just $ Mapping v tm
    multiMatchVar _  _         = Nothing

    multiMakeTerm = TmVar

instance Arbitrary Type where
    arbitrary = do
        a <- arbitrary
        b <- arbitrary
        n <- oneof $ map return ["a", "b", "c", "t", "t'"]
        fv <- oneof $ map return ["A", "B", "C", "T"]
        oneof $ map return [a :-> b, BasicType n, TyVar $ TypeVar fv]

    shrink (BasicType _) = []
    shrink (TyVar _)     = []
    shrink (a :-> b)     = [a, b] ++ (concatMap shrink [a, b])

instance Arbitrary Term where
    arbitrary = do
        a <- arbitrary
        b <- arbitrary
        t <- arbitrary
        n <- oneof $ map return ["a", "b", "c", "t", "t'"]
        fv <- oneof $ map return ["A", "B", "C", "T"]
        oneof $ map return [a :$: b, BasicTerm n, TmVar $ TermVar fv, Lam n t a]

    shrink (BasicTerm _) = []
    shrink (TmVar _)     = []
    shrink (Lam v ty tm) = [tm] ++ [Lam v ty' tm' | tm' <- shrink tm, ty' <- shrink ty]
    shrink (a :$: b)     = [a, b] ++ (concatMap shrink [a, b])

isNothing Nothing = True
isNothing _       = False

isNotNothing = not . isNothing

--we can test unify further if we check errors
checkError :: (MultiUnifiable schema var) => UnificationError (var schema) schema -> Bool
checkError (UnableToUnify a b) = isNothing $ multiMatch a b --ensure that these things do not match as far as the client says
checkError (ErrWrapper s)      = checkError s --just change types and check if there is an error there
checkError (SubError s a b)    = (isNotNothing $ multiMatch a b) && checkError s --check that there is an error not in this pair but the sub part
checkError (OccursCheck v t)   = v `isMember` (multiFreeVars t) --check that the varible does occur where it should not

-- if sub=unify(x, y) then x(sub) == y(sub)
-- if x and y do not unify then the error should be evidence to the fact
unifyProp :: (Term, Term) -> Bool
unifyProp (a, b) = case unify a b of
  Left sub -> (multiApply sub a) == (multiApply sub b)
  Right err -> checkError err

x `implies` y = not x || y

-- a formula with no free varibles should always unify with itself
-- addtionally it should unify to the empty set
unifySame :: Term -> Bool
unifySame a = (multiFreeVars a == []) `implies` case unify a a of
  Left sub -> case sub of
                  [] -> True
                  (x:xs) -> False
  Right _  -> False

args = Args {replay = Nothing, chatty = True, maxSuccess = 10000, maxDiscardRatio = 3, maxSize = 20}
--veryify both of the properties
testUnifyProp = quickCheckWith args unifyProp
testUnifySame = quickCheckWith args unifySame