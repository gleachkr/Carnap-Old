{-#LANGUAGE GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, RankNTypes, FunctionalDependencies #-}

module Unification where

import qualified Data.Map as Map
import qualified Data.Set as Set

--testing code
import Test.QuickCheck
import Test.QuickCheck.Property

type Subst = Map.Map
type Set = Set.Set

class (Show var, Show t, Eq t, Eq var, Ord var) => Types var t | t -> var where
  ftv :: t -> Set var
  apply ::  Subst var t -> t -> t

class Types var t => Unifiable var t | t -> var where
  match :: t -> t -> Maybe [(t, t)]
  matchVar :: t -> t -> Maybe (var, t)
  makeTerm :: var -> t

--these are things that can't quite be unified but contain things that can be
--for instance proofs can be "unified" with proof sketches to see if they match up
--however the varibles are in the 
class Unifiable var t' => CompositeUnifiable var t' t | t -> var t' where
  matchParts :: t -> t -> Maybe [(t', t')]
  applySub :: Subst var t' -> t -> t

x ... y = (Map.map (apply y) x) `Map.union` y

data UnificationError var t where
    UnableToUnify :: Show t => t -> t -> UnificationError var t
    SubError :: (Show var, Show t', Show t) => UnificationError var t' -> t -> t -> UnificationError var t
    OccursCheck :: (Show var, Show t) => var -> t -> UnificationError var t

instance Show (UnificationError var t) where
    show (UnableToUnify a b) = "Unable to unify " ++ show a ++ " with " ++ show b
    show (SubError err a b)  = "When matching " ++ show a ++ " with " ++ show b ++ ",\n" ++ show err
    show (OccursCheck v t)   = "Cannot construct infinite type " ++ show v ++ " = " ++ show t

(Left x) .<. f = Left (f x)
e        .<. f = e

(Right x) .>. f = Right (f x)
e         .>. f = e

--maps a function over like pairs of things
pmap f = map (\(x, y) -> (f x, f y)) 

occursCheck :: (Unifiable var t) => var -> t -> Either (Subst var t) (UnificationError var t)
occursCheck v sub | makeTerm v == sub            = Left $ Map.empty
occursCheck v sub | not $ Set.member v (ftv sub) = Left $ Map.singleton v sub
occursCheck v sub                                = Right $ OccursCheck v sub

unify :: (Show var, Show t, Unifiable var t) => t -> t -> Either (Subst var t) (UnificationError var t)
unify a b = case (matchVar a b, matchVar b a) of
  (Just (v, sub), _) -> occursCheck v sub
  (_, Just (v, sub)) -> occursCheck v sub
  _                -> case match a b of
    Just    children -> unifyChildren children
    Nothing          -> Right $ UnableToUnify a b
  where unifyChildren ((x, y):xs) = case unify x y of
          Left  sub -> (unifyChildren $ pmap (apply sub) xs) .<. (... sub) .>. (\e -> SubError e x y)
          Right err -> Right (SubError err x y)
        unifyChildren [] = Left $ Map.empty

--testing
data TestTerm = Constructor String [TestTerm]
              | FreeVar String
    deriving(Show, Eq, Ord)

projectFreeVar (FreeVar x) = Just $ x
projectFreeVar _           = Nothing
    
instance Types String TestTerm where
  ftv (Constructor s ps) = foldr (Set.union . ftv) Set.empty ps
  ftv (FreeVar nm)       = Set.singleton nm

  apply sub (Constructor s ps) = Constructor s (map (apply sub) ps)
  apply sub (FreeVar nm)       = case Map.lookup nm sub of
      Just t  -> apply sub t --recursivlly apply the substitution to make sure nothing gets passed us
      Nothing -> FreeVar nm

instance Unifiable String TestTerm where
  match (Constructor a xs) (Constructor b ys) 
      | a == b && (length xs == length ys)  = Just $ zip xs ys
  match (FreeVar a)        _           = Just []
  match _                  (FreeVar a) = Just []
  match _                  _           = Nothing

  matchVar (FreeVar a) x = Just $ (a, x)
  matchVar _           _ = Nothing

  makeTerm = FreeVar

instance Arbitrary TestTerm where
    arbitrary     = do
       (s, n) <- oneof $ map return [("P", 2), ("S", 1), ("Cons", 2), ("->", 2), ("0", 0), ("Nil", 0), ("t", 0)]
       children <- vector n
       v <- oneof $ map return ["A", "B", "C", "D", "E"]
       oneof $ map return [FreeVar v, Constructor s children]

    shrink (FreeVar v) = []
    shrink (Constructor s children) = children ++ (concatMap shrink children)

--the fact that these two properties are satisfied so well makes be belive that the unification code works well
unifyProp :: (TestTerm, TestTerm) -> Bool
unifyProp (a, b) = case unify a b of
  Left sub -> (apply sub a) == (apply sub b)
  Right _  -> True

x `implies` y = not x || y

unifySame :: TestTerm -> Bool
unifySame a = (ftv a == Set.empty) `implies` case unify a a of
  Left sub -> sub == Map.empty
  Right _  -> False

args = Args {replay = Nothing, chatty = True, maxSuccess = 10000, maxDiscardRatio = 3, maxSize = 20}
testUnifyProp = quickCheckWith args unifyProp
testUnifySame = quickCheckWith args unifySame
