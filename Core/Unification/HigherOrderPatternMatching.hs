{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes #-}

module Carnap.Core.Unification.HigherOrderPatternMatching (
	UniformlyEquaitable, eq, neq,
	Pairing(Pairing),
	FreeVar(FreeVar),
	Mapping(LambdaMapping),
	Subst,
	EquaitableVar, getLikeSchema,
	Hilbert, freeVars, apply,
	Matchable, match, matchVar, makeTerm, toSchema,
	MatchError(UnableToMatch, ErrWrapper, SubError, OccursCheck),
	patternMatch, matchChildren,
	fvMapLookup
) where

import Data.List

--------------------------------------------------------
--0. We need some helper classes first
--------------------------------------------------------

--might want to factor this out as it seems like a very useful concept
class UniformlyEquaitable f where
    eq :: f a -> f b -> Bool
    eq x y = not (neq x y)
    neq :: f a -> f b -> Bool
    neq x y = not (eq x y)

--------------------------------------------------------
--1. Define exisitinesal types for homogenous values
--------------------------------------------------------

--allows for sub parts to be paired up for matching
data Pairing var where
    Pairing :: Matchable concrete schema var => schema -> concrete -> Pairing var

--allows for abitrary kinds of varibles
data FreeVar var where
    FreeVar :: (Show (var schema'), UniformlyEquaitable var) => var schema' -> FreeVar var

--like FreeVar except it adds in a schmea' and a list of arguments
--for the old kind of mappings 
data Mapping var where
    LambdaMapping :: (Matchable concrete schema var) => var schema -> [FreeVar var] -> schema -> Mapping var

--just defines a quick alias
type Subst var = [Mapping var]

--define an Eq instance for FreeVar so that we can use union with it
--it just falls back on being uniformly equaitable
instance Eq (FreeVar var) where
    (FreeVar v1) == (FreeVar v2) = eq v1 v2

instance Show (FreeVar var) where
    show (FreeVar v) = show v

instance Show (Mapping var) where
    show (LambdaMapping v [] s) = show v ++ " -> " ++ show s
    show (LambdaMapping v xs s) = show v ++ " -> lam" ++ concatMap ((" " ++) . show) xs ++ ". " ++ show s

--------------------------------------------------------
--2. Define the type classes
--------------------------------------------------------

--this is just to help people out with creating
--code that performs subtititutions
--it is not actully used by the unification code
class EquaitableVar var where
  --turns the schema' into a schema if the varibles are equal
  getLikeSchema :: var schema -> var schema' -> schema' -> Maybe schema

instance EquaitableVar var => UniformlyEquaitable var where
  eq v1 v2 = case getLikeSchema v1 v2 undefined of
      Just _  -> True  --do not evaluate the argument of this
      Nothing -> False

--defines how to get free varibles and how to perform substiutions
class (UniformlyEquaitable var, Show (var schema), Eq schema, Show schema) => Hilbert schema var | schema -> var where
    freeVars :: schema -> [FreeVar var]
    apply :: Subst var -> schema -> schema

--finally we need a few more helper terms to define how pattern matching works
class (Hilbert schema var, Show concrete, Eq concrete) => Matchable concrete schema var | schema -> var concrete where
    match :: schema -> concrete -> Maybe [Pairing var]
    matchVar :: schema -> concrete -> [Mapping var]
    makeTerm :: var schema -> schema
    toSchema :: concrete -> schema

--------------------------------------------------------
--3. Unification errors
--------------------------------------------------------

data MatchError var schema where
    UnableToMatch :: (Matchable concrete schema var, Show schema, Show concrete) => schema -> concrete -> MatchError (var schema) schema
    ErrWrapper :: Matchable concrete schema' var => MatchError (var schema') schema' -> MatchError (var schema) schema
    SubError :: (Show schema, Show concrete, Matchable concrete schema var) => MatchError (var schema) schema -> schema -> concrete -> MatchError (var schema) schema
    OccursCheck :: (Show var, Show schema) => var -> schema -> MatchError var schema

instance Show (MatchError var t) where
    show (UnableToMatch a b) = "Unable to match " ++ show a ++ " with " ++ show b
    show (ErrWrapper e) = show e
    show (SubError err a b)  = "When matching " ++ show a ++ " with " ++ show b ++ ",\n" ++ show err
    show (OccursCheck v t)   = "Cannot construct infinite term " ++ show v ++ " = " ++ show t

--------------------------------------------------------
--4. Helper functions for unification
--------------------------------------------------------

--this also just becomes concatenation when doing pattern matching
--we need a way to compose mappings
(...) :: Subst var -> Subst var -> Subst var
x ... y = x ++ y

--maps a function over both elements of a paring
pairingMap :: (forall schema concrete. Matchable concrete schema var => schema -> schema) -> Pairing var -> Pairing var
pairingMap f (Pairing x y) = Pairing (f x) y

--maps a function over a Left
(Left x) .<. f = Left (f x)
e        .<. f = e

--maps a function over a right
(Right x) .>. f = Right (f x)
e         .>. f = e

isLeft (Left _) = True
isLeft _        = False

--------------------------------------------------------
--5. Pattern Matching code 
--------------------------------------------------------

--errors are currently not being reported correctly
--there are multiple issues
--first is the issue of keep track of forced substitutions
--second is the issue of keeping track of all possible substitutions
matchChildren :: (Matchable concrete schema var) => [Pairing var] -> Either [Subst var] (MatchError (var schema) schema)
matchChildren ((Pairing a b):xs) = case patternMatch a b of
    Left []     -> (matchChildren xs) .>. ErrWrapper
    Left substs -> let steps = map step substs
                       workable = filter isLeft steps
                   in if null workable
                      then head steps .>. ErrWrapper
                      else Left $ concatMap (\(Left subs) -> subs) workable
    Right err  -> Right (ErrWrapper err)
    where step subst = let children = map (pairingMap (apply subst)) xs
                       in (matchChildren children) .<. (map (subst ...)) .>. ErrWrapper
matchChildren [] = Left [[]]

patternMatch :: (Matchable concrete schema var) => schema -> concrete -> Either [Subst var] (MatchError (var schema) schema)
patternMatch a b = case (matchVar a b) of
  [] -> case match a b of
      Just children -> matchChildren children .>. (\e -> SubError e a b)
      Nothing       -> Right $ UnableToMatch a b
  lms -> let steps = map (\x-> patternMatch (apply [x] a) b .<. (map ([x] ...))) lms
             workable = filter isLeft steps
         in if null workable
            then head steps
            else Left $ concatMap (\(Left subs) -> subs) workable

--------------------------------------------------------
--5.1 Want to give users a nice lookup function
--------------------------------------------------------

fvMapLookup :: EquaitableVar var => var schema -> Subst var -> Maybe (Mapping var)
fvMapLookup v ((LambdaMapping v' args tm):xs) = case getLikeSchema v v' tm of
    Just tm' -> Just (LambdaMapping v' args tm)
    Nothing  -> fvMapLookup v xs
fvMapLookup v []                              = Nothing