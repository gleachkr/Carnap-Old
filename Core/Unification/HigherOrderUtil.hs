{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes, TupleSections #-}


module HigherOrderUtil (Throne, makeSub, Royal, makeChoice, children) where

import Carnap.Core.Unification.HigherOrderPatternMatching
import Data.List

--the person that sits on the throne (the highlighted node)
data Throne concrete schema var where
   (:~:) :: (Royal schema var) => (var schema, schema) -> (schema, [(schema -> schema, Maybe (schema -> Throne schema var))]) -> Throne schema var

--someone is royal if they can accend to the throne (become a zipper)
class (Matchable concrete schema var) => Royal concrete schema var | concrete -> schema where
    --makes a choice operator out of a set of children
    makeChoice :: [schema] -> schema
    --each child should be a pair of the actual child and a function that if given the child forms a new one
    children :: concrete -> ([concrete], [concrete] -> concrete)

--defines the order of succession
--first your child inherits the throne
--then your siblings inherit the throne if you have no children
--if you have no younger siblings then your parrents sibling is next in line or their successor if there is none
--if no such person is next in line then the royal family dies
successor :: Throne schema var -> [Throne schema var]
successor ((v, arg) :~: (s, fs)) | not . null . fst . children $ s = [(v, arg) :~: (child, (\child' -> redo $ child':ss, makeNext [] s ss):fs)]
    where (child:ss, redo) = children s
          makeNext args king []     = Nothing
          makeNext args king (x:xs) = let backTrack king' x' = redo $ args ++ [king', x'] ++ xs
                                          younger king'      = makeNext (args ++ [king']) x xs
                                      in Just $ \king' -> ((v, arg)) :~: (x, (backTrack king', younger king'):fs)
                                                            
successor ((_, _) :~: (s, (_, Just younger):_)) = [younger s]
successor z = nextInLine z

nextInLine :: Throne schema var -> [Throne schema var]
nextInLine ((v, arg) :~: (s, (f, Nothing):fs)) = nextInLine $ (v, arg) :~: (f s, fs)
nextInLine ((_, _) :~: (s, (_, Just younger):_)) = [younger s]
nextInLine ((_, _) :~: (_, [])) = []

progenitor ((_, _) :~: (s, []))          = s
progenitor ((v, arg) :~: (s, (f, _):fs)) = progenitor $ (v, arg) :~: (f s, fs)

getSchema ((_, _) :~: (s, _)) = s

makeSub :: (Royal schema var) => Throne concrete var -> Throne schema var
makeSub zipper | null $ successor zipper = progenitor zipper
makeSub zipper@((v, arg) :~: (s, fs)) = case match arg s of
    Left sub -> let c1 = successor $ (v, apply sub arg) :~: (makeTerm v, fs)
                    c2 = successor $ (v, arg) :~: (s, fs)
                in makeChoice $ map makeSub (c1 ++ c2)
    Right err -> makeSub . head . successor $ zipper

--------------------------------------------------------
--7. Lets do a diffrent sort of test
--------------------------------------------------------

{-
data Term = Term String
data FormulaVar a where
    FormulaVar :: String -> FormulaVar Formula
    TermVar :: String -> FormulaVar Term

--these are simple types
data Formula = Connective String [Formula]
             | Predicate String [FormulaVar Term]
    deriving(Eq, Show)

instance Show (FormulaVar a) where
    show (FormulaVar s) = s
    show (TermVar s) = s

instance EquaitableVar FormulaVar where
  getLikeSchema (FormulaVar v) (FormulaVar v') s' | v == v' = Just s'
  getLikeSchema _              _               _            = Nothing

instance Eq (FormulaVar a) where
    a == b = eq a b

--first lets do types 
instance MultiMatchable Formula FormulaVar where
    multiMatch (Connective v args)  (Connective v' args') 
        | v == v' && length args == length args'  = Just $ eZip args args'
        where eZip (x:xs) (y:ys) = (UnifiablePairing x y) : (eZip xs ys)
              eZip []     _      = []
              eZip _      []     = []
    multiMatch (Predicate a args) expr            = Just []
    multiMatch expr (Predicate a args)            = Just []

--I think these two functions are cheating
--I do not belive you could write these for somthing more complex with multiple varible types
--I'll try and create a more general version after I have this basic higher order version down
convert :: FormulaVar schema -> FormulaVar Formula
convert (FormulaVar s) = FormulaVar s

convertTerm :: FormulaVar schema -> schema -> Formula
convertTerm v s = case getLikeSchema (convert v) v s of
    Just s' -> s'

instance MultiHilbert Formula FormulaVar where
    multiFreeVars (Connective v args) = foldl union [] (map multiFreeVars args) 
    multiFreeVars (Predicate v  args) = [FreeVar (FormulaVar v)] ++ map FreeVar args

    --multiApply = undefined
    multiApply subst (Connective v args) = Connective v (map (multiApply subst) args)
    multiApply subst (Predicate  v )   = case fvMapLookup (FormulaVar v) subst of
        Just (Mapping v' tm) -> convertTerm v' tm
        Nothing              -> Predicate  v []
    multiApply subst (Predicate  v args) = case fvMapLookup (FormulaVar v) subst of
        Just (LambdaMapping v vargs tm) -> applyEach (convertTerm v tm) (zip vargs args)
        Nothing                         -> Predicate v args
        where applyEach :: Formula -> [(FreeVar FormulaVar, Formula)] -> Formula
              applyEach tm (((FreeVar v'), arg):xs) = applyEach (multiApply [Mapping (convert v') arg] tm) xs

--I'm not done with this yet
instance MultiUnifiable Formula FormulaVar where
    multiMatchVar (Predicate v vars) term = undefined
    multiMakeTerm = undefined
    --multiMatchVar (Predicate v args) tm = Just $ Mapping v tm
    --multiMatchVar tm (Predicate v args) = Just $ Mapping v tm
    --multiMatchVar _  _                  = Nothing

    --multiMakeTerm = TyVar
    -}

    as I edit
    