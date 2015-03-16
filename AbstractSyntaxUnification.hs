{-#LANGUAGE EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, FunctionalDependencies #-}

module AbstractSyntaxUnification where

import Unification
import AbstractSyntaxDataTypes
import Data.Set as Set
import Data.Map as Map

--This module contains some early attemtps at implementing unification at
--the level of abstract syntax.

--------------------------------------------------------
--1. Unification for Schematic Terms
--------------------------------------------------------

instance (Schematizable f, Schematizable sv) => 
            Hilbert SSymbol (SchematicTerm f sv a) (SchematicTerm f sv a) where

        ftv ( S_ConstantTermBuilder _ ) = Set.empty
        ftv ( S_ConstantSchematicTermBuilder c ) = Set.singleton c
        ftv ( S_UnaryFuncApp _ t ) = ftv t
        ftv ( S_UnarySchematicFuncApp f t ) = Set.union (Set.singleton f) (ftv t)
        ftv ( S_BinaryFuncApp _ t1 t2 ) = Set.union (ftv t1) (ftv t2)
        ftv ( S_BinarySchematicFuncApp f t1 t2 ) = Set.unions [Set.singleton f, ftv t1, ftv t2]
        ftv ( S_BlankTerm ) = Set.empty

        apply _ (S_ConstantTermBuilder c) = S_ConstantTermBuilder c
        apply sub t@(S_ConstantSchematicTermBuilder c) = case Map.lookup c sub of
            Just t' -> apply sub t'
            Nothing -> t
        apply sub ( S_UnaryFuncApp f t ) = S_UnaryFuncApp f $ apply sub t
        --we need to use blank terms to be able to represent substituends
        --for schematic function symbols as schematic terms
        apply sub (S_UnarySchematicFuncApp f t2) = case Map.lookup f sub of 
            Just (S_UnarySchematicFuncApp f' S_BlankTerm) 
                -> apply sub $ S_UnarySchematicFuncApp f' t2
            Just (S_UnaryFuncApp f' S_BlankTerm) -> S_UnaryFuncApp f' (apply sub t2)
            _ -> S_UnarySchematicFuncApp f (apply sub t2)
        apply sub (S_BinaryFuncApp f t1 t2) = S_BinaryFuncApp f (apply sub t1) (apply sub t2)
        apply sub (S_BinarySchematicFuncApp f t1 t2) = case Map.lookup f sub of
            Just (S_BinarySchematicFuncApp f' S_BlankTerm S_BlankTerm) 
                -> apply sub $ S_BinarySchematicFuncApp f' t1 t2
            Just (S_BinaryFuncApp f' S_BlankTerm S_BlankTerm) 
                -> S_BinaryFuncApp f' (apply sub t1) (apply sub t2)
            _ -> S_UnarySchematicFuncApp f (apply sub t2)
        apply _ (S_BlankTerm) = S_BlankTerm

instance (UniformlyEq f, UniformlyEq sv, Schematizable sv, Schematizable f) => 
        Matchable (SchematicTerm f sv ()) (SchematicTerm f sv ()) where

        --for purposes of later unification, we include schematic function
        --symbols, with blanks, among the children of a given term, and
        --match these to schematic function symbols as well as functions
        
        --the following cases are things that have no matchable children.
        match (S_ConstantTermBuilder c) (S_ConstantTermBuilder c')
            | c =* c' = Just []
        match (S_ConstantSchematicTermBuilder _) _ = Just []
        match _ (S_ConstantSchematicTermBuilder _) = Just []
        --FIXME: I now think that several of these should fail to match.
        --But the bad cases probably will not arise in practice.
        match (S_UnarySchematicFuncApp _ S_BlankTerm) _ = Just []
        match _ (S_UnarySchematicFuncApp _ S_BlankTerm) = Just []
        match (S_BinarySchematicFuncApp _ S_BlankTerm S_BlankTerm) _ = Just []
        match _ (S_BinarySchematicFuncApp _ S_BlankTerm S_BlankTerm) = Just []
        --the following cases have matchable children
        match (S_UnaryFuncApp f t) (S_UnaryFuncApp f' t') 
            | f =* f' = Just [(t,t')]
        match t1@(S_UnarySchematicFuncApp _ t) t2@(S_UnaryFuncApp _ t')
            = Just [(unsaturateT t1, unsaturateT t2), (t, t')]
        match t1@(S_UnarySchematicFuncApp _ t) t2@(S_UnarySchematicFuncApp _ t')
            = Just [(unsaturateT t1, unsaturateT t2), (t, t')]
        match t1@(S_UnaryFuncApp _ t) t2@(S_UnarySchematicFuncApp _ t')
            = Just [(unsaturateT t1, unsaturateT t2), (t, t')]
        match (S_BinaryFuncApp f t1 t2) (S_BinaryFuncApp f' t1' t2')
            | f =* f' = Just [(t1,t1'),(t2,t2')]
        match t@(S_BinarySchematicFuncApp _ t1 t2) t'@(S_BinaryFuncApp _ t1' t2')
            = Just [(unsaturateT t, unsaturateT t'),(t1,t1'),(t2,t2')]
        match t@(S_BinarySchematicFuncApp _ t1 t2) t'@(S_BinarySchematicFuncApp _ t1' t2')
            = Just [(unsaturateT t, unsaturateT t'),(t1,t1'),(t2,t2')]
        match t@(S_BinaryFuncApp _ t1 t2) t'@(S_BinarySchematicFuncApp _ t1' t2')
            = Just [(unsaturateT t, unsaturateT t'),(t1,t1'),(t2,t2')]
        --everything else counts as failure to match
        match _ _ = Nothing

instance (UniformlyEq f, UniformlyEq sv, Schematizable sv, Schematizable f) =>
        Unifiable SSymbol (SchematicTerm f sv ()) where

        matchVar (S_ConstantSchematicTermBuilder c) t = Just (c,t)
        matchVar (S_UnarySchematicFuncApp f S_BlankTerm) t@(S_UnaryFuncApp _ S_BlankTerm) 
            = Just (f,t) 
        matchVar (S_UnarySchematicFuncApp f S_BlankTerm ) t@(S_UnarySchematicFuncApp _ S_BlankTerm) 
            = Just (f,t) 
        matchVar (S_BinarySchematicFuncApp f S_BlankTerm S_BlankTerm) t@(S_BinaryFuncApp _ S_BlankTerm S_BlankTerm) 
            = Just (f,t) 
        matchVar (S_BinarySchematicFuncApp f S_BlankTerm S_BlankTerm ) t@(S_BinarySchematicFuncApp _ S_BlankTerm S_BlankTerm) 
            = Just (f,t)
        matchVar _ _ = Nothing

        makeTerm symb@(C,_) = S_ConstantSchematicTermBuilder symb
        makeTerm symb@(F1,_) = S_UnarySchematicFuncApp symb S_BlankTerm
        makeTerm symb@(F2,_) = S_BinarySchematicFuncApp symb S_BlankTerm S_BlankTerm
        makeTerm _ = S_BlankTerm


--------------------------------------------------------
--2. Unification for Schematic Forms
--------------------------------------------------------


--does not drive the substititon down to to level of terms. We probably
--want a separate instance for that. But this will do for propositional
--logic.
instance (Schematizable pred, Schematizable con, Schematizable quant, Schematizable f, Schematizable sv, 
        S_NextVar sv quant, SchemeVar sv) => 
        Hilbert SSymbol (SchematicForm pred con quant f sv ()) (SchematicForm pred con quant f sv ()) where

        ftv ( S_BlankForm) = Set.empty
        ftv ( S_ConstantFormBuilder c ) = Set.empty
        ftv ( S_ConstantSchematicFormBuilder c ) = Set.singleton c
        ftv ( S_UnaryPredicate p t ) = ftv t
        ftv ( S_UnarySchematicPredicate p t ) = Set.union (Set.singleton p) (ftv t)
        ftv ( S_BinaryPredicate p t1 t2 ) = Set.union (ftv t1) (ftv t2)
        ftv ( S_BinarySchematicPredicate p t1 t2 ) = Set.unions [Set.singleton p, ftv t1, ftv t2]
        ftv ( S_UnaryConnect p f ) = ftv f
        ftv ( S_UnarySchematicConnect c f ) = Set.union (Set.singleton c) (ftv f)
        ftv ( S_BinaryConnect c f1 f2 ) = Set.union (ftv f1) (ftv f2)
        ftv ( S_BinarySchematicConnect c f1 f2 ) = Set.unions [Set.singleton c, ftv f1, ftv f2]
        ftv ( S_Bind q q'ed ) = ftv (q'ed BlankTerm)
        ftv ( S_SchematicBind q q'ed ) = Set.union (Set.singleton q) (ftv $ q'ed BlankTerm)

        apply sub f@(S_ConstantSchematicFormBuilder c) = case Map.lookup c sub of
            Just f' -> apply sub f'
            _ -> f
        apply sub f@(S_UnarySchematicPredicate p t) = case Map.lookup p sub of
            Just (S_UnarySchematicPredicate p' S_BlankTerm) -> apply sub $ S_UnarySchematicPredicate p' t
            Just (S_UnaryPredicate p' S_BlankTerm) -> S_UnaryPredicate p' t
            _ -> f
        apply sub f@(S_BinarySchematicPredicate p t1 t2) = case Map.lookup p sub of 
            Just (S_BinarySchematicPredicate p' S_BlankTerm S_BlankTerm) -> apply sub $ S_BinarySchematicPredicate p' t1 t2
            Just (S_BinaryPredicate p' S_BlankTerm S_BlankTerm) -> apply sub $ S_BinaryPredicate p' t1 t2
            _ -> f
        apply sub (S_UnaryConnect c f) = S_UnaryConnect c $ apply sub f
        apply sub (S_UnarySchematicConnect c f) = case Map.lookup c sub of 
            Just (S_UnarySchematicConnect c' S_BlankForm) -> apply sub $ S_UnarySchematicConnect c' f
            Just (S_UnaryConnect c' S_BlankForm) -> S_UnaryConnect c' $ apply sub f
            _ -> S_UnarySchematicConnect c $ apply sub f
        apply sub (S_BinaryConnect c f1 f2) = S_BinaryConnect c (apply sub f1) (apply sub f2)
        apply sub (S_BinarySchematicConnect c f1 f2) = case Map.lookup c sub of
            Just (S_BinarySchematicConnect c' S_BlankForm S_BlankForm) -> apply sub $ S_BinarySchematicConnect c' f1 f2
            Just (S_BinaryConnect c' S_BlankForm S_BlankForm) -> apply sub $ S_BinaryConnect c' (apply sub f1) (apply sub f2)
            _ -> S_BinarySchematicConnect c (apply sub f1) (apply sub f2)
        apply sub (S_Bind q q'ed) = S_Bind q (\x -> apply sub $ q'ed x)
        apply sub (S_SchematicBind q q'ed) = case Map.lookup q sub of
            Just (S_SchematicBind q' _) -> apply sub (S_SchematicBind q' q'ed)
            Just (S_Bind q' _) -> S_Bind q' (\x -> apply sub $ q'ed x)
            _ -> S_SchematicBind q (\x -> apply sub $ q'ed x)
        apply _ f = f

instance (UniformlyEq f, UniformlyEq pred, UniformlyEq sv, UniformlyEq con, UniformlyEq quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant) =>
        Matchable (SchematicForm pred con quant f sv ()) (SchematicForm pred con quant f sv ()) where
        
        --leaves of the parsing
        match (S_ConstantSchematicFormBuilder _) _                     = Just []
        match _ (S_ConstantSchematicFormBuilder _)                     = Just []
        match (S_UnaryPredicate _ S_BlankTerm) _                       = Just []
        match _ (S_UnaryPredicate _ S_BlankTerm)                       = Just []
        match (S_BinaryPredicate _ S_BlankTerm S_BlankTerm) _          = Just []
        match _ (S_BinaryPredicate _ S_BlankTerm S_BlankTerm)          = Just []
        match _ (S_UnaryConnect _ S_BlankForm)                         = Just []
        match (S_UnaryConnect _ S_BlankForm) _                         = Just []
        match _ (S_BinaryConnect _ S_BlankForm S_BlankForm)            = Just []
        match (S_BinaryConnect _ S_BlankForm S_BlankForm) _            = Just []
        match (S_UnarySchematicPredicate _ S_BlankTerm) _              = Just []
        match _ (S_UnarySchematicPredicate _ S_BlankTerm)              = Just []
        match (S_BinarySchematicPredicate _ S_BlankTerm S_BlankTerm) _ = Just []
        match _ (S_BinarySchematicPredicate _ S_BlankTerm S_BlankTerm) = Just []
        match _ (S_UnarySchematicConnect _ S_BlankForm)                = Just []
        match (S_UnarySchematicConnect _ S_BlankForm) _                = Just []
        match _ (S_BinarySchematicConnect _ S_BlankForm S_BlankForm)   = Just []
        match (S_BinarySchematicConnect _ S_BlankForm S_BlankForm) _   = Just []
        --cases where a constructor must match
        match (S_ConstantFormBuilder c) (S_ConstantFormBuilder c')
            | c =* c' = Just []
        match f@(S_UnaryPredicate p t1 ) f'@(S_UnaryPredicate p' t1' )
            | p =* p' = Just []
        match f@(S_BinaryPredicate p t1 t2) f'@(S_BinaryPredicate p' t1' t2')
            | p =* p' = Just []
        match f@(S_UnaryConnect c f1 ) f'@(S_UnaryConnect c' f1' )
            | c =* c' = Just [(f1,f1')]
        match f@(S_BinaryConnect c f1 f2) f'@(S_BinaryConnect c' f1' f2')
            | c =* c' = Just [(f1,f1'), (f2,f2')]
        --schematic cases, where the match doesn't require a matching
        --constructor
        match f@(S_BinarySchematicConnect _ f1 f2) f'@(S_BinaryConnect _ f1' f2')
            = Just [(unsaturateF f, unsaturateF f'), (f1,f1'), (f2,f2')]
        match f@(S_BinarySchematicConnect c f1 f2) f'@(S_BinarySchematicConnect c' f1' f2')
            = Just [(unsaturateF f, unsaturateF f'), (f1,f1'), (f2,f2')]
        match f@(S_UnarySchematicConnect c f1 ) f'@(S_UnaryConnect c' f1')
            = Just [(unsaturateF f, unsaturateF f'), (f1,f1')] 
        match f@(S_UnarySchematicConnect c f1 ) f'@(S_UnarySchematicConnect c' f1' )
            = Just [(unsaturateF f, unsaturateF f'), (f1,f1')]
        match f@(S_BinarySchematicPredicate c t1 t2) f'@(S_BinaryPredicate c' t1' t2')
            = Just [(unsaturateF f, unsaturateF f')]
        match f@(S_BinarySchematicPredicate c t1 t2) f'@(S_BinarySchematicPredicate c' t1' t2')
            = Just [(unsaturateF f, unsaturateF f')]
        match f@(S_UnarySchematicPredicate c t1 ) f'@(S_UnaryPredicate c' t1')
            = Just [(unsaturateF f, unsaturateF f')]
        match f@(S_UnarySchematicPredicate c t1 ) f'@(S_UnarySchematicPredicate c' t1' )
            = Just [(unsaturateF f, unsaturateF f')]
        match _ _ = Nothing

instance (UniformlyEq f, UniformlyEq pred, UniformlyEq sv, UniformlyEq con, UniformlyEq quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
        S_NextVar sv quant, SchemeVar sv)
        => Unifiable SSymbol (SchematicForm pred con quant f sv ()) where

        matchVar (S_ConstantSchematicFormBuilder c) f = Just (c,f)
        matchVar (S_UnarySchematicPredicate p S_BlankTerm) f@(S_UnaryPredicate _ S_BlankTerm)
            = Just (p, f)
        matchVar (S_UnarySchematicPredicate p S_BlankTerm) f@(S_UnarySchematicPredicate _ S_BlankTerm)
            = Just (p, f)
        matchVar (S_BinarySchematicPredicate p S_BlankTerm S_BlankTerm) f@(S_BinaryPredicate _ S_BlankTerm S_BlankTerm)
            = Just (p, f)
        matchVar (S_BinarySchematicPredicate p S_BlankTerm S_BlankTerm) f@(S_BinarySchematicPredicate _ S_BlankTerm S_BlankTerm)
            = Just (p, f)
        matchVar (S_UnarySchematicConnect c S_BlankForm) f@(S_UnaryConnect _ S_BlankForm) 
            = Just (c, f)
        matchVar (S_UnarySchematicConnect c S_BlankForm) f@(S_UnarySchematicConnect _ S_BlankForm) 
            = Just (c, f)
        matchVar (S_BinarySchematicConnect c S_BlankForm S_BlankForm) f@(S_BinaryConnect _ S_BlankForm S_BlankForm) 
            = Just (c, f)
        matchVar (S_BinarySchematicConnect c S_BlankForm S_BlankForm) f@(S_BinarySchematicConnect _ S_BlankForm S_BlankForm) 
            = Just (c, f)
        matchVar _ _ = Nothing

        makeTerm symb@(S,_) = S_ConstantSchematicFormBuilder symb
        makeTerm symb@(P1,_) = S_UnarySchematicPredicate symb S_BlankTerm
        makeTerm symb@(P2,_) = S_BinarySchematicPredicate symb S_BlankTerm S_BlankTerm
        makeTerm symb@(CN1,_) = S_UnarySchematicConnect symb S_BlankForm
        makeTerm symb@(CN2,_) = S_BinarySchematicConnect symb S_BlankForm S_BlankForm 
        
--------------------------------------------------------
--3. Mixed Unification
--------------------------------------------------------

type LanguageItem pred con quant f sv a = Either (Form pred con quant f sv a ) (Term f sv a) 

type S_LanguageItem pred con quant f sv = Either ( SchematicForm pred con quant f sv () ) (SchematicTerm f sv ())

toForm :: S_LanguageItem pred con quant f sv -> ( SchematicForm pred con quant f sv () )
toForm (Left x) = x
toForm _ = undefined

fRecur :: (S_LanguageItem pred con quant f sv -> S_LanguageItem pred con quant f sv) -> 
        SchematicForm pred con quant f sv () -> SchematicForm pred con quant f sv ()
fRecur f = toForm . f . Left

toTerm :: S_LanguageItem pred con quant f sv -> (SchematicTerm f sv ())
toTerm (Right x) = x
toTerm _ = undefined

tRecur :: (S_LanguageItem pred con quant f sv -> S_LanguageItem pred con quant f sv) -> 
        SchematicTerm f sv () -> SchematicTerm f sv ()
tRecur f = toTerm . f . Right

lUnsaturateF (Left x) = Left $ unsaturateF x

rUnsaturateT (Right x) = Right $ unsaturateT x

(|+|) :: a -> a -> (Either a b,Either a b)
(|+|) x y = (Left x , Left y)

(|*|) :: b -> b -> (Either a b,Either a b)
(|*|) x y = (Right x , Right y)

--an attempt at mixed unification

instance Scheme (LanguageItem pred con quant f sv a) (S_LanguageItem pred con quant f sv) where
    liftToScheme (Left f) = Left (liftToScheme f)
    liftToScheme (Right t) = Right (liftToScheme t)

instance (Schematizable pred, Schematizable con, Schematizable quant, Schematizable f, Schematizable sv, 
        S_NextVar sv quant, SchemeVar sv) => 
            Hilbert SSymbol (S_LanguageItem pred con quant f sv) (S_LanguageItem pred con quant f sv)  where

        ftv (Left f) = ftv f
        ftv (Right t) = ftv t

        apply _ f@(Left (S_ConstantFormBuilder c)) = f
        apply sub f@(Left (S_ConstantSchematicFormBuilder c)) = case Map.lookup c sub of
            Just f' -> apply sub f'
            _ -> f
        apply sub (Left (S_UnarySchematicPredicate p t)) = case Map.lookup p sub of
            Just (Left (S_UnarySchematicPredicate p' S_BlankTerm)) -> 
                apply sub (Left $ S_UnarySchematicPredicate p' t)
            Just (Left (S_UnaryPredicate p' S_BlankTerm )) -> 
                Left $ S_UnaryPredicate p' $ tRecur (apply sub) t
            _ -> Left $ S_UnarySchematicPredicate p $ tRecur (apply sub) t
        apply sub (Left (S_BinarySchematicPredicate p t1 t2) ) = case Map.lookup p sub of 
            Just (Left ( S_BinarySchematicPredicate p' S_BlankTerm S_BlankTerm )) -> 
                apply sub $ Left $ S_BinarySchematicPredicate p' t1 t2
            Just (Left ( S_BinaryPredicate p' S_BlankTerm S_BlankTerm )) -> 
                Left $ S_BinaryPredicate p' (tRecur (apply sub) t1) (tRecur (apply sub) t2)
            _ -> Left $ S_BinarySchematicPredicate p (tRecur (apply sub) t1) (tRecur (apply sub) t2)
        apply sub (Left ( S_UnaryConnect c f )) = 
            Left $ S_UnaryConnect c $ fRecur (apply sub) f
        apply sub (Left ( S_UnarySchematicConnect c f )) = case Map.lookup c sub of 
            Just (Left ( S_UnarySchematicConnect c' S_BlankForm )) -> 
                apply sub $ Left $ S_UnarySchematicConnect c' f
            Just (Left (S_UnaryConnect c' S_BlankForm)) -> 
                Left $ S_UnaryConnect c' $ fRecur (apply sub) f
            _ -> Left $ S_UnarySchematicConnect c $ fRecur (apply sub) f
        apply sub (Left (S_BinaryConnect c f1 f2)) = 
            Left $ S_BinaryConnect c (fRecur (apply sub) f1) (fRecur (apply sub) f2)
        apply sub (Left (S_BinarySchematicConnect c f1 f2)) = case Map.lookup c sub of
            Just (Left (S_BinarySchematicConnect c' S_BlankForm S_BlankForm)) -> 
                apply sub $ Left $ S_BinarySchematicConnect c' f1 f2
            Just (Left (S_BinaryConnect c' S_BlankForm S_BlankForm)) -> 
                Left $ S_BinaryConnect c' (fRecur (apply sub) f1) (fRecur (apply sub) f2)
            _ -> Left $ S_BinarySchematicConnect c (fRecur (apply sub) f1) (fRecur (apply sub) f2)
        apply sub (Left (S_Bind q q'ed)) = Left $ S_Bind q (\x -> fRecur (apply sub) $ q'ed x)
        apply sub (Left (S_SchematicBind q q'ed)) = case Map.lookup q sub of
            Just (Left (S_SchematicBind q' _)) -> apply sub $ Left $ S_SchematicBind q' q'ed
            Just (Left (S_Bind q' _)) -> Left $ S_Bind q' (\x -> fRecur (apply sub) $ q'ed x)
            _ -> Left $ S_SchematicBind q (\x -> fRecur (apply sub) $ q'ed x)

        apply _ t@(Right (S_ConstantTermBuilder _)) = t
        apply sub t@(Right (S_ConstantSchematicTermBuilder c)) = case Map.lookup c sub of
            Just t' -> apply sub t'
            Nothing -> t
        apply sub (Right (S_UnaryFuncApp f t)) = Right $ S_UnaryFuncApp f $ tRecur (apply sub) t
        apply sub (Right (S_UnarySchematicFuncApp f t2)) = case Map.lookup f sub of 
            Just (Right (S_UnarySchematicFuncApp f' S_BlankTerm))
                 -> apply sub $ Right $ S_UnarySchematicFuncApp f' t2
            Just (Right (S_UnaryFuncApp f' S_BlankTerm)) -> Right $ S_UnaryFuncApp f' $ tRecur (apply sub) t2
            _ -> Right $ S_UnarySchematicFuncApp f $ tRecur (apply sub) t2
        apply sub (Right (S_BinaryFuncApp f t1 t2)) = Right $ S_BinaryFuncApp f (tRecur (apply sub) t1) (tRecur (apply sub) t2)
        apply sub (Right (S_BinarySchematicFuncApp f t1 t2)) = case Map.lookup f sub of
            Just (Right (S_BinarySchematicFuncApp f' S_BlankTerm S_BlankTerm))
                 -> apply sub $ Right $ S_BinarySchematicFuncApp f' t1 t2
            Just (Right (S_BinaryFuncApp f' S_BlankTerm S_BlankTerm) )
                 -> Right $ S_BinaryFuncApp f' (tRecur (apply sub) t1) (tRecur (apply sub) t2)
            _ -> Right $ S_UnarySchematicFuncApp f $ tRecur (apply sub) t2

        apply _ x = x

instance (UniformlyEq f, UniformlyEq pred, UniformlyEq sv, UniformlyEq con, UniformlyEq quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant) =>
        Matchable (S_LanguageItem pred con quant f sv)  (S_LanguageItem pred con quant f sv) where

        --leaves of the parsing
        match (Right (  S_ConstantSchematicTermBuilder _ )) (Right _)           = Just []
        match (Right _) (Right (  S_ConstantSchematicTermBuilder _ ))           = Just []
        match (Left(  S_ConstantSchematicFormBuilder _ )) (Left _)              = Just []
        match (Left _) (Left(  S_ConstantSchematicFormBuilder _ ))              = Just []
        -- I think these are actually error cases
        -- match (Right (S_UnarySchematicFuncApp _ S_BlankTerm )) _                = Just []
        -- match _ (Right (S_UnarySchematicFuncApp _ S_BlankTerm ))                = Just []
        -- match (Right (S_BinarySchematicFuncApp _ S_BlankTerm S_BlankTerm )) _   = Just []
        -- match _ (Right (S_BinarySchematicFuncApp _ S_BlankTerm S_BlankTerm ))   = Just []
        -- match (Left(  S_UnaryPredicate _ S_BlankTerm )) _                       = Just []
        -- match _ (Left(  S_UnaryPredicate _ S_BlankTerm ))                       = Just []
        -- match (Left(  S_BinaryPredicate _ S_BlankTerm S_BlankTerm )) _          = Just []
        -- match _ (Left(  S_BinaryPredicate _ S_BlankTerm S_BlankTerm ))          = Just []
        -- match _ (Left(  S_UnaryConnect _ S_BlankForm ))                         = Just []
        -- match (Left(  S_UnaryConnect _ S_BlankForm )) _                         = Just []
        -- match _ (Left(  S_BinaryConnect _ S_BlankForm S_BlankForm ))            = Just []
        -- match (Left(  S_BinaryConnect _ S_BlankForm S_BlankForm )) _            = Just []
        -- match (Left(  S_UnarySchematicPredicate _ S_BlankTerm )) _              = Just []
        -- match _ (Left(  S_UnarySchematicPredicate _ S_BlankTerm ))              = Just []
        -- match (Left(  S_BinarySchematicPredicate _ S_BlankTerm S_BlankTerm )) _ = Just []
        -- match _ (Left(  S_BinarySchematicPredicate _ S_BlankTerm S_BlankTerm )) = Just []
        -- match _ (Left(  S_UnarySchematicConnect _ S_BlankForm ))                = Just []
        -- match (Left(  S_UnarySchematicConnect _ S_BlankForm )) _                = Just []
        -- match _ (Left(  S_BinarySchematicConnect _ S_BlankForm S_BlankForm ))   = Just []
        -- match (Left(  S_BinarySchematicConnect _ S_BlankForm S_BlankForm )) _   = Just []
        --cases where a constructor must match
        match (Left (S_ConstantFormBuilder c)) (Left (S_ConstantFormBuilder c'))
            | c =* c'= Just []
        match (Right (S_ConstantTermBuilder c)) (Right (S_ConstantTermBuilder c'))
            | c =* c' = Just []
        match (Right (S_UnaryFuncApp f t)) (Right (S_UnaryFuncApp f' t'))
            | f =* f' = Just [( t |*| t')]
        match (Right (S_BinaryFuncApp f t1 t2)) (Right (S_BinaryFuncApp f' t1' t2'))
            | f =* f' = Just [( t1 |*| t1'),( t2 |*| t2')]
        match (Left (S_UnaryPredicate p t )) (Left (S_UnaryPredicate p' t' ))
            | p =* p' = Just [( t |*| t')]
        match (Left (S_BinaryPredicate p t1 t2)) (Left (S_BinaryPredicate p' t1' t2'))
            | p =* p' = Just [( t1 |*| t1'), ( t2 |*| t2')]
        match (Left (S_UnaryConnect c f1 )) (Left (S_UnaryConnect c' f1' ))
            | c =* c' = Just [(f1 |+| f1')]
        match (Left (S_BinaryConnect c f1 f2)) (Left (S_BinaryConnect c' f1' f2'))
            | c =* c' = Just [(f1 |+| f1'), (f2 |+| f2')]
        --schematic cases, where the match doesn't require a matching
        --constructor 
        --FIXME: some cases missing here.
        match f@(Left (S_BinarySchematicConnect _ f1 f2)) f'@(Left (S_BinaryConnect _ f1' f2'))
            = Just [(lUnsaturateF f, lUnsaturateF f'), (f1 |+| f1'), (f2 |+| f2')]
        match f@(Left (S_BinaryConnect _ f1 f2)) f'@(Left (S_BinarySchematicConnect _ f1' f2'))
            = Just [(lUnsaturateF f, lUnsaturateF f'), (f1 |+| f1'), (f2 |+| f2')]
        match f@(Left (S_BinarySchematicConnect c f1 f2)) f'@(Left (S_BinarySchematicConnect c' f1' f2'))
            = Just [(lUnsaturateF f, lUnsaturateF f'), (f1 |+| f1'), (f2 |+| f2')]
        match f@(Left (S_UnarySchematicConnect c f1 )) f'@(Left (S_UnaryConnect c' f1'))
            = Just [(lUnsaturateF f, lUnsaturateF f'), (f1 |+| f1')] 
        match f@(Left (S_UnaryConnect c f1 )) f'@(Left (S_UnarySchematicConnect c' f1'))
            = Just [(lUnsaturateF f, lUnsaturateF f'), (f1 |+| f1')] 
        match f@(Left (S_UnarySchematicConnect c f1 )) f'@(Left (S_UnarySchematicConnect c' f1' ))
            = Just [(lUnsaturateF f, lUnsaturateF f'), (f1 |+| f1')]
        match f@(Left (S_BinarySchematicPredicate c t1 t2)) f'@(Left (S_BinaryPredicate c' t1' t2'))
            = Just [(lUnsaturateF f, lUnsaturateF f'), (t1 |*| t1'), (t2 |*| t2')]
        match f@(Left (S_BinaryPredicate c t1 t2)) f'@(Left (S_BinarySchematicPredicate c' t1' t2'))
            = Just [(lUnsaturateF f, lUnsaturateF f'), (t1 |*| t1'), (t2 |*| t2')]
        match f@(Left (S_BinarySchematicPredicate c t1 t2)) f'@(Left (S_BinarySchematicPredicate c' t1' t2'))
            = Just [(lUnsaturateF f, lUnsaturateF f'), (t1 |*| t1'), (t2 |*| t2')]
        match f@(Left (S_UnarySchematicPredicate c t1 )) f'@(Left (S_UnaryPredicate c' t1'))
            = Just [(lUnsaturateF f, lUnsaturateF f'), (t1 |*| t1')]
        match f@(Left (S_UnaryPredicate c t1 )) f'@(Left (S_UnarySchematicPredicate c' t1'))
            = Just [(lUnsaturateF f, lUnsaturateF f'), (t1 |*| t1')]
        match f@(Left (S_UnarySchematicPredicate c t1 )) f'@(Left (S_UnarySchematicPredicate c' t1' ))
            = Just [(lUnsaturateF f, lUnsaturateF f'), (t1 |*| t1')]
        match t1@(Right (S_UnarySchematicFuncApp _ t)) t2@(Right (S_UnaryFuncApp _ t'))
            = Just [(rUnsaturateT t1, rUnsaturateT t2), (t |*| t')]
        match t1@(Right (S_UnaryFuncApp _ t)) t2@(Right (S_UnarySchematicFuncApp _ t'))
            = Just [(rUnsaturateT t1, rUnsaturateT t2), (t |*| t')]
        match t1@(Right (S_UnarySchematicFuncApp _ t)) t2@(Right (S_UnarySchematicFuncApp _ t'))
            = Just [(rUnsaturateT t1, rUnsaturateT t2), (t |*| t')]
        match t@(Right (S_BinarySchematicFuncApp _ t1 t2)) t'@(Right (S_BinaryFuncApp _ t1' t2'))
            = Just [(rUnsaturateT t, rUnsaturateT t'), (t1 |*| t1'), (t2 |*| t2')]
        match t@(Right (S_BinaryFuncApp _ t1 t2)) t'@(Right (S_BinarySchematicFuncApp _ t1' t2'))
            = Just [(rUnsaturateT t, rUnsaturateT t'),(t1 |*| t1'),(t2 |*| t2')]
        match t@(Right (S_BinarySchematicFuncApp _ t1 t2)) t'@(Right (S_BinarySchematicFuncApp _ t1' t2'))
            = Just [(rUnsaturateT t, rUnsaturateT t'),(t1 |*| t1'), (t2 |*| t2')]
        --anything else is a failure to match
        match _ _ = Nothing

instance (UniformlyEq f, UniformlyEq pred, UniformlyEq sv, UniformlyEq con, UniformlyEq quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
        S_NextVar sv quant, SchemeVar sv) => Unifiable SSymbol (S_LanguageItem pred con quant f sv) where

        matchVar (Left (S_ConstantSchematicFormBuilder c)) f@(Left _) = Just (c,f)
        matchVar (Left (S_UnarySchematicPredicate p S_BlankTerm)) f@(Left (S_UnaryPredicate _ S_BlankTerm))
            = Just (p, f)
        matchVar (Left (S_UnarySchematicPredicate p S_BlankTerm)) f@(Left (S_UnarySchematicPredicate _ S_BlankTerm))
            = Just (p, f)
        matchVar (Left (S_BinarySchematicPredicate p S_BlankTerm S_BlankTerm)) f@(Left (S_BinaryPredicate _ S_BlankTerm S_BlankTerm))
            = Just (p, f)
        matchVar (Left (S_BinarySchematicPredicate p S_BlankTerm S_BlankTerm)) f@(Left (S_BinarySchematicPredicate _ S_BlankTerm S_BlankTerm))
            = Just (p, f)
        matchVar (Left (S_UnarySchematicConnect c S_BlankForm)) f@(Left (S_UnaryConnect _ S_BlankForm))
            = Just (c, f)
        matchVar (Left (S_UnarySchematicConnect c S_BlankForm)) f@(Left (S_UnarySchematicConnect _ S_BlankForm))
            = Just (c, f)
        matchVar (Left (S_BinarySchematicConnect c S_BlankForm S_BlankForm)) f@(Left (S_BinaryConnect _ S_BlankForm S_BlankForm))
            = Just (c, f)
        matchVar (Left (S_BinarySchematicConnect c S_BlankForm S_BlankForm)) f@(Left (S_BinarySchematicConnect _ S_BlankForm S_BlankForm))
            = Just (c, f)
        matchVar (Right (S_ConstantSchematicTermBuilder c )) t = Just (c,t)
        matchVar (Right (S_UnarySchematicFuncApp f S_BlankTerm )) t@(Right ( S_UnaryFuncApp _ S_BlankTerm )) 
            = Just (f,t) 
        matchVar (Right (S_UnarySchematicFuncApp f S_BlankTerm  )) t@(Right ( S_UnarySchematicFuncApp _ S_BlankTerm )) 
            = Just (f,t) 
        matchVar (Right (S_BinarySchematicFuncApp f S_BlankTerm S_BlankTerm )) t@(Right ( S_BinaryFuncApp _ S_BlankTerm S_BlankTerm )) 
            = Just (f,t) 
        matchVar (Right (S_BinarySchematicFuncApp f S_BlankTerm S_BlankTerm)) t@(Right (S_BinarySchematicFuncApp _ S_BlankTerm S_BlankTerm)) 
            = Just (f,t)
        matchVar _ _ = Nothing

        makeTerm symb@(S,_)   = Left $ S_ConstantSchematicFormBuilder symb
        makeTerm symb@(P1,_)  = Left $ S_UnarySchematicPredicate symb S_BlankTerm
        makeTerm symb@(P2,_)  = Left $ S_BinarySchematicPredicate symb S_BlankTerm S_BlankTerm
        makeTerm symb@(CN1,_) = Left $ S_UnarySchematicConnect symb S_BlankForm
        makeTerm symb@(CN2,_) = Left $ S_BinarySchematicConnect symb S_BlankForm S_BlankForm
        makeTerm symb@(C,_)   = Right $ S_ConstantSchematicTermBuilder symb
        makeTerm symb@(F1,_)  = Right $ S_UnarySchematicFuncApp symb S_BlankTerm
        makeTerm symb@(F2,_)  = Right $ S_BinarySchematicFuncApp symb S_BlankTerm S_BlankTerm


--------------------------------------------------------
--4. Helper Functions
--------------------------------------------------------

unsaturateT (S_UnaryFuncApp f t) = S_UnaryFuncApp f S_BlankTerm
unsaturateT (S_UnarySchematicFuncApp f t) = S_UnarySchematicFuncApp f S_BlankTerm
unsaturateT (S_BinaryFuncApp f t1 t2) = S_BinaryFuncApp f S_BlankTerm S_BlankTerm
unsaturateT (S_BinarySchematicFuncApp f t1 t2) = S_BinarySchematicFuncApp f S_BlankTerm S_BlankTerm
unsaturateT x = x

unsaturateF (S_UnaryPredicate p _) = S_UnaryPredicate p S_BlankTerm
unsaturateF (S_UnarySchematicPredicate p _) = S_UnarySchematicPredicate p S_BlankTerm
unsaturateF (S_BinaryPredicate p _ _) = S_BinaryPredicate p S_BlankTerm S_BlankTerm 
unsaturateF (S_BinarySchematicPredicate p _ _) = S_BinarySchematicPredicate p S_BlankTerm S_BlankTerm
unsaturateF (S_UnaryConnect c _) = S_UnaryConnect c S_BlankForm
unsaturateF (S_UnarySchematicConnect c _) = S_UnarySchematicConnect c S_BlankForm
unsaturateF (S_BinaryConnect c _ _) = S_BinaryConnect c S_BlankForm S_BlankForm 
unsaturateF (S_BinarySchematicConnect c _ _) = S_BinarySchematicConnect c S_BlankForm S_BlankForm
unsaturateF x = x
