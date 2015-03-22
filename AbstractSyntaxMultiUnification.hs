{-#LANGUAGE EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, FunctionalDependencies #-}

module AbstractSyntaxMultiUnification where

import MultiUnification
import AbstractSyntaxDataTypes
import Data.List

--------------------------------------------------------
--1.Generalities
--------------------------------------------------------

--------------------------------------------------------
--1.1 Schematic Symbols
--------------------------------------------------------

data Var pred con quant f sv a s where
        ConstantTermVar :: String -> Var pred con quant f sv () (SchematicTerm pred con quant f sv ())
        UnaryFuncVar :: String -> Var pred con quant f sv () (SchematicTerm pred con quant f sv ())
        BinaryFuncVar :: String -> Var pred con quant f sv () (SchematicTerm pred con quant f sv ())
        ConstantFormVar :: String -> Var pred con quant f sv () (SchematicForm pred con quant f sv ())
        UnaryPredVar :: String -> Var pred con quant f sv () (SchematicForm pred con quant f sv ())
        BinaryPredVar :: String -> Var pred con quant f sv () (SchematicForm pred con quant f sv ())
        UnaryConnectVar :: String -> Var pred con quant f sv () (SchematicForm pred con quant f sv ())
        BinaryConnectVar :: String -> Var pred con quant f sv () (SchematicForm pred con quant f sv ())
        QuantVar :: String -> Var pred con quant f sv () (SchematicForm pred con quant f sv ())

instance Show (Var pred con quant f sv a s) where
        show ( ConstantTermVar s ) = s
        show ( UnaryFuncVar s ) = s
        show ( BinaryFuncVar s ) = s
        show ( ConstantFormVar s) = s
        show ( UnaryPredVar s) = s
        show ( BinaryPredVar s) = s
        show ( UnaryConnectVar s) = s
        show ( BinaryConnectVar s) = s
        show ( QuantVar s) = s

instance EquaitableVar (Var pred con quant f sv a) where
    getLikeSchema (ConstantTermVar s) (ConstantTermVar s') t | s == s' = Just t
    getLikeSchema (UnaryFuncVar s) (UnaryFuncVar s') t | s == s' = Just t
    getLikeSchema (BinaryFuncVar s) (BinaryFuncVar s') t | s == s' = Just t
    getLikeSchema (ConstantFormVar s) (ConstantFormVar s') t | s == s' = Just t
    getLikeSchema (UnaryPredVar s) (UnaryPredVar s') t | s == s' = Just t
    getLikeSchema (BinaryPredVar s) (BinaryPredVar s') t | s == s' = Just t
    getLikeSchema (UnaryConnectVar s) (UnaryConnectVar s') t | s == s' = Just t
    getLikeSchema (BinaryConnectVar s) (BinaryConnectVar s') t | s == s' = Just t
    getLikeSchema (QuantVar s) (QuantVar s') t | s == s' = Just t
    getLikeSchema _           _            _           = Nothing

instance Eq (Var pred con quant f sv a s) where
    (ConstantTermVar s) == (ConstantTermVar s') = s == s'
    (UnaryFuncVar s) == (UnaryFuncVar s') = s == s'
    (BinaryFuncVar s) == (BinaryFuncVar s') = s == s'
    (ConstantFormVar s) == (ConstantFormVar s') = s == s' 
    (UnaryPredVar s) == (UnaryPredVar s') = s == s' 
    (BinaryPredVar s) == (BinaryPredVar s') = s == s' 
    (UnaryConnectVar s) == (UnaryConnectVar s') = s == s' 
    (BinaryConnectVar s) == (BinaryConnectVar s') = s == s' 
    (QuantVar s) == (QuantVar s') = s == s' 
    _           == _            = False

instance UniformlyEquaitable (Var pred con quant f sv a) where
    eq (ConstantTermVar s) (ConstantTermVar s') = s == s'
    eq (UnaryFuncVar s) (UnaryFuncVar s') = s == s'
    eq (BinaryFuncVar s) (BinaryFuncVar s') = s == s'
    eq (ConstantFormVar s) (ConstantFormVar s') = s == s' 
    eq (UnaryPredVar s) (UnaryPredVar s') = s == s' 
    eq (BinaryPredVar s) (BinaryPredVar s') = s == s' 
    eq (UnaryConnectVar s) (UnaryConnectVar s') = s == s' 
    eq (BinaryConnectVar s) (BinaryConnectVar s') = s == s' 
    eq (QuantVar s) (QuantVar s') = s == s' 
    eq _           _            = False

--------------------------------------------------------
--1.2 Schematic Typeclass and Instance Variations
--------------------------------------------------------

class S_NextVar sv quant where
        s_appropriateVariable :: SchematicForm pred con quant f sv () -> quant ((sv b -> c) -> a) -> String

class SchemeVar sv where
        appropriateSchematicVariable :: SchematicForm pred con quant f sv a -> Var pred con quant f sv a (SchematicForm pred con quant f sv a) -> String

instance S_NextVar a Nothing where
        s_appropriateVariable _ _ = undefined

--------------------------------------------------------
--2. MultiUnification for Schematic Terms
--------------------------------------------------------

--------------------------------------------------------
--2.1 Data Types
--------------------------------------------------------

data SchematicTerm pred con quant f sv a where 
        S_BlankTerm                    ::   SchematicTerm pred con quant f sv ()
        S_ConstantTermBuilder          ::   {      s_cVal :: sv a } -> SchematicTerm pred con quant f sv ()
        S_ConstantSchematicTermBuilder ::   {  schemeBVal :: Var pred con quant f sv () (SchematicTerm pred con quant f sv ())} -> SchematicTerm pred con quant f sv ()
        S_UnaryFuncApp                 ::   {     s_uFunc :: f ( b -> a ) , 
                                                  s_uTerm :: SchematicTerm pred con quant f sv () } 
                                            -> SchematicTerm pred con quant f sv ()
        S_UnarySchematicFuncApp        ::   { schemeUFunc :: Var pred con quant f sv () (SchematicTerm pred con quant f sv ()), 
                                                  s_uTerm :: SchematicTerm pred con quant f sv () } 
                                            -> SchematicTerm pred con quant f sv ()
        S_BinaryFuncApp                ::   {     s_bFunc :: f ( b -> c -> a), 
                                                 s_bTerm1 :: SchematicTerm pred con quant f sv (), 
                                                 s_bTerm2 :: SchematicTerm pred con quant f sv ()} 
                                            -> SchematicTerm pred con quant f sv ()
        S_BinarySchematicFuncApp       ::   { schemeBFunc :: Var pred con quant f sv () (SchematicTerm pred con quant f sv ()), 
                                                 s_bTerm1 :: SchematicTerm pred con quant f sv (), 
                                                 s_bTerm2 :: SchematicTerm pred con quant f sv ()} 
                                            -> SchematicTerm pred con quant f sv ()

instance Scheme (Term f sv a) (SchematicTerm pred con quant f sv ()) where
        liftToScheme (ConstantTermBuilder c) = S_ConstantTermBuilder c
        liftToScheme (UnaryFuncApp f t) = S_UnaryFuncApp f $ liftToScheme t
        liftToScheme (BinaryFuncApp f t1 t2) 
            = S_BinaryFuncApp f (liftToScheme t1) (liftToScheme t2)
        liftToScheme BlankTerm = S_BlankTerm

instance (Schematizable sv, Schematizable f) => Schematizable ( SchematicTerm pred con quant f sv ) where
        schematize (S_ConstantTermBuilder x) = \_ -> schematize x [] 
        schematize (S_ConstantSchematicTermBuilder x) = \_ -> show x
        schematize (S_UnaryFuncApp f x) = \y -> schematize f [schematize x y]
        schematize (S_UnarySchematicFuncApp f x) 
            = \y -> show f ++ "(" ++ schematize x y ++ ")"
        schematize (S_BinaryFuncApp f x y) 
            = \z -> schematize f [schematize x z , schematize y z]
        schematize (S_BinarySchematicFuncApp f x y) 
            = \z -> show f ++ "(" ++ schematize x z ++ "," ++ schematize y z ++ ")"

instance Schematizable (SchematicTerm pred con quant f sv) => Show (SchematicTerm pred con quant f sv a) where
        show x = schematize x ["_"] --inserts a literal blank for semantic blanks. 

instance Schematizable (SchematicTerm pred con quant f sv) => Eq (SchematicTerm pred con quant f sv a) where
        (==) t1 t2 = show t1 == show t2

--------------------------------------------------------
--2.2 MultiUnification Instances
--------------------------------------------------------

instance (Schematizable f, Schematizable sv) => 
            MultiHilbert (SchematicTerm pred con quant f sv ()) (Var pred con quant f sv ()) where

        multiFreeVars ( S_ConstantTermBuilder _ ) = []
        multiFreeVars ( S_ConstantSchematicTermBuilder c ) = [FreeVar c]
        multiFreeVars ( S_UnaryFuncApp _ t ) = multiFreeVars t
        multiFreeVars ( S_UnarySchematicFuncApp f t ) = [FreeVar f] `union` multiFreeVars t
        multiFreeVars ( S_BinaryFuncApp _ t1 t2 ) = multiFreeVars t1 `union` multiFreeVars t2
        multiFreeVars ( S_BinarySchematicFuncApp f t1 t2 ) = [FreeVar f] `union` multiFreeVars t1 `union` multiFreeVars t2
        multiFreeVars ( S_BlankTerm ) = []

        multiApply _ (S_ConstantTermBuilder c) = S_ConstantTermBuilder c
        multiApply sub t@(S_ConstantSchematicTermBuilder c) = case fvLookup c sub of
            Just t' -> multiApply sub t'
            Nothing -> t
        multiApply sub ( S_UnaryFuncApp f t ) = S_UnaryFuncApp f $ multiApply sub t
        --we need to use blank terms to be able to represent substituends
        --for schematic function symbols as schematic terms
        multiApply sub (S_UnarySchematicFuncApp f t2) = case fvLookup f sub of 
            Just (S_UnarySchematicFuncApp f' S_BlankTerm) 
                -> multiApply sub $ S_UnarySchematicFuncApp f' t2
            Just (S_UnaryFuncApp f' S_BlankTerm) -> S_UnaryFuncApp f' (multiApply sub t2)
            _ -> S_UnarySchematicFuncApp f (multiApply sub t2)
        multiApply sub (S_BinaryFuncApp f t1 t2) = S_BinaryFuncApp f (multiApply sub t1) (multiApply sub t2)
        multiApply sub (S_BinarySchematicFuncApp f t1 t2) = case fvLookup f sub of
            Just (S_BinarySchematicFuncApp f' S_BlankTerm S_BlankTerm) 
                -> multiApply sub $ S_BinarySchematicFuncApp f' t1 t2
            Just (S_BinaryFuncApp f' S_BlankTerm S_BlankTerm) 
                -> S_BinaryFuncApp f' (multiApply sub t1) (multiApply sub t2)
            _ -> S_UnarySchematicFuncApp f (multiApply sub t2)
        multiApply _ (S_BlankTerm) = S_BlankTerm

instance (UniformlyEq f, UniformlyEq sv, Schematizable sv, Schematizable f) => 
        MultiMatchable (SchematicTerm pred con quant f sv ()) (Var pred con quant f sv ()) where

        --for purposes of later unification, we include schematic function
        --symbols, with blanks, among the children of a given term, and
        --match these to schematic function symbols as well as functions
        
        --the following cases are things that have no matchable children.
        multiMatch (S_ConstantTermBuilder c) (S_ConstantTermBuilder c')
            | c =* c' = Just []
        multiMatch (S_ConstantSchematicTermBuilder _) _ = Just []
        multiMatch _ (S_ConstantSchematicTermBuilder _) = Just []
        --FIXME: I now think that several of these should fail to multiMatch.
        --But the bad cases probably will not arise in practice.
        multiMatch (S_UnarySchematicFuncApp _ S_BlankTerm) _ = Just []
        multiMatch _ (S_UnarySchematicFuncApp _ S_BlankTerm) = Just []
        multiMatch (S_BinarySchematicFuncApp _ S_BlankTerm S_BlankTerm) _ = Just []
        multiMatch _ (S_BinarySchematicFuncApp _ S_BlankTerm S_BlankTerm) = Just []
        --the following cases have multiMatchable children
        multiMatch (S_UnaryFuncApp f t) (S_UnaryFuncApp f' t') 
            | f =* f' = Just [t |-| t']
        multiMatch t1@(S_UnarySchematicFuncApp _ t) t2@(S_UnaryFuncApp _ t')
            = Just [unsaturateT t1 |-| unsaturateT t2, t |-| t']
        multiMatch t1@(S_UnarySchematicFuncApp _ t) t2@(S_UnarySchematicFuncApp _ t')
            = Just [unsaturateT t1 |-| unsaturateT t2, t |-| t']
        multiMatch t1@(S_UnaryFuncApp _ t) t2@(S_UnarySchematicFuncApp _ t')
            = Just [unsaturateT t1 |-| unsaturateT t2, t |-| t']
        multiMatch (S_BinaryFuncApp f t1 t2) (S_BinaryFuncApp f' t1' t2')
            | f =* f' = Just [t1 |-| t1',t2 |-| t2']
        multiMatch t@(S_BinarySchematicFuncApp _ t1 t2) t'@(S_BinaryFuncApp _ t1' t2')
            = Just [unsaturateT t |-| unsaturateT t',t1 |-| t1' , t2 |-| t2']
        multiMatch t@(S_BinarySchematicFuncApp _ t1 t2) t'@(S_BinarySchematicFuncApp _ t1' t2')
            = Just [unsaturateT t |-| unsaturateT t', t1 |-| t1', t2 |-| t2']
        multiMatch t@(S_BinaryFuncApp _ t1 t2) t'@(S_BinarySchematicFuncApp _ t1' t2')
            = Just [unsaturateT t |-| unsaturateT t', t1 |-| t1', t2 |-| t2']
        --everything else counts as failure to multiMatch
        multiMatch _ _ = Nothing

instance (UniformlyEq f, UniformlyEq sv, Schematizable sv, Schematizable f) =>
        MultiUnifiable (SchematicTerm pred con quant f sv ()) (Var pred con quant f sv ()) where

        multiMatchVar (S_ConstantSchematicTermBuilder c) t = Just (Mapping c t)
        multiMatchVar (S_UnarySchematicFuncApp f S_BlankTerm) t@(S_UnaryFuncApp _ S_BlankTerm) 
            = Just (Mapping f t) 
        multiMatchVar (S_UnarySchematicFuncApp f S_BlankTerm ) t@(S_UnarySchematicFuncApp _ S_BlankTerm) 
            = Just (Mapping f t) 
        multiMatchVar (S_BinarySchematicFuncApp f S_BlankTerm S_BlankTerm) t@(S_BinaryFuncApp _ S_BlankTerm S_BlankTerm) 
            = Just (Mapping f t) 
        multiMatchVar (S_BinarySchematicFuncApp f S_BlankTerm S_BlankTerm ) t@(S_BinarySchematicFuncApp _ S_BlankTerm S_BlankTerm) 
            = Just (Mapping f t)
        multiMatchVar _ _ = Nothing

        multiMakeTerm (v@(ConstantTermVar _)) = S_ConstantSchematicTermBuilder v
        multiMakeTerm (v@(UnaryFuncVar _))= S_UnarySchematicFuncApp v S_BlankTerm
        multiMakeTerm (v@(BinaryFuncVar _)) = S_BinarySchematicFuncApp v S_BlankTerm S_BlankTerm
        multiMakeTerm _ = S_BlankTerm

--------------------------------------------------------
--3. MultiUnification for Formulas
--------------------------------------------------------

--------------------------------------------------------
--3.1 Data Types
--------------------------------------------------------

data SchematicForm pred con quant f sv a where
        S_BlankForm                          :: SchematicForm pred con quant f sv ()
        S_ConstantFormBuilder                :: {s_pVal            :: sv a}
                                                                   -> SchematicForm pred con quant f sv ()
        S_ConstantSchematicFormBuilder       :: {schemePVal        :: Var pred con quant f sv () (SchematicForm pred con quant f sv ())}
                                                                   -> SchematicForm pred con quant f sv ()
        S_UnaryPredicate                     :: { s_uPred          :: pred (b -> a),
                                                s_uSub             :: SchematicTerm pred con quant f sv ()}
                                                                   -> SchematicForm pred con quant f sv ()
        S_UnarySchematicPredicate            :: { schemeUPred      :: Var pred con quant f sv () (SchematicForm pred con quant f sv ()),
                                                s_uSub             :: SchematicTerm pred con quant f sv ()}
                                                                   -> SchematicForm pred con quant f sv ()
        S_BinaryPredicate                    :: { s_bPred          :: pred (b -> c -> a),
                                                s_bSub1            :: SchematicTerm pred con quant f sv (),
                                                s_bSub2            :: SchematicTerm pred con quant f sv ()}
                                                                   -> SchematicForm pred con quant f sv ()
        S_BinarySchematicPredicate           :: { schemeBPred      :: Var pred con quant f sv () (SchematicForm pred con quant f sv ()),
                                                s_bSub1            :: SchematicTerm pred con quant f sv (),
                                                s_bSub2            :: SchematicTerm pred con quant f sv ()}
                                                                   -> SchematicForm pred con quant f sv ()
        S_UnaryConnect                       :: { s_uConn          :: con (b -> a),
                                                s_uForm            :: SchematicForm pred con quant f sv () } 
                                                                   -> SchematicForm pred con quant f sv ()
        S_UnarySchematicConnect              :: { schemeUConn      :: Var pred con quant f sv () (SchematicForm pred con quant f sv ()),
                                                s_uForm            :: SchematicForm pred con quant f sv () } 
                                                                   -> SchematicForm pred con quant f sv ()
        S_BinaryConnect                      :: { s_bConn          :: con (b -> c -> a),
                                                s_bForm1           :: SchematicForm pred con quant f sv (),
                                                s_bForm2           :: SchematicForm pred con quant f sv () }
                                                                   -> SchematicForm pred con quant f sv ()
        S_BinarySchematicConnect             :: { schemeBConn      :: Var pred con quant f sv () (SchematicForm pred con quant f sv ()),
                                                s_bForm1           :: SchematicForm pred con quant f sv (),
                                                s_bForm2           :: SchematicForm pred con quant f sv () }
                                                                   -> SchematicForm pred con quant f sv ()
        S_Bind                               :: { s_quantifier     :: quant ((sv b ->c) -> a) ,
                                                s_quantified       :: Term f sv d -> SchematicForm pred con quant f sv ()
                                                }                  -> SchematicForm pred con quant f sv ()
        S_SchematicBind                      :: { schemeQuantifier :: Var pred con quant f sv () (SchematicForm pred con quant f sv ()),
                                                s_quantified       :: Term f sv d -> SchematicForm pred con quant f sv ()
                                                }                  -> SchematicForm pred con quant f sv ()
                                                

instance Scheme ( Form pred con quant f sv a ) ( SchematicForm pred con quant f sv () ) where
        liftToScheme (ConstantFormBuilder c) = S_ConstantFormBuilder c
        liftToScheme (UnaryPredicate p t) = S_UnaryPredicate p $ liftToScheme t
        liftToScheme (BinaryPredicate p t1 t2) = S_BinaryPredicate p (liftToScheme t1) (liftToScheme t2)
        liftToScheme (UnaryConnect c f) = S_UnaryConnect c $ liftToScheme f
        liftToScheme (BinaryConnect c f1 f2) = S_BinaryConnect c (liftToScheme f1) (liftToScheme f2)
        liftToScheme (Bind q q'ed) = S_Bind q $ \x -> liftToScheme (q'ed x)
        liftToScheme BlankForm = S_BlankForm

instance (Schematizable pred, Schematizable con, Schematizable quant, Schematizable sv,
        Schematizable f, S_NextVar sv quant, SchemeVar sv)
        => Schematizable (SchematicForm pred con quant f sv) where
                schematize (S_ConstantFormBuilder x) = \_ -> schematize x []
                schematize (S_ConstantSchematicFormBuilder x) = \_ -> show x 
                schematize (S_UnaryPredicate p t) = 
                    \y -> schematize p [schematize t y]
                schematize (S_UnarySchematicPredicate p t) = 
                    \y -> show p ++ "(" ++ schematize t y ++ ")"
                schematize (S_BinaryPredicate p t1 t2) = 
                    \y -> schematize p [schematize t1 y, schematize t2 y]
                schematize (S_BinarySchematicPredicate p t1 t2) = 
                    \y -> show p ++ "(" ++ schematize t1 y ++ "," ++ schematize t2 y ++ ")"
                schematize (S_UnaryConnect c f) = 
                    \y -> schematize c [schematize f y]
                schematize (S_UnarySchematicConnect c f) = 
                    \y -> show c ++ schematize f y
                schematize (S_BinaryConnect c f1 f2) = 
                    \y -> schematize c [schematize f1 y,schematize f2 y]
                schematize (S_BinarySchematicConnect c f1 f2) = 
                    \y -> "(" ++ schematize f1 y ++ show c ++ schematize f2 y ++ ")"
                schematize (S_Bind q f) = 
                    \_ -> schematize q [s_appropriateVariable (f BlankTerm) q, 
                        schematize (f BlankTerm) [s_appropriateVariable (f BlankTerm) q]]
                schematize (S_SchematicBind q f) = 
                    \_ -> show q ++ appropriateSchematicVariable (f BlankTerm) q ++ "(" ++
                        schematize (f BlankTerm) [appropriateSchematicVariable (f BlankTerm) q] ++ ")"
                schematize _ = \_ -> ""

instance Schematizable (SchematicForm pred con quant f sv) => Show (SchematicForm pred con quant f sv a) where
        show x = schematize x ["_"] --inserts a literal blank for semantic blanks. 

instance Schematizable (SchematicForm pred con quant f sv) => Eq (SchematicForm pred con quant f sv a) where
        (==) f1 f2 = show f1 == show f2

instance Schematizable (SchematicForm pred con quant f sv) => Ord (SchematicForm pred con quant f sv a) where
        (<=) f1 f2 = show f1 <= show f2

--------------------------------------------------------
--3.2 MultiUnification Instances
--------------------------------------------------------

instance (Schematizable pred, Schematizable con, Schematizable quant, Schematizable f, Schematizable sv, 
        S_NextVar sv quant, SchemeVar sv) => 
        MultiHilbert (SchematicForm pred con quant f sv ()) (Var pred con quant f sv ()) where

        multiFreeVars ( S_BlankForm) = []
        multiFreeVars ( S_ConstantFormBuilder c ) = []
        multiFreeVars ( S_ConstantSchematicFormBuilder c ) = [FreeVar c]
        multiFreeVars ( S_UnaryPredicate p t ) = multiFreeVars t
        multiFreeVars ( S_UnarySchematicPredicate p t ) = [FreeVar p] `union` multiFreeVars t
        multiFreeVars ( S_BinaryPredicate p t1 t2 ) = multiFreeVars t1 `union` multiFreeVars t2
        multiFreeVars ( S_BinarySchematicPredicate p t1 t2 ) = [FreeVar p] `union` multiFreeVars t1 `union` multiFreeVars t2
        multiFreeVars ( S_UnaryConnect p f ) = multiFreeVars f
        multiFreeVars ( S_UnarySchematicConnect c f ) = [FreeVar c] `union` multiFreeVars f
        multiFreeVars ( S_BinaryConnect c f1 f2 ) = multiFreeVars f1 `union` multiFreeVars f2
        multiFreeVars ( S_BinarySchematicConnect c f1 f2 ) = [FreeVar c] `union` multiFreeVars f1 `union` multiFreeVars f2
        multiFreeVars ( S_Bind q q'ed ) = multiFreeVars (q'ed BlankTerm)
        multiFreeVars ( S_SchematicBind q q'ed ) = [FreeVar q] `union` (multiFreeVars $ q'ed BlankTerm)

        multiApply sub f@(S_ConstantSchematicFormBuilder c) = case fvLookup c sub of
            Just f' -> multiApply sub f'
            _ -> f
        multiApply sub f@(S_UnarySchematicPredicate p t) = case fvLookup p sub of
            Just (S_UnarySchematicPredicate p' S_BlankTerm) -> multiApply sub $ S_UnarySchematicPredicate p' t
            Just (S_UnaryPredicate p' S_BlankTerm) -> S_UnaryPredicate p' t
            _ -> f
        multiApply sub f@(S_BinarySchematicPredicate p t1 t2) = case fvLookup p sub of 
            Just (S_BinarySchematicPredicate p' S_BlankTerm S_BlankTerm) -> multiApply sub $ S_BinarySchematicPredicate p' t1 t2
            Just (S_BinaryPredicate p' S_BlankTerm S_BlankTerm) -> multiApply sub $ S_BinaryPredicate p' t1 t2
            _ -> f
        multiApply sub (S_UnaryConnect c f) = S_UnaryConnect c $ multiApply sub f
        multiApply sub (S_UnarySchematicConnect c f) = case fvLookup c sub of 
            Just (S_UnarySchematicConnect c' S_BlankForm) -> multiApply sub $ S_UnarySchematicConnect c' f
            Just (S_UnaryConnect c' S_BlankForm) -> S_UnaryConnect c' $ multiApply sub f
            _ -> S_UnarySchematicConnect c $ multiApply sub f
        multiApply sub (S_BinaryConnect c f1 f2) = S_BinaryConnect c (multiApply sub f1) (multiApply sub f2)
        multiApply sub (S_BinarySchematicConnect c f1 f2) = case fvLookup c sub of
            Just (S_BinarySchematicConnect c' S_BlankForm S_BlankForm) -> multiApply sub $ S_BinarySchematicConnect c' f1 f2
            Just (S_BinaryConnect c' S_BlankForm S_BlankForm) -> multiApply sub $ S_BinaryConnect c' (multiApply sub f1) (multiApply sub f2)
            _ -> S_BinarySchematicConnect c (multiApply sub f1) (multiApply sub f2)
        multiApply sub (S_Bind q q'ed) = S_Bind q (\x -> multiApply sub $ q'ed x)
        multiApply sub (S_SchematicBind q q'ed) = case fvLookup q sub of
            Just (S_SchematicBind q' _) -> multiApply sub (S_SchematicBind q' q'ed)
            Just (S_Bind q' _) -> S_Bind q' (\x -> multiApply sub $ q'ed x)
            _ -> S_SchematicBind q (\x -> multiApply sub $ q'ed x)
        multiApply _ f = f

instance (UniformlyEq f, UniformlyEq pred, UniformlyEq sv, UniformlyEq con, UniformlyEq quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
        S_NextVar sv quant, SchemeVar sv)
        => MultiMatchable (SchematicForm pred con quant f sv ()) (Var pred con quant f sv ()) where
        
        --leaves of the parsing
        multiMatch (S_ConstantSchematicFormBuilder _) _                     = Just []
        multiMatch _ (S_ConstantSchematicFormBuilder _)                     = Just []
        multiMatch (S_UnaryPredicate _ S_BlankTerm) _                       = Just []
        multiMatch _ (S_UnaryPredicate _ S_BlankTerm)                       = Just []
        multiMatch (S_BinaryPredicate _ S_BlankTerm S_BlankTerm) _          = Just []
        multiMatch _ (S_BinaryPredicate _ S_BlankTerm S_BlankTerm)          = Just []
        multiMatch _ (S_UnaryConnect _ S_BlankForm)                         = Just []
        multiMatch (S_UnaryConnect _ S_BlankForm) _                         = Just []
        multiMatch _ (S_BinaryConnect _ S_BlankForm S_BlankForm)            = Just []
        multiMatch (S_BinaryConnect _ S_BlankForm S_BlankForm) _            = Just []
        multiMatch (S_UnarySchematicPredicate _ S_BlankTerm) _              = Just []
        multiMatch _ (S_UnarySchematicPredicate _ S_BlankTerm)              = Just []
        multiMatch (S_BinarySchematicPredicate _ S_BlankTerm S_BlankTerm) _ = Just []
        multiMatch _ (S_BinarySchematicPredicate _ S_BlankTerm S_BlankTerm) = Just []
        multiMatch _ (S_UnarySchematicConnect _ S_BlankForm)                = Just []
        multiMatch (S_UnarySchematicConnect _ S_BlankForm) _                = Just []
        multiMatch _ (S_BinarySchematicConnect _ S_BlankForm S_BlankForm)   = Just []
        multiMatch (S_BinarySchematicConnect _ S_BlankForm S_BlankForm) _   = Just []
        --cases where a constructor must multiMatch
        multiMatch (S_ConstantFormBuilder c) (S_ConstantFormBuilder c')
            | c =* c' = Just []
        multiMatch f@(S_UnaryPredicate p t1 ) f'@(S_UnaryPredicate p' t1' )
            | p =* p' = Just []
        multiMatch f@(S_BinaryPredicate p t1 t2) f'@(S_BinaryPredicate p' t1' t2')
            | p =* p' = Just []
        multiMatch f@(S_UnaryConnect c f1 ) f'@(S_UnaryConnect c' f1' )
            | c =* c' = Just [f1 |+| f1']
        multiMatch f@(S_BinaryConnect c f1 f2) f'@(S_BinaryConnect c' f1' f2')
            | c =* c' = Just [f1 |+| f1', f2 |+| f2']
        --schematic cases, where the multiMatch doesn't require a multiMatching
        --constructor
        multiMatch f@(S_BinarySchematicConnect _ f1 f2) f'@(S_BinaryConnect _ f1' f2')
            = Just [unsaturateF f |+| unsaturateF f', f1 |+| f1', f2 |+| f2']
        multiMatch f@(S_BinarySchematicConnect c f1 f2) f'@(S_BinarySchematicConnect c' f1' f2')
            = Just [unsaturateF f |+| unsaturateF f', f1 |+| f1', f2 |+| f2']
        multiMatch f@(S_UnarySchematicConnect c f1 ) f'@(S_UnaryConnect c' f1')
            = Just [unsaturateF f |+| unsaturateF f', f1 |+| f1'] 
        multiMatch f@(S_UnarySchematicConnect c f1 ) f'@(S_UnarySchematicConnect c' f1' )
            = Just [unsaturateF f |+| unsaturateF f', f1 |+| f1']
        multiMatch f@(S_BinarySchematicPredicate c t1 t2) f'@(S_BinaryPredicate c' t1' t2')
            = Just [unsaturateF f |+| unsaturateF f']
        multiMatch f@(S_BinarySchematicPredicate c t1 t2) f'@(S_BinarySchematicPredicate c' t1' t2')
            = Just [unsaturateF f |+| unsaturateF f']
        multiMatch f@(S_UnarySchematicPredicate c t1 ) f'@(S_UnaryPredicate c' t1')
            = Just [unsaturateF f |+| unsaturateF f']
        multiMatch f@(S_UnarySchematicPredicate c t1 ) f'@(S_UnarySchematicPredicate c' t1' )
            = Just [unsaturateF f |+| unsaturateF f']
        multiMatch _ _ = Nothing

instance (UniformlyEq f, UniformlyEq pred, UniformlyEq sv, UniformlyEq con, UniformlyEq quant, 
        Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
        S_NextVar sv quant, SchemeVar sv)
        => MultiUnifiable (SchematicForm pred con quant f sv ()) (Var pred con quant f sv()) where

        multiMatchVar (S_ConstantSchematicFormBuilder c) f = Just (Mapping c f)
        multiMatchVar (S_UnarySchematicPredicate p S_BlankTerm) f@(S_UnaryPredicate _ S_BlankTerm)
            = Just (Mapping p f)
        multiMatchVar (S_UnarySchematicPredicate p S_BlankTerm) f@(S_UnarySchematicPredicate _ S_BlankTerm)
            = Just (Mapping p f)
        multiMatchVar (S_BinarySchematicPredicate p S_BlankTerm S_BlankTerm) f@(S_BinaryPredicate _ S_BlankTerm S_BlankTerm)
            = Just (Mapping p f)
        multiMatchVar (S_BinarySchematicPredicate p S_BlankTerm S_BlankTerm) f@(S_BinarySchematicPredicate _ S_BlankTerm S_BlankTerm)
            = Just (Mapping p f)
        multiMatchVar (S_UnarySchematicConnect c S_BlankForm) f@(S_UnaryConnect _ S_BlankForm) 
            = Just (Mapping c f)
        multiMatchVar (S_UnarySchematicConnect c S_BlankForm) f@(S_UnarySchematicConnect _ S_BlankForm) 
            = Just (Mapping c f)
        multiMatchVar (S_BinarySchematicConnect c S_BlankForm S_BlankForm) f@(S_BinaryConnect _ S_BlankForm S_BlankForm) 
            = Just (Mapping c f)
        multiMatchVar (S_BinarySchematicConnect c S_BlankForm S_BlankForm) f@(S_BinarySchematicConnect _ S_BlankForm S_BlankForm) 
            = Just (Mapping c f)
        multiMatchVar _ _ = Nothing

        multiMakeTerm v@(ConstantFormVar _) = S_ConstantSchematicFormBuilder v
        multiMakeTerm v@(UnaryPredVar _) = S_UnarySchematicPredicate v S_BlankTerm
        multiMakeTerm v@(BinaryPredVar _) = S_BinarySchematicPredicate v S_BlankTerm S_BlankTerm
        multiMakeTerm v@(UnaryConnectVar _) = S_UnarySchematicConnect v S_BlankForm
        multiMakeTerm v@(BinaryConnectVar _) = S_BinarySchematicConnect v S_BlankForm S_BlankForm 
        
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

(|+|) :: (UniformlyEq f, UniformlyEq pred, UniformlyEq sv, UniformlyEq con, UniformlyEq quant, 
            Schematizable f, Schematizable pred, Schematizable sv, Schematizable con, Schematizable quant,
            S_NextVar sv quant, SchemeVar sv) => 
            SchematicForm pred con quant f sv () -> SchematicForm pred con quant f sv () -> Paring (Var pred con quant f sv ())
(|+|) = UnifiablePairing

(|-|) :: (UniformlyEq f, UniformlyEq sv, Schematizable sv, Schematizable f) => 
            SchematicTerm pred con quant f sv () -> SchematicTerm pred con quant f sv () -> Paring (Var pred con quant f sv ())
(|-|) = UnifiablePairing
