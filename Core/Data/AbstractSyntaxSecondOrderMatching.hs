{-#LANGUAGE GADTs, TypeSynonymInstances, FunctionalDependencies, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables #-}

module Carnap.Core.Data.AbstractSyntaxSecondOrderMatching where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Unification.HigherOrderMatching
import Carnap.Core.Unification.HigherOrderUtil
import Control.Lens
import Control.Lens.Plated
import Data.List
import Control.Applicative

--I tried copy as much over from the previous attempts at Unification as possible

--------------------------------------------------------
--1.Generalities
--------------------------------------------------------

--------------------------------------------------------
--1.1 Schematic Symbols
--------------------------------------------------------

data Var pred con quant f sv a s where
        ConstantTermVar  :: String -> Var pred con quant f sv () (SchematicTerm pred con quant f sv ())
        UnaryFuncVar     :: String -> Var pred con quant f sv () (SchematicTerm pred con quant f sv ())
        BinaryFuncVar    :: String -> Var pred con quant f sv () (SchematicTerm pred con quant f sv ())

        ConstantFormVar  :: String -> Var pred con quant f sv () (SchematicForm pred con quant f sv ())
        UnaryPredVar     :: String -> Var pred con quant f sv () (SchematicForm pred con quant f sv ())
        BinaryPredVar    :: String -> Var pred con quant f sv () (SchematicForm pred con quant f sv ())
        UnaryConnectVar  :: String -> Var pred con quant f sv () (SchematicForm pred con quant f sv ())
        BinaryConnectVar :: String -> Var pred con quant f sv () (SchematicForm pred con quant f sv ())
        QuantVar         :: String -> Var pred con quant f sv () (SchematicForm pred con quant f sv ())

        SideForms        :: String -> Var pred con quant f sv () (SSequentItem pred con quant f sv)

instance Show (Var pred con quant f sv a s) where
        show ( ConstantTermVar s ) = s
        show ( UnaryFuncVar s )    = s
        show ( BinaryFuncVar s )   = s
        show ( ConstantFormVar s)  = s
        show ( UnaryPredVar s)     = s
        show ( BinaryPredVar s)    = s
        show ( UnaryConnectVar s)  = s
        show ( BinaryConnectVar s) = s
        show ( QuantVar s)         = s
        show ( SideForms s)        = s

instance EquaitableVar (Var pred con quant f sv a) where
    getLikeSchema (ConstantTermVar s) (ConstantTermVar s') t   | s == s' = Just t
    getLikeSchema (UnaryFuncVar s) (UnaryFuncVar s') t         | s == s' = Just t
    getLikeSchema (BinaryFuncVar s) (BinaryFuncVar s') t       | s == s' = Just t
    getLikeSchema (ConstantFormVar s) (ConstantFormVar s') t   | s == s' = Just t
    getLikeSchema (UnaryPredVar s) (UnaryPredVar s') t         | s == s' = Just t
    getLikeSchema (BinaryPredVar s) (BinaryPredVar s') t       | s == s' = Just t
    getLikeSchema (UnaryConnectVar s) (UnaryConnectVar s') t   | s == s' = Just t
    getLikeSchema (BinaryConnectVar s) (BinaryConnectVar s') t | s == s' = Just t
    getLikeSchema (QuantVar s) (QuantVar s') t                 | s == s' = Just t
    getLikeSchema (SideForms s) (SideForms s') t               | s == s' = Just t
    getLikeSchema _           _            _           = Nothing

instance Eq (Var pred con quant f sv a s) where
        s == s' = eq s s'

instance Ord (Var pred con quant f sv a s) where
        s <= s' = show s <= show s'

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
        S_BlankTerm                    ::   String -> SchematicTerm pred con quant f sv ()
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
        liftToScheme (BlankTerm s) = S_BlankTerm s

instance (Schematizable sv, Schematizable f) => Schematizable ( SchematicTerm pred con quant f sv ) where
        schematize (S_BlankTerm s) = const s
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
--2.2 Lens stuff
--------------------------------------------------------

--need this to make isomorphisms over functions so we can look at them
--this is basically the inverse of applying a blank term with a certain name
makeTermLam :: String -> SchematicTerm pred con quant f sv () -> Term f sv d -> SchematicTerm pred con quant f sv ()
makeTermLam s b@(S_BlankTerm s')
    | s == s'   = \t -> liftToScheme t
    | otherwise = \t -> b
makeTermLam s (S_UnaryFuncApp func tm)                = \t -> S_UnaryFuncApp func (makeTermLam s tm t)
makeTermLam s (S_UnarySchematicFuncApp func tm)       = \t -> S_UnarySchematicFuncApp func (makeTermLam s tm t)
makeTermLam s (S_BinaryFuncApp func tm1 tm2)          = \t -> S_BinaryFuncApp func (makeTermLam s tm1 t) (makeTermLam s tm2 t)
makeTermLam s (S_BinarySchematicFuncApp func tm1 tm2) = \t -> S_BinarySchematicFuncApp func (makeTermLam s tm1 t) (makeTermLam s tm2 t)
makeTermLam _ node                                    = \t -> node

instance Plated (SchematicTerm pred con quant f sv a) where
    plate f (S_UnaryFuncApp func tm)                = (S_UnaryFuncApp func) <$> (plate f tm)
    plate f (S_UnarySchematicFuncApp func tm)       = S_UnarySchematicFuncApp func <$> (plate f tm)
    plate f (S_BinaryFuncApp func tm1 tm2)          = (S_BinaryFuncApp func) <$> (plate f tm1) <*> (plate f tm2)
    plate f (S_BinarySchematicFuncApp func tm1 tm2) = (S_BinarySchematicFuncApp func) <$> (plate f tm1) <*> (plate f tm2)
    plate _ node                                    = pure node

--------------------------------------------------------
--2.3 Second Order Matching Instances
--------------------------------------------------------

--this is only for the purpose of zipping terms up in a lambda
--for the the purposes of performing a "Beta" like reduction
--highly specilized and also really really annoying to write
--this also enforces second orderness!
getLikeTerm :: Var pred con quant f sv a schema' -> SchematicTerm pred con quant f sv a -> Maybe schema'
getLikeTerm (ConstantTermVar v) s = Just s
getLikeTerm _                   _ = Nothing

--zipTermLamMapping :: Matchable concrete schema var => [FreeVar var] -> [schema] -> Maybe [Mapping var]
zipTermLamMapping ((FreeVar v):xs) (s:ss) = do
    s' <- getLikeTerm v s
    rest <- zipTermLamMapping xs ss
    return $ (LambdaMapping v [] s') : rest
zipTermLamMapping [] [] = Just []

--again I am cheating and reserving some strange names here
--We can look at how to do this better later
--we only have binary varibles so we only need two varibles as long as these terms never occur anywhere else
cheatVars = map ConstantTermVar ["alpha", "beta"]

termHasBlanks :: (SchemeVar sv, S_NextVar sv quant) => SchematicTerm pred con quant f sv () -> Bool
termHasBlanks (S_BlankTerm _) = True
termHasBlanks node            = composOpFold False (||) termHasBlanks node

formHasBlanks :: forall pred con quant f sv. (SchemeVar sv, S_NextVar sv quant) => SchematicForm pred con quant f sv () -> Bool
formHasBlanks node = any termHasBlanks (toListOf mplate node)
    where mplate = multiplate :: Simple Traversal (SchematicForm pred con quant f sv ()) (SchematicTerm pred con quant f sv ())

mapHasBlanks :: (SchemeVar sv, S_NextVar sv quant) => Mapping (Var pred con quant f sv a) -> Bool
mapHasBlanks (LambdaMapping (ConstantTermVar _) _ s)  = termHasBlanks s
mapHasBlanks (LambdaMapping (ConstantFormVar _) _ s)  = formHasBlanks s
mapHasBlanks (LambdaMapping (UnaryFuncVar _) _ s)     = termHasBlanks s
mapHasBlanks (LambdaMapping (BinaryFuncVar _) _ s)    = termHasBlanks s
mapHasBlanks (LambdaMapping (UnaryConnectVar _) _ s)  = formHasBlanks s
mapHasBlanks (LambdaMapping (BinaryConnectVar _) _ s) = formHasBlanks s
mapHasBlanks (LambdaMapping (UnaryPredVar _) _ s)     = formHasBlanks s
mapHasBlanks (LambdaMapping (BinaryPredVar _) _ s)    = formHasBlanks s
mapHasBlanks (LambdaMapping (QuantVar _) _ s)         = formHasBlanks s

--finally we need a few more helper terms to define how pattern matching works
instance (SchemeVar sv, S_NextVar sv quant, UniformlyEquaitable f, UniformlyEquaitable sv, Schematizable sv, Schematizable f) => Matchable (SchematicTerm pred con quant f sv ()) (Var pred con quant f sv ()) where
    freeVars (S_ConstantSchematicTermBuilder v) = [FreeVar v]
    freeVars (S_UnarySchematicFuncApp func tm) = [FreeVar func] `union` (freeVars tm)
    freeVars (S_BinarySchematicFuncApp func tm1 tm2) = [FreeVar func] `union` (freeVars tm1) `union` (freeVars tm2)
    freeVars node = composOpFold [] union freeVars node

    apply sub old@(S_ConstantSchematicTermBuilder v) = case fvLookup v sub of
        Just new -> new
        Nothing -> old
    apply sub old@(S_UnarySchematicFuncApp func tm) = case fvKMapLookup func sub of
        Just (KLambdaMapping _ fvs new) -> case zipTermLamMapping fvs [apply sub tm] of
            Just argSub -> apply argSub new
            Nothing     -> over plate (apply sub) old
        Nothing         -> over plate (apply sub) old
    apply sub old@(S_BinarySchematicFuncApp func tm1 tm2) = case fvKMapLookup func sub of
        Just (KLambdaMapping _ fvs new) -> case zipTermLamMapping fvs [apply sub tm1, apply sub tm2] of
            Just argSub -> apply argSub new
            Nothing     -> over plate (apply sub) old
        Nothing         -> over plate (apply sub) old
    --apply sub (S_BinarySchematicFuncApp func tm1 tm2) = [FreeVar func] `union` (apply tm1) `union` (apply tm2)
    apply sub node = over plate (apply sub) node

    match (S_BlankTerm s) (S_BlankTerm s') | s == s'   = Just []
    match (S_ConstantTermBuilder c) (S_ConstantTermBuilder c') | c `eq` c' = Just []
    match (S_UnaryFuncApp f tm) (S_UnaryFuncApp f' tm') | f `eq` f' = Just [tm :=: tm']
    match (S_BinaryFuncApp f tm1 tm2) (S_BinaryFuncApp f' tm1' tm2') | f `eq` f' = Just [tm1 :=: tm1', tm2 :=: tm2']
    match _ _ = Nothing

    matchVar (S_ConstantSchematicTermBuilder v)   c = [LambdaMapping v [] c]
    matchVar (S_UnarySchematicFuncApp f tm)       c = filter (not . mapHasBlanks) $ makeSub f (zip cheatVars [tm]) c
    matchVar (S_BinarySchematicFuncApp f tm1 tm2) c = filter (not . mapHasBlanks) $ makeSub f (zip cheatVars [tm1, tm2]) c
    matchVar _                                    _ = []

    makeTerm = S_ConstantSchematicTermBuilder

--------------------------------------------------------
--3. Unification for Formulas
--------------------------------------------------------

--------------------------------------------------------
--3.0 Lens stuff
--------------------------------------------------------

--need this to make isomorphisms over functions so we can look at them
--this is basically the inverse of applying a blank term with a certain name
makeFormLam :: String -> SchematicForm pred con quant f sv () -> Term f sv d -> SchematicForm pred con quant f sv ()
makeFormLam s (S_UnaryConnect func tm)                  = \t -> S_UnaryConnect func (makeFormLam s tm t)
makeFormLam s (S_UnarySchematicConnect func tm)         = \t -> S_UnarySchematicConnect func (makeFormLam s tm t)
makeFormLam s (S_BinaryConnect func tm1 tm2)            = \t -> S_BinaryConnect func (makeFormLam s tm1 t) (makeFormLam s tm2 t)
makeFormLam s (S_BinarySchematicConnect func tm1 tm2)   = \t -> S_BinarySchematicConnect func (makeFormLam s tm1 t) (makeFormLam s tm2 t)
makeFormLam s (S_UnaryPredicate func tm)                = \t -> S_UnaryPredicate func (makeTermLam s tm t)
makeFormLam s (S_UnarySchematicPredicate func tm)       = \t -> S_UnarySchematicPredicate func (makeTermLam s tm t)
makeFormLam s (S_BinaryPredicate func tm1 tm2)          = \t -> S_BinaryPredicate func (makeTermLam s tm1 t) (makeTermLam s tm2 t)
makeFormLam s (S_BinarySchematicPredicate func tm1 tm2) = \t -> S_BinarySchematicPredicate func (makeTermLam s tm1 t) (makeTermLam s tm2 t)
makeFormLam s (S_Bind q sub)                            = \t -> S_Bind q (\t' -> makeFormLam s (sub t') t)
makeFormLam s (S_SchematicBind q sub)                   = \t -> S_SchematicBind q (\t' -> makeFormLam s (sub t') t)
makeFormLam _ node                                      = \t -> node

makeIso quant sub = iso to from
    where varName = s_appropriateVariable (sub $ BlankTerm "*") quant
          to sub' = sub' $ BlankTerm varName
          from to' = makeFormLam varName to'

makeIso2 quant sub = iso to from
    where varName = appropriateSchematicVariable (sub $ BlankTerm "*") quant
          to sub' = sub' $ BlankTerm varName
          from to' = makeFormLam varName to'

instance (SchemeVar sv, S_NextVar sv quant) => Plated (SchematicForm pred con quant f sv ()) where
    plate f (S_UnaryConnect c sub)                 = (S_UnaryConnect c) <$> f sub
    plate f (S_UnarySchematicConnect v sub)        = (S_UnarySchematicConnect v) <$> f sub
    plate f (S_BinaryConnect p sub1 sub2)          = (S_BinaryConnect p) <$> f sub1 <*> f sub2
    plate f (S_BinarySchematicConnect v sub1 sub2) = (S_BinarySchematicConnect v) <$> f sub1 <*> f sub2
    plate f (S_Bind q sub)                         = (S_Bind q) <$> (makeIso q sub) f sub
    plate f (S_SchematicBind q sub)                = (S_SchematicBind q) <$> (makeIso2 q sub) f sub
    plate _ node                                   = pure node

instance (SchemeVar sv, S_NextVar sv quant) => MultiPlated (SchematicForm pred con quant f sv ()) (SchematicTerm pred con quant f sv ()) where
    multiplate f (S_UnaryPredicate c sub)                 = (S_UnaryPredicate c) <$> f sub
    multiplate f (S_UnarySchematicPredicate v sub)        = (S_UnarySchematicPredicate v) <$> f sub
    multiplate f (S_BinaryPredicate p sub1 sub2)          = (S_BinaryPredicate p) <$> f sub1 <*> f sub2
    multiplate f (S_BinarySchematicPredicate v sub1 sub2) = (S_BinarySchematicPredicate v) <$> f sub1 <*> f sub2

    multiplate f (S_UnaryConnect c sub)                   = (S_UnaryConnect c) <$> multiplate f sub
    multiplate f (S_UnarySchematicConnect v sub)          = (S_UnarySchematicConnect v) <$> multiplate f sub
    multiplate f (S_BinaryConnect p sub1 sub2)            = (S_BinaryConnect p) <$> multiplate f sub1 <*> multiplate f sub2
    multiplate f (S_BinarySchematicConnect v sub1 sub2)   = (S_BinarySchematicConnect) v <$> multiplate f sub1 <*> multiplate f sub2
    multiplate f (S_Bind q sub)                           = (S_Bind q) <$> (makeIso q sub . multiplate) f sub
    multiplate f (S_SchematicBind q sub)                  = (S_SchematicBind q) <$> (makeIso2 q sub . multiplate) f sub
    multiplate _ node                                     = pure node

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
        S_Bind                               :: { s_quantifier     :: quant ((sv b -> c) -> a) ,
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
        liftToScheme (BlankForm _) = S_BlankForm

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
                    \l -> schematize q [s_appropriateVariable (f $ BlankTerm "*") q, 
                        schematize (f $ BlankTerm $ s_appropriateVariable (f $ BlankTerm "*") q) l]
                schematize (S_SchematicBind q f) = 
                    \l -> show q ++ appropriateSchematicVariable (f $ BlankTerm "*") q ++ "(" ++
                        schematize (f $ BlankTerm $ appropriateSchematicVariable (f $ BlankTerm "*") q) l ++ ")"
                schematize _ = const ""

instance Schematizable (SchematicForm pred con quant f sv) => Show (SchematicForm pred con quant f sv a) where
        show x = schematize x ["_"] --inserts a literal blank for semantic blanks. 

instance Schematizable (SchematicForm pred con quant f sv) => Eq (SchematicForm pred con quant f sv a) where
        (==) f1 f2 = show f1 == show f2

instance Schematizable (SchematicForm pred con quant f sv) => Ord (SchematicForm pred con quant f sv a) where
        (<=) f1 f2 = show f1 <= show f2     

--------------------------------------------------------
--3.3 Second Order Matching Instances
--------------------------------------------------------

getLikeForm :: Var pred con quant f sv a schema' -> SchematicForm pred con quant f sv a -> Maybe schema'
getLikeForm (ConstantFormVar v) s = Just s
getLikeForm _                   _ = Nothing


zipFormLamMapping ((FreeVar v):xs) (s:ss) = do
    s' <- getLikeForm v s
    rest <- zipFormLamMapping xs ss
    return $ (LambdaMapping v [] s') : rest
zipFormLamMapping [] [] = Just []

--again I am cheating and reserving some strange names here
--We can look at how to do this better later
--we only have binary varibles so we only need two varibles as long as these terms never occur anywhere else
cheatFormVars = map ConstantFormVar ["alpha", "beta"]

--this formating looks awkward
instance (Schematizable pred, 
          Schematizable con, 
          Schematizable quant,
          Schematizable sv, 
          Schematizable f,
          SchemeVar sv, 
          S_NextVar sv quant, 
          UniformlyEquaitable f,
          UniformlyEquaitable sv,
          UniformlyEquaitable pred,
          UniformlyEquaitable con,
          UniformlyEquaitable quant) => Matchable (SchematicForm pred con quant f sv ()) (Var pred con quant f sv ()) where

    freeVars (S_ConstantSchematicFormBuilder v) = [FreeVar v]
    freeVars (S_UnarySchematicPredicate func tm) = [FreeVar func] `union` (freeVars tm)
    freeVars (S_BinarySchematicPredicate func tm1 tm2) = [FreeVar func] `union` (freeVars tm1) `union` (freeVars tm2)
    freeVars (S_UnarySchematicConnect func tm) = [FreeVar func] `union` (freeVars tm)
    freeVars (S_BinarySchematicConnect func tm1 tm2) = [FreeVar func] `union` (freeVars tm1) `union` (freeVars tm2)
    freeVars (S_SchematicBind q sub) = [FreeVar q]
    freeVars node = composOpFold [] union freeVars node

    apply sub (S_UnaryPredicate pred tm) = S_UnaryPredicate pred (apply sub tm)
    apply sub (S_BinaryPredicate pred tm1 tm2) = S_BinaryPredicate pred (apply sub tm1) (apply sub tm2)
    apply sub old@(S_ConstantSchematicFormBuilder v) = case fvLookup v sub of
        Just new -> new 
        Nothing -> old
    apply sub old@(S_UnarySchematicPredicate func tm) = case fvKMapLookup func sub of
        Just (KLambdaMapping _ fvs new) -> case zipTermLamMapping fvs [apply sub tm] of
            Just argSub -> apply argSub new
            Nothing     -> S_UnarySchematicPredicate func (apply sub tm)
        Nothing         -> S_UnarySchematicPredicate func (apply sub tm)
    apply sub old@(S_BinarySchematicPredicate func tm1 tm2) = case fvKMapLookup func sub of
        Just (KLambdaMapping _ fvs new) -> case zipTermLamMapping fvs $ map (apply sub) [tm1, tm2] of
            Just argSub -> apply argSub new
            Nothing     -> S_BinarySchematicPredicate func (apply sub tm1) (apply sub tm2)
        Nothing         -> S_BinarySchematicPredicate func (apply sub tm1) (apply sub tm2)
    apply sub old@(S_UnarySchematicConnect func tm) = case fvKMapLookup func sub of
        Just (KLambdaMapping _ fvs new) -> case zipFormLamMapping fvs [apply sub tm] of
            Just argSub -> apply argSub new
            Nothing     -> over plate (apply sub) old
        Nothing         -> over plate (apply sub) old
    apply sub old@(S_BinarySchematicConnect func tm1 tm2) = case fvKMapLookup func sub of
        Just (KLambdaMapping _ fvs new) -> case zipFormLamMapping fvs $ map (apply sub) [tm1, tm2] of
            Just argSub -> apply argSub new
            Nothing     -> over plate (apply sub) old
        Nothing         -> over plate (apply sub) old
    apply sub node = over plate (apply sub) node

    match (S_BlankForm) (S_BlankForm) = Just []
    match (S_ConstantFormBuilder c) (S_ConstantFormBuilder c') | c `eq` c' = Just []
    match (S_UnaryPredicate f tm) (S_UnaryPredicate f' tm') | f `eq` f' = Just [tm :=: tm']
    match (S_BinaryPredicate f tm1 tm2) (S_BinaryPredicate f' tm1' tm2') | f `eq` f' = Just [tm1 :=: tm1', tm2 :=: tm2']
    match (S_UnaryConnect f tm) (S_UnaryConnect f' tm') | f `eq` f' = Just [tm :=: tm']
    match (S_BinaryConnect f tm1 tm2) (S_BinaryConnect f' tm1' tm2') | f `eq` f' = Just [tm1 :=: tm1', tm2 :=: tm2']
    match b@(S_Bind q sub) b'@(S_Bind q' sub') | q `eq` q' = Just [(sub $ BlankTerm varName) :=: (sub' $ BlankTerm varName)]
        where varName = s_appropriateVariable (sub $ BlankTerm "*") q
    match _ _ = Nothing

    matchVar (S_ConstantSchematicFormBuilder v)     c                = [LambdaMapping v [] c]
    matchVar (S_UnarySchematicPredicate f tm)       c                = filter (not . mapHasBlanks) $ makeSub f (zip cheatVars [tm]) c
    matchVar (S_BinarySchematicPredicate f tm1 tm2) c                = filter (not . mapHasBlanks) $ makeSub f (zip cheatVars [tm1, tm2]) c
    matchVar (S_UnarySchematicConnect f tm)         c                = filter (not . mapHasBlanks) $ makeSub f (zip cheatFormVars [tm]) c
    matchVar (S_BinarySchematicConnect f tm1 tm2)   c                = filter (not . mapHasBlanks) $ makeSub f (zip cheatFormVars [tm1, tm2]) c
    --matchVar (S_SchematicBind q sub)                (S_Bind q' sub') = LambdaMapping
    matchVar _                                      _ = []

    makeTerm = S_ConstantSchematicFormBuilder

--------------------------------------------------------
--4. Schematic Sequent Items
--------------------------------------------------------

--used in AbstractSyntaxDerivationsMultiUnification; defined here so that
--we can have schematic variables over these.

data SSequentItem pred con quant f sv = SeqVar (Var pred con quant f sv () (SSequentItem pred con quant f sv)) 
                                      | SeqList [SchematicForm pred con quant f sv ()]
                                      deriving (Ord)

instance (Schematizable pred, Schematizable con, Schematizable quant, Schematizable f, Schematizable sv, 
        S_NextVar sv quant, SchemeVar sv) => Show (SSequentItem pred con quant f sv) where
            show (SeqVar c) = show c 
            show (SeqList fs) = intercalate " . " (map show fs)

instance (Schematizable pred, Schematizable con, Schematizable quant, Schematizable f, Schematizable sv, 
        S_NextVar sv quant, SchemeVar sv) => Eq (SSequentItem pred con quant f sv) where
            a == b = show a == show b
