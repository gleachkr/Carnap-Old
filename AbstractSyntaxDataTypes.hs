{-#LANGUAGE EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, FunctionalDependencies #-}

module AbstractSyntaxDataTypes where 

import Unification
import Data.Set as Set
import Data.Map as Map

--This module attempts to provide abstract syntax types that would cover
--a wide variety of languages

--------------------------------------------------------
--1. Abstract typeclasses
--------------------------------------------------------

--class of types that we can directly compute a fregean denotation for
class Evaluable f where
        eval :: f a -> a

--class of types that we can compute a fregean denotation for, relative to
--a model or assignment of some sort.
class Modelable f m where
        satisfies :: m -> f a -> a

--a semantic value type that can be associated with new variables. The idea is
--that appropriateVariable, given f, q generates new concrete variable,
--not yet occuring in f, of a type appropriate to be bound by q.
class NextVar sv quant where
        appropriateVariable :: Form pred con quant f sv c -> quant ((sv b -> c) -> a) -> String

class S_NextVar sv quant where
        s_appropriateVariable :: SchematicForm pred con quant f sv () -> quant ((sv b -> c) -> a) -> String

--similarly, for schematic quantifiers
class SchemeVar sv where
        appropriateSchematicVariable :: SchematicForm pred con quant f sv c -> SSymbol -> String

--a class for types of things to which we want to associate strings with
--multiple blanks. For example:
--
--  1. terms with occurances of the blank term
--  2. function and connective symbols that we might want to write inline,
--  or with various sorts of parentheses

class Schematizable f where
        schematize :: f a -> [String] -> String

--a class for things where we might want to impose a uniform standard of
--identity across the instances--e.g. for function-symbol types
class UniformlyEq f where
        (=*) :: f a -> f b -> Bool

class Scheme f s | f -> s where
        liftToScheme :: f -> s

--------------------------------------------------------
--1. Abstract Types
--------------------------------------------------------

--Here are some types for abstract syntax. The two basic categories that
--are presupposed are terms and formulas.

--We use the idea of a semantic value to indicate approximately a fregean
--sense, or intension: approximately a function from models to fregean
--denotations in those models

--------------------------------------------------------
--1.0 Schematic Symbols
--------------------------------------------------------

data SynType = C | --constant symbol
              F1 | --unary and binary function symbol
              F2 |
               S | --sentence letter
              P1 | --unary and binary predicate symbol
              P2 | 
             CN1 | --unary and binary connective
             CN2 |
               Q | --quantifier
              PL --premise list, as in a sequent
             deriving (Show, Eq, Ord)

type SSymbol = (SynType, String)

--It might be useful to have tags to keep schematic symbols that stand for
--objects of different syntactic categories separate.

synType :: (a, b) -> a
synType = fst

shapeOfSymbol :: (a, b) -> b
shapeOfSymbol = snd

--TODO: ultimately, this should be eliminated, and the type of schematic
--symbol should be part of the specification of the schematic langage type.
--This might muck up the functional dependency of schematic language on
--language.

--------------------------------------------------------
--1.1 Abstract Terms
--------------------------------------------------------

--the terms of a language are determined by the function symbols used, and
--the semantic values assigned to the constant terms and sentence letters
--of the language
--
--f is a type of function symbols, sv is a semantic-value type (intutively,
--fregean intensions denoting whatever sv wraps)
data Term f sv a where 
        BlankTerm           :: Term f sv b
        ConstantTermBuilder :: { cVal  :: sv a } -> Term f sv a
        UnaryFuncApp        :: { uFunc :: f ( b -> a ) , 
                                uTerm :: Term f sv b } -> Term f sv a
        BinaryFuncApp       :: { bFunc :: f (b -> c -> a) , 
                            bTerm1 :: Term f sv b, 
                            bTerm2 :: Term f sv c} -> Term f sv a
--TODO: missing from this list are variable-binding term-forming operators, both
--those that form terms out of formulas (e.g. a definition description
--operator, or Hilbert's epsilon operator) and those that form terms out of
--terms that contain free variables (e.g. Church's lambda)

instance (Evaluable f, Evaluable sv) => Evaluable (Term f sv) where
        eval (ConstantTermBuilder x) = eval x
        eval (UnaryFuncApp g x)      = eval g (eval x)
        eval (BinaryFuncApp g x y)   = eval g (eval x) (eval y)
        eval BlankTerm               = undefined

instance (Modelable f m, Modelable sv m) => Modelable (Term f sv) m where
        satisfies m (ConstantTermBuilder x) = satisfies m x
        satisfies m (UnaryFuncApp g x)      = satisfies m g (satisfies m x)
        satisfies m (BinaryFuncApp g x y)   = satisfies m g (satisfies m x) (satisfies m y)
        satisfies _ BlankTerm               = undefined

instance (Schematizable sv, Schematizable f) => Schematizable ( Term f sv ) where
        schematize (ConstantTermBuilder x) = \_ -> schematize x [] 
        schematize (UnaryFuncApp f x) = \y -> schematize f [schematize x y]
        schematize (BinaryFuncApp f x y) = \z -> schematize f [schematize x z , schematize y z]
        schematize BlankTerm = \x -> case x of  [] -> undefined
                                                y  -> head y

instance Schematizable (Term f sv) => Show (Term f sv a) where
        show x = schematize x ["_"] --inserts a literal blank for semantic blanks. 

--------------------------------------------------------
--1.2 Abstract Term Schemata
--------------------------------------------------------

--these are schematic abstract terms, i.e. terms with schematic variables
--(as opposed to non-schematic variables of the type that can be bound by
--quantifiers in the language itself) in them. These schematic variables
--are useful for unification
--
--f is a type of function symbols, sv is a semantic-value type (intutively,
--fregean intensions denoting whatever sv wraps)
--
--The naming convention is that the things that are in effect just concrete
--symbols get names prefixed by S_ or s_ and that's all. The constructors
--for actual variables get names with Schematic before the first now. the
--selectors that are definitely pulling out variables get scheme as their
--first word.
--
--Because we will not eval Schematic terms, we throw away information about
--semantic types; this simplifies matching later on.
data SchematicTerm f sv a where 
        S_BlankTerm                    ::   SchematicTerm f sv ()
        S_ConstantTermBuilder          ::   {      s_cVal :: sv a } -> SchematicTerm f sv ()
        S_ConstantSchematicTermBuilder ::   {  schemeBVal :: SSymbol } -> SchematicTerm f sv ()
        S_UnaryFuncApp                 ::   {     s_uFunc :: f ( b -> a ) , 
                                                  s_uTerm :: SchematicTerm f sv () } -> SchematicTerm f sv ()
        S_UnarySchematicFuncApp        ::   { schemeUFunc :: SSymbol , 
                                                  s_uTerm :: SchematicTerm f sv () } -> SchematicTerm f sv ()
        S_BinaryFuncApp                ::   {     s_bFunc :: f ( b -> c -> a), 
                                                 s_bTerm1 :: SchematicTerm f sv (), 
                                                 s_bTerm2 :: SchematicTerm f sv ()} -> SchematicTerm f sv ()
        S_BinarySchematicFuncApp       ::   { schemeBFunc :: SSymbol , 
                                                 s_bTerm1 :: SchematicTerm f sv (), 
                                                 s_bTerm2 :: SchematicTerm f sv ()} -> SchematicTerm f sv ()
--XXX:Reduplication is ugly.

unsaturateT (S_UnaryFuncApp f t) = S_UnaryFuncApp f S_BlankTerm
unsaturateT (S_UnarySchematicFuncApp f t) = S_UnarySchematicFuncApp f S_BlankTerm
unsaturateT (S_BinaryFuncApp f t1 t2) = S_BinaryFuncApp f S_BlankTerm S_BlankTerm
unsaturateT (S_BinarySchematicFuncApp f t1 t2) = S_BinarySchematicFuncApp f S_BlankTerm S_BlankTerm
unsaturateT x = x

instance Scheme (Term f sv a) (SchematicTerm f sv ()) where
        liftToScheme (ConstantTermBuilder c) = S_ConstantTermBuilder c
        liftToScheme (UnaryFuncApp f t) = S_UnaryFuncApp f $ liftToScheme t
        liftToScheme (BinaryFuncApp f t1 t2) 
            = S_BinaryFuncApp f (liftToScheme t1) (liftToScheme t2)
        liftToScheme BlankTerm = undefined
                            
--TODO: Eventually we should add a "schematic symbol type" as a new parameter
--to Schematic terms and formulas. When that's done, this can be made more
--generic, by introducing typeclass for concrete types that we want to
--associated a schematization function to, and requiring that the schematic
--symbol type be a member of that class.
instance (Schematizable sv, Schematizable f) => Schematizable ( SchematicTerm f sv ) where
        schematize (S_ConstantTermBuilder x) = \_ -> schematize x [] 
        schematize (S_ConstantSchematicTermBuilder x) = \_ -> shapeOfSymbol x
        schematize (S_UnaryFuncApp f x) = \y -> schematize f [schematize x y]
        schematize (S_UnarySchematicFuncApp f x) 
            = \y -> shapeOfSymbol f ++ "(" ++ schematize x y ++ ")"
        schematize (S_BinaryFuncApp f x y) 
            = \z -> schematize f [schematize x z , schematize y z]
        schematize (S_BinarySchematicFuncApp f x y) 
            = \z -> shapeOfSymbol f ++ "(" ++ schematize x z ++ "," ++ schematize y z ++ ")"

instance Schematizable (SchematicTerm f sv) => Show (SchematicTerm f sv a) where
        show x = schematize x ["_"] --inserts a literal blank for semantic blanks. 

instance Schematizable (SchematicTerm f sv) => Eq (SchematicTerm f sv a) where
        (==) t1 t2 = show t1 == show t2

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
--2.1 Abstract Formulas
--------------------------------------------------------

--the propositions of lanugage are determined by the predicate, connective,
--and quantifier symbols used, along with the semantic values assigned to
--the constant terms and predicates of the language
data Form pred con quant f sv a where
        BlankForm           :: Form pred con quant f sv b
        ConstantFormBuilder :: {pVal :: sv a} -> Form pred con quant f sv a
        UnaryPredicate      :: { uPred :: pred (b -> a), 
                                uSub  :: Term f sv b} -> Form pred con quant f sv a
        BinaryPredicate     :: { bPred :: pred (b -> c -> a),
                                bSub1   :: Term f sv b,
                                bSub2   :: Term f sv c} -> Form pred con quant f sv a
        UnaryConnect        :: { uConn :: con (b -> a),
                                uForm   :: Form pred con quant f sv b } -> Form pred con quant f sv a
        BinaryConnect       :: { bConn :: con (b -> c -> a),
                                bForm1  :: Form pred con quant f sv b,
                                bForm2  :: Form pred con quant f sv c } -> Form pred con quant f sv a
        --The quantifier set up here is a rudimentary attempt at
        --implementing abstract higher-order syntax. It almost certainly
        --can be improved, and will probably need to be modified when we
        --actually try to do something with it.
        --
        --takes an (sv b -> c) rather than a (b->c) because all we know is
        --that our open formula determines a function from the sv b of the
        --term to an sv c (which could then be evaluated in a model to get
        --a c. 
        --
        --So the picture here is basically substitutional. Need to think
        --about how to get an FOL kind of thing out of it. Basically seems
        --like you might need two kind of svs: one for variables, and one
        --for constants. 
        --
        --It can also take an arbitrary function from terms to forms. So this
        --will let you build some non-formulas. The language is embedded in
        --this data type; but the data type is not isomorphic to the language.
        Bind                :: { quantifier :: quant ((sv b ->c) -> a) , 
                                quantified :: Term f sv b -> Form pred con quant f sv c
                                } -> Form pred con quant f sv a
        --TODO: missing are "subnectives", constructors that take a formula
        --without and return a "proposition" and constructors that take
        --a formula with free variables, bind these, and return
        --a "property".

instance (Evaluable pred, Evaluable con, Evaluable quant, Evaluable f, Evaluable sv) 
        => Evaluable (Form pred con quant f sv) where
            eval (ConstantFormBuilder x)   = eval x
            eval (UnaryPredicate p t)      = eval p (eval t)
            eval (BinaryPredicate p t1 t2) = eval p (eval t1) (eval t2)
            eval (UnaryConnect c f1)       = eval c (eval f1)
            eval (BinaryConnect c f1 f2)   = eval c (eval f1) (eval f2)
            eval (Bind q openf)            = eval q $ \x -> eval (openf (ConstantTermBuilder x))
            eval BlankForm                 = undefined

instance (Modelable pred m, Modelable con m, Modelable quant m, Modelable f m, Modelable sv m) 
        => Modelable (Form pred con quant f sv) m where
            satisfies m (ConstantFormBuilder x)   = satisfies m x
            satisfies m (UnaryPredicate p t)      = satisfies m p (satisfies m t)
            satisfies m (BinaryPredicate p t1 t2) = satisfies m p (satisfies m t1) (satisfies m t2)
            satisfies m (UnaryConnect c f1)       = satisfies m c (satisfies m f1)
            satisfies m (BinaryConnect c f1 f2)   = satisfies m c (satisfies m f1) (satisfies m f2)
            satisfies m (Bind q openf)            = satisfies m q $ \x -> satisfies m (openf (ConstantTermBuilder x))
            satisfies _ BlankForm                 = undefined

--create a schematic instance of a formula, into which a variable may be plugged
--Since we're putting in the Variables Showable constraint here, 
instance (Schematizable pred, Schematizable con, Schematizable quant, Schematizable sv,
        Schematizable f, NextVar sv quant)
        => Schematizable (Form pred con quant f sv) where
                schematize (ConstantFormBuilder x) = \_ -> schematize x []
                schematize (UnaryPredicate p t) = 
                    \y -> schematize p [schematize t y]
                schematize (BinaryPredicate p t1 t2) = 
                    \y -> schematize p [schematize t1 y, schematize t2 y]
                schematize (UnaryConnect c f ) = 
                    \y -> schematize c [schematize f y]
                schematize (BinaryConnect c f1 f2) = 
                    \y -> schematize c [schematize f1 y,schematize f2 y]
                schematize (Bind q f) = 
                --The idea is to figure out what variables (of the type
                --we're binding), already occur in the formula when it's
                --combined with a blank term, and then to insert the next
                --such variable into the spot that the blank-term was
                --filling. We look at the quantifier to get the type of
                --variable bound, and we look at the formula with a blank
                --inserted to get the occurances that we've already used 
                    \_ -> schematize q [appropriateVariable (f BlankTerm) q, 
                        schematize (f BlankTerm) [appropriateVariable (f BlankTerm) q]]
                schematize _ = \_ -> ""

instance Schematizable (Form pred con quant f sv) => Show (Form pred con quant f sv a) where
        show x = schematize x ["_"] --inserts a literal blank for semantic blanks. 

--------------------------------------------------------
--2.2 Abstract Formula Schemata
--------------------------------------------------------

--The naming convention is that the things that are in effect just concrete
--symbols get names prefixed by S_ or s_ and that's all. The constructors
--for actual variables get names with Schematic before the first now. the
--selectors that are definitely pulling out variables get scheme as their
--first word.
--
--NOTE: There's a kind of subtle thing here. Should our schematic variables be
--semantic type agnostic---so that they can match concrete symbols of any
--semantic type---or should they themselves be semantically typed? In
--actual practice, I think the type-agnostic form of scheme is definitely
--the standard thing. But why shouldn't there sematically-typed schematic
--variables?
--
--As with Schematic terms, we throw away semantic information that is no
--longer relevant, in order to make substitution easier.
data SchematicForm pred con quant f sv a where
        S_BlankForm                          :: SchematicForm pred con quant f sv ()
        S_ConstantFormBuilder                :: {s_pVal            :: sv a}
                                                                   -> SchematicForm pred con quant f sv ()
        S_ConstantSchematicFormBuilder       :: {schemePVal        :: SSymbol}
                                                                   -> SchematicForm pred con quant f sv ()
        S_UnaryPredicate                     :: { s_uPred          :: pred (b -> a),
                                                s_uSub             :: SchematicTerm f sv ()}
                                                                   -> SchematicForm pred con quant f sv ()
        S_UnarySchematicPredicate            :: { schemeUPred      :: SSymbol,
                                                s_uSub             :: SchematicTerm f sv ()}
                                                                   -> SchematicForm pred con quant f sv ()
        S_BinaryPredicate                    :: { s_bPred          :: pred (b -> c -> a),
                                                s_bSub1            :: SchematicTerm f sv (),
                                                s_bSub2            :: SchematicTerm f sv ()}
                                                                   -> SchematicForm pred con quant f sv ()
        S_BinarySchematicPredicate           :: { schemeBPred      :: SSymbol,
                                                s_bSub1            :: SchematicTerm f sv (),
                                                s_bSub2            :: SchematicTerm f sv ()}
                                                                   -> SchematicForm pred con quant f sv ()
        S_UnaryConnect                       :: { s_uConn          :: con (b -> a),
                                                s_uForm            :: SchematicForm pred con quant f sv () } 
                                                                   -> SchematicForm pred con quant f sv ()
        S_UnarySchematicConnect              :: { schemeUConn      :: SSymbol,
                                                s_uForm            :: SchematicForm pred con quant f sv () } 
                                                                   -> SchematicForm pred con quant f sv ()
        S_BinaryConnect                      :: { s_bConn          :: con (b -> c -> a),
                                                s_bForm1           :: SchematicForm pred con quant f sv (),
                                                s_bForm2           :: SchematicForm pred con quant f sv () }
                                                                   -> SchematicForm pred con quant f sv ()
        S_BinarySchematicConnect             :: { schemeBConn      :: SSymbol,
                                                s_bForm1           :: SchematicForm pred con quant f sv (),
                                                s_bForm2           :: SchematicForm pred con quant f sv () }
                                                                   -> SchematicForm pred con quant f sv ()
        S_Bind                               :: { s_quantifier     :: quant ((sv b ->c) -> a) ,
                                                s_quantified       :: Term f sv d -> SchematicForm pred con quant f sv ()
                                                }                  -> SchematicForm pred con quant f sv ()
        S_SchematicBind                      :: { schemeQuantifier :: SSymbol,
                                                s_quantified       :: Term f sv d -> SchematicForm pred con quant f sv ()
                                                }                  -> SchematicForm pred con quant f sv ()
--XXX: Reduplication is ugly. Possible Solution: dispense with Form, and
--simply work with schematic formulas all the time.

unsaturateF (S_UnaryPredicate p _) = S_UnaryPredicate p S_BlankTerm
unsaturateF (S_UnarySchematicPredicate p _) = S_UnarySchematicPredicate p S_BlankTerm
unsaturateF (S_BinaryPredicate p _ _) = S_BinaryPredicate p S_BlankTerm S_BlankTerm 
unsaturateF (S_BinarySchematicPredicate p _ _) = S_BinarySchematicPredicate p S_BlankTerm S_BlankTerm
unsaturateF (S_UnaryConnect c _) = S_UnaryConnect c S_BlankForm
unsaturateF (S_UnarySchematicConnect c _) = S_UnarySchematicConnect c S_BlankForm
unsaturateF (S_BinaryConnect c _ _) = S_BinaryConnect c S_BlankForm S_BlankForm 
unsaturateF (S_BinarySchematicConnect c _ _) = S_BinarySchematicConnect c S_BlankForm S_BlankForm
unsaturateF x = x

instance Scheme ( Form pred con quant f sv a ) ( SchematicForm pred con quant f sv () ) where
        liftToScheme (ConstantFormBuilder c) = S_ConstantFormBuilder c
        liftToScheme (UnaryPredicate p t) = S_UnaryPredicate p $ liftToScheme t
        liftToScheme (BinaryPredicate p t1 t2) = S_BinaryPredicate p (liftToScheme t1) (liftToScheme t2)
        liftToScheme (UnaryConnect c f) = S_UnaryConnect c $ liftToScheme f
        liftToScheme (BinaryConnect c f1 f2) = S_BinaryConnect c (liftToScheme f1) (liftToScheme f2)
        liftToScheme (Bind q q'ed) = S_Bind q $ \x -> liftToScheme (q'ed x)
        liftToScheme BlankForm = S_BlankForm

--XXX: This gets around schematizing schematic variables (which themselves
--don't have a schematizable instance) in a kind of quick and dirty way.
--Ultimately, this should be done better.
instance (Schematizable pred, Schematizable con, Schematizable quant, Schematizable sv,
        Schematizable f, S_NextVar sv quant, SchemeVar sv)
        => Schematizable (SchematicForm pred con quant f sv) where
                schematize (S_ConstantFormBuilder x) = \_ -> schematize x []
                schematize (S_ConstantSchematicFormBuilder x) = \_ -> shapeOfSymbol x 
                schematize (S_UnaryPredicate p t) = 
                    \y -> schematize p [schematize t y]
                schematize (S_UnarySchematicPredicate p t) = 
                    \y -> shapeOfSymbol p ++ "(" ++ schematize t y ++ ")"
                schematize (S_BinaryPredicate p t1 t2) = 
                    \y -> schematize p [schematize t1 y, schematize t2 y]
                schematize (S_BinarySchematicPredicate p t1 t2) = 
                    \y -> shapeOfSymbol p ++ "(" ++ schematize t1 y ++ "," ++ schematize t2 y ++ ")"
                schematize (S_UnaryConnect c f) = 
                    \y -> schematize c [schematize f y]
                schematize (S_UnarySchematicConnect c f) = 
                    \y -> shapeOfSymbol c ++ schematize f y
                schematize (S_BinaryConnect c f1 f2) = 
                    \y -> schematize c [schematize f1 y,schematize f2 y]
                schematize (S_BinarySchematicConnect c f1 f2) = 
                    \y -> "(" ++ schematize f1 y ++ shapeOfSymbol c ++ schematize f2 y ++ ")"
                schematize (S_Bind q f) = 
                    \_ -> schematize q [s_appropriateVariable (f BlankTerm) q, 
                        schematize (f BlankTerm) [s_appropriateVariable (f BlankTerm) q]]
                schematize (S_SchematicBind q f) = 
                    \_ -> shapeOfSymbol q ++ appropriateSchematicVariable (f BlankTerm) q ++ "(" ++
                        schematize (f BlankTerm) [appropriateSchematicVariable (f BlankTerm) q] ++ ")"
                schematize _ = \_ -> ""

instance Schematizable (SchematicForm pred con quant f sv) => Show (SchematicForm pred con quant f sv a) where
        show x = schematize x ["_"] --inserts a literal blank for semantic blanks. 

instance Schematizable (SchematicForm pred con quant f sv) => Eq (SchematicForm pred con quant f sv a) where
        (==) f1 f2 = show f1 == show f2

instance Schematizable (SchematicForm pred con quant f sv) => Ord (SchematicForm pred con quant f sv a) where
        (<=) f1 f2 = show f1 <= show f2

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
--3 Mixed Unification
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
--4 Helper types and functions
--------------------------------------------------------
--Nothing is perfect for constructing langauges which lack some of the
--categories above, e.g. the propositional language which lacks quantifiers
--and terms. But in case of emergency, the type below will help.

data Nothing a 

instance Evaluable Nothing where
        eval _ = undefined
instance Modelable Nothing m where
        satisfies _ _ = undefined
instance Schematizable Nothing where
        schematize _ = undefined
instance NextVar a Nothing where
        appropriateVariable _ _ = undefined
instance S_NextVar a Nothing where
        s_appropriateVariable _ _ = undefined
instance UniformlyEq Nothing where
        _ =* _ = undefined

