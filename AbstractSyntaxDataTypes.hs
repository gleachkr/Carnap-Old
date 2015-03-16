{-#LANGUAGE EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, FunctionalDependencies #-}

module AbstractSyntaxDataTypes where 

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


--------------------------------------------------------
--3. Helper types and functions
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

