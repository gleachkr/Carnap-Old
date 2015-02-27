{-#LANGUAGE EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}

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

--a class for types of things to which we want to associate strings with
--multiple blanks. For example:
--
--  1. terms with occurances of the blank term
--  2. function and connective symbols that we might want to write inline,
--  or with various sorts of parentheses
class Schematizable f where
        schematize :: f a -> [String] -> String

--------------------------------------------------------
--1. Abstract Types
--------------------------------------------------------

--Here are some types for abstract syntax. The two basic categories that
--are presupposed are terms and formulas.

--We use the idea of a semantic value to indicate approximately a fregean
--sense, or intension: approximately a function from models to fregean
--denotations in those models

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
data SchematicTerm f sv a where 
        S_ConstantTermBuilder          ::   {      s_cVal :: sv a } -> SchematicTerm f sv a
        S_ConstantSchematicTermBuilder ::   {  schemeBVal :: Int } -> SchematicTerm f sv a
        S_UnaryFuncApp                 ::   {     s_uFunc :: f ( b -> a ) , 
                                                  s_uTerm :: SchematicTerm f sv b } -> SchematicTerm f sv a
        S_UnarySchematicFuncApp        ::   {  schemeUFunc :: f ( b -> a ) , 
                                                  s_uTerm :: SchematicTerm f sv b } -> SchematicTerm f sv a
        S_BinarySchematicFuncApp       ::   { schemeBFunc :: f (b -> c -> a) , 
                                                 s_bTerm1 :: SchematicTerm f sv b, 
                                                 s_bTerm2 :: SchematicTerm f sv c} -> SchematicTerm f sv a
        S_BinaryFuncApp                ::   {     s_bFunc :: f (b -> c -> a) , 
                                                 s_bTerm1 :: SchematicTerm f sv b, 
                                                 s_bTerm2 :: SchematicTerm f sv c} -> SchematicTerm f sv a
--XXX:Reduplication is ugly.
                            
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
data SchematicForm pred con quant f sv a where
        S_ConstantFormBuilder                :: {s_pVal            :: sv a}
                                                                   -> SchematicForm pred con quant f sv a
        S_ConstantSchematicFormBuilder       :: {schemePVal        :: Int}
                                                                   -> SchematicForm pred con quant f sv a
        S_UnaryPredicate                     :: { s_uPred          :: pred (b -> a),
                                                s_uSub             :: SchematicTerm f sv b}
                                                                   -> SchematicForm pred con quant f sv a
        S_UnarySchematicPredicate            :: { schemeUPred      :: pred (b -> a),
                                                s_uSub             :: SchematicTerm f sv b}
                                                                   -> SchematicForm pred con quant f sv a
        S_BinaryPredicate                    :: { s_bPred          :: pred (b -> c -> a),
                                                s_bSub1            :: SchematicTerm f sv b,
                                                s_bSub2            :: SchematicTerm f sv c}
                                                                   -> SchematicForm pred con quant f sv a
        S_BinarySchematicPredicate           :: { schemeBPred      :: pred (b -> c -> a),
                                                s_bSub1            :: SchematicTerm f sv b,
                                                s_bSub2            :: SchematicTerm f sv c}
                                                                   -> SchematicForm pred con quant f sv a
        S_UnaryConnect                       :: { s_uConn          :: con (b -> a),
                                                s_uForm            :: SchematicForm pred con quant f sv b } -> SchematicForm pred con quant f sv a
        S_UnarySchematicConnect              :: { schemeUConn      :: Int,
                                                s_uForm            :: SchematicForm pred con quant f sv b } -> SchematicForm pred con quant f sv a
        S_BinaryConnect                      :: { s_bConn          :: con (b -> c -> a),
                                                s_bForm1           :: SchematicForm pred con quant f sv b,
                                                s_bForm2           :: SchematicForm pred con quant f sv c }
                                                                   -> SchematicForm pred con quant f sv a
        S_BinarySchematicConnect             :: { schemeBConn      :: Int,
                                                s_bForm1           :: SchematicForm pred con quant f sv b,
                                                s_bForm2           :: SchematicForm pred con quant f sv c }
                                                                   -> SchematicForm pred con quant f sv a
        S_Bind                               :: { s_quantifier     :: quant ((sv b ->c) -> a) ,
                                                s_quantified       :: SchematicTerm f sv b -> SchematicForm pred con quant f sv c
                                                }                  -> SchematicForm pred con quant f sv a
        S_SchematicBind                      :: { schemeQuantifier :: Int,
                                                s_quantified       :: SchematicTerm f sv b -> SchematicForm pred con quant f sv c
                                                }                  -> SchematicForm pred con quant f sv a
--XXX: Reduplication is ugly
--------------------------------------------------------
--3 Helper types
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

