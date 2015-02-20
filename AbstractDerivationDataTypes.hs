
---vim:fdm=marker
{-#LANGUAGE GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}

module AbstractDerivationDataTypes where 

import Control.Monad.Identity

                            
--TODO: Monad Instance.
-- Looks like you might just be able to use the identity monad, with infix
-- line constructors, so that it looks like
--
-- l4 <- phi1 land phi2 byMP l2 l3

data Judgement contents justification where
                            Line :: {lineContents :: contents, lineJustification :: justification} 
                                -> Judgement contents justification

type Derivation = Identity

assert :: Judgement a b -> Derivation (Judgement a b)
assert = Identity

conclusion :: Derivation (Judgement a b) -> Judgement a b
conclusion = runIdentity

subproof :: Derivation (Judgement a b, Judgement a b -> b) -> (Judgement a b, Judgement a b -> b)
subproof = runIdentity

--TODO: show, equality instances.

--TODO: test for correct derivations. Could this be done using blanks to
--deal with variable binding situations?



