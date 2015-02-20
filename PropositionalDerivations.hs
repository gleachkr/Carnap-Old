{-#LANGUAGE MultiParamTypeClasses, EmptyDataDecls, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module PropositionalDerivations where

import PropositionalLanguage
import AbstractSyntaxDataTypes
import AbstractDerivationDataTypes

type PropositionalJudgement = Judgement PropositionalFormula PropJustification

type Argument = ([PropositionalFormula], PropositionalFormula)

data PropJustification = Premise
                       | ConditionalProof PropositionalJudgement 
                       | ModusPonens PropositionalJudgement PropositionalJudgement
                       | Adjunction PropositionalJudgement PropositionalJudgement 
                       --The check for correctness is going to involve
                       --verifying that the cited derivation itself proves
                       --the validity of the right argument.

type PropDerivation = Derivation PropositionalJudgement

data PropRule = PR | MP | CP | ADJ | SHOW
              deriving Show

modusPonens :: PropositionalFormula -> PropositionalFormula -> PropositionalFormula -> Bool
modusPonens x@(BinaryConnect If y z) w@(BinaryConnect If s t) c = (s == x && c == t ) || (y == w && c == z)
modusPonens x (BinaryConnect If s t) c = s == x && c == t 
modusPonens (BinaryConnect If y z) w c = y == w && c == z
modusPonens  _ _ _ = False

adjunction :: PropositionalFormula -> PropositionalFormula -> PropositionalFormula -> Bool
adjunction x y z = z == (BinaryConnect And x y)

unitePremises :: Argument -> Argument -> [PropositionalFormula]
unitePremises (ps1, _ ) (ps2, _ ) = ps1 ++ ps2

--maybe it'd be more elegant to fold modusPonens and other conditions in
--here as guards.
derivationProves :: PropositionalJudgement -> Maybe ([PropositionalFormula],PropositionalFormula)
derivationProves (Line p Premise) = Just ([p],p)
derivationProves (Line c (ModusPonens l1@(Line p1 _) l2@(Line p2 _))) = if modusPonens p1 p2 c 
                                                                        then do arg1 <- derivationProves l1
                                                                                arg2 <- derivationProves l2
                                                                                return (unitePremises arg1 arg2, c)
                                                                        else Nothing
derivationProves (Line c (Adjunction l1@(Line p1 _) l2@(Line p2 _))) = if adjunction p1 p2 c 
                                                                        then do arg1 <- derivationProves l1
                                                                                arg2 <- derivationProves l2
                                                                                return (unitePremises arg1 arg2, c)
                                                                        else Nothing
derivationProves (Line c (ConditionalProof l)) = case c of (BinaryConnect If antec conseq) -> retractHypothesis antec conseq c (derivationProves l)
                                                           _ -> Nothing
                                                           where retractHypothesis antec conseq cond shown = 
                                                                    case shown of Just ([],conc)      -> if conc == conseq 
                                                                                                            then Just ([], cond) 
                                                                                                            else Nothing
                                                                                  Just ((x:etc),conc) -> if conc == conseq 
                                                                                                            then if x == antec 
                                                                                                                then Just (etc,cond)
                                                                                                                else Just (x:etc,cond)
                                                                                                            else Nothing
                                                                                  _ -> Nothing
derivationProves _ = Nothing

mpRule :: a -> PropositionalJudgement -> PropositionalJudgement -> Derivation (Judgement a PropJustification)
mpRule x y z = assert $ Line x $ ModusPonens y z

adRule :: a -> PropositionalJudgement -> PropositionalJudgement -> Derivation (Judgement a PropJustification)
adRule x y z = assert $ Line x $ Adjunction y z

--finishes a subderivation, returning the attached derivation type, to feed
--into a show line
cdRule :: PropositionalJudgement -> Derivation (PropositionalJudgement,
                                               PropositionalJudgement ->
                                               PropJustification)
cdRule y = return (y,ConditionalProof)

prRule :: a -> Derivation (Judgement a PropJustification)
prRule x     = assert $ Line x Premise

prove :: PropositionalFormula -> Derivation (PropositionalJudgement, PropositionalJudgement -> PropJustification) -> PropDerivation
prove phi subder = assert $ Line phi $ (snd $ subproof subder) (fst $ subproof subder) 

