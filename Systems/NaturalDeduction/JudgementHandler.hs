{-#LANGUAGE MultiParamTypeClasses, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module Carnap.Systems.NaturalDeduction.JudgementHandler where

import Carnap.Core.Data.AbstractDerivationDataTypes
import Carnap.Core.Data.AbstractSyntaxMultiUnification
import Carnap.Core.Data.AbstractDerivationMultiUnification()
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.Rules as Rules
import Carnap.Core.Unification.MultiUnification

import Data.Set as Set

--This module houses a function (derivationProves) that, given a set of
--ambigious rules, checks a Judgement with simple justifications (either
--premises, or judgements based on prior judgements, with an InferenceRule)
--and returns a Maybe schematic sequent that this judgement supports. 
--
--TODO: if we want to return more than one sequent (so that we can see
--what's going on step-by-step through the proof) this is where we'll have
--to do it.

--------------------------------------------------------
--1. Rule Manipulation
--------------------------------------------------------

lookupRule :: String -> Set.Set (AmbiguousRule term) -> AmbiguousRule term
lookupRule rule set = findMin $ Set.filter (\r -> ruleName r == rule) set 

--converts a rule on an type a, which can be associated with a schematic
--form to a Sequent of scematic forms. The premises are in one large
--SeqList, thus: [phi_1 .. phi_n] ⊢ [chi]
toSchematicSequent :: (Scheme a (SchematicForm pred con quant f sv ()), RuleLike a t) => t -> Sequent (SSequentItem pred con quant f sv)
toSchematicSequent s = Sequent [SeqList $ Prelude.map liftToScheme $ premises s] (SeqList [liftToScheme $ Rules.conclusion s])

--------------------------------------------------------
--2. Sequent Manipulation
--------------------------------------------------------

--positions n sequents of schematic forms for matching
freeSome :: Int -> Sequent (SSequentItem pred con quant f sv) -> Sequent (SSequentItem pred con quant f sv)
freeSome n (Sequent ((SeqList fs):etc) c) = Sequent ((SeqList $ take n fs):(SeqList $ drop n fs):etc) c
freeSome _ x = x

--gets the size of an inital SeqList
blockSize :: Sequent (SSequentItem t t1 t2 t3 t4) -> Int
blockSize (Sequent ((SeqList fs):_) _) = length fs
blockSize _ = 0

--aligns s1 sequent for matching with s2, where s1 is assumed to be of the
--form [phi_1 .. phi_n] ⊢ [chi]. The premises of s2 are assumed to contain
--at most one seqvar.
align :: Sequent (SSequentItem pred con quant f sv) -> Sequent (SSequentItem t t1 t2 t3 t4) -> Sequent (SSequentItem pred con quant f sv)
align s1 s2 = case s2 of 
                Sequent ((SeqList _):_) _ -> freeSome (blockSize s2) s1
                Sequent [SeqVar _] _ -> s1

--flattens the premises of a sequent, for alignment; 
flatten :: [SSequentItem t t1 t2 t3 t4] -> [SchematicForm t t1 t2 t3 t4 ()]
flatten ((SeqList fs):etc) = fs ++ flatten etc
flatten _ = []

seek :: Eq a => a -> [a] -> [a]
seek p fs = if elem p fs then  p:(Prelude.filter (\x -> not (x == p)) fs) else fs

clean :: Sequent (SSequentItem pred con quant f sv) -> Sequent (SSequentItem pred con quant f sv)
clean (Sequent ps c) = Sequent [SeqList $ flatten ps] c

maybeSeekandClean :: (S_NextVar sv quant, SchemeVar sv, Schematizable sv, Schematizable f, 
                     Schematizable quant, Schematizable con, Schematizable pred) => 
                     Maybe (SchematicForm pred con quant f sv ()) -> Sequent (SSequentItem pred con quant f sv) 
                     -> Sequent (SSequentItem pred con quant f sv)
maybeSeekandClean mp s = case mp of 
                            Just p -> case clean s of
                                          Sequent [SeqList fs] c -> Sequent [SeqList (seek p fs)] c
                                          _ -> clean s
                            Nothing -> clean s

--------------------------------------------------------
--3. Checking
--------------------------------------------------------

--converts some schematic sequents, and a statement they're being used to support,
--to a putative rule-instance, which we can then check for unification. It
--incorporates a number of interchange and contraction inferences, to try
--to get the premise sequents into shape.
toInstanceOfAbs :: (S_NextVar t4 t2, SchemeVar t4, 
                   Schematizable t4, Schematizable t3, Schematizable t2, Schematizable t1, Schematizable t, 
                   Scheme f (SchematicForm t t1 t2 t3 t4 ()), 
                   UniformlyEq t4, UniformlyEq t3, UniformlyEq t2, UniformlyEq t1, UniformlyEq t, 
                   RuleLike (Sequent (SSequentItem t t1 t2 t3 t4)) t5) => 
                   t5 -> [Sequent (SSequentItem t t1 t2 t3 t4)] -> f -> AbsRule (Sequent (SSequentItem t t1 t2 t3 t4))
toInstanceOfAbs rule ps c = AbsRule (zipWith interchange ps (premises rule))
                                 (Sequent (premises $ Rules.conclusion rule) $ SeqList [sc])
                        where sc = liftToScheme c
                              conc (Sequent _ (SeqList [x])) = x
                              initialSub = case unify (conc $ Rules.conclusion rule) sc of
                                            Right s -> s
                                            Left _ -> []
                              firstOf p = case premises p of 
                                            (SeqList fs):_ -> Just $ multiApply initialSub $ head fs
                                            _ -> Nothing 
                              interchange x y = align (maybeSeekandClean (firstOf y) x) y

checkWithAmbig :: (S_NextVar t4 t2, SchemeVar t4, 
                  Schematizable t4, Schematizable t3, Schematizable t2, Schematizable t1, Schematizable t, 
                  Scheme f (SchematicForm t t1 t2 t3 t4 ()), 
                  UniformlyEq t4, UniformlyEq t3, UniformlyEq t2, UniformlyEq t1, UniformlyEq t) => 
                  AmbiguousRule (Sequent (SSequentItem t t1 t2 t3 t4)) -> [Sequent (SSequentItem t t1 t2 t3 t4)] -> f -> Maybe (Sequent (SSequentItem t t1 t2 t3 t4))
checkWithAmbig rule ps c = if Prelude.null matches then Nothing
                                           else case unify theMatch theInstance of
                                                    Right sub -> Just $ multiApply sub (Rules.conclusion theInstance)
                                                    _ -> Nothing
                        where match r = case unify (toInstanceOfAbs r ps c) r of 
                                            Right _  -> True
                                            Left _ -> False
                              matches = Prelude.filter match (ruleVersions rule)
                              theMatch = head matches
                              theInstance = toInstanceOfAbs theMatch ps c

derivationProves :: (S_NextVar sv quant, SchemeVar sv, 
                    Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred, 
                    Scheme f1 (SchematicForm pred con quant f sv ()), 
                    UniformlyEq sv, UniformlyEq f, UniformlyEq quant, UniformlyEq con, UniformlyEq pred) => 
                    Set.Set (AmbiguousRule (Sequent (SSequentItem pred con quant f sv))) -> Judgement f1 (SimpleJustification f1) -> Maybe (Sequent (SSequentItem pred con quant f sv))
derivationProves _ (Line p Premise) = Just $ Sequent [SeqList [liftToScheme p]] ( SeqList [liftToScheme p])
derivationProves ruleSet (Line c (Inference s l)) = do
        l' <- mapM (derivationProves ruleSet) l 
        checkWithAmbig (lookupRule s ruleSet) l' c
