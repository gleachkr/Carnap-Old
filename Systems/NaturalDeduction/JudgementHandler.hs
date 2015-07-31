{-#LANGUAGE MultiParamTypeClasses, GADTs, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module Carnap.Systems.NaturalDeduction.JudgementHandler where

import Carnap.Core.Data.AbstractDerivationDataTypes
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.Rules as Rules
import Carnap.Core.Unification.HigherOrderMatching
import Carnap.Core.Data.AbstractSyntaxSecondOrderMatching

import Data.Set as Set
import Data.Either as Either

--This module houses a function (derivationProves) that, given a set of
--ambigious rules with checks, checks a Judgement with simple
--justifications (either premises, or judgements based on prior judgements,
--with an InferenceRule) and returns a Maybe schematic sequent that this
--judgement supports. 
--
--TODO: if we want to return more than one sequent (so that we can see
--what's going on step-by-step through the proof) this is where we'll have
--to do it.

--------------------------------------------------------
--1. Rule Manipulation
--------------------------------------------------------

lookupRule :: String -> Set.Set (AmbiguousRulePlus term) -> AmbiguousRulePlus term
lookupRule rule set = findMin $ Set.filter (\r -> ruleName (losePlus r) == rule) set 

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
freeSome n (Sequent (SeqList fs : etc) c) = Sequent ((SeqList $ take n fs):(SeqList $ drop n fs):etc) c
freeSome _ x = x

--gets the size of an inital SeqList
blockSize :: Sequent (SSequentItem t t1 t2 t3 t4) -> Int
blockSize (Sequent (SeqList fs : _) _) = length fs
blockSize _ = 0

--aligns s1 sequent for matching with s2, where s1 is assumed to be of the
--form [phi_1 .. phi_n] ⊢ [chi]. The premises of s2 are assumed to contain
--at most one seqvar.
align :: Sequent (SSequentItem pred con quant f sv) -> Sequent (SSequentItem t t1 t2 t3 t4) -> Sequent (SSequentItem pred con quant f sv)
align s1 s2 = case s2 of 
                Sequent (SeqList _ : _) _ -> freeSome (blockSize s2) s1
                Sequent [SeqVar _] _ -> s1

--flattens the premises of a sequent, for alignment; 
flatten :: [SSequentItem t t1 t2 t3 t4] -> [SchematicForm t t1 t2 t3 t4 ()]
flatten (SeqList fs : etc) = fs ++ flatten etc
flatten _ = []

seek :: Eq a => a -> [a] -> [a]
seek p fs = if p `elem` fs then  p: Prelude.filter (/= p) fs else fs

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
--to get the premise sequents into shape. Because we have only pattern
--matching, and not unification, the returned putative instance does not
--have anything on the left side of its conclusion-sequent. That
--information needs to be filled in down the line
toInstanceOfAbs :: (S_NextVar t4 t2, SchemeVar t4, Schematizable t4, Schematizable t3, Schematizable t2, Schematizable t1, Schematizable t, 
                   Scheme f (SchematicForm t t1 t2 t3 t4 ()), RuleLike (Sequent (SSequentItem t t1 t2 t3 t4)) t5, 
                   UniformlyEquaitable t4, UniformlyEquaitable t3, UniformlyEquaitable t2, UniformlyEquaitable t1, UniformlyEquaitable t, 
                   Carnap.Core.Unification.HigherOrderMatching.Matchable (Sequent (SSequentItem t t1 t2 t3 t4)) (Var t t1 t2 t3 t4 ())) => 
                   t5 -> [Sequent (SSequentItem t t1 t2 t3 t4)] -> f -> AbsRule (Sequent (SSequentItem t t1 t2 t3 t4))
toInstanceOfAbs rule ps c = AbsRule (zipWith interchange ps (premises rule))
                                 (Sequent [] $ SeqList [sc]) --empty andtecedent conclusion sequent
                        where sc = liftToScheme c
                              conc (Sequent _ (SeqList [x])) = x
                              initialSub = case patternMatch (conc $ Rules.conclusion rule) sc of
                                            Right s -> head s
                                            Left _ -> []
                              firstOf p = case premises p of 
                                            SeqList fs : _ -> Just $ apply initialSub $ head fs
                                            _ -> Nothing 
                              interchange x y = align (maybeSeekandClean (firstOf y) x) y

checkWithAmbig :: (S_NextVar t4 t2, SchemeVar t4, Schematizable t4, Schematizable t3, Schematizable t2, Schematizable t1, Schematizable t, 
                  Scheme f (SchematicForm t t1 t2 t3 t4 ()), UniformlyEquaitable t4, UniformlyEquaitable t3, UniformlyEquaitable t2, UniformlyEquaitable t1, UniformlyEquaitable t, 
                  Carnap.Core.Unification.HigherOrderMatching.Matchable (Sequent (SSequentItem t t1 t2 t3 t4)) (Var t t1 t2 t3 t4 ()), 
                  Carnap.Core.Unification.HigherOrderMatching.Matchable (AbsRule (Sequent (SSequentItem t t1 t2 t3 t4))) (Var t t1 t2 t3 t4 ())) => 
                  AmbiguousRulePlus (Sequent (SSequentItem t t1 t2 t3 t4)) -> [Sequent (SSequentItem t t1 t2 t3 t4)] -> f -> 
                  Either [MatchError (Var t t1 t2 t3 t4 () (AbsRule (Sequent (SSequentItem t t1 t2 t3 t4)))) (AbsRule (Sequent (SSequentItem t t1 t2 t3 t4)))] 
                         (Sequent (SSequentItem t t1 t2 t3 t4))
checkWithAmbig rule ps c = do m <- theMatch 
                              let theInstance = toInstanceOfAbs m ps c
                              sub <- singletonize $ patternMatch (anteUp [] m) theInstance
                              return $ apply sub (Rules.conclusion $ anteUp (anteOut m) theInstance)
                        where matchRule r = case patternMatch (anteUp [] r) (toInstanceOfAbs r ps c) of
                                            Right _ -> Right r
                                            Left e -> Left e
                              matches = Prelude.map matchRule (ruleVersions (losePlus rule))
                              summarize l = Left $ lefts l
                              theMatch = case rights matches of [] -> summarize matches
                                                                _ -> Right $ head $ rights matches
                              singletonize x = case x of Right r -> Right $ head r
                                                         Left l -> Left [l]
                              anteUp new (AbsRule ps' (Sequent _ c')) = AbsRule ps' (Sequent new c')
                              anteOut (AbsRule _ (Sequent ps' _)) = ps'


derivationProves :: (S_NextVar sv quant, SchemeVar sv, Schematizable sv, Schematizable f, Schematizable quant, Schematizable con, Schematizable pred, 
                    UniformlyEquaitable sv, UniformlyEquaitable f, UniformlyEquaitable quant, UniformlyEquaitable con, UniformlyEquaitable pred, 
                    Carnap.Core.Unification.HigherOrderMatching.Matchable (Sequent (SSequentItem pred con quant f sv)) (Var pred con quant f sv ()), 
                    Carnap.Core.Unification.HigherOrderMatching.Matchable (AbsRule (Sequent (SSequentItem pred con quant f sv))) (Var pred con quant f sv ())) => 
                    Set.Set (AmbiguousRulePlus (Sequent (SSequentItem pred con quant f sv))) -> Judgement (Form pred con quant f sv a) (SimpleJustification (Form pred con quant f sv a)) -> 
                    Either [MatchError (Var pred con quant f sv () (AbsRule (Sequent (SSequentItem pred con quant f sv)))) (AbsRule (Sequent (SSequentItem pred con quant f sv)))] 
                           (Sequent (SSequentItem pred con quant f sv))
derivationProves _ (Line p Premise) = Right $ Sequent [SeqList [liftToScheme p]] ( SeqList [liftToScheme p])
derivationProves ruleSet (Line c (Inference s l)) = do l' <- mapM (derivationProves ruleSet) l 
                                                       checkWithAmbig (lookupRule s ruleSet) l' c
