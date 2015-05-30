{-#LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, RankNTypes, TupleSections #-}

module Carnap.Core.ModelChecker.SatSolver(SatFormula, SatReduction, BooleanModel) where

import Data.List
import Control.Monad.State.Lazy
import qualified Data.Map as Map
import qualified Data.IntSet as IntSet

--------------------------------------------------------
--0. Basic Data Types
--------------------------------------------------------  

--what problems should get converted to
data SatFormula = SatFormula :&: SatFormula
                | SatFormula :|: SatFormula
                | SatFormula :->: SatFormula
                | SatFormula :<->: SatFormula
                | SatFormula :+: SatFormula
                | SatVar Int
                | Neg SatFormula

--when backtracking
data Clause = Watched Int Int [Int]      --Watched x1 x2 [x3 or ... or xN]
            | Unwatched Int Clause [Int] --Unwatched lvl old [x1 or ... or xN]

type CNF = [Clause]
--the type of assignments to varibles
type BooleanModel = [Int]

--------------------------------------------------------
--1. Conversion to CNF
--------------------------------------------------------

--gets max varible used in SAT formula
maxVar (p :&: q)   = max (maxVar p) (maxVar q)
maxVar (p :|: q)   = max (maxVar p) (maxVar q)
maxVar (p :->: q)  = max (maxVar p) (maxVar q)
maxVar (p :<->: q) = max (maxVar p) (maxVar q)
maxVar (p :+: q)   = max (maxVar p) (maxVar q)
maxVar (SatVar v)  = v
maxVar (Neg p)     = maxVar p

--based on http://www.cs.jhu.edu/~jason/tutorials/convert-to-CNF.html
--needs to keep track of the maximum varible at any given time
--converts to an equisatisfiable formula and not an equivlent formula
toCNF' :: SatFormula -> State Int [[Int]]
toCNF' (p :&: q) = do 
    pcnf <- toCNF' p
    qcnf <- toCNF' q
    return $ pcnf ++ qcnf
toCNF' (p :|: q) = do
    m <- get
    put (m + 1)
    pcnf <- toCNF' p
    qcnf <- toCNF' q
    let pcnf' = map (m:) pcnf
    let qcnf' = map ((0 - m):) qcnf
    return $ pcnf' ++ qcnf'
toCNF' (p :->: q)        = toCNF' ((Neg p) :|: q)
toCNF' (p :<->: q)       = toCNF' $ (p :->: q) :&: (q :->: p)
toCNF' (SatVar v)        = return [[v + 2]]
toCNF' (p :+: q)         = toCNF' $ Neg (p :<->: q)
toCNF' (Neg (SatVar v))  = return [[-v - 2]] --reserve 0 and 1
toCNF' (Neg (Neg p))     = toCNF' p
toCNF' (Neg (p :&: q))   = toCNF' $ (Neg p) :|: (Neg q)
toCNF' (Neg (p :|: q))   = toCNF' $ (Neg p) :&: (Neg q)
toCNF' (Neg (p :->: q))  = toCNF' $ p :&: (Neg q)
toCNF' (Neg (p :<->: q)) = toCNF' $ Neg ((p :->: q) :&: (q :->: p))
toCNF' (Neg (p :+: q))   = toCNF' (p :<->: q)

toCNF :: SatFormula -> [[Int]]
toCNF satform = evalState (toCNF' satform) (1 + maxVar satform)

makeClause :: [Int] -> Clause
makeClause (x:y:xs) = Watched x y xs

--finds empty cluases
hasEmpty :: [[Int]] -> Bool
hasEmpty = any null

has1 [x] = True
has1 _   = False

--filter out single clauses so that they can be immediently assumed
getSingles :: [[Int]] -> ([[Int]], [Int])
getSingles cnf = (filter (not . has1) cnf, concat $ filter has1 cnf)

--converts [[Int]] to a watchable CNF CNF
convertCNF :: [[Int]] -> CNF
convertCNF = map makeClause

--to put it all togethor
--

--------------------------------------------------------
--2. Typeclasses
--------------------------------------------------------

class (problem ~ model) => SatReduction problem model where
    solveProblem :: problem -> (SatFormula -> Maybe BooleanModel) -> Maybe model

--we needed a type class for defining hureistics
--common needs factored out of http://www.cs.utexas.edu/~isil/cs780-02/matthew-pirocchi.pdf
class DecisionHureistic h where
    initHureistic :: [[Int]] -> h
    newConflictClause :: [Int] -> h -> h
    newAssignment :: Int -> h -> h
    --backtrack current old = <hureistic state to use in backtracked postion>
    --the intended implementations are the following
    	--backtrack cur old = cur (for somthing like VSIDS)
    	--backtrack cur old = old (for like everthing else)
    backtrack :: h -> h -> h
    --the main funciton of intrest
    decideVarible :: h -> Int

--------------------------------------------------------
--3. CNF state solver and types
--------------------------------------------------------

type ImplGraph = Map.Map Int [(Int, Int)]

--the state of the solver at any given moment (and a stack of these is maintained)
data SolverState h = SolverState {formula :: CNF, implGraph :: ImplGraph, learned :: CNF, hureistic :: h, assignment :: IntSet.IntSet}

--------------------------------------------------------
--4. "Variable State-Independent Decaying Sum"
--------------------------------------------------------

count x = genericLength . filter (==x)

--representation is important here
	--I need the following: fast choice of best free varible ideally O(1)
	--                      polynomial setup becuase fuck setup, who cares
	--                      ideally O(n) update on conflict per conflict varible O(n*log(m)) acceptable
	--                      logrithmic update of free varibles
	--                      instance update of free varibles on backtrack
data VSIDS = VSIDS { scores :: [(Double, Int)], bound :: IntSet.IntSet }

instance DecisionHureistic VSIDS where
	--init the hureistic to select count number of clauses used
    initHureistic cnf = VSIDS { scores = numOccurences, bound = IntSet.empty }
        where occurences = map abs $ concat cnf
              numOccurences = map (\x -> (count x occurences, x)) (nub occurences)

    --now adjust values for recent conflict
    newConflictClause values vsids = vsids {scores = sort $ map (\(s, v) -> if v `elem` values then (s + 1, v) else (s, v)) (scores vsids) } --0.96 is just my best guess at a value
        where bump mp []     = mp
              bump mp (x:xs) = bump (Map.adjust (+1) (abs x) mp) xs --plus 1 is also just my best guess at how much to bump by

    newAssignment a vsids = vsids { bound = IntSet.insert (abs a) (bound vsids) }

    backtrack cur old = VSIDS {scores = scores cur, bound = bound old}

    decideVarible (VSIDS {scores = [(_, x)], bound=_})      = x --how do I know weather to make it posative or negative? 
    decideVarible (VSIDS {scores = ((_, x) : xs), bound=b}) = if not $ x `IntSet.member` b then x else decideVarible $ VSIDS {scores = xs, bound = b}

--------------------------------------------------------
--5. "Dynamic Largest Individual Sum"
--------------------------------------------------------

--varible is stored negative or posative depending on weather
--negatives or posatives occur more often
--[(numPos, numNeg, varible] or [(numNeg, numPos, -varible]]
newtype DLIS = DLIS [(Int, Int, Int)]

instance DecisionHureistic DLIS where
    initHureistic cnf = DLIS $ sort numOccurences
        where occurences = concat cnf
              numOccurences = map getTuple (map abs . nub $ occurences)
              getTuple x | negScore >= posScore = (negScore, posScore, negate x)
                         | otherwise            = (posScore, negScore, x)
                  where negScore = count (negate x) occurences
                        posScore = count x occurences
    newConflictClause clause (DLIS lst) = DLIS $ sort (map updateTuple lst)
        where updateTuple (a, b, v) = (a + count v clause, b + count (negate v) clause, v)
    --get rid of the old one                    
    newAssignment a (DLIS lst) = DLIS $ deleteBy (\(_, _, a) (_, _, b) -> abs a == abs b) (undefined, undefined, a) lst
    --completelly state dependent
    backtrack cur old = old
    --now decide a varible by quickly pulling somthing off the top
    decideVarible (DLIS ((_, _, x):xs)) = x

--------------------------------------------------------
--7. Define propegation (BCP algorithm)
--------------------------------------------------------

data PropState = PropState { decisionLevel :: Int, assignStack :: [Int], cnfState :: CNF, propImplGraph :: ImplGraph, propAssign :: IntSet.IntSet }

popAssignStack :: State PropState ()
popAssignStack = do
    st <- get
    put $ st { assignStack = tail (assignStack st) }

clearCNFState :: State PropState ()
clearCNFState = do
    st <- get
    put $ st { cnfState = [] }

addImpl :: Int -> Int -> State PropState ()
addImpl ant con = do
    st <- get
    put $ st { propImplGraph = Map.insertWith (++) con [(ant, con)] (propImplGraph st) }

addImpls :: [Int] -> Int -> State PropState ()
addImpls ants con = mapM_ (\a -> addImpl a con) ants

addClause :: Clause -> State PropState ()
addClause c = do
    st <- get
    put $ st { cnfState = c : (cnfState st) }

getDecisionLevel :: State PropState Int
getDecisionLevel = do
    st <- get
    return $ decisionLevel st

getMemberPred :: State PropState (Int -> Bool)
getMemberPred = do
    st <- get
    return $ \a -> a `IntSet.member` (propAssign st)

pushNewAssign :: Int -> State PropState ()
pushNewAssign a = do
    st <- get
    put $ st { assignStack = a : (assignStack st) }

newAssign :: Int -> State PropState ()
newAssign a = do
    st <- get
    put $ st { propAssign = IntSet.insert a (propAssign st) }

--this either returns a new CNF or a conflict
propagateSingle :: Int -> CNF -> State PropState (Maybe Int)
propagateSingle a (c@(Unwatched _ _ _):cs) = do
    addClause c
    propagateSingle a cs
propagateSingle a (c@(Watched x y rest):cs) | x == a || y == a = do
    lvl <- getDecisionLevel
    addClause $ Unwatched lvl c (x:y:rest)
    propagateSingle a cs
propagateSingle a (c@(Watched x y rest):cs) | let na = negate a in x == na || y == na = do
    let whole = (x:y:rest)
    set <- getMemberPred
    let unset = filter (\v -> not $ set v || set (negate v)) whole
    case unset of
        [new] -> if set (negate new)
            then return $ Just new
            else do addImpls (delete new whole) new
                    pushNewAssign new
                    lvl <- getDecisionLevel
                    addClause (Unwatched lvl c whole)
                    propagateSingle a cs
        watchable -> do
            let [w1, w2] = take 2 watchable
            addClause $ Watched w1 w2 (whole \\ [w1, w2])
            propagateSingle a cs
propagateSingle a (c:cs) = do
    addClause c
    propagateSingle a cs

--keeps on propagateing new assignments until it can't
--the result is a new CNF, ImplGraph, and assignment
--it could occur that a conflict about a certain assignment arrises (Returns Just A)
--in which case the impl graph is in the proper state to handle such a thing
--the propgation algorithm is given the current decision level
propagate' :: State PropState (Maybe Int)
propagate' = do
    st <- get
    case assignStack st of
        (assign:as) -> do
            newAssign assign
            popAssignStack
            let cnf = cnfState st
            clearCNFState
            propagateSingle assign cnf
            propagate' --keep going, there might be more in the stack!!
        [] -> return Nothing --we made it to the end!! 

{-
addImpl :: Int -> Int -> State PropState ()
addImpl ant con = do
    st <- get
    put $ st { newImpls = (ant, con) : (newImpls st) }

addImpls :: [Int] -> Int -> State PropState ()
addImpls ant con = mapM_ (\a -> addImpl a con) ant

addClause :: [Int] -> State PropState ()
addClause clause = do
    st <- get
    put $ st { newCNF = clause : (newCNF st) }
-}

{-
propegateQ :: Int -> (Int -> Bool) -> CNF -> State PropState (Maybe Int)
propegateQ a set ((x:y:xs):cs)   | x == a || y == a = propegateQ a set cs
propegateQ a set (c@(x:y:xs):cs) | negate a == x || negate a == y = do
    let unassigned = filter (\x -> not $ set x || set (negate x)) c
    case unassigned of
        [newAssign] -> if set (negate newAssign) --if we have fond a conflict!
            then return $ Just newAssign --then stop here say where the conflict occured
            else do 
                addImpls (delete newAssign c) newAssign
                propegateQ a set cs
        watchable -> do
            let watched = take 2 watchable
            addClause $ watched ++ (c \\ watched)
            propegateQ a set cs
propegateQ a set (c:cs) = do
    addClause c
    propegateQ a set cs
propegateQ a set [] = return Nothing --we made it to the end without conflct

propogate' :: Int -> (Int -> Bool) -> CNF -> State PropState (Maybe Int)
propogate' a set cnf = do
	propegateQ a set cnf
    st <- get
    let impls = nub $ newImpls st
    let newcnf = newCNF st
    case impls of
        ((ant, con):imps) -> do
            set $ PropState {newImpls = imps, newCNF = []}
            propogate' con set
-}

--------------------------------------------------------
--7. Define cutting for conflict cluases
--------------------------------------------------------

conflictCut gph n1 n2 = e1 ++ e2
    where (Just e1) = Map.lookup n1 gph
          (Just e2) = Map.lookup n2 gph

--finding the conflict clause from the cut is super easy
conflictClause cut = map (negate . fst) cut

--------------------------------------------------------
--8. Define the actual solver
--------------------------------------------------------
{-
backtrack :: DecisionHureistic h => State [SolverState h] (SolverState h)
backtrack clause = do
    state <- getState
    if null $ (assignment state)
      then return state
      else do let change = head $ assignment state
              if change `elem` clause
                then popState

cnfSatSolve :: DecisionHureistic h => State [SolverState h] (SolverState h)
cnfSatSolve = do
    state <- getState
    pushState --allow ourselves the ability to backtrack
    let choice = decideVarible (hureistic state) --choose a varible assignment
    --add the assginment to our system
    assign choice
    addNode choice
    --propogate the choice
    propegate
    --now check for panic/conflict
    if (panic state)
-}      

--------------------------------------------------------
--9. SAT solver
--------------------------------------------------------

--solve :: SatReduction problem model => problem -> Maybe model
--solve problem = undefined




