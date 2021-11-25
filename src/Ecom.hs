{-
Module      : Ecom (update from November 18, 2021)
Copyright   : (c) Peter Padawitz and Jos Kusiek, 2021
License     : BSD3
Stability   : experimental
Portability : portable

Ecom contains the solver and the enumerator.
-}

module Ecom where

import Eterm
import Epaint
import Esolve
import Prelude ()
import qualified Base.Haskell as Haskell
import Base.System

initialFont :: String
initialFont = "Sans 16"

data PossAct = Add [[Int]] | Remove [Int] | Replace [[Int]]

-- PROOFS

data ProofElem = ProofElem
    { peMsg,peMsgL,peTreeMode :: String
    , peTreePoss              :: [[Int]]
    , peCurr                  :: Int
    , pePerms                 :: Int -> [Int]
    , peVarCounter            :: String -> Int
    , peNewPreds              :: ([String],[String])
    , peSolPositions          :: [Int]
    , peSubstitution          :: (SubstS,[String])
    , peJoined                :: Bool
    , peConstraints           :: (Bool,[String])
    , peAxioms,peNewAxioms,peTheorems,peNewTheorems,peTrees :: [TermS]
    }

showDeriv :: [ProofElem] -> [Term String] -> [Int] -> String
showDeriv proof trees solPositions = concat (zipWith f (indices_ proof) proof)
                                            ++ solsMsg
               where f i proofElem = show i ++ ". " ++ peMsg proofElem ++ "\n\n"
                     sols = map (trees!!) solPositions
                     solsMsg = if null sols then ""
                               else "Solutions:" ++ concatMap f sols
                               where f t = "\n\n" ++ showTree False t

showCurr :: Bool -> TermS -> String -> String
showCurr fast t tm = "\nThe current "++tm++" is given by\n\n"++ showTree fast t

showNew :: Bool -> Int -> TermS -> String -> Int -> [[Int]] -> String -> String
showNew fast 1 t msg n ps tm = preceding msg ps tm n ++ "a single " ++ tm ++
                               ",\nwhich is given by\n\n" ++ showTree fast t
showNew fast k t msg n ps tm = preceding msg ps tm n ++ show k ++ ' ':tm ++
                               "s." ++ showCurr fast t tm

showPre fast t msg n ps tm = preceding msg ps tm n ++ '\n':'\n':showTree fast t

preceding msg ps tm n = msg ++ (if take 3 msg `elem` ["BUI","MIN"] then ""
                                else str1 ++ showPS ps ++ tm ++ 's':
                                    (str2 `onlyif` nrs)) ++ " leads to "
     where str1 = if last msg == '\n' then "" else " "
           str2 = " (" ++ if n == 1 then "one step)" else show n++ " steps)"
           nrs = take 3 msg `elem` words "NAR REW SIM"
           showPS []  = ("to " `ifnot` nrs) ++ "the preceding "
           showPS ps = "at positions" ++ concatMap f ps ++ "\nof the preceding "
           f p = '\n':show p `minus1` ' '

-- PROOF TERM functions

deriveStep (Mark _ _)       = False
deriveStep (Matching _ _)   = False
deriveStep (Refuting _)     = False
deriveStep (SafeSimpl _)    = False
deriveStep (Simplifying _)  = False
deriveStep (SimplStrat _ _) = False
deriveStep _                = True

command :: Parser Step
command = concat
          [symbol "AddAxioms" >> list linearTerm >>= return . AddAxioms,
           symbol "ApplySubst" >> return ApplySubst,
           do symbol "ApplySubstTo"; x <- token quoted
              enclosed linearTerm >>= return . ApplySubstTo x,
           symbol "ApplyTransitivity" >> return ApplyTransitivity,
           symbol "BuildKripke" >> token int >>= return . BuildKripke,
           symbol "BuildRE" >> return BuildRE,
           symbol "Coinduction" >> return Coinduction,
           symbol "CollapseStep" >> token bool >>= return . CollapseStep,
           symbol "CollapseVars" >> return CollapseVars,
           symbol "ComposePointers" >> return ComposePointers,
           symbol "CopySubtrees" >> return CopySubtrees,
           symbol "CreateIndHyp" >> return CreateIndHyp,
           symbol "CreateInvariant" >> token bool >>= return . CreateInvariant,
           symbol "DecomposeAtom" >> return DecomposeAtom,
           symbol "DerefNodes" >> return DerefNodes,
           symbol "DetKripke" >> return DetKripke,
           symbol "Distribute" >> return Distribute,
           symbol "EvaluateTrees" >> return EvaluateTrees,
           do symbol "ExpandTree"; b <- token bool
              token int >>= return . ExpandTree b,
           symbol "FlattenImpl" >> return FlattenImpl,
           symbol "Generalize" >> list linearTerm >>= return . Generalize,
           symbol "Induction" >> return Induction,
           do symbol "Mark"; ps <- list (list int)
              list (list int) >>= return . Mark ps,
           do symbol "Matching"; n <- token int
              token int >>= return . Matching n,
           symbol "Minimize" >> return Minimize,
           symbol "ModifyEqs" >> token int >>= return . ModifyEqs,
           symbol "MoveQuant" >> return MoveQuant,
           do symbol "Narrow"; limit <- token int
              token bool >>= return . Narrow limit,
           do symbol "NegateAxioms"; ps <- list quoted
              list quoted >>= return . NegateAxioms ps,
           symbol "PermuteSubtrees" >> return PermuteSubtrees,
           symbol "RandomLabels" >> return RandomLabels,
           symbol "RandomTree" >> return RandomTree,
           symbol "ReduceRE" >> token int >>= return . ReduceRE,
           symbol "RefNodes" >> return RefNodes,
           symbol "Refuting" >> token bool >>= return . Refuting,
           symbol "ReleaseNode" >> return ReleaseNode,
           symbol "ReleaseSubtree" >> return ReleaseSubtree,
           symbol "ReleaseTree" >> return ReleaseTree,
           symbol "RemoveCopies" >> return RemoveCopies,
           symbol "RemoveEdges" >> token bool >>= return . RemoveEdges,
           symbol "RemoveNode" >> return RemoveNode,
           symbol "RemoveOthers" >> return RemoveOthers,
           symbol "RemovePath" >> return RemovePath,
           symbol "RemoveSubtrees" >> return RemoveSubtrees,
           symbol "RenameVar" >> token quoted >>= return . RenameVar,
           symbol "ReplaceNodes" >> token quoted >>= return . ReplaceNodes,
           symbol "ReplaceOther" >> return ReplaceOther,
           do symbol "ReplaceSubtrees"; ps <- list $ list int
              list linearTerm >>= return . ReplaceSubtrees ps,
           symbol "ReplaceText" >> token quoted >>= return . ReplaceText,
           do symbol "ReplaceVar"; x <- token quoted; u <- enclosed linearTerm
              list int >>= return . ReplaceVar x u,
           symbol "ReverseSubtrees" >> return ReverseSubtrees,
           symbol "SafeSimpl" >> token bool >>= return . SafeSimpl,
           do symbol "SetAdmitted"; block <- token bool
              list quoted >>= return . SetAdmitted block,
           do symbol "SetCurr"; msg <- token quoted
              token int >>= return . SetCurr msg,
           symbol "ShiftPattern" >> return ShiftPattern,
           symbol "ShiftQuants" >> return ShiftQuants,
           symbol "ShiftSubs" >> list (list int) >>= return . ShiftSubs,
           do symbol "Simplify"; limit <- token int
              token bool >>= return . Simplify limit,
           symbol "ShowKripke" >> return ShowKripke,
           symbol "Simplifying" >> token bool >>= return . Simplifying,
           do symbol "SimplStrat"; s <- token strategy
              token strategy >>= return . SimplStrat s,
           symbol "SplitTree" >> return SplitTree,
           symbol "SubsumeSubtrees" >> return SubsumeSubtrees,
           do symbol "Theorem"; b <- token bool
              enclosed linearTerm >>= return . Theorem b,
           symbol "Transform" >> token int >>= return . Transform,
           symbol "UnifySubtrees" >> return UnifySubtrees]

linearTerm :: Parser (Term String)
linearTerm = concat [do symbol "F"; x <- token quoted
                        list linearTerm >>= return . F x,
                     symbol "V" >> token quoted >>= return . V]

-- SOLVER messages

start :: String
start = "Welcome to Expander3 (November 15, 2021)"

startOther :: String -> String
startOther solve = "Load and parse a term or formula in " ++ solve ++ "!"

addAxsMsg msg = "The set of axioms is extended by\n\n" ++ drop 4 msg

admits b str str' = str ++ (if b then " admits " else " forbids ") ++ str'

admitted :: Bool -> [String] -> String
admitted True []  = "All simplifications are admitted."
admitted block xs = (if block then "All simplifications except those for "
                              else "Only simplifications for ") ++
                    showStrList xs ++ " are admitted."

applied :: Bool -> String -> String
applied b str = "Applying the " ++ s ++ str ++ "\n\n"
          where s = if b then if '!' `elem` str then "induction hypothesis\n\n"
                                                else "axiom or theorem\n\n"
                         else "axioms\n\n"

appliedToSub :: (Eq a, Num a, Show a) => String -> a -> String
appliedToSub str 1 = "A " ++str++" step has been applied to the selected tree."
appliedToSub str n = show n ++ " " ++ str ++
                     " steps have been applied to the selected trees."

arcInserted :: (Show a, Show a1) => a -> a1 -> String
arcInserted p q = "An arc from position " ++ show p ++ " to position " ++
                    show q ++ " has been inserted."

atomDecomposed :: String
atomDecomposed = "The selected atom has been decomposed."

atomNotDecomposed :: String
atomNotDecomposed = "The selected atom cannot be decomposed."

axsRemovedFor :: Show a => a -> String
axsRemovedFor xs = "The axioms for " ++ showStrList xs ++ " have been removed."

badNoProcs = "Enter a number > 1 into the entry field."

check rest = "\n-- CHECK FROM HERE:\n" ++ rest

circle :: (Show a, Show a1) => a -> a1 -> String
circle p q = "The operation fails because the current tree contains a back " ++
             "pointer from position "++ show p ++" to position "++ show q ++"."

circlesUnfolded :: (Eq a, Num a, Show a) => a -> String
circlesUnfolded 1 = "\nCircles were unfolded one time."
circlesUnfolded n = "\nCircles were unfolded " ++ show n ++ " times."

copiesRemoved :: String
copiesRemoved = "Copies of the selected tree have been removed."

collapsed :: String
collapsed = "The selected tree has been collapsed."

collapsedVars = "The free variables of the selected trees have been collapsed."

complsAdded :: Show t => [t] -> String
complsAdded xs = "Axioms for the complement" ++ str ++ showStrList xs ++
                  " have been added."
                 where str = case xs of [_] -> " of "; _ -> "s of "

concCallsPrem = "Some conclusion contains the root of the corresponding " ++
                " premise."

creatingInvariant str ax = str ++ " for the iterative program\n\n" ++
                        showTree False ax ++ "\n\n"

dereferenced :: String
dereferenced = "The selected pointers have been dereferenced."

deterministic n = "The Kripke model has been made deterministic. It has " ++ 
                  show' n "state" ++ "."

distributed = "The selected factor/summand/premise/conclusion has been " ++
            " distributed over the selected dis- or conjunction."

edgesRemoved :: Bool -> String
edgesRemoved True = "Cycles have been removed."
edgesRemoved _    = "Forward arcs have been turned into tree edges."

dangling :: String
dangling = "The selected subtree cannot be removed because it is referenced."

emptyProof :: String
emptyProof = "The proof is empty."

emptySubst :: String
emptySubst = "The substitution is empty."

emptyPicDir :: String
emptyPicDir = "The picture directory is empty."

endOfProof :: String
endOfProof = "The end of the derivation has been reached."

entered = "The canvas shows a new graph."

enterNumber :: String
enterNumber = "Enter the number of a formula shown in " ++ tfield ++ "!"

enterTfield str = "Enter " ++ str ++ " into " ++ tfield ++ "!"

enterNumbers :: String
enterNumbers = "Enter numbers of formulas shown in " ++ tfield ++ "!"

eqInverted :: String
eqInverted = "The selected equation has been inverted."

eqsModified :: String
eqsModified = "The selected regular equations have been modified."

evaluated :: String
evaluated = "The selected trees have been evaluated."

expandMsg = "The selected trees have been expanded."

extendedSubst :: String
extendedSubst = "The equations in " ++ tfield ++
                " have been added to the substitution."

finishedNar :: (Eq a, Num a, Show a) => Bool -> a -> String
finishedNar True 1 = "A narrowing step has been performed.\n"
finishedNar _    1 = "A rewriting step has been performed.\n"
finishedNar True n = show n ++ " narrowing steps have been performed.\n"
finishedNar _ n    = show n ++ " rewriting steps have been performed.\n"

finishedSimpl :: (Eq a, Num a, Show a) => a -> String
finishedSimpl 1 = "A simplification step has been performed.\n"
finishedSimpl n = show n ++ " simplification steps have been performed.\n"

flattened :: String
flattened = "The selected clause has been flattened."

formString :: Bool -> String
formString b = if b then "formula" else "term"

generalized :: String
generalized = "The selected formula has been generalized with the formulas" ++
              " in " ++ tfield ++ "."

illformed str = "The " ++ str ++ " in " ++ tfield ++ " is not well-formed."

indApplied str = str ++ " has been applied to the selected formulas." ++
                 "\nSee the new axioms in the text field."

indHypsCreated [x] = "The induction variable is " ++ showStr x ++
     ".\nSee the induction hypotheses in the text field.\nEnter axioms for >>."

indHypsCreated xs = "The induction variables are " ++ showStrList xs ++
    ".\nInduction hypotheses have been added to the theorems." ++
    "\nSpecify the induction ordering >> on " ++ show (length xs) ++ "-tuples!"

iniSigMap :: String
iniSigMap = "The signature map is the identity."

iniSpec :: String
iniSpec = "The specification consists of built-in symbols. "

instantiateVars = "Select iterative equations and variables on right-hand " ++
   "sides to be expanded!\nRecursively defined variables are not expanded!"

invCreated :: Bool -> String
invCreated b =
   "The selected formula has been transformed into conditions on a " ++
   (if b then "Hoare" else "subgoal") ++ " invariant INV.\nAdd axioms for INV!"

kripkeBuilt :: ( Eq a, Eq c, Eq d, Eq e
               , Num a, Num b, Num c,  Num d, Num e
               , Show b, Show c, Show d, Show e
               , Ord b
               ) => a -> b -> c -> d -> e -> String
kripkeBuilt mode procs sts labs ats =
      "A " ++ f mode ++ " Kripke model with " ++ 
      (if procs > 0 then show procs ++ " processes, " else "") ++ 
      show' sts "state" ++ ", " ++ show' ats "atom" ++ " and " ++ 
      show' labs "label" ++ "\nhas been built from the " ++ g mode
      where f 0 = "cycle-free"; f 1 = "pointer-free"; f _ = ""
            g 3 = "current graph."; g 4 = "regular expression."; g _ = "axioms."

kripkeMsg = "BUILDING A KRIPKE MODEL"
    
leavesExpanded :: String
leavesExpanded = "The selected trees have been expanded at their leaves."

levelMsg :: (Eq a, Num a, Show a) => a -> String
levelMsg i = "The current tree has been collapsed at " ++
             (if i == 0 then "leaf level." else "the " ++ show (i+1) ++
             " lowest levels.")

loaded :: String -> String
loaded file = file ++ " has been loaded into the text field."

minimized n = "The Kripke model has been minimized. It has " ++ 
              show' n "states."

moved :: String
moved = "The selected quantifiers have been moved to the parent node."

newCls :: String -> String -> String
newCls cls file = "The " ++ cls ++ str ++ file ++ " have been added."
                  where str = if file == tfield then " in " else " of "

newCurr :: String
newCurr = "The tree slider has been moved."

newInterpreter eval t = eval ++ " is the actual widget-term interpreter. " ++
                        showTerm0 t ++ " is applied before painting."

newPredicate :: String -> String -> String -> String
newPredicate str1 str2 x = "The " ++ str1 ++ ' ':x ++
                            " has been turned into a " ++ str2 ++ "."

newSig :: String -> String
newSig file = "The symbols in " ++ file ++ " have been added to the signature."

newSigMap :: String -> String
newSigMap file = "The assignments in " ++ file ++
                 " have been added to the signature map."

noApp :: String -> String
noApp str = str ++ " is not applicable to the selected trees."

noAppT :: Maybe Int -> String
noAppT k = case k of Just n -> "Theorem no. " ++ show n ++ str
                     _ -> "The theorem in the text field" ++ str
           where str = " is not applicable to the selected trees."

noAxiomsFor :: Show a => a -> String
noAxiomsFor xs = "There are no axioms for " ++ showStrList xs ++ "."

nodesReplaced :: Show a => a -> String
nodesReplaced a = "The roots of the selected trees have been replaced by "
                  ++ showStr a ++ "."

notDisCon :: String
notDisCon = "The theorem to be applied is not a distributed clause."

noTheorem :: Show a => Maybe a -> String
noTheorem k = (case k of Just n -> "No. " ++ show n
                         _ -> "The clause in the text field") ++
              " is neither an axiom nor a theorem."

noTheoremsFor xs = "There are no theorems for " ++ showStrList xs ++ "."

notInstantiable :: String
notInstantiable =
                "The selected variable cannot be instantiated at this position."

notUnifiable :: Show a => Maybe a -> String
notUnifiable k = (case k of Just n -> "Theorem no. " ++ show n
                            _ -> "The theorem in the text field") ++
                 " is not unifiable with any selected redex."

noUnifier :: String
noUnifier = "The selected subtrees are not unifiable."

ocFailed :: String -> String
ocFailed x = x ++ " cannot be unified with a term that contains " ++ x ++
             " and is not a variable."

onlyRew :: String
onlyRew = "\nThe selected tree is a term. " ++
          "Hence formula producing axioms are not applicable!"

orderMsg :: String -> String
orderMsg str = "The nodes of the selected tree have been labelled with " ++
                str ++ "."

partialUnifier :: String
partialUnifier = "The selected trees are only partially unifiable."

permuted :: String
permuted = "The list of maximal proper subtrees has been permuted."

pointersComposed :: String
pointersComposed = "The pointers in the selected trees have been composed."

posInSubst :: String
posInSubst = "There is a pointer in a substitution."

procsMsg n = "New number of processes: " ++ show n

proofLoaded :: String -> String
proofLoaded file = "The proof term has been loaded from " ++ file ++ "."

quantifierMoved = "A quantifier has been moved down the selected subtree."

referenced = "The node selected at first is the target of pointers " ++
             "from the predecessors of the other selected nodes."

refuteMsg b = admits (not b) "Narrowing" "refutation."

regBuilt :: String
regBuilt = "A regular expression has been built from the Kripke model."

regReduced :: String
regReduced = "The selected regular expressions have been reduced."

removed :: String
removed = "The selected trees have been removed."

removedOthers :: String
removedOthers = "All trees except the one below have been removed."

replacedTerm :: String
replacedTerm = "The selected terms have been replaced by equivalent ones."

replaceIn :: String -> String
replaceIn solve = "The subtree has been replaced by the tree of "++solve++"."

reversed :: String
reversed = "The list of selected (sub)trees has been reversed."

safeMsg b = admits (not b) "Simplification" "pure expansion."

see :: String -> String
see str = "See the " ++ str ++ " in the text field."

selectCorrectSubformula :: String
selectCorrectSubformula = "Select an implication, a conjunction or a " ++
                          "disjunction and subterms to be replaced!"

selectDistribute = "Select a factor, summand, premise or conclusion to be " ++
                   "distributed and a dis- or conjunction!"

selectSub :: String
selectSub = "Select a proper non-hidden subtree!"

shifted = "The selected subformulas have been shifted to the premise " ++
          " or conclusion."

show' 1 obj = "one " ++ obj
show' n obj = show n ++ ' ':obj ++ "s"

sigMapError :: String -> String
sigMapError other = "The signature map does not map to the signature of " ++
                    other ++ "."

simplifiedPar :: String
simplifiedPar = "A simplification step has been applied to the root position "
                ++ "of each selected tree."

solved :: (Eq a, Num a, Show a) => [a] -> String
solved [n]    = "A solution is at position " ++ show n ++ "."
solved (n:ns) = "Solutions " ++ "are at positions " ++
                splitString 27 63 (mkRanges ns n) ++ "."
solved _      = "There are no solutions."

stretched :: String
stretched = "The selected conditional equation has been stretched."

subMsg :: String -> String -> String
subMsg str x = str ++ " has been substituted for " ++ x ++ "."

subsAppliedToAll :: String
subsAppliedToAll = "The substitution has been applied to all variables."

subsAppliedTo :: String -> String
subsAppliedTo x = "The substitution has been applied to " ++ x ++ ". "

subsumed :: String -> String
subsumed object = "The selected tree results from the subsumption of a " ++
                   object ++ "."

subtreesNarrowed :: (Eq a, Num a, Show a) =>
                    Maybe a -> String
subtreesNarrowed k = (case k of Just n
                                 -> if n == -1 then "Axioms are not"
                                      else "Theorem no. " ++ show n ++ " is not"
                                _ -> "No clause is") ++
                     " applicable to the selected trees."

thApplied :: (Eq a, Num a, Show a) => Maybe a -> String
thApplied k = (case k of Just n -> if n == -1 then "Axioms have"
                                    else "Theorem no. " ++ show n ++ " has"
                         _ -> "The clauses in the text field have") ++
              " been applied to the selected trees."

termsStored :: String
termsStored = "Storable subterms of the selected trees have been stored."

textInserted :: String
textInserted = "The tree in "++tfield++" replaces/precedes the selected trees."

tfield = "the text field"

transformed :: String
transformed = "The selected graph has been transformed."

transitivityApplied :: String
transitivityApplied
              = "The transitivity axiom has been applied to the selected atoms."

treeParsed =
        "The text field contains a string representation of the selected tree."

treesSimplified :: String
treesSimplified = "The trees are simplified."

unified :: String -> String
unified object = "The selected tree results from the unification of two " ++
                  object ++ "s."

unifiedT :: String
unifiedT = "The selected trees have been unified. "

wrongArity :: Show a => String -> a -> String
wrongArity f lg = "The number in the entry field is too big. " ++ f ++
                  " has only " ++ show lg ++ " arguments."

enumerators,interpreters,specfiles1,specfiles2,specfiles3 :: [String]

enumerators  = words "alignment palindrome dissection" ++ ["level partition",
                     "preord partition","heap partition","hill partition"]

interpreters = words "tree widgets matrices" ++ ["matrix solution",
                     "linear equations","level partition","preord partition",
                     "heap partition","hill partition","dissection"]

specfiles1 =
  words "abp account align auto1 auto2 base bool bottle bottleac bottlef" ++
  words "btree cobintree coin coregs cse cycle dna echo echoac election" ++
  words "factflow flowers FP gauss graphs hanoi hanoilab hinze infbintree" ++
  words "kino knight kripke1 kripke2"

specfiles2 =
  words "lazy lift liftlab list listeval listrev log log4 lr1 lr2 micro" ++
  words "modal mutex mutexco mutexquad nat NATths needcoind newman obdd" ++ 
  words "obst partn penroseS phil philac polygons prims prog puzzle queens"

specfiles3 =
  words "regeqs relalg relalgdb relalgp robot ROBOTacts sendmore set" ++
  words "shelves simpl stack STACKimpl STACKimpl2 stream trans0 trans1" ++
  words "trans2 turtles widgets zip"

-- SOLVER template

solver :: String -> IORef Solver -> Enumerator -> Painter -> Template Solver
solver this solveRef enum paint = do
    builder <- loadGlade "Solver"
    let getObject :: GObjectClass cls => (GObject -> cls) -> String -> IO cls
        getObject = builderGetObject builder
        getButton = getObject castToButton
        getMenuItem   = getObject castToMenuItem
        getMenu   = getObject castToMenu
    
    win <- getObject castToWindow "win"
    applyBut <- getButton "applyBut"
    backBut <- getButton "backBut"
    canv <- canvas
    scrollCanv <- getObject castToScrolledWindow "scrollCanv"
    checkerRef <- newIORef $ error "checkerRef undefined"
    deriveBut <- getButton "deriveBut"
    treeSlider <- getObject castToScale "treeSlider"
    ent <- getObject castToEntry "ent"
    fontSize <- getObject castToScale "fontSize"
    fastBut <- getButton "fastBut"
    forwBut <- getButton "forwBut"
    hideBut <- getButton "hideBut"
    interpreterLabel <- getObject castToLabel "interpreterLabel"
    lab <- getObject castToLabel "lab"
    matchBut <- getButton "matchBut"
    narrowBut <- getButton "narrowBut"
    quit <- getButton "quit"
    randomBut <- getButton "randomBut"
    refuteButRef <- newIORef undefined
    safeButRef <- newIORef undefined
    simplBut <- getButton "simplBut"
    splitBut <- getButton "splitBut"
    stratBut <- getButton "stratBut"
    tedit <- getObject castToTextView "tedit"
    termBut <- getObject castToLabel "termBut"
    lab2 <- getObject castToLabel "lab2"
    eqsButRef <- newIORef undefined
    treeSize <- getObject castToScale "treeSize"

    fontRef <- newIORef $ error "fontRef undefined"

    -- signals
    
    deriveButSignalRef <- newIORef undefined
    backButSignalRef <- newIORef undefined
    forwButSignalRef <- newIORef undefined
    quitSignalRef <- newIORef undefined

    ctreeRef <- newIORef Nothing
    nodeRef <- newIORef Nothing
    penposRef <- newIORef Nothing
    subtreeRef <- newIORef Nothing
    isSubtreeRef <- newIORef Nothing
    suptreeRef <- newIORef Nothing
    osciRef <- newIORef Nothing

    formulaRef <- newIORef True
    joinedRef <- newIORef True
    safeSimplRef <- newIORef True
    firstMoveRef <- newIORef True
    showStateRef <- newIORef True
    firstClickRef <- newIORef True

    fastRef <- newIORef False
    checkingRef <- newIORef False
    checkingPRef <- newIORef (False,False)
    refutingRef <- newIORef False
    simplifyingRef <- newIORef False
    collSimplsRef <- newIORef False
    newTreesRef <- newIORef False
    restoreRef <- newIORef False
    trsOnCanvasRef <- newIORef False

    axiomsRef <- newIORef []
    theoremsRef <- newIORef []
    conjectsRef <- newIORef []
    newAxiomsRef <- newIORef []
    newTheoremsRef <- newIORef []
    oldTreepossRef <- newIORef []
    proofRef <- newIORef []
    proofTermRef <- newIORef []
    ruleStringRef <- newIORef []
    simplRulesRef <- newIORef []
    solPositionsRef <- newIORef []
    specfilesRef <- newIORef []
    termsRef <- newIORef []
    transRulesRef <- newIORef []
    treepossRef <- newIORef []
    treesRef <- newIORef []
    iniStatesRef <- newIORef []

    kripkeRef <- newIORef ([],[],[],[],[],[],[])

    canvSizeRef <- newIORef (0,0)
    cornerRef <- newIORef (30,20)
    currRef <- newIORef 0
    -- curr1Ref <- newIORef 0 -- Gtk does not need this
    matchingRef <- newIORef 0
    noProcsRef <- newIORef 2
    proofPtrRef <- newIORef 0
    proofTPtrRef <- newIORef 0
    picNoRef <- newIORef 0
    simplStratRef <- newIORef PA

    numberedExpsRef <- newIORef ([],True)
    constraintsRef <- newIORef (True,[])

    drawFunRef <- newIORef $ leaf "id"
    picEvalRef <- newIORef "tree"
    picDirRef <- newIORef "picDir"

    signatureMapRef <- newIORef (id,[])
    newPredsRef <- newIORef nil2
    partRef <- newIORef (id,[])
    substitutionRef <- newIORef (V,[])
    treeModeRef <- newIORef "tree"
    symbolsRef <- newIORef iniSymbols
    randRef <- newIORef seed
    sizeStateRef <- newIORef sizes0
    spreadRef <- newIORef (10,30)
    timesRef <- newIORef (0,300)
    speedRef <- newIORef 500
    counterRef <- newIORef $ const 0
    varCounterRef <- newIORef $ const 0
    permsRef <- newIORef $ \n -> [0..n-1]

    let mkSub :: Menu -> String -> Request Menu
        mkSub m text = cascade m text menuOpt {menuFont = font16}
        
        mkBut :: Menu -> String -> Action -> Request MenuItem
        mkBut m text cmd = do
          item <- menuItemNewWithLabel text
          addContextClass item "font14"
          item `on` menuItemActivated $ cmd
          menuShellAppend m item
          item `gtkSet` [widgetVisible := True]
          return item

        mkButF m cmd file = mkBut m file $ cmd file

        mkButs = zipWithM . mkBut

        kripkeButs1 m xs = do
          solve <- readIORef solveRef
          other <- getSolver solve
          mkButs m 
           ["here","with selected output","with state equivalence","in painter",
            "in " ++ other] $ map showKripke xs
                         
        kripkeButs2 m cmd = mkButs m 
           ["canvas","index transitions","state transitions","atom values",
            "state output"] . map cmd

        setCmd but text cmd = do
          but `gtkSet` [ buttonLabel := text ]
          but `on` buttonActivated $ cmd

        setCmdGtk but cmd = but `on` buttonActivated $ cmd
        
        setCmdSig but sig cmd = (but `on` buttonActivated $ cmd)
            >>= writeIORef sig

        buildSolve :: Action
        buildSolve = do
          icon <- iconPixbuf
          win `gtkSet` [windowTitle := this,
                        windowIcon := Just icon,
                        windowDefaultWidth := 1200,
                        windowDefaultHeight := 820]
          let da = getDrawingArea canv
          widgetAddEvents  da [ButtonMotionMask]
          on da buttonPressEvent $ do
              button <- eventButton
              pt0 <- eventCoordinates
              let pt = round2 pt0
              lift $ case button of LeftButton -> catchSubtree pt
                                    MiddleButton -> catchTree pt
                                    RightButton -> catchNode pt
                                    _ -> done
              return False
          on da motionNotifyEvent $ do
              lift $ do
                  dw <- widgetGetParentWindow da
                  (_, x, y, modifier) <- drawWindowGetPointerPos dw
                  let pt = (x, y)
                      button = Haskell.find (`elem` [Button1, Button2, Button3])
                                            modifier
                  case button of Just Button1 -> moveSubtree pt
                                 Just Button2 -> moveTree pt
                                 Just Button3 -> moveNode pt
                                 _ -> done
              return False
          da `on` buttonReleaseEvent $ do
              button <- eventButton
              lift $ case button of LeftButton -> releaseSubtree
                                    MiddleButton -> releaseTree
                                    RightButton -> releaseNode
                                    _ -> done
              return False
          let takeCurr = do 
                         curr1 <- fmap truncate $ treeSlider `gtkGet` rangeValue
                         setCurr newCurr curr1
          treeSlider `on` valueChanged $ takeCurr
          
          fmap Just (fontDescriptionFromString monospace) 
                         >>= widgetOverrideFont ent
          ent `on` keyPressEvent $ do
              name <- fmap unpack eventKeyName
              lift $ case name of
                     "Up" -> getFileAnd $ loadText True
                     "Down" -> getFileAnd saveGraph
                     "Right" -> applyClause False False False
                     "Left" -> applyClause False True False
                     "Return" -> do removeSpec; getFileAnd addSpecWithBase
                     _ -> done
              return False
          fmap Just labFont >>= widgetOverrideFont lab
          setBackground lab blueback
          gtkSet lab [labelLabel := start]
          on lab keyPressEvent $ do
                   name <- eventKeyName
                   lift $ case unpack name of "c" -> copySubtrees
                                              "d" -> distribute
                                              "i" -> replaceText
                                              "l" -> replaceNodes
                                              "L" -> randomLabels
                                              "m" -> permuteSubtrees
                                              "n" -> negateAxioms
                                              "o" -> removeNode
                                              "p" -> removePath
                                              "r" -> removeSubtrees
                                              "s" -> saveProof
                                              "T" -> randomTree
                                              "v" -> reverseSubtrees
                                              "x" -> showAxiomsFor
                                              "Left" -> incrCurr False
                                              "Right" -> incrCurr True
                                              _ -> done
                   return False
          fmap Just labFont >>= widgetOverrideFont lab2
          setBackground lab2 blueback
          fmap Just (fontDescriptionFromString monospace)
                            >>= widgetModifyFont tedit
          tedit `on` keyPressEvent $ do name <- fmap unpack eventKeyName
                                        lift $ case name of "Up" -> parseText
                                                            "Down" -> parseTree
                                                            _ -> done
                                        return False
          setCmdGtk matchBut $ setNarrow 1
          setCmdGtk randomBut $ setNarrow 2
          setCmdGtk narrowBut narrow
          setCmdSig forwBut forwButSignalRef proofForward'
          setCmdSig backBut backButSignalRef proofBackward
          setCmdSig deriveBut deriveButSignalRef setDeriveMode
          setCmdGtk hideBut hideOrShow
          setCmdSig quit quitSignalRef mainQuit
          setCmdGtk stratBut changeStrat
          setCmdGtk simplBut simplify
          setCmdGtk splitBut splitTree
          setCmdGtk fastBut switchFast
          setPicDir True
          buildSolve1
        
        buildSolve1 :: Action
        buildSolve1 = do
          solve <- readIORef solveRef
          other <- getSolver solve
          indBut <- getButton "indBut"
          setCmdGtk indBut induction
          coindBut <- getButton "coindBut"
          setCmdGtk coindBut coinduction
          minusBut <- getButton "minusBut"
          setCmdGtk minusBut $ incrEntry False
          plusBut <- getButton "plusBut"
          setCmdGtk plusBut $ incrEntry True
          paintBut <- getButton "paintBut"
          setCmdGtk paintBut showPicts
          downBut <- getButton "downBut"
          setCmdGtk downBut parseTree
          upBut <- getButton "upBut"
          setCmdGtk upBut parseText
          clearS <- getButton "clearS"
          setCmdGtk clearS redrawTree
          clearT <- getButton "clearT"
          setCmdGtk clearT $ do clearText; writeIORef numberedExpsRef ([],True)
          saveDBut <- getButton "saveDBut"
          setCmdGtk saveDBut saveGraphD
          dirBut <- getButton "dirBut"
          setCmdGtk dirBut $ setPicDir False
          
          axsMenu <- getMenu "axsMenu"
          mkBut axsMenu "show axioms" $ showAxioms True
          mkBut axsMenu ".. for symbols (x)" showAxiomsFor
          mkBut axsMenu (".. in " ++ other) $ showAxioms False
          subMenu <- mkSub axsMenu "add"
          createSub 0 subMenu
          mkBut axsMenu "combine for symbol" $ compressAxioms True
          mkBut axsMenu ".. in entry field" compressClauses
          mkBut axsMenu "invert for symbol" $ compressAxioms False
          mkBut axsMenu "negate for symbols (n)" negateAxioms
          mkBut axsMenu "Kleene axioms for symbols" kleeneAxioms
          mkBut axsMenu "remove in entry field" $ removeClauses 0
          mkBut axsMenu ".. for symbols" removeAxiomsFor
          
          fontDescriptionFromString initialFont >>= writeIORef fontRef
          fontBut <- getObject castToFontButton "fontBut"
          fontBut `gtkSet` [fontButtonUseSize  := False,
                            fontButtonFontName := initialFont]
          fontBut `onFontSet` do
              fd <- (fontBut `gtkGet` fontButtonFontName :: IO String)
                                  >>= fontDescriptionFromString
              setFont fd
          Just size <- readIORef fontRef >>= fontDescriptionGetSize
          fontSize `gtkSet` [rangeValue := size]
          fontSize `on` valueChanged $ setFontSize
          fontSize `on` buttonReleaseEvent $ do
              button <- eventButton
              when (button == LeftButton) $ lift drawNewCurr
              return False
              
          graphMenu <- getMenu "graphMenu"
          mkBut graphMenu "expand" $ expandTree False
          mkBut graphMenu "expand one" $ expandTree True
          mkBut graphMenu "split cycles" $ removeEdges True
          mkBut graphMenu "more tree arcs" $ removeEdges False
          mkBut graphMenu "compose pointers" composePointers
          mkBut graphMenu "collapse variables" collapseVarsCom
          mkBut graphMenu "collapse -->" $ transformGraph 3
          mkBut graphMenu "collapse level --> " $ collapseStep True
          mkBut graphMenu "reset level" resetLevel
          mkBut graphMenu "collapse <--" $ transformGraph 4
          mkBut graphMenu "collapse level <-- " $ collapseStep False
          mkBut graphMenu "remove copies" removeCopies
          mkBut graphMenu "graph (with new root)" $ transformGraph 0
          subMenu <- mkSub graphMenu "  of index transitions"
          kripkeButs1 subMenu [0..4]
          subMenu <- mkSub graphMenu "  of state transitions"
          kripkeButs1 subMenu [5..9]
          subMenu <- mkSub graphMenu "  of atom transitions"
          mkButs subMenu ["here","in painter","in " ++ other]
                         $ map showKripke [10..12]
          mkBut graphMenu "build iterative equations" $ transformGraph 1
          but <- mkBut graphMenu "connect equations" $ modifyEqs 0
          writeIORef eqsButRef but
          
          relMenu <- getMenu "relMenu"
          -- relBut <- win.menuButton [Text "relations", font12]
          -- relMenu <- relBut.menu []
          subMenu <- mkSub relMenu "Boolean matrix of"
          kripkeButs2 subMenu ((initCanvas >>). showMatrix) [0..4]
          subMenu <- mkSub relMenu "list matrix of"
          kripkeButs2 subMenu ((initCanvas >>). showMatrix) [5..9]
          subMenu <- mkSub relMenu "binary relation of"
          kripkeButs2 subMenu showRelation [0..4]
          subMenu <- mkSub relMenu "ternary relation of"
          kripkeButs2 subMenu showRelation [5..9]
          
          treeMenu <- getMenu "treeMenu"
          subMenu <- mkSub treeMenu "call enumerator"
          mapM_ (mkButF subMenu callEnum) enumerators
          mkBut treeMenu "remove other trees" removeOthers
          mkBut treeMenu "show changed" showChanged
          mkBut treeMenu "show proof" $ showProof True
          mkBut treeMenu (".. in " ++ other) $ showProof False
          mkBut treeMenu "save proof to file (s)" saveProof
          mkBut treeMenu "show proof term" showProofTerm
          mkBut treeMenu "check proof term from file" $ checkProofF False
          mkBut treeMenu ".. in painter" $ checkProofF True
          mkBut treeMenu ".. from text field" $ checkProofT False
          mkBut treeMenu ".. in painter" $ checkProofT True
          mkBut treeMenu "create induction hypotheses" createIndHyp
          mkBut treeMenu ("load text from file to " ++ other) $ getFileAnd
                                                              $ loadText False
          nodesMenu <- getMenu "nodesMenu"
          mkBut nodesMenu "label roots with entry (l)" replaceNodes
          mkBut nodesMenu "reference" refNodes
          mkBut nodesMenu "dereference" derefNodes
          mkBut nodesMenu "greatest lower bound" showGlb
          mkBut nodesMenu "predecessors" showPreds
          mkBut nodesMenu "successors" showSucs
          mkBut nodesMenu "constructors" $ showSyms constrPositions
          mkBut nodesMenu "variables" $ showSyms varPositions
          mkBut nodesMenu "free variables" $ showSyms freePositions
          mkBut nodesMenu "polarities" showPolarities
          mkBut nodesMenu "positions" showPositions
          mkBut nodesMenu "fixpositions" showFixPositions
          mkBut nodesMenu "level numbers" $ showNumbers 1
          mkBut nodesMenu "preorder numbers" $ showNumbers 2
          mkBut nodesMenu "heap numbers" $ showNumbers 3
          mkBut nodesMenu "hill numbers" $ showNumbers 4
          mkBut nodesMenu "coordinates" showCoords
          mkBut nodesMenu "cycle targets" showCycleTargets
          
          interpreterMenu <- getMenu "interpreterMenu"
          mapM_ (mkButF interpreterMenu setInterpreter) interpreters

          sigMenu <- getMenu "sigMenu"
          but <- mkBut sigMenu (refuteMsg False) switchRefute
          writeIORef refuteButRef but
          but <- mkBut sigMenu (safeMsg True) switchSafe
          writeIORef safeButRef but
          mkBut sigMenu "admit all simplifications" $ setAdmitted' True []
          mkBut sigMenu ".. except for symbols" $ setAdmitted True
          mkBut sigMenu ".. for symbols" $ setAdmitted False
          mkBut sigMenu "collapse after simplify" setCollapse
          mkBut sigMenu "show sig" showSig
          mkBut sigMenu "show map" showSigMap
          mkBut sigMenu "apply map" applySigMap
          mkBut sigMenu "save map to file" $ getFileAnd saveSigMap
          addMapMenu <- mkSub sigMenu "add map"
          mkBut addMapMenu "STACK2IMPL" $ addSigMap "STACK2IMPL"
          mkBut addMapMenu "from text field" addSigMapT
          mkBut addMapMenu "from file" $ getFileAnd addSigMap
          mkBut addMapMenu "remove map" removeSigMap

          streeMenu <- getMenu "streeMenu"
          mkBut streeMenu "specialize" specialize
          mkBut streeMenu "generalize" generalize
          mkBut streeMenu "instantiate" instantiate
          mkBut streeMenu "build unifier" buildUnifier
          mkBut streeMenu ("unify with tree of " ++ other) unifyOther
          mkBut streeMenu ("replace by tree of " ++ other) replaceOther
          mkBut streeMenu "replace by other sides of in/equations"
                  replaceSubtrees
          mkBut streeMenu "move down quantifier" moveQuant
          mkBut streeMenu "move up quantifiers" shiftQuants
          mkBut streeMenu "distribute (d)" distribute
          mkBut streeMenu "decompose atom" decomposeAtom
          mkBut streeMenu "use transitivity" applyTransitivity
          subMenu <- mkSub streeMenu "apply clause"
          mkBut subMenu "Left to right (Left)" $ applyClause False False False
          mkBut subMenu ".. and save redex" $ applyClause False False True
          mkBut subMenu ".. lazily" $ applyClause True False False
          mkBut subMenu ".. and save redex" $ applyClause True False True
          mkBut subMenu "Right to left (Right)" $ applyClause False True False
          mkBut subMenu ".. and save redex" $ applyClause False True True
          mkBut subMenu ".. lazily" $ applyClause True True False
          mkBut subMenu ".. and save redex" $ applyClause True True True
          mkBut streeMenu "create Hoare invariant" $ createInvariant True
          mkBut streeMenu "create subgoal invariant" $ createInvariant False
          mkBut streeMenu "flatten (co-)Horn clause" flattenImpl
          mkBut streeMenu "shift pattern to rhs" shiftPattern
          mkBut streeMenu "shift subformulas" shiftSubs
          mkBut streeMenu "stretch premise" $ stretch False
          mkBut streeMenu "stretch conclusion" $ stretch True
          mkBut streeMenu "subsume" subsumeSubtrees
          mkBut streeMenu "evaluate" evaluateTrees
          mkBut streeMenu "copy (c)" copySubtrees
          mkBut streeMenu "remove (r)" removeSubtrees
          mkBut streeMenu "remove node (o)" removeNode
          mkBut streeMenu "reverse (v)" reverseSubtrees
          mkBut streeMenu "permute subtrees (m)" permuteSubtrees
          mkBut streeMenu "insert/replace by text (i)" replaceText
          mkBut streeMenu "random labels (L)" randomLabels
          mkBut streeMenu "random tree (T)" randomTree
          mkBut streeMenu "remove path (p)" removePath

          subsMenu <- getMenu "subsMenu"
          mkBut subsMenu "add from text field" addSubst
          mkBut subsMenu "apply" applySubst
          mkBut subsMenu "rename" renameVar
          mkBut subsMenu "remove" removeSubst
          mkBut subsMenu "show" $ showSubst 0
          mkBut subsMenu (".. in text field of " ++ other) $ showSubst 1
          mkBut subsMenu (".. on canvas of " ++ other) $ showSubst 2
          mkBut subsMenu ".. solutions" showSolutions

          specMenu <- getMenu "specMenu"
          mkBut specMenu "re-add" reAddSpec
          mkBut specMenu "remove" $ do removeSpec
                                       labGreen $ iniSpec ++ iniSigMap
          mkBut specMenu "set pic directory (t)" $ setPicDir False
          mkBut specMenu "build Kripke model" $ buildKripke 2
          mkBut specMenu ".. from current graph" $ buildKripke 3
          mkBut specMenu ".. from regular expression" $ buildKripke 4
          mkBut specMenu ".. cycle-free" $ buildKripke 0
          mkBut specMenu ".. pointer-free" $ buildKripke 1
          mkBut specMenu "make deterministic" detKripke
          mkBut specMenu "state equivalence" stateEquiv
          mkBut specMenu "minimize" minimize
          mkBut specMenu "regular expression" buildRegExp
          mkBut specMenu "distribute products over sums" $ reduceRegExp 0
          mkBut specMenu "reduce left factors" $ reduceRegExp 1
          mkBut specMenu "reduce right factors" $ reduceRegExp 2
          mkBut specMenu "regular equations" $ modifyEqs 1
          mkBut specMenu "substitute variables" $ modifyEqs 2
          mkBut specMenu "solve regular equation" $ modifyEqs 3
          mkBut specMenu "save to file" $ getFileAnd saveSpec
          subMenu <- mkSub specMenu "load text"
          createSpecMenu False subMenu
          subMenu <- mkSub specMenu "add"
          createSpecMenu True subMenu

          thsMenu <- getMenu "thsMenu"
          mkBut thsMenu "show theorems" $ showTheorems True
          mkBut thsMenu ".. for symbols" showTheoremsFor
          mkBut thsMenu (".. in " ++ other) $ showTheorems False
          mkBut thsMenu "remove theorems" removeTheorems
          mkBut thsMenu ".. in entry field" $ removeClauses 1
          subMenu <- mkSub thsMenu "add theorems"
          createSub 1 subMenu
          mkBut thsMenu "show terms" showTerms
          mkBut thsMenu "show conjects" showConjects
          mkBut thsMenu ".. in entry field" $ removeClauses 3
          mkBut thsMenu "remove conjects" removeConjects
          mkBut thsMenu ".. in entry field" $ removeClauses 2
          subMenu <- mkSub thsMenu "add conjects"
          createSub 2 subMenu

          treeSize `on` valueChanged $ drawNewCurr
          
          horBut <- getObject castToScale "horBut"
          on horBut valueChanged $ do val <- gtkGet horBut rangeValue
                                      blowHor $ truncate val
                                      drawNewCurr
          
          verBut <- getObject castToScale "verBut"
          on verBut valueChanged $ do val <- gtkGet verBut rangeValue
                                      blowVer $ truncate val
                                      drawShrinked            

          -- scroll support for canvas
          containerAdd scrollCanv $ getDrawingArea canv
          changeCanvasBackground white

          on win deleteEvent $ lift mainQuit >> return False
          widgetShowAll win

-- end of buildSolve

-- The other methods of solver are listed in alphabetical order:

        addAxioms :: TermS -> String -> Action
        addAxioms t file = do
          sig <- getSignature
          let axs = if isConjunct t then subterms t else [t]
              cls = filter (not . (isAxiom sig ||| isSimpl)) axs
          if null cls then
               do writeIORef solPositionsRef []
                  modifyIORef simplRulesRef
                     $ \simplRules -> simplRules `join` srules ["==","<==>"] axs
                  modifyIORef axiomsRef $ \axioms -> axioms `joinTerms` axs
                  labGreen $ newCls "axioms" file
          else do enterFormulas cls
                  labRed $ "The clauses in " ++ tfield ++ " are not axioms."
                  
        -- used by addClauses and addSpec

        addCongAxioms :: Action
        addCongAxioms = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               str <- ent `gtkGet` entryText
               sig <- getSignature
               trees <- readIORef treesRef
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               let pars = words str
                   b par = par `elem` words "refl symm tran" ||
                           (isConstruct sig ||| isDefunct sig) (init par) &&
                           just (parse digit [last par])
                   t = trees!!curr
                   p = emptyOrLast treeposs
                   pars' = filter b pars
                   axs = case getSubterm t p of
                              F equiv [_,_] -> congAxs equiv pars'
                              _ -> []
               if null pars'
                  then labRed "Enter axiom names into the entry field."
               else if null axs then
                       labRed "Select a binary relation in the current tree."
                    else addCongAxioms' axs

        addCongAxioms' axs = do
          modifyIORef axiomsRef $ \axioms -> joinTerms axioms axs
          enterFormulas axs
          extendPT $ AddAxioms axs
          setProof True False ("ADDC" ++ showFactors axs) [] $
                   newCls "axioms" tfield

        addClauses :: Int -> FilePath -> Action
        addClauses cltype file = do
          str <- if text then getTextHere else lookupLibs file
          let str' = removeComment 0 str
              file' = if text then tfield else file
          sig <- getSignature
          case cltype of 0 -> case parseE (implication sig) str' of
                                   Correct t -> do addAxioms t file'; done
                                   p -> incorrect p str' $ illformed "formula"
                         1 -> case parseE (implication sig) str' of
                                   Correct t -> do addTheorems t file'; done
                                   p -> incorrect p str' $ illformed "formula"
                         _ -> parseConjects sig file' str'
          where text = null file

        -- | Called by menu items /STACK2IMPL/ and /from file/ from menu
        -- /signature/.
        addSigMap :: FilePath -> IO ()
        addSigMap file = do
            str <- lookupLibs file
            parseSigMap file $ removeComment 0 str

        -- Called by menu items /from text field/ and /from file/ from menu
        -- /signature/.
        addSigMapT :: Action
        addSigMapT = do
            str <- getTextHere
            parseSigMap tfield str

        -- Adds a specification from file. Used by 'addSpecWithBase',
        -- 'parseSig'
        addSpec :: Bool -> FilePath -> Action
        addSpec b file = do
          checking <- readIORef checkingRef
          when (not checking) $ do
              when b $ modifyIORef specfilesRef $ \specfiles -> file:specfiles
              str <- get
              if null str then labRed $ file ++ " is not a file name."
              else do
                  let (sig,axs,ths,conjs,ts) = splitSpec $ removeComment 0 str
                      act1 = do
                          sig <- getSignature
                          if onlySpace axs then act2 sig
                          else case parseE (implication sig) axs of
                               Correct t -> do
                                 addAxioms t file'
                                 delay $ act2 sig
                               p -> incorrect p axs $ illformed "formula"
                      act2 sig =
                          if onlySpace ths then act3 sig
                          else case parseE (implication sig) ths of
                              Correct t -> do
                                  addTheorems t file'
                                  delay $ act3 sig
                              p -> incorrect p ths $ illformed "formula"
                      act3 sig =
                          if onlySpace conjs then act4 sig
                          else do
                              parseConjects sig file' conjs
                              delay $ act4 sig
                      act4 sig =
                          if onlySpace ts then delay $ done
                          else parseTerms sig file' ts
                  if onlySpace sig then act1
                  else do
                       (ps,cps,cs,ds,fs,hs) <- readIORef symbolsRef
                       let syms = ps++cps++cs++ds++fs++map fst hs
                       case parseE (signature ([],ps,cps,cs,ds,fs,hs)) sig of
                            Correct (specs,ps,cps,cs,ds,fs,hs)
                              -> do
                                writeIORef symbolsRef (ps,cps,cs,ds,fs,hs)
                                let finish = do
                                      writeIORef varCounterRef $ iniVC syms
                                      labGreen $ newSig file'
                                      delay act1
                                specfiles <- readIORef specfilesRef
                                mapM_ (addSpec False) $ specs `minus` specfiles
                                delay finish
                            Partial (_,ps,cps,cs,ds,fs,hs) rest
                              -> do
                                 enterText $ showSignature (ps,cps,cs,ds,fs,hs)
                                           $ check rest
                                 labRed $ illformed "signature"
                            _ -> do
                                 enterText sig
                                 labRed $ illformed "signature"
         where (file',get) = if null file then (tfield,getTextHere)
                                          else (file,lookupLibs file)
               onlySpace = all (`elem` " \t\n")
        
        -- Adds base specification first, then loads specification from
        -- given file by calling 'addSpec'. Used by multiple entries from
        -- the "specification" menu. Pressing "Reteurn" in entry field is
        -- equal to menu item "specification"->"add"->"from file (Return)".
        addSpecWithBase :: FilePath -> Action
        addSpecWithBase spec = do
          addSpec True "base"
          unless (spec == "base") $ addSpec True spec
        
        -- Adds substitutions. Called by menu item
        -- /add from text field/ from menu /substitution/.
        addSubst :: Action
        addSubst = do
            str <- getTextHere
            sig <- getSignature
            case parseE (conjunct sig) str of
                Correct t ->
                    if hasPos t then labRed posInSubst
                    else case eqsToSubst $ mkFactors t of
                        Just (f,dom) -> do
                            (g,xs) <- readIORef substitutionRef
                            setSubst (g `andThen` f, xs `join` dom)
                            labGreen extendedSubst
                        _ -> labRed $ illformed "substitution"
                p -> incorrect p str $ illformed "substitution"
        
        addText :: [String] -> Action
        addText ls = do
            buffer <- tedit `gtkGet` textViewBuffer
            end <- textBufferGetEndIter buffer
            textBufferInsert buffer end text
         where addNo :: Int -> [String] -> [String]
               addNo _ []               = []
               addNo n ([]:ls)          = []:addNo n ls
               -- addNo 0 ((' ':l):ls)     = (" 0> " ++ l):addNo 1 ls
               -- addNo n ((' ':l):ls)     = ("    " ++ l):addNo n ls
               -- addNo n (('.':l):ls)     = ("   ." ++ l):addNo n ls
               addNo n (l:ls) | n < 10  = (' ':' ':show n ++ '>':l):f n
                              | n < 100 = (' ':show n ++ '>':l):f n
                              | True    = (show n ++ '>':l):f n
                                          where f n = addNo (n+1) ls
               split []                  = []
               split l | length l <= 85 = [l]
                       | True           = take 85 l:split ('.':drop 85 l)
               text = unlines $ addNo 0 $ concatMap split ls
        
        -- used by enterFormulas, enterTerms, enterText and enterRef

        -- | Add theorems from file. Used by 'addClauses', 'addSpec'
        -- and /from SolverN/ menu items created by 'createClsMenu'.
        
        addTheorems :: TermS -> FilePath -> Action
        addTheorems t file = do
            modifyIORef theoremsRef $ \theorems ->
                theorems `join` if isConjunct t then subterms t else [t]
            labGreen $ newCls "theorems" file
        
        -- | Called by menu item /apply clause/ from menu /transform selection/.
        
        applyClause :: Bool -> Bool -> Bool -> Action
        applyClause lazy invert saveRedex = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                str <- ent `gtkGet` entryText
                numberedExps <- readIORef numberedExpsRef
                let (exps,b) = numberedExps
                case parse nat str of
                    k@(Just n) | n < length exps
                      -> if b then if lazy then stretchAndApply k $ exps!!n
                                           else finish k $ exps!!n
                        else labMag $ enterTfield "formulas"
                    _ -> do
                        str <- getTextHere
                        sig <- getSignature
                        case parseE (implication sig) str of
                              Correct cl | lazy -> stretchAndApply Nothing cl
                                         | True -> finish Nothing cl
                              p -> incorrect p str $ illformed "formula"
          where stretchAndApply k cl = do
                 varCounter <- readIORef varCounterRef
                 let vcz = varCounter "z"
                 case preStretch False (const True) cl of
                      Just (_,varps) -> do
                                        setZcounter n
                                        finish k clp
                                        where (clp,n) = stretchPrem vcz varps cl
                      _ -> case preStretch True (const True) cl of
                                Just (_,varps) -> do
                                                  setZcounter n
                                                  finish k clc
                                        where (clc,n) = stretchConc vcz varps cl
                                _ -> notStretchable "The left-hand side"
                finish k cl = applyTheorem saveRedex k
                                        $ if invert then invertClause cl else cl

        -- | Used by 'applyTheorem'.
        applyDisCon :: Maybe Int -> TermS -> [TermS] -> TermS -> [[Int]] -> Sig
                    -> String -> Action
        applyDisCon k (F "|" ts) redices t ps sig msg =
            applyDisCon k (F "<===" [F "|" ts,mkTrue]) redices t ps sig msg
        applyDisCon k (F "&" ts) redices t ps sig msg =
            applyDisCon k (F "<===" [F "&" ts,mkTrue]) redices t ps sig msg
        applyDisCon k (F "<===" [F "|" ts,prem]) redices t ps sig msg = do
          let pred = glbPos ps
              u = getSubterm t pred
              qs = map (restPos pred) ps
          if all noQuants ts && polarity True t pred && isDisjunct u &&
             all (isProp sig ||| isAnyQ) (sucTerms u qs)
             then finishDisCon k False True ts prem redices t ps pred qs sig msg
          else labRed $ noAppT k
        applyDisCon k (F "<===" [F "&" ts,prem]) redices t ps sig msg = do
          let pred = glbPos ps
              u = getSubterm t pred
              qs = map (restPos pred) ps
          if all noQuants ts && polarity True t pred && isConjunct u &&
             all (isProp sig ||| isAllQ) (sucTerms u qs)
            then finishDisCon k False False ts prem redices t ps pred qs sig msg
          else labRed $ noAppT k
        applyDisCon k (F "===>" [F "&" ts,conc]) redices t ps sig msg = do
          let pred = glbPos ps
              u = getSubterm t pred
              qs = map (restPos pred) ps
          if all noQuants ts && polarity False t pred && isConjunct u &&
             all (isProp sig ||| isAllQ) (sucTerms u qs)
             then finishDisCon k True True ts conc redices t ps pred qs sig msg
          else labRed $ noAppT k
        applyDisCon k (F "===>" [F "|" ts,conc]) redices t ps sig msg = do
          let pred = glbPos ps
              u = getSubterm t pred
              qs = map (restPos pred) ps
          if all noQuants ts && polarity False t pred && isDisjunct u &&
             all (isProp sig ||| isAnyQ) (sucTerms u qs)
             then finishDisCon k True False ts conc redices t ps pred qs sig msg
          else labRed $ noAppT k

        -- Used by 'applyCoinduction' and 'applyInduction'.
        applyInd :: String -> [TermS] -> [String] -> [TermS]
                 -> TermS -> [Int] -> [TermS] -> Action
        applyInd rule conjs indsyms axs t p rest = do
          sig <- getSignature
          varCounter <- readIORef varCounterRef
          symbols <- readIORef symbolsRef
          (nps,ncps) <- readIORef newPredsRef
          let syms = if rule == "COINDUCTION" then nps else ncps
              vc1 = decrVC varCounter syms
              xs = indsyms `join` map getPrevious syms
              (f,vc2) = renaming vc1 xs
           -- g replaces an equation x(t,..)=u with x in xs by the logical atom
           -- f(x)(t,..,u) and other symbols x of t by f(x)
              g eq@(F "=" [F x ts,u])
                         = if x `elem` xs then F (f x) $ ts++[u] else eq
              g (F x ts) = F (f x) $ map g ts
              g t        = t
              axsWithGuard = map mergeWithGuard axs
              mkAx (F x [t,u]) = F x [g t,u]
              mkAx t           = leaf "applyInd"
              (ps,cps,cs,ds,fs,hs) = symbols
              (ps',cps') = if rule == "COINDUCTION" then (map f xs,[])
                                                    else ([],map f xs)
              newAxs = concatMap (splitHorn . decrSuffixes sig . mkAx) conjs
          writeIORef symbolsRef (ps `join` ps',cps `join` cps',cs,ds,fs,hs)
          writeIORef newPredsRef (nps `join` ps',ncps `join` cps')
          modifyIORef newAxiomsRef
            $ \newAxioms -> joinTermsS sig newAxioms newAxs
          modifyIORef axiomsRef $ \axioms -> joinTermsS sig axioms newAxs
          newAxioms <- readIORef newAxiomsRef
          enterFormulas newAxioms
          sig <- getSignature
          let (cls,vc3) = applyToHead sig newAxs (map g axsWithGuard) vc2
              conj = mkConjunct cls
              xs = [x | x <- frees sig conj, noExcl x]
              u = replace t p $ mkConjunct $ mkAll xs conj:rest
              msg = "ADDI" ++ showFactors newAxs ++ "\n\nApplying " ++ rule ++
                    " wrt\n\n" ++ showFactors axsWithGuard ++ "\n\n"
          writeIORef varCounterRef vc3
          extendPT $ if rule == "COINDUCTION" then Coinduction else Induction
          maybeSimplify sig u
          makeTrees sig
          setTreesFrame []
          setProof True True msg [p] $ indApplied rule
        
        applySigMap :: Action          -- called by button signature > apply map
        applySigMap = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                signatureMap <- readIORef signatureMapRef
                curr <- readIORef currRef
                formula <- readIORef formulaRef
                solve <- readIORef solveRef
                other <- getSolver solve
                sig <- getSignature
                sig' <- getSignatureR solve
                case applySignatureMap sig sig' (fst signatureMap) $ trees!!curr
                     of Just t -> do bigWinR solve; enterTreeR solve formula t
                        _ -> labRed $ sigMapError other
                
        applySubst :: Action             -- called by substitution > apply
        applySubst = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                substitution <- readIORef substitutionRef
                let t = trees!!curr
                    (g,dom) = substitution
                    f t p = replace t p $ getSubterm t p>>>g
                    ts = substToEqs g dom
                    ps = emptyOrAll treeposs
                    msg = "The substitution\n\n" ++ showFactors ts ++ "\n\n"
                writeIORef treesRef $ updList trees curr $ foldl f t ps
                extendPT ApplySubst
                setProof False False msg ps subsAppliedToAll
                clearAndDraw
        
        applySubstTo :: String -> Action                -- used by setSubst
        applySubstTo x = do
            trees <- readIORef treesRef
            substitution <- readIORef substitutionRef
            if null trees then labBlue start
                          else applySubstTo' x $ fst substitution x
       
        applySubstTo' :: String -> TermS -> Action      -- used by applySubstTo
        applySubstTo' x v = do
            trees <- readIORef treesRef
            curr <- readIORef currRef
            treeposs <- readIORef treepossRef

            let t = trees!!curr
                p = emptyOrLast treeposs
                msg = "SUBSTITUTING " ++ showTerm0 v ++ " for " ++ x
            sig <- getSignature
            case isAny t x p of
             Just q | polarity True t q -> finish (q++[0]) t sig msg True
             _ -> case isAll t x p of
                   Just q | polarity False t q -> finish (q++[0]) t sig msg True
                   _ -> finish p t sig msg False
            where finish p t sig msg b = 
                                do updateCurr t'
                                   extendPT $ ApplySubstTo x v
                                   drawThis "green" t' ps
                                   setProof b False msg [p] $ subsAppliedTo x
                                   substitution <- readIORef substitutionRef
                                   let (f,dom) = substitution
                                   setSubst (upd f x $ V x, dom `minus1` x)
                                   where t' = replace t p $ u>>>for v x
                                         u = getSubterm t p
                                         ps = map (p++) $ freeXPositions sig u x
 
        applyTheorem :: Bool -> Maybe Int -> TermS -> Action
        applyTheorem saveRedex k th = do
          sig <- getSignature
          extendPT $ Theorem saveRedex th
          trees <- readIORef treesRef
          curr <- readIORef currRef
          treeposs <- readIORef treepossRef
          varCounter <- readIORef varCounterRef
          let t = trees!!curr
              ps = emptyOrAll treeposs
              redices = map (getSubterm t) ps
              n = length ps
              ([th'],vc) = renameApply sig t varCounter
                                     [if saveRedex then copyRedex th else th]
              f t (redex:rest) (p:ps) qs = case applySingle th' redex t p sig of
                                                Just t -> f t rest ps (p:qs)
                                                _ -> f t rest ps qs
              f _ _ _ [] = labRed $ notUnifiable k
              f t _ _ qs = do
                           maybeSimplify sig t
                           makeTrees sig
                           setTreesFrame []
                           setProof True True (applied True str) qs
                             $ thApplied k
              str = showTree False $ case th of
                  F "===>" [F "True" [],th] -> th
                  F "<===" [F "False" [],th] -> mkNot sig th
                  _ -> th
          when (nothing k) $ enterText str
          if isTaut th then do
              writeIORef varCounterRef vc
              f t redices ps []
          else
              if n > 1 && isDisCon th && n == noOfComps th
              then do
                  writeIORef varCounterRef vc
                  applyDisCon k th' redices t ps sig $ applied True str
              else if saveRedex || isSimpl th || all (correctPolarity th t) ps
                       then -- if isAxiom sig th then
                            -- narrowOrRewritePar t sig k [th] saveRedex ps done
                            if isTheorem th
                               then do
                                    writeIORef varCounterRef vc
                                    f t redices ps []
                            else labRed $ noTheorem k
                    else labRed $ noAppT k
                    
        -- used by specialize,applyClause
 
        applyTransitivity :: Action       -- called by 
        applyTransitivity = do            -- button selection > use transitivity
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do curr <- readIORef currRef
                  treeposs <- readIORef treepossRef
                  let t = trees!!curr
                      ps = emptyOrAll treeposs
                      redices = map (getSubterm1 t) ps
                  case redices of
                   F x [l,r]:_ 
                     -> do varCounter <- readIORef varCounterRef
                           let p:qs = ps
                               vcz = varCounter "z"
                               z = 'z':show vcz
                               vz = V z
                               n = vcz+1
                           if isRel x && null qs && polarity True t p then
                              do let u = anyConj [z] [F x [l,vz],F x [vz,r]]
                                 updateCurr $ replace1 t p u
                                 setZcounter n
                           else do let z' = 'z':show n
                                       vz' = V z'
                                       u | qs == [p ++ [0]] 
                                                = anyConj [z] [mkEq l vz,
                                                               F x [vz,r]]
                                         | qs == [p ++ [1]]
                                                = anyConj [z] [F x [l,vz],
                                                               mkEq vz r]
                                         | True = anyConj [z,z'] [mkEq l vz,
                                                                  F x [vz,vz'],
                                                                  mkEq vz' r]
                                   updateCurr $ replace1 t p u
                                   setZcounter $ n+1
                           finish ps
                   _ -> if any null ps then labMag "Select proper subtrees!"
                        else 
                         do let qs = map init ps
                                q = head qs
                                u = getSubterm t q
                                vs = removeTerms (subterms u) redices
                            if allEqual qs && isConjunct u then
                               case transClosure redices of
                                  Just v -> if polarity False t q then 
                                               do updateCurr $ replace1 t q 
                                                             $ mkConjunct $ v:vs
                                                  finish ps
                                            else labRed $ noApp "Transitivity"
                                  _ -> labMag "Select composable atoms!"
                            else labRed $ noApp "Transitivity"
            where anyConj xs = mkAny xs . F "&"
                  finish ps = do extendPT ApplyTransitivity
                                 setProof True False "TRANSITIVITY" ps
                                          transitivityApplied
                                 clearAndDraw

        backProof :: Action             -- called by button "<---" or key "Up" 
        backProof = do                  -- while cursor in label field
            restore <- readIORef restoreRef
            if restore then do
                oldTreeposs <- readIORef oldTreepossRef
                writeIORef treepossRef oldTreeposs
                writeIORef restoreRef False
                drawCurr
            else do
                checking <- readIORef checkingRef
                if checking then checkBackward
                else do
                    proofPtr <- readIORef proofPtrRef
                    proofTPtr <- readIORef proofTPtrRef
                    proofTerm <- readIORef proofTermRef
                    if proofPtr < 1 then labMag emptyProof
                    else do
                        proof <- readIORef proofRef
                        let ps = peTreePoss (proof!!proofPtr)
                        modifyIORef proofPtrRef pred
                        proofPtr <- readIORef proofPtrRef
                        changeState proofPtr ps
                    let n = searchback deriveStep $ take proofTPtr proofTerm
                    writeIORef proofTPtrRef $ Haskell.fromMaybe 0 n
                    
        backWin = windowIconify win   
        
        bigWin = windowDeiconify win >> windowPresent win
        
        blowHor :: Int -> Action                        -- used by slider horBut
        blowHor i = modifyIORef spreadRef $ \spread -> (i,snd spread)
        
        blowVer :: Int -> Action                        -- used by slider verBut
        blowVer i = modifyIORef spreadRef $ \spread -> (fst spread,i)
 
        buildKripke :: Int -> Action
        buildKripke 3 = do                              -- from current graph
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               sig <- getSignature
               curr <- readIORef currRef
               axioms <- readIORef axiomsRef
               let labels = getFrom sig axioms "labels"
                   t = trees!!curr
               case graphToRules sig (map showTerm0 labels) t of
                 Just (states,atoms,rules) -> do
                      writeIORef kripkeRef (states,labels,atoms,[],[],[],[])
                      iniStates <- readIORef iniStatesRef
                      writeIORef iniStatesRef [leaf "root"]
                      changeSimpl "states" $ mkList states
                      changeSimpl "labels" $ mkList labels
                      changeSimpl "atoms"  $ mkList atoms
                      writeIORef transRulesRef rules
                      sig <- getSignature
                      let (_,rs,rsL) = buildTrans sig states
                          (_,rs',rsL') = buildTrans sig atoms
                          tr = pairsToInts states rs states
                          trL = tripsToInts states labels rsL states
                          va = pairsToInts states rs' atoms
                          vaL = tripsToInts states labels rsL' atoms
                          [l,m,n] = map length [states,labels,atoms]
                      writeIORef kripkeRef (states,labels,atoms,tr,trL,va,vaL)
                      setProof True False kripkeMsg [] $ kripkeBuilt 3 0 l m n
                 _ -> labMag "Enter a graph that shows (labelled) transitions!"

        buildKripke 4 = do                            -- from regular expression
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               sig <- getSignature
               trees <- readIORef treesRef
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               let t = trees!!curr
                   p = emptyOrLast treeposs
               case parseRE sig $ getSubterm t p of
                    Just (e,labs)
                      -> do
                         let (sts,(trans,transL)) = regToAuto e
                             sts' = map mkConst sts
                             final = getInd sts' $ mkConst 1
                             labels = map leaf labs
                             atoms = [leaf "final"]
                             tr = funToList sts sts trans
                             trL = funLToList sts labs sts transL
                         writeIORef iniStatesRef [mkConst 0]
                         changeSimpl "states" $ mkList sts'
                         changeSimpl "labels" $ mkList labels
                         changeSimpl "atoms"  $ mkList atoms
                         writeIORef kripkeRef 
                                    (sts',labels,atoms,tr,trL,[[final]],[])
                         setProof True False kripkeMsg [] $
                                  kripkeBuilt 4 0 (length sts) (length labs) 1
                    _ -> labMag "Select a regular expression!"

        buildKripke mode = do                       -- from transition axioms
                                                    -- mode = 1 ==> cycle-free
                                                    -- mode = 2 ==> pointer-free
                                                    -- mode = 3 ==> full
          enterTree False $ V "building Kripke model ..."
          str <- ent `gtkGet` entryText
          writeIORef noProcsRef
            $ case parse nat str of Just n | n > 2 -> n; _ -> 2
          noProcs <- readIORef noProcsRef
          changeSimpl "noProcs" $ mkConst noProcs
          sig <- getSignature
          axioms <- readIORef axiomsRef
          let sts = getFrom sig axioms "states"
              labs = getFrom sig axioms "labels"
              ats = getFrom sig axioms "atoms"
          writeIORef kripkeRef (sts,labs,ats,[],[],[],[])
          writeIORef iniStatesRef sts
          changeSimpl "states" $ mkList sts
          changeSimpl "labels" $ mkList labs
          changeSimpl "atoms"  $ mkList ats
          axioms <- readIORef axiomsRef
          writeIORef transRulesRef $ srules ["->"] axioms
          sig <- getSignature
          let (sts,rs,rsL) = buildTransLoop sig mode
              tr  = pairsToInts sts rs sts
              trL = tripsToInts sts (labels sig) rsL sts
          changeSimpl "states" $ mkList sts
          writeIORef kripkeRef (sts,labels sig,atoms sig,tr,trL,[],[])
          delay $ buildKripkeValues mode
        
-- called when the menu item specification > build Kripke model > .. is selected

        buildKripkeValues mode = do
          sig <- getSignature
          let (sts,rs,rsL) = buildTrans sig $ atoms sig
              va = pairsToInts sts rs $ atoms sig
              vaL = tripsToInts sts (labels sig) rsL $ atoms sig
              [l,m,n] = map length [sts,labels sig,atoms sig]
          changeSimpl "states" $ mkList sts
          writeIORef kripkeRef 
                     (sts,labels sig,atoms sig,trans sig,transL sig,va,vaL)
          noProcs <- readIORef noProcsRef
          setProof True False kripkeMsg [] $ kripkeBuilt mode noProcs l m n
          enterTree False $ V "building Kripke model finished"
        
        buildRegExp = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               str <- ent `gtkGet` entryText
               sig <- getSignature
               let finish start = do
                      trees <- readIORef treesRef
                      curr <- readIORef currRef
                      writeIORef treesRef
                        $ updList trees curr $ showRE $ autoToReg sig start
                      extendPT BuildRE
                      setProof False False "BUILDING A REGULAR EXPRESSION" []
                                           regBuilt
                      clearAndDraw
                   parser = parse $ singleTerm sig
               case parser str of
                    Just start | start `elem` states sig -> finish start
                    _ -> do
                         trees <- readIORef treesRef
                         curr <- readIORef currRef
                         treeposs <- readIORef treepossRef
                         let start = label (trees!!curr) $ emptyOrLast treeposs
                         case parser $ takeWhile (/= ':') start of
                              Just start | start `elem` states sig
                                -> finish start
                              _ -> labRed "Enter or select an initial state!"
        
        -- | Called by menu item /build unifier/ from menu
        -- /transform selection/.
        buildUnifier :: Action
        buildUnifier = do
            treeposs <- readIORef treepossRef
            if length treeposs /= 2 || any null treeposs
            then labMag "Select two proper subtrees!"
            else do
                trees <- readIORef treesRef
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    [p,q] = treeposs
                    u = getSubterm t p
                    v = getSubterm t q
                unifyAct u v t t p q
        
        -- | Called by all menu items from /call enumerators/ sub menu of the
        -- tree menu.
        callEnum :: String -> Action
        callEnum obj = do
            writeIORef formulaRef False
            writeIORef joinedRef False
            writeIORef matchingRef 0
            matchBut `gtkSet` [ buttonLabel := "match" ]
            splitBut `gtkSet` [ buttonLabel := "join" ]
            setTreeposs $ Replace []
            setInterpreter obj
            sig <- getSignature
            let ts = case simplifyFix sig $ F "compl" [] of F "[]" us -> us
                                                            _ -> []
                compl = curry $ setToFun $ zipWith f (evens ts) $ odds ts
                        where f t u = (showTerm0 t,showTerm0 u)
            buildEnum enum obj $ if obj `elem` ["alignment","palindrome"]
                                 then compl else const2 False
        
        -- | Initialize the 'moveNode' action. Called if the right mouse
        -- button is clicked on a node inside the canvas.
        catchNode :: Pos -> Action
        catchNode (x, y) = do
            treeposs <- readIORef treepossRef

            if null treeposs then labMag "Select a target node!"
            else do
                ctree <- readIORef ctreeRef

                -- should be fine without: (x,y) <- adaptPos pt
                case getSubtree (get ctree) x y of
                    Just (p,cu) -> do
                        let z = root cu
                        if last treeposs <<= p then drawNode z cyan
                                               else drawNode z magenta
                        writeIORef nodeRef $ Just (z,p)
                        canv `gtkSet` [ canvasCursor := SbUpArrow ]
                    _ -> done
        
        -- | Initialize the 'moveSubtree' action. Called if the left mouse
        -- button is clicked on a node inside the canvas.
        catchSubtree :: Pos -> Action
        catchSubtree pt@(x, y) = do
            trees <- readIORef treesRef

            when (notnull trees) $ do
                Just ct <- readIORef ctreeRef
                treeposs <- readIORef treepossRef

                -- should be fine without: (x,y) <- adaptPos pt
                case getSubtree ct x y of
                    Just (p,cu)
                        | p `elem` treeposs -> do -- deselect subtree
                            setTreeposs $ Remove p
                            drawSubtrees
                        | True -> do -- select subtree
                            writeIORef isSubtreeRef $ Just False
                            setTreeposs $ Add [p]
                            writeIORef nodeRef $ Just (root cu,p)
                            writeIORef penposRef $ Just pt
                            writeIORef subtreeRef $ Just cu
                            writeIORef suptreeRef $ Just ct
                            canv `gtkSet` [ canvasCursor := Hand2 ]
                            drawSubtrees
                    _ -> when (notnull treeposs) $ do -- deselect last
                            setTreeposs $ Remove $ last treeposs
                            drawSubtrees
        
        -- | Initialize the 'moveTree' action. Called if the middle mouse button
        -- is clicked on a node inside the canvas.
        catchTree :: Pos -> Action
        catchTree pt@(x, y) = do
            trees <- readIORef treesRef

            when (notnull trees) $ do
                ctree <- readIORef ctreeRef
                treeposs <- readIORef treepossRef

                -- should be fine without: (x,y) <- adaptPos pt
                let Just ct = ctree
                case getSubtree ct x y of
                    Just (p,cu) | p `elem` treeposs -> do -- cut subtree
                        writeIORef isSubtreeRef $ Just True
                        let a = root cu
                        writeIORef nodeRef $ Just (a,p)
                        writeIORef penposRef $ Just pt
                        writeIORef subtreeRef $ Just cu
                        writeIORef suptreeRef $ Just $ replace0 ct p $ V a
                        canv `gtkSet` [ canvasCursor := Hand2 ]
                    _ -> do            -- move tree
                        writeIORef isSubtreeRef $ Just False
                        writeIORef penposRef $ Just pt
                        canv `gtkSet` [ canvasCursor := Crosshair ]
        
        changeCanvasBackground c@(RGB r g b) = do    -- Gtk only
            gtkSet canv [canvasBackground := c]
            widgetModifyBg scrollCanv StateNormal $ gtkColor (f r) (f g) (f b)
            where f n = fromIntegral $ n * 256
        
        -- | Used by 'releaseSubtree' and 'replaceText''.
        changeMode :: TermS -> Action
        changeMode t = do
            formula <- readIORef formulaRef

            sig <- getSignature
            let b = isFormula sig t
                str = if b then "formula" else "term"
            if b /= formula
            then do
                writeIORef formulaRef b
                writeIORef treeModeRef "tree"
                writeIORef treesRef [t]
                modifyIORef counterRef $ \counter -> upd counter 't' 1
                writeIORef currRef 0
                treeSlider `gtkSet` [ widgetSensitive := False ]
                setCurrInPaint paint 0
                termBut `gtkSet` [ labelText := str ]
                setNarrow 0
            else do
                curr <- readIORef currRef
                trees <- readIORef treesRef
                writeIORef treesRef $ updList trees curr t
        
        changeSimpl x t = do
          simplRules <- readIORef simplRulesRef
          case search ((== x) . root . pr1) simplRules of 
               Just i -> modifyIORef simplRulesRef $ \simpleRules ->
                               updList simplRules i rule
               _ -> modifyIORef simplRulesRef $ \simpleRules -> rule:simplRules
          where rule = (leaf x,[],t)
        
        -- | Used by 'checkBackward', 'forwProof'' and 'backProof'.
        
        changeState :: Int -> [[Int]] -> Action
        changeState ptr ps = do
          proof <- readIORef proofRef
          trees <- readIORef treesRef
          joined <- readIORef joinedRef
          let proofElem = proof!!ptr
          writeIORef axiomsRef $ peAxioms proofElem
          writeIORef theoremsRef $ peTheorems proofElem
          writeIORef newPredsRef $ peNewPreds proofElem
          writeIORef newAxiomsRef $ peNewAxioms proofElem
          writeIORef newTheoremsRef $ peNewTheorems proofElem
          writeIORef treeModeRef $ peTreeMode proofElem
          writeIORef treesRef $ peTrees proofElem
          modifyIORef counterRef $ \counter -> upd counter 't' $ length trees
          writeIORef currRef $ peCurr proofElem
          writeIORef permsRef $ pePerms proofElem
          writeIORef varCounterRef $ peVarCounter proofElem
          writeIORef solPositionsRef $ peSolPositions proofElem
          writeIORef constraintsRef $ peConstraints proofElem
          writeIORef joinedRef $ peJoined proofElem
          setTreesFrame ps
          setSubst $ peSubstitution proofElem
          labGreen $ peMsgL proofElem
          splitBut `gtkSet` [buttonLabel := if joined then "split" else "join"]

        changeStrat = do
          oldStrat <- readIORef simplStratRef
          modifyIORef simplStratRef
            $ \simplStrat -> case simplStrat of DF -> BF; BF -> PA; PA -> DF
          simplStrat <- readIORef simplStratRef
          extendPT $ SimplStrat oldStrat simplStrat
          simplStrat <- readIORef simplStratRef
          let str = stratWord simplStrat
          collSimpls <- readIORef collSimplsRef
          stratBut `gtkSet`
            [ buttonLabel := if collSimpls then str++"C" else str]

        -- | Used by 'backProof'.
        
        checkBackward :: Action
        checkBackward = do
          proofTPtr <- readIORef proofTPtrRef
          if proofTPtr < 1 then do labMag emptyProof
                                   labSolver paint emptyProof
                                   enterRef
          else do
               modifyIORef proofTPtrRef pred
               proofTPtr <- readIORef proofTPtrRef
               proofTerm <- readIORef proofTermRef
               case proofTerm!!proofTPtr of
                    Mark ps _      -> do writeIORef treepossRef ps
                                         drawCurr
                    Matching n _   -> writeIORef matchingRef n
                    Refuting b     -> writeIORef refutingRef $ not b
                    SafeSimpl b    -> writeIORef safeSimplRef $ not b
                    SimplStrat s _ -> writeIORef simplStratRef s
                    Simplifying b  -> writeIORef simplifyingRef $ not b
                    _ -> do
                        proofPtr <- readIORef proofPtrRef
                        when (proofPtr > 0) $ do
                            proof <- readIORef proofRef
                            modifyIORef proofPtrRef pred
                            proofPtr <- readIORef proofPtrRef
                            changeState proofPtr $ peTreePoss (proof!!proofPtr)
               enterRef
        
        -- | Used by 'forwProof'' and 'runChecker'.
        
        checkForward :: Action
        checkForward = do
            proofTPtr <- readIORef proofTPtrRef
            proofTerm <- readIORef proofTermRef
            if proofTPtr >= length proofTerm
              then do labMag endOfProof; labSolver paint endOfProof; enterRef
            else do
                proofPtr <- readIORef proofPtrRef
                let step = proofTerm!!proofTPtr
                    k = proofPtr+1
                proof <- readIORef proofRef
                when (deriveStep step && k < length proof)
                    $ writeIORef proofPtrRef k
                case step of
                    AddAxioms axs -> addCongAxioms' axs
                    ApplySubst -> applySubst
                    ApplySubstTo x t -> applySubstTo' x t
                    ApplyTransitivity -> applyTransitivity
                    BuildKripke m -> buildKripke m
                    BuildRE -> buildRegExp
                    Coinduction -> coinduction
                    CollapseStep b -> collapseStep b
                    CollapseVars -> collapseVarsCom
                    ComposePointers -> composePointers
                    CopySubtrees -> copySubtrees
                    CreateIndHyp -> createIndHyp
                    CreateInvariant b -> createInvariant b
                    DecomposeAtom -> decomposeAtom
                    DetKripke -> detKripke
                    Distribute -> distribute
                    EvaluateTrees -> evaluateTrees
                    ExpandTree b n -> expandTree' b n
                    FlattenImpl -> flattenImpl
                    Generalize cls -> generalize' cls
                    Induction -> induction
                    Mark _ ps -> do writeIORef treepossRef ps
                                    drawCurr
                    Matching _ n -> writeIORef matchingRef n 
                    Minimize -> minimize
                    ModifyEqs mode -> modifyEqs mode
                    MoveQuant -> moveQuant
                    Narrow limit sub -> narrow' limit sub
                    NegateAxioms ps cps -> negateAxioms' ps cps
                    PermuteSubtrees -> permuteSubtrees
                    RandomLabels -> randomLabels
                    RandomTree -> randomTree
                    ReduceRE m -> reduceRegExp m
                    Refuting b -> writeIORef refutingRef b
                    ReleaseNode -> releaseNode
                    ReleaseSubtree -> releaseSubtree
                    ReleaseTree -> releaseTree
                    RemoveCopies -> removeCopies
                    RemoveEdges b -> removeEdges b
                    RemoveNode -> removeNode
                    RemoveOthers -> removeOthers
                    RemovePath -> removePath
                    RemoveSubtrees -> removeSubtrees
                    RenameVar x -> renameVar' x
                    ReplaceNodes x -> replaceNodes' x
                    ReplaceOther -> replaceOther
                    ReplaceSubtrees ps ts -> replaceSubtrees' ps ts
                    ReplaceText x -> replaceText' x
                    ReplaceVar x u p -> replaceVar x u p
                    ReverseSubtrees -> reverseSubtrees
                    SafeSimpl b -> writeIORef safeSimplRef b
                    SetAdmitted block xs -> setAdmitted' block xs
                    SetCurr msg n -> setCurr msg n
                    ShiftPattern -> shiftPattern
                    ShiftQuants -> shiftQuants
                    ShiftSubs ps -> shiftSubs' ps
                    Simplify limit sub -> simplify' limit sub
                    Simplifying b -> writeIORef simplifyingRef b
                    SimplStrat _ s -> writeIORef simplStratRef s
                    SplitTree -> splitTree
                    StretchConclusion -> stretch False
                    StretchPremise -> stretch True
                    SubsumeSubtrees -> subsumeSubtrees
                    Theorem b th -> applyTheorem b Nothing th
                    Transform mode -> transformGraph mode
                    UnifySubtrees -> unifySubtrees
                modifyIORef proofTPtrRef (+1)
                enterRef
        
        -- | Exported by public 'Epaint.Solver' method 'Epaint.checkInSolver'.
        
        checkInSolver :: Action
        checkInSolver = writeIORef checkingPRef (False,True)
        
        -- | Used by 'checkProofF' and 'checkProofT'.
        
        checkProof :: String -> Bool -> String -> Action
        checkProof pterm inPainter file = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else case parse (list command) $ removeComment 0 pterm of
               Just pt -> do
                 writeIORef checkingRef True
                 when inPainter $ do writeIORef checkingPRef (True,False)
                                     buildPaint paint True
                                     showTreePicts
                 writeIORef proofTermRef pt
                 writeIORef proofTPtrRef 0
                 enterRef
                 trees <- readIORef treesRef
                 curr <- readIORef currRef
                 fast <- readIORef fastRef
                 initialize [] $ showTree fast $ trees!!curr
                 quit `gtkSet` [ buttonLabel := "quit check" ]
                 replaceCommandButton quitSignalRef quit setDeriveMode
                 labGreen $ proofLoaded file
                 checkingP <- readIORef checkingPRef
                 runChecker False
               _ -> labRed $ "There is no proof term in " ++ file ++ "."
        
        -- | Called by check proof options in tree menu.
        
        checkProofF :: Bool -> Action
        checkProofF inPainter = do
          str <- ent `gtkGet` entryText
          case words str of
               [file,sp] -> do
                            let newSpeed = parse pnat sp
                                fileT = file++"T"
                            when (just newSpeed) $ writeIORef speedRef
                                                 $ get newSpeed
                            pterm <- lookupLibs fileT
                            checkProof pterm inPainter fileT
               [file]    -> do
                            let fileT = file++"T"
                            pterm <- lookupLibs fileT
                            checkProof pterm inPainter fileT
               _         -> labMag "Enter a file name!"
        
        -- | Called by check proof options in tree menu.
        
        checkProofT :: Bool -> Action
        checkProofT inPainter = do
            sp <- ent `gtkGet` entryText
            let newSpeed = parse pnat sp
            when (just newSpeed) $ writeIORef speedRef $ get newSpeed
            pterm <- getTextHere
            checkProof pterm inPainter tfield

        clearAndDraw :: Action
        clearAndDraw = do
          setTreeposs $ Replace []
          drawCurr
        
        clearText :: Action
        clearText = do
            buffer <- tedit `gtkGet` textViewBuffer
            buffer `gtkSet` [ textBufferText := "" ]
        
        -- used by enterFormulas, enterTerms, enterText and enterRef
        -- called by button remove text

        coinduction = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               sig <- getSignature
               trees <- readIORef treesRef
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               varCounter <- readIORef varCounterRef
               axioms <- readIORef axiomsRef
               newPreds <- readIORef newPredsRef
               let t = trees!!curr
                   qs@(p:ps) = emptyOrAll treeposs
                   rs@(r:_) = map init qs
                   u = getSubterm t r
                   us = subterms u
                   rest = map (us!!) $ indices_ us `minus` map last qs
                   rule = "COINDUCTION"
                   f = preStretch True $ isCopred sig
                   g = stretchConc $ varCounter "z"
                   h x = if x `elem` fst newPreds then getPrevious x else x
                   getAxioms = flip noSimplsFor axioms
                   conjs@(conj:_) = map (mapT h . getSubterm t) qs
               if notnull qs && any null ps then labRed $ noApp rule
               else if null ps && universal sig t p conj then
                       case f conj of
                       Just (x,varps)
                         -> do
                            let (conj',k) = g varps conj
                                axs = getAxioms [x]
                            setZcounter k
                            applyInd rule [conj'] [x] axs t p []
                       _ -> notStretchable "The conclusion"
                    else if allEqual rs && isConjunct u
                                        && universal sig t r u then
                           case mapM f conjs of
                           Just symvarpss
                             -> do
                                let (xs,varpss) = unzip symvarpss
                                    (conjs',ks) = unzip $ zipWith g varpss conjs
                                    ys = mkSet xs
                                    axs = getAxioms ys
                                setZcounter $ maximum ks
                                applyInd rule conjs' ys axs t r rest
                           _ -> notStretchable "Some conclusion"
                         else labRed $ noApp rule

        -- | Used by 'checkForward'. Called by menu item /collapse level/
        -- from /graph/ menu.
        
        collapseStep :: Bool -> Action
        collapseStep b = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               counter <- readIORef counterRef
               part <- readIORef partRef
               let t = trees!!curr
                   p = emptyOrLast treeposs
                   u = getSubterm1 t p
                   n = counter 'c'
                   (v,part') = collapseLoop b (u,part) n
                   setPr = setProof True False "COLLAPSING THE SUBTREE" [p]
               extendPT $ CollapseStep b
               if u == v then do setPr collapsed
                                 setTreeposs $ Replace []
                                 resetLevel
                                 writeIORef partRef (id,[])
                         else do updateCurr $ replace1 t p v
                                 setPr $ levelMsg n
                                 drawCurr
                                 modifyIORef counterRef $
                                             \counter -> incr counter 'c'
                                 writeIORef partRef part'

        collapseVarsCom :: Action
        collapseVarsCom = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               sig <- getSignature
               trees <- readIORef treesRef
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               let t = trees!!curr
                   ps = emptyOrAll treeposs
                   ts = map (getSubterm1 t) ps
                   us = zipWith (collapseVars sig) (map (frees sig) ts) ts
               updateCurr $ fold2 replace1 t ps us
               extendPT CollapseVars
               setProof True False "COLLAPSING FREE VARIABLES" ps collapsedVars
               drawCurr

        -- | Used by 'checkForward'. Called by menu item /compose pointers/
        -- from /graph/ menu. 
        
        composePointers :: Action
        composePointers = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                -- sig <- getSignature
                let t = trees!!curr
                    ps = emptyOrAll treeposs
                    ts = map (composePtrs . getSubterm1 t) ps
                writeIORef treesRef
                    $ updList trees curr $ fold2 replace1 t ps ts
                extendPT ComposePointers
                setProof True False "COMBINING THE POINTERS OF THE TREES" ps
                   pointersComposed
                drawCurr
        
        -- | Called by menu items /combine for symbol/ ('True') and
        -- /invert for symbol/ ('False') from /axioms/ menu.
        
        compressAxioms :: Bool -> Action
        compressAxioms b = do
          sig <- getSignature
          str <- ent `gtkGet` entryText
          trees <- readIORef treesRef
          treeposs <- readIORef treepossRef
          axioms <- readIORef axiomsRef
          x <- if null trees || null treeposs then return str
               else do
                  curr <- readIORef currRef
                  return $ label (trees!!curr) $ head treeposs
          let axs = noSimplsFor [x] axioms
          if isPred sig x || isDefunct sig x || isCopred sig x
          then if null axs then labRed $ noAxiomsFor [x]
               else do varCounter <- readIORef varCounterRef
                       let (th,k) = compressAll b sig (varCounter "z") axs
                       modifyIORef theoremsRef $ \theorems -> th:theorems
                       setZcounter k
                       enterFormulas [th]
                       labGreen $ newCls "theorems" tfield
          else labMag "Enter a predicate, a defined function or a copredicate!"
        
        -- | Called by menu item /[combine for symbol].. in entry field/ from
        -- /axioms/ menu.
        
        compressClauses :: Action
        compressClauses = do
            sig <- getSignature
            str <- ent `gtkGet` entryText
            numberedExps <- readIORef numberedExpsRef
            let (exps,b) = numberedExps
            case parse intRanges str of
                Just (n:ks) | n < length exps ->
                    if b then do
                        varCounter <- readIORef varCounterRef
                        let vcz = varCounter "z"
                            (th,k) = combineOne sig vcz ks (exps!!n) exps
                        modifyIORef theoremsRef $ \theorems -> th:theorems
                        setZcounter k
                        enterFormulas [th]
                        labGreen $ newCls "theorems" tfield
                    else labMag $ enterTfield "clauses"
                _ -> labMag $ enterNumber ++ " Enter argument positions!"
        
        copySubtrees :: Action
        copySubtrees = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                treeposs <- readIORef treepossRef
                curr <- readIORef currRef
                let ps = emptyOrAll treeposs
                    t = trees!!curr
                if any null ps then labMag "Select proper subtrees!"
                else do
                    writeIORef treesRef $ updList trees curr $ copy ps t
                    extendPT CopySubtrees
                    let b = all idempotent $ map (label t . init) ps
                    setProof b False "COPYING THE SUBTREES" ps
                                     "The selected trees have been copied."
                    drawCurr
            where copy (p:ps) t = copy (map (rshiftPos0 p) ps) t3
                             where t1 = rshiftPos p t; q = init p; k = last p+1
                                   F x ts = getSubterm t1 q
                                   u = F x $ take k ts++V"":drop k ts
                                   t2 = mapT dec $ replace0 t1 q u
                                   n = length p-1; p' = incrPos p n
                                   t3 = replace0 t2 p' $ getSubterm t1 p
                                   dec x = if isPos x && p' <<= q
                                           then mkPos0 $ decrPos q n else x
                                           where q = getPos x
                  copy _ t      = t
        
        -- called by button transform selection > copy or by key c while the 
        -- the cursor is in the label field
        
        createIndHyp :: Action
        createIndHyp = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do treeposs <- readIORef treepossRef
                  if null treeposs then labMag "Select induction variables!"
                  else do 
                    curr <- readIORef currRef
                    let t = trees!!curr; xs = map (label t) treeposs
                    sig <- getSignature
                    if all (isFovar sig) xs &&
                       and (zipWith (isAllOrFree t) xs treeposs)
                       then do
                          let f x = V $ if x `elem` xs then '!':x else x
                              g f = mkTup $ map f xs
                              hyps = mkIndHyps t $ F ">>" [g f,g V]
                          modifyIORef newTheoremsRef
                              $ \newTheorems ->joinTerms newTheorems hyps
                          newTheorems <- readIORef newTheoremsRef
                          enterFormulas newTheorems
                          modifyIORef theoremsRef
                              $ \theorems -> joinTerms theorems hyps
                          updateCurr $ mkAll (frees sig t `minus` xs) $ t>>>f
                          extendPT CreateIndHyp
                          treeposs <- readIORef treepossRef
                          setProof True False "SELECTING INDUCTION VARIABLES"
                                   treeposs $ indHypsCreated xs
                          clearAndDraw
                    else labMag "Select induction variables!"
                    
        -- called by button tree > create induction hypotheses
        
        -- Called by create invariant menu items from
        -- /transform selection/ menu.
        
        createInvariant :: Bool -> Action
        createInvariant b = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
                sig <- getSignature
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    (p,conj,i) = case treeposs of
                               [] -> ([],t,0)
                               [q] | isFormula sig u -> (q,u,0)
                                   | notnull q -> ([],t,last q)
                                     where u = getSubterm t q
                               [q,r] | notnull r -> (q,getSubterm t q,last r)
                               _ -> ([],t,-1)
                if i > -1 && universal sig t p conj then
                   case preStretch False (isDefunct sig) conj of
                     Just (f,varps) -> do
                       varCounter <- readIORef varCounterRef
                       case stretchPrem (varCounter "z") varps conj of
                         (F "===>" [F "=" [F _ xs,d],conc],m) 
                           -> do let lg = length xs
                                 if i < lg
                                 then 
                                   do axioms <- readIORef axiomsRef
                                      case derivedFun sig f xs i lg axioms of
                                           -- ax is f(xs)=loop(take i xs++inits)
                                        Just (loop,inits,ax) 
                                           -> do let n = m+length inits
                                                     (as,bs) = splitAt (lg-i) xs
                                                     cs = map newVar [m..n-1]
                                                     u = mkInvs b loop as bs cs 
                                                                inits d conc
                                                 updateCurr $ replace t p u
                                                 setZcounter n
                                                 extendPT $ CreateInvariant b
                                                 setProof True False
                                                      (creatingInvariant str ax)
                                                      [p] $ invCreated b
                                                 clearAndDraw
                                        _ -> labRed $ 
                                              f ++ " is not a derived function."
                                 else labRed $ wrongArity f lg
                         _ -> labRed concCallsPrem
                     _ -> notStretchable "The premise"
                else labRed $ noApp str
          where str = if b then "HOARE INVARIANT CREATION"
                           else "SUBGOAL INVARIANT CREATION"
         
        createSpecMenu :: Bool -> Menu -> Action
        createSpecMenu add m = do
            mapM_ (mkButF m cmd) specfiles1
            mkBut m (if add then "from file (Return)" else "from file")
                    $ getFileAnd cmd
            when add $ Haskell.void $ mkBut m "from text field" 
                                    $ addSpecWithBase ""
            subMenu <- mkSub m "more"
            mapM_ (mkButF subMenu cmd) specfiles2
            subMenu <- mkSub subMenu "more"
            mapM_ (mkButF subMenu cmd) specfiles3
            done
            where cmd = if add then addSpecWithBase else loadText True

        createSub mode menu = do
          mkBut menu "from file" $ getFileAnd $ addClauses mode
          mkBut menu "from text field" $ addClauses mode ""
          when (mode == 0) $ do mkBut menu "from entry field" addCongAxioms
                                done
          solve <- readIORef solveRef
          other <- getSolver solve
          mkBut menu ("from "++ other) $ do tree <- getTreeR solve
                                            case tree of
                                                 Just t -> addTheorems t other
                                                 _ -> labBlue $ startOther other
          done

        decomposeAtom :: Action          -- called by selection > decompose atom
        decomposeAtom = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    p = emptyOrLast treeposs
                    b = polarity True t p
                    F x [l,r] = getSubterm1 t p
                    finish u = do updateCurr $ replace1 t p u
                                  extendPT DecomposeAtom
                                  setProof True False "DECOMPOSING THE ATOM" [p]
                                           atomDecomposed
                                  clearAndDraw
                sig <- getSignature
                case x of "=" | b -> finish $ splitEq sig True l r
                          "=/=" | not b -> finish $ splitEq sig False l r
                          _ -> labRed atomNotDecomposed
         
        delay :: Action -> Action
        delay = gtkDelay 100

        derefNodes = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               let t = trees!!curr
                   ps = emptyOrAll treeposs
               if all (isPos . root) $ map (getSubterm t) ps then do
                  updateCurr $ dereference t ps
                  extendPT DerefNodes
                  setProof True False "DEREFERENCING THE NODES" ps dereferenced
                  clearAndDraw
               else labMag "Select pointers!"
                                
        detKripke = do
          sig <- getSignature
          if null $ states sig then labMag "The Kripke model is empty!"
          else do 
               iniStates <- readIORef iniStatesRef
               let (sts,inits,trL,va,vaL) = powerAuto sig iniStates
                   sts' = map mkConst sts
               changeSimpl "states" $ mkList sts'
               writeIORef kripkeRef (sts',labels sig,atoms sig,[],trL,va,vaL)
               writeIORef iniStatesRef $ map mkConst inits
               extendPT DetKripke
               setProof True False "MAKING THE KRIPKE MODEL DETERMINISTIC" [] $ 
                        deterministic $ length sts

        distribute = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               trees <- readIORef treesRef
               curr <- readIORef currRef
               let t = trees!!curr
               treeposs <- readIORef treepossRef
               case treeposs of
                 ps@[p@(_:_),collPos@(_:_)] | q == init collPos && any b [0..3]
                   -> do updateCurr $ replace1 t q reduct
                         extendPT Distribute
                         setProof True False "DISTRIBUTING" ps distributed
                         clearAndDraw
                         where q = init p
                               n = last p
                               F x ts = getSubterm1 t q
                               u = getSubterm1 t p
                               coll = getSubterm1 t collPos
                               b 0 = x == "&" && isDisjunct coll
                               b 1 = x == "|" && isConjunct coll
                               b 2 = x == "==>" && n == 0 && isConjunct coll
                               b _ = x == "==>" && n == 1 && isDisjunct coll
                               reduct = if b 0 || b 1
                                        then F x $ context n
                                                 $ updList ts (last collPos)
                                                 $ insertFormula x u coll
                                        else insertFormula "==>" u coll
                 _ -> labMag selectDistribute

        draw :: TermSP -> Action
        draw ct = do
            sizeState <- readIORef sizeStateRef
            treeposs <- readIORef treepossRef
            clear canv
            writeIORef ctreeRef $ Just ct
            let (_,_,maxx,maxy) = minmax $ foldT (bds sizeState) ct
                -- Expander2: Size does not fit. Added size to avoid crop.
                sizefix = 100
                size@(_,h) = (max 100 (maxx+sizefix),max 100 (maxy+sizefix))
            writeIORef canvSizeRef size
            -- TODO check
            when (h > 100) $ tedit `gtkSet` [ widgetHeightRequest := 0]
            canv `gtkSet` [ canvasSize := size]
            if null treeposs then drawTree ct ct black blue []
            else drawTree2 ct ct black blue red darkGreen [] treeposs
            -- when (notnull treeDir) $
            --      readIORef picNoRef >>= delay 100 $ saveGraphD' treeDir
          where bds (n,w) (a,(x,y)) pss = (x-x',y-y'):(x+x',y+y'):concat pss
                               where (x',y') = (nodeWidth w a,n`div`2)
        
        -- drawArc p ct draws a line from position p to the root node of the 
        -- tree ct. The font size that has been set is substracted from the 
        -- line. 
        
        drawArc :: Pos -> TermSP -> Color -> Action
        drawArc (x,y) ct color =
             when (not $ isPos a) $ do font <- readIORef fontRef
                                       (above,below) <- getTextHeight canv font
                                       line canv [(x,y+below),(x',y'-above)] $
                                                 lineOpt {lineFill = color}
                                       done
             where (a,(x',y')) = root ct
        
        drawCurr :: Action
        drawCurr = do
            trees <- readIORef treesRef
            curr <- readIORef currRef
            drawThis "" (trees!!curr) []
        
        -- used by all functions that (re-)draw the current tree
        -- called if font size button is changed

        drawNewCurr :: Action
        drawNewCurr = do
            trees <- readIORef treesRef
            when (notnull trees) drawCurr
            
        -- called if horBut or treeSlider is changed
        
        drawNode :: (String, Pos) -> Color -> Action
        drawNode (a,p) c =
          if isPos a then done
          else do font <- readIORef fontRef
                  canvasText canv p textOpt {textFont = Just font,
                                             textFill = c',
                                             textJustify = CenterAlign}
                                    $ delQuotes a
                  done
         where c' = case parse colPre a of Just (c,_) -> c; _ -> c
       
        -- used by drawTree,drawTree2,moveNode,moveSubtree,catchNode
        
        drawRef :: TermSP -> Color -> [Int] -> Pos -> [Int] -> Action
        drawRef ct ac p mid@(x,y) q = do
          font <- readIORef fontRef
          (above,below) <- getTextHeight canv font
          let arc = [(x1,y1+below),(x,y-above)]
              target = (x',if y <= y' then y'-above else y'+above)
          if q `elem` allPoss ct then do
             draw (arc++[mid,target]) $ f $ if q << p then orange else magenta
             done
          else do draw (arc++[(x-10,y+10)]) $ f red; done    -- dangling pointer
          where (_,(x1,y1)) = label ct $ init p              -- pred of source
                (_,(x',y')) = label ct q                     -- target
                f color = if ac == white then white else color
                draw path color = line canv path lineOpt {lineFill = color,
                                                          lineArrow = Just Last,
                                                          lineSmooth = True}
        -- used by drawTree
       
        drawShrinked :: Action
        drawShrinked = do
            trees <- readIORef treesRef
            corner <- readIORef cornerRef
            spread <- readIORef spreadRef
            ctree <- readIORef ctreeRef
            when (notnull trees)
                $ draw $ shrinkTree (snd corner) (snd spread) $ get ctree

        -- called on change by verBut
        
        drawSubtrees :: Action
        drawSubtrees = do
            Just ct <- readIORef ctreeRef
            treeposs <- readIORef treepossRef
            oldTreeposs <- readIORef oldTreepossRef
            drawTree3 ct ct black blue red darkGreen [] treeposs $
                      minis (<<=) $ treeposs `join` oldTreeposs
         
        -- used by releaseSubtree,setSubtrees,catchSubtree
        
        drawThis col t ps = do
            showState <- readIORef showStateRef
            treeposs <- readIORef treepossRef
            maxHeap <- getMaxHeap
            font <- readIORef fontRef
            spread <- readIORef spreadRef
            corner <- readIORef cornerRef
            let qs = if showState then [] else treeposs
                u = mapConsts chgDouble $ cutTree maxHeap (drawHidden t) ps col 
                                          qs
            sizes@(_,w) <- mkSizes canv font $ nodeLabels u
            writeIORef sizeStateRef sizes
            draw $ coordTree w spread corner u
            done
       
        -- used by applySubstTo',drawCurr,showCoords,showCycleTargets,
        -- showGlb,showNumbers,showPolarities,showPositions,showPreds,showSucs,
        -- showSyms,showVals

-- drawTree ct ct nc ac [] draws the nodes of ct in color nc and the arcs of ct
-- in color ac. 
       
        drawTree :: TermSP -> TermSP -- type of ct
                           -> Color -- type of nc
                           -> Color -- type of ac
                           -> [Int] -- type of p
                           -> Action
        drawTree (F cx@(_,q) cts) ct nc ac p = do
            drawNode cx nc
            drawTrees cts $ succsInd p cts
            where drawTrees (ct':cts) (p:ps) = do drawArc q ct' ac
                                                  drawTree ct' ct nc ac p
                                                  drawTrees cts ps
                  drawTrees _ _ = done
        drawTree (V cx@(a,q)) ct nc ac p
            | isPos a = drawRef ct ac p q $ getPos a
            | True    = drawNode cx nc
            
        -- used by draw,drawTree2,moveSubtree,releaseSubtree

-- drawTree2 ct ct nc ac nc' ac' [] qs draws the nested ones among the subtrees
-- at positions qs alternately in (text,line)-colors (nc,ac) and (nc',ac'). 

        drawTree2 :: TermSP  -- type of ct
                  -> TermSP  -- type of ct0
                  -> Color   -- type of nc
                  -> Color   -- type of ac
                  -> Color   -- type of nc'
                  -> Color   -- type of ac'
                  -> [Int]
                  -> [[Int]] -- type of qs
                  -> Action
        drawTree2 ct@(V _) ct0 nc ac nc' ac' p qs
            | p `elem` qs = drawTree ct ct0 nc' ac' p
            | True      = drawTree ct ct0 nc ac p
        drawTree2 (F cx@(_,q) cts) ct nc ac nc' ac' p qs
            | p `elem` qs = do drawNode cx nc'
                               drawTrees2 q cts nc' ac' nc ac ps
            | True        = do drawNode cx nc
                               drawTrees2 q cts nc ac nc' ac' ps
                            where ps = succsInd p cts
                                  drawTrees2 q (ct':cts) nc ac nc' ac' (p:ps) = 
                                          do drawArc q ct' ac
                                             drawTree2 ct' ct nc ac nc' ac' p qs
                                             drawTrees2 q cts nc ac nc' ac' ps
                                  drawTrees2 _ _ _ _ _ _ _ = done
                          
        -- used by draw and drawTree3
        
-- drawTree3 ct .. rs applies drawTree2 ct .. to the subtrees of ct at positions
-- and is used by drawSubtrees.

        drawTree3 :: TermSP -- type of ct'
                  -> TermSP -- type of ct
                  -> Color  -- type of nc
                  -> Color  -- type of ac
                  -> Color  -- type of nc'
                  -> Color  -- type of ac'
                  -> [Int]
                  -> [[Int]] -- type of qs
                  -> [[Int]] -- type of rs
                  -> Action
        drawTree3 ct' ct nc ac nc' ac' p qs rs | any (<<= p) rs
                = drawTree2 ct' ct nc ac nc' ac' p qs
        drawTree3 (V _) _ _ _ _ _ _ _ _ = done
        drawTree3 (F (_,q) cts) ct nc ac nc' ac' p qs rs
                = drawTrees3 q cts nc ac nc' ac' ps
            where ps = succsInd p cts
                  drawTrees3 q (ct':cts) nc ac nc' ac' (p:ps) = do
                        drawTree3 ct' ct nc ac nc' ac' p qs rs
                        drawTrees3 q cts nc ac nc' ac' ps
                  drawTrees3 _ _ _ _ _ _ _ = done
        
        -- Show formulas in textfield. Exported by public
        -- 'Epaint.Solver' method 'Epaint.enterFormulas'.
        enterFormulas :: [TermS] -> Action
        enterFormulas fs = do
            checking <- readIORef checkingRef
            when (not checking) $ do
                clearText
                addText $ lines $ showFactors fs
                writeIORef numberedExpsRef (fs,True)
        
        {-  Show pointer in textfield. Used by 'checkBackward', 'checkForward',
            'checkProof', 'setDeriveMode' and 'showProofTerm'. Exported by
            public 'Epaint.Solver' method 'Epaint.enterRef'.
        -}
        enterRef :: Action
        enterRef = do clearText
                      proofTPtr <- readIORef proofTPtrRef
                      proofTerm <- readIORef proofTermRef
                      addText $ lines $ show
                              $ addPtr proofTPtr proofTerm
            where addPtr 0 (step:pt) = POINTER step:pt
                  addPtr n (step:pt) = step:addPtr (n-1) pt
                  addPtr _ pt        = pt

        -- Show terms in textfield. Used by 'showTerms'.
        enterTerms :: [TermS] -> Action
        enterTerms ts = do
            checking <- readIORef checkingRef
            when (not checking) $ do
                clearText
                addText $ lines $ showSum ts
                writeIORef numberedExpsRef (ts,False)
        
        {- | 
            Show text in textfield. Used by 'applyTheorem', 'incorrect',
            'loadText', 'parseSig', 'parseSigMap', 'parseTree', 'showProof',
            'showSig' and 'showSigMap'. Exported by public 'Epaint.Solver'
            method 'Epaint.enterText'.
        -}
        enterText :: String -> Action
        enterText str = do
            checking <- readIORef checkingRef
            when (not checking) $ do
                clearText
                addText $ lines str
                writeIORef numberedExpsRef ([],True)
                
        {- Show tree in canvas. Used by 'initCanvas', 'parseText',
            'randomTree', 'showEqsOrGraph' and 'showRelation'. 
        -}
        enterTree :: Bool -> TermS -> Action
        enterTree b t = do
          osci <- readIORef osciRef
          when (just osci) $ stopRun0 $ get osci
          setTime
          writeIORef formulaRef b
          writeIORef treeModeRef "tree"
          writeIORef treesRef [t]
          modifyIORef counterRef $ \counter -> upd counter 't' 1
          writeIORef proofTermRef []
          writeIORef proofTPtrRef 0
          setTreeposs $ Replace []
          sig <- getSignature
          makeTrees sig
          fast <- readIORef fastRef
          initialize (sigVars sig t) $ showTree fast t
          setTreesFrame []
        
        -- Called by "evaluate" menu item
        -- from "transform selection" menu.
        evaluateTrees :: Action
        evaluateTrees = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                sig <- getSignature
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    ps = emptyOrAll treeposs
                    ts = map (evaluate sig . getSubterm1 t) ps
                writeIORef treesRef
                    $ updList trees curr $ fold2 replace1 t ps ts
                extendPT EvaluateTrees
                setProof True False "EVALUATING THE TREES" ps evaluated
                clearAndDraw
        
        -- | Called by expand menu items from
        -- "graph" menu.
        expandTree :: Bool -> Action
        expandTree b = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                limit <- ent `gtkGet` entryText
                expandTree' b $ case parse pnat limit of Just n -> n; _ -> 0
        
        -- | Used by 'expandTree'
        expandTree' :: Bool -> Int -> Action
        expandTree' b limit = do
            trees <- readIORef treesRef
            curr <- readIORef currRef
            treeposs <- readIORef treepossRef
            let t = trees!!curr
                ps = emptyOrAll treeposs
                f u p = replace0 u p
                        $ (if b then expandOne else expand) limit t p
            writeIORef treesRef $ updList trees curr $ moreTree $ foldl f t ps
            extendPT $ ExpandTree b limit
            setProof True False "EXPANDING THE SUBTREES" ps $
                expandMsg ++ circlesUnfolded limit
            clearAndDraw

        extendPT step = do
          checking <- readIORef checkingRef
          when (not checking) $ do
             proofTPtr <- readIORef proofTPtrRef
             modifyIORef proofTermRef
               $ \proofTerm -> take proofTPtr proofTerm ++ [step]
             proofTerm <- readIORef proofTermRef
             writeIORef proofTPtrRef $ length proofTerm

        -- | Used by 'applyDisCon'.
        finishDisCon :: Maybe Int
                     -> Bool
                     -> Bool
                     -> [TermS]
                     -> TermS
                     -> [TermS]
                     -> TermS
                     -> [[Int]]
                     -> [Int]
                     -> [[Int]]
                     -> Sig
                     -> String
                     -> Action
        finishDisCon k b c ts reduct redices t ps pred qs sig msg = do
          case applyMany b c ts reduct redices t ps pred qs sig of
               Just t -> do
                         maybeSimplify sig t
                         setProof True True msg ps $ thApplied k
                         clearAndDraw
               _ -> labRed $ notUnifiable k
        
        -- | Used by 'releaseSubtree' and 'releaseTree'.
        finishRelease :: TermS -> [Int] -> Step -> Action
        finishRelease t p step = do
            trees <- readIORef treesRef
            curr <- readIORef currRef

            writeIORef treesRef $ updList trees curr t
            extendPT step
            clearAndDraw
            setProof False False "REPLACING THE SUBTREE" [p]
                                 "The selected tree has been replaced."
        
        -- Called by /flatten (co-)Horn clause/ menu
        -- item from /transform selection/ menu.
        flattenImpl :: Action
        flattenImpl = do
            trees <- readIORef treesRef
            formula <- readIORef formulaRef
            if null trees || not formula
            then labMag "Load and parse a Horn or co-Horn clause!"
            else do
                   sig <- getSignature
                   curr <- readIORef currRef
                   treeposs <- readIORef treepossRef
                   varCounter <- readIORef varCounterRef
                   let t = trees!!curr
                       xs = if null treeposs then defuncts sig t
                            else filter (isDefunct sig) $ map (label t) treeposs
                       (u,n) = flatten (varCounter "z") xs t
                   writeIORef treesRef $ updList trees curr u
                   setZcounter n
                   extendPT FlattenImpl
                   setProof True False "FLATTENING" [[]] flattened
                   clearAndDraw
        
        foldrM :: Monad m => (a -> b -> m b) -> b -> [a] -> m b
        foldrM = Haskell.foldrM

        -- | Called by /generalize/ menu item
        -- from /transform selection/ menu.
        generalize :: Action
        generalize = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    p = emptyOrLast treeposs
                    cl = getSubterm t p
                sig <- getSignature
                if isTerm sig cl then labRed "Select a formula!"
                else do
                    str <- ent `gtkGet` entryText
                    numberedExps <- readIORef numberedExpsRef
                    let (exps,b) = numberedExps
                    case parse intRanges str of
                        Just ns | all (< length exps) ns ->
                            if b then generalizeEnd t p cl $ map (exps!!) ns
                            else labMag $ enterTfield "formulas"
                        _ -> do
                            str <- getTextHere
                            case parseE (implication sig) str of
                                Correct cl' -> generalizeEnd t p cl [cl']
                                p -> incorrect p str $ illformed "formula"
        
        generalize' :: [TermS] -> Action
        generalize' cls = do
            trees <- readIORef treesRef
            curr <- readIORef currRef
            treeposs <- readIORef treepossRef
            let t = trees!!curr
                p = emptyOrLast treeposs
            generalizeEnd t p (getSubterm1 t p) cls
        
        -- | Used by 'generalize' and 'generalize''.
        generalizeEnd :: TermS -> [Int] -> TermS -> [TermS] -> Action
        generalizeEnd t p cl cls = do
            curr <- readIORef currRef
            updateCurr $ replace1 t p $ f $ cl:cls
            enterFormulas cls
            extendPT $ Generalize cls
            setProof True False "GENERALIZING" [p] generalized
            clearAndDraw
            where f = if polarity True t p then mkConjunct else mkDisjunct
        
        -- Get string from entry field ('ent'). Exported by public
        -- 'Epaint.Solver' method 'Epaint.getEntry'.
        getEntry' :: Request String
        getEntry' = ent `gtkGet` entryText
        
        -- | Apply action @act@ on filename entered in entry field 'ent'. Used
        -- by all load and store operation on files.
        getFileAnd :: (String -> Action) -> Action
        getFileAnd act = do -- Note [Filechooser]
            file <- ent `gtkGet` entryText
            if null file then labMag "Enter a file name!" else act file
        
        {- Note [Filechooser]
        ~~~~~~~~~~~~~~~~~~~~~
        This should be replaced by usage of the GTK+ file chooser. But seperated
        operations are needed for open and save dialogs. As a result all
        @getFileAnd@ function calls must be identified as load or store
        operation.
        -}
        
        -- | Used by 'showSubtreePicts' and 'showTreePicts'.
        getInterpreter = do
          sig <- getSignature
          picEval <- readIORef picEvalRef
          return $ case picEval of 
                        "tree"               -> widgetTree sig
                        "matrices"           -> searchPic $ matrix sig
                        "matrix solution"    -> solPic sig matrix
                        "linear equations"   -> leqs
                        "level partition"    -> searchPic $ plan 0
                        "preord partition"   -> searchPic $ plan 1
                        "heap partition"     -> searchPic $ plan 2
                        "hill partition"     -> searchPic $ plan 3
                        "alignment"          -> searchPic alig
                        "palindrome"         -> searchPic alig
                        "dissection"         -> searchPic diss
                        _                    -> searchPic $ widgets sig black
          where leqs      = const . linearEqs
                plan mode = const . planes mode
                alig      = const . alignment 
                diss      = const2 dissection
        
        -- | Get value of 'treeSize' scale. Used by 'drawThis'.
        getMaxHeap :: Request Int
        getMaxHeap = truncate <$> (treeSize `gtkGet` rangeValue)

        -- | Used by most other 'Epaint.Solver' functions. Exported by public
        -- 'Epaint.Solver' method 'Epaint.getSignatureR'.
        getSignature :: Request Sig
        getSignature = do
          (ps,cps,cs,ds,fs,hs) <- readIORef symbolsRef
          (sts,labs,ats,tr,trL,va,vaL) <- readIORef kripkeRef
          simplRules <- readIORef simplRulesRef
          transRules <- readIORef transRulesRef
          (block,xs) <- readIORef constraintsRef
          iniStates <- readIORef iniStatesRef
          safeSimpl <- readIORef safeSimplRef
          let isPred       = (`elem` ps)  ||| projection
              isCopred     = (`elem` cps) ||| projection
              isConstruct  = (`elem` cs)  ||| just . parse real |||
                             just . parse quoted ||| just . parse (strNat "inj")
              isDefunct    = (`elem` ds) ||| projection
              isFovar      = (`elem` fs) . base
              isHovar      = (`elem` (map fst hs)) . base
              hovarRel x y = isHovar x &&
                             case lookup (base x) hs of
                                  Just es@(_:_) -> isHovar y || y `elem` es
                                  _ -> not $ isFovar y
              blocked x = if block then z `elem` xs else z `notElem` xs
                          where z = head $ words x
              simpls = simplRules; transitions = transRules
              states = sts; labels = labs; atoms = ats; inits = iniStates
              trans = tr; transL = trL; value = va; valueL = vaL
              notSafe = not safeSimpl; redexPos = []
              base x = y where (y,_,_,_) = splitVar x
          return $ let
           in Sig
              { isPred      = isPred 
              , isCopred    = isCopred
              , isConstruct = isConstruct
              , isDefunct   = isDefunct
              , isFovar     = isFovar
              , isHovar     = isHovar
              , blocked     = blocked
              , hovarRel    = hovarRel
              , simpls      = simpls
              , transitions = transitions
              , states      = states
              , atoms       = atoms
              , labels      = labels
              , inits       = inits
              , trans       = trans
              , value       = value
              , transL      = transL
              , valueL      = valueL
              , notSafe     = notSafe
              }
        
        -- | Returns content of text area. Used by 'addClauses',
        -- 'addSigMapT', 'addSpec', 'addSubst', 'applyClause', 'checkProofT',
        -- 'generalize', 'parseText', 'replaceText' and 'specialize'. Exported
        -- by public 'Epaint.Solver' method 'Epaint.getText'.
        getTextHere :: Request String
        getTextHere = do 
          buffer <- tedit `gtkGet` textViewBuffer
          strs <- lines <$> buffer `gtkGet` textBufferText
          return $ removeDot $ unlines $ map (removeCommentL . f) strs
          where f (' ':' ':x:'>':str) | isDigit x           = str
                f (' ':x:y:'>':str)   | all isDigit [x,y]   = str
                f (x:y:z:'>':str)     | all isDigit [x,y,z] = str
                f str = str
        
        -- | Exported by public 'Epaint.Solver' method 'Epaint.getTree'.
        getTree :: Request (Maybe TermS)
        getTree = do
            trees <- readIORef treesRef
            if null trees then do labBlue start
                                  return Nothing
                          else do curr <- readIORef currRef
                                  return $ Just $ trees!!curr
        
        -- | Called by button "hide" ('hideBut').
        hideOrShow :: Action
        hideOrShow = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do drawCurr
                    modifyIORef showStateRef not
                    showState <- readIORef showStateRef
                    hideBut `gtkSet`
                           [buttonLabel := if showState then "hide" else "show"]
        
        -- | Handles incorrect parser results. Used by 'addClauses', 'addSpec',
        -- 'addSubst', 'applyClause', 'generalize', 'instantiate',
        -- 'parseConjects', 'parseText', 'parseTerms', 'replaceText'' and
        -- 'specialize'.
        incorrect :: Parse TermS -> String -> String -> Action
        incorrect p str error = do
            case p of
                Partial t rest -> enterText $ showTree False t ++ check rest
                _ -> enterText str
            labRed error
        
        -- | Called on keypress @Left@ or @Right@ while left label ('lab') is
        -- active.
        incrCurr :: Bool -> Action
        incrCurr b = do
            curr <- readIORef currRef
            let next = if b then curr+1 else curr-1
            trees <- readIORef treesRef
            setCurr newCurr $ next `mod` length trees
        
        -- | Lower or raise a number in the entry field by one. Called by
        -- buttons /entry-1/ ('minusBut') and /entry+1/ ('plusBut').
        incrEntry :: Bool -> Action
        incrEntry b = do
            str <- ent `gtkGet` entryText
            let k = parse nat str; f = entrySetText ent . show
            if b then case k of
                Just n -> f $ n+1
                _ -> ent `gtkSet` [ entryText := "0" ]
            else case k of
                Just n | n > 0 -> f $ n-1
                _ -> ent `gtkSet` [ entryText := "" ]

        induction = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               sig <- getSignature
               trees <- readIORef treesRef
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               varCounter <- readIORef varCounterRef
               newPreds <- readIORef newPredsRef
               axioms <- readIORef axiomsRef
               let t = trees!!curr
                   qs@(p:ps) = emptyOrAll treeposs
                   rs@(r:_) = map init qs
                   u = getSubterm t r
                   us = subterms u
                   rest = map (us!!) $ indices_ us `minus` map last qs
                   rule = "FIXPOINT INDUCTION"
                   f = preStretch False $ isPred sig ||| isDefunct sig
                   g = stretchPrem $ varCounter "z"
                   h (F x ts) = if x `elem` snd newPreds
                                then if isPred sig z then F z ts
                                     else mkEq (F z $ init ts) $ last ts
                                else F x $ map h ts where z = getPrevious x
                   h t = t
                   getAxioms ks xs = unzip $ map f $ noSimplsFor xs axioms
                                     where f = flatten (maximum ks) $
                                                       filter (isDefunct sig) xs
                   conjs@(conj:_) = map (h . getSubterm t) qs
               if notnull qs && any null ps then labRed $ noApp rule
               else if null ps && universal sig t p conj
                       then case f conj of
                            Just (x,varps)
                              -> do
                                 let (conj',k) = g varps conj
                                     (axs,ms) = getAxioms [k] [x]
                                 setZcounter $ maximum ms
                                 applyInd rule [conj'] [x] axs t p []
                            _ -> notStretchable "The premise"
                    else if allEqual rs && isConjunct u
                                        && universal sig t r u then
                           case mapM f conjs of
                           Just symvarpss
                             -> do
                                let (xs,varpss) = unzip symvarpss
                                    (conjs',ks) = unzip $ zipWith g varpss conjs
                                    ys = mkSet xs
                                    (axs,ms) = getAxioms ks ys
                                setZcounter $ maximum ms
                                applyInd rule conjs' ys axs t r rest
                           _ -> notStretchable "Some premise"
                         else labRed $ noApp rule

        -- | Used by all menu items /[show graph].. in painter/ and
        -- /[show matrix].. of (...)/ from /graph/ menu.
        initCanvas :: Action
        initCanvas = do
            trees <- readIORef treesRef
            when (null trees) $ enterTree False $ F "see painter" []
                             -- delay 100 $ done
        
        -- | Used by 'checkProof', 'enterTree and 'setNewTrees''.
        initialize :: [String] -> String -> Action
        initialize vars str = do
          symbols@(ps,cps,cs,ds,fs,hs) <- readIORef symbolsRef
          newPreds <- readIORef newPredsRef
          let (ps',cps') = (ps,cps) `minus2` newPreds
          constraints@(block,xs) <- readIORef constraintsRef
          writeIORef symbolsRef (ps',cps',cs,ds,fs,hs)
          proof <- readIORef proofRef
          writeIORef newPredsRef nil2
          newAxioms <- readIORef newAxiomsRef
          modifyIORef axiomsRef $ \axioms -> axioms `minus` newAxioms
          writeIORef newAxiomsRef []
          newTheorems <- readIORef newTheoremsRef
          modifyIORef theoremsRef $ \theorems -> theorems `minus` newTheorems
          writeIORef newTheoremsRef []
          writeIORef varCounterRef
            $ iniVC $ ps'++cps'++cs++ds++fs++map fst hs++vars
          writeIORef solPositionsRef []
          setSubst (V,[])
          writeIORef partRef (id,[])
          writeIORef permsRef $ \n -> [0..n-1]
          varCounter <- readIORef varCounterRef
          perms <- readIORef permsRef
          axioms <- readIORef axiomsRef
          theorems <- readIORef theoremsRef
          treeMode <- readIORef treeModeRef
          trees <- readIORef treesRef
          varCounter <- readIORef varCounterRef
          joined <- readIORef joinedRef
          refuting <- readIORef refutingRef
          safeSimpl <- readIORef safeSimplRef
          writeIORef proofRef
              [ ProofElem
                  { peMsg = "Derivation of\n\n"++str++
                            '\n':'\n':admitted block xs++
                            '\n':refuteMsg refuting++
                            '\n':safeMsg safeSimpl
                  , peMsgL = ""
                  , peAxioms = axioms
                  , peTheorems = theorems
                  , peNewPreds = nil2
                  , peNewAxioms = []
                  , peNewTheorems = []
                  , peTreeMode = treeMode
                  , peTrees = trees
                  , peTreePoss = []
                  , peCurr = 0
                  , peVarCounter = varCounter
                  , pePerms = perms
                  , peSolPositions = []
                  , peSubstitution = (V,[])
                  , peConstraints = constraints
                  , peJoined = joined
                  }
              ]
          writeIORef proofPtrRef 0
          writeIORef counterRef $ const 0
          writeIORef currRef 0
        
        -- | Called by menu item /instantiate/ from /transform selection/ menu
        instantiate :: Action
        instantiate = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                sig <- getSignature
                str <- ent `gtkGet` entryText
                let str' = removeComment 0 str
                case parseE (term sig) str' of
                    Correct t -> do
                        treeposs <- readIORef treepossRef
                        replaceQuant t (emptyOrLast treeposs)
                        labRed notInstantiable
                    p -> incorrect p str' $ illformed "term"
        
        -- | Called by menu item /Kleene axioms for symbols/ from menu /axioms/
        
        kleeneAxioms :: Action
        kleeneAxioms = do
            sig <- getSignature
            str <- ent `gtkGet` entryText
            trees <- readIORef treesRef
            treeposs <- readIORef treepossRef
            curr <- readIORef currRef
            let x = if null trees || null treeposs then str
                    else label (trees!!curr) $ head treeposs
                copred = isCopred sig x
                f = if copred then mkHornLoop else mkCoHornLoop
            if copred || isPred sig x then 
             do axioms <- readIORef axiomsRef
                let axs = noSimplsFor [x] axioms
                if null axs then labRed $ noAxiomsFor [x]
                else do varCounter <- readIORef varCounterRef
                        symbols <- readIORef symbolsRef
                        let i = V $ 'i':show (varCounter "i")
                            (axs',k) = f sig x axs i $ varCounter "z"
                            (ps,cps,cs,ds,fs,hs) = symbols
                            ps' = x:(x++"Loop"):ps
                        writeIORef symbolsRef (ps',cps`minus1`x,cs,ds,fs,hs)
                        modifyIORef axiomsRef
                            $ \axioms -> joinTerms (axioms `minus` axs) axs'
                        modifyIORef varCounterRef
                            $ \varCounter -> upd (incr varCounter "i") "z" k
                        enterFormulas axs'
                        labGreen $ if copred then newPredicate str1 str2 x
                                             else newPredicate str2 str1 x
            else labMag "Enter either a predicate or a copredicate!"
            where (str1,str2) = ("copredicate","predicate")
        
        labColor :: String -> Background -> Action
        labColor str color = do gtkSet lab [labelText := str]
                                setBackground lab color
        
        labBlue,labGreen,labMag,labRed :: String -> Action
        labBlue  = flip labColor blueback
        labGreen = flip labColor greenback
        labMag   = flip labColor magback
        labRed   = flip labColor redpulseback
       
        labColorToPaint :: Background -> String -> Action
        labColorToPaint col str = do labColor str col
                                     labSolver paint str
        
        labColorToPaintT col str = do
            (time0,_) <-  readIORef timesRef
            if time0 == 0 then labColor str col
            else do time <- getCPUTime
                    writeIORef timesRef (0,300)
                    labColor (str++'\n':show (mkSecs time0 time)++" sec") col
            labSolver paint str
        
        -- | Lookup @file@ and load content into text area.
        -- Called by all menu items in "load text" submenu from tree menu and
        -- "specification" menu.
        loadText :: Bool -> FilePath -> Action
        loadText b file = do
          str <- lookupLibs file
          if null str then labRed $ file ++ " is not a file name."
          else if b then do enterText str; labGreen $ loaded file
                    else do solve <- readIORef solveRef; bigWinR solve
                            enterTextR solve str
        
        -- | Used by 'applyInd', 'applyTheorem', 'enterTree, 'narrowLoop',
        -- 'narrowPar', 'replaceSubtrees'', 'replaceVar', 'simplify' and
        -- 'splitTree'.
        makeTrees :: Sig -> Action
        makeTrees sig = do
          treeMode <- readIORef treeModeRef
          trees <- readIORef treesRef
          case treeMode of
            "tree"    -> do
                         joined <- readIORef joinedRef
                         if joined then done
                         else do
                             case trees of
                              [t@(F "|" _)]   -> do
                                                 writeIORef solPositionsRef []
                                                 separate mkSummands t "summand"
                              [t@(F "&" _)]   -> do
                                                 writeIORef solPositionsRef []
                                                 separate mkFactors t "factor"
                              [t@(F "<+>" _)] -> separate mkTerms t "term"
                              _               -> done
            "summand" -> if null ts then actMore [mkFalse] "tree"
                                    else actMore ts treeMode
                         where ts = mkSummands $ F "|" trees
            "factor"  -> if null ts then actMore [mkTrue] "tree"
                                    else actMore ts treeMode
                         where ts = mkFactors $ F "&" trees
            _         -> if null ts then actMore [unit] "tree"
                                    else actMore ts treeMode
                         where ts = mkTerms $ F "<+>" trees
          where separate f = actMore . map (dropnFromPoss 1) . f . separateComps
                actMore ts mode = do
                     newTrees <- readIORef newTreesRef
                     curr <- readIORef currRef
                     counter <- readIORef counterRef
                     formula <- readIORef formulaRef
                     trees <- readIORef treesRef

                     writeIORef newTreesRef $ newTrees || lg /= length trees
                     writeIORef currRef $ curr `mod` lg
                     writeIORef treesRef ts
                     writeIORef counterRef $ upd counter 't' lg
                     writeIORef treeModeRef $ if lg == 1 then "tree" else mode
                     writeIORef solPositionsRef $ if formula then solPoss sig ts
                                                             else []
                     where lg = length ts
        
        -- used by 'applyInd', 'applyTheorem', 'finishDisCon', 'narrowPar',
        -- 'replaceSubtrees'' and 'replaceVar'.
        maybeSimplify :: Sig -> TermS -> Action
        maybeSimplify sig t = do
          simplifying <- readIORef simplifyingRef
          updateCurr $ if simplifying then simplifyFix sig t else t
 
        minimize :: Action          -- called by button specification > minimize
        minimize = do
          sig <- getSignature
          if null $ states sig then labMag "The Kripke model is empty!"
          else do iniStates <- readIORef iniStatesRef
                  let (sts,inits,tr,trL,va,vaL) = mkQuotient sig iniStates
                  changeSimpl "states" $ mkList sts
                  writeIORef kripkeRef (sts,labels sig,atoms sig,tr,trL,va,vaL)
                  writeIORef iniStatesRef inits
                  extendPT Minimize
                  setProof True False "MINIMIZING THE KRIPKE MODEL" [] $
                           minimized $ length sts
        
        modifyEqs mode = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do sig <- getSignature
                  trees <- readIORef treesRef
                  curr <- readIORef currRef
                  treeposs <- readIORef treepossRef
                  let t = trees!!curr
                      ps@(p:qs) = emptyOrAll treeposs
                      u = getSubterm1 t p
                      msg = "MODIFYING THE EQUATIONS"
                      act p u = do
                       writeIORef treesRef $ updList trees curr $ replace1 t p u
                       extendPT $ ModifyEqs mode
                       setProof False False msg [p] eqsModified
                       clearAndDraw
                  case mode of
                    0 -> case parseEqs u of
                         Just eqs -> do
                                     let t = connectEqs eqs
                                     firstClick <- readIORef firstClickRef
                                     if firstClick then do
                                        act p t     -- rhs variables to pointers
                                        writeIORef substitutionRef (const t,[])
                                        writeIORef firstClickRef False
                                        eqsBut <- readIORef eqsButRef
                                        eqsBut `gtkSet`
                                          [ menuItemLabel := "separate graphs"]
                                     else do
                                          (f,_) <- readIORef substitutionRef
                                          act p $ separateComps $ f ""
                                          writeIORef substitutionRef (V,[])
                                          writeIORef firstClickRef True
                                          eqsBut <- readIORef eqsButRef
                                          eqsBut `gtkSet` [ menuItemLabel
                                            := "connect equations"]
                         _ -> labMag "Select iterative equations!"
                    1 -> case parseEqs u of                 -- regular equations
                         Just eqs -> act p $ eqsTerm $ autoEqsToRegEqs sig eqs
                         _ -> labMag "Select iterative equations!"
                    2 | isV u -> case parseEqs t of      -- substitute variables
                                      Just eqs | just v -> act [] $ get v
                                               where v = substituteVars t eqs ps
                                      _ -> labMag instantiateVars
                      | True  -> case parseEqs u of
                                      Just eqs | just v -> act p $ get v
                                               where v = substituteVars t eqs qs
                                      _ -> labMag instantiateVars
                    _ -> case parseIterEq u of         -- solve regular equation
                              Just eq | just t -> act p $ get t
                                                     where t = solveRegEq sig eq
                              _ -> labMag "Select a regular equation!"

        {- |
            Moves a node of a tree on the canvas. Click and hold the right
            mouse button over a node. Move the node to its new destination. When
            the mouse button is released the node will be inserted into the new
            position. It is initialized with 'catchNode' on mouse button press
            and finished with 'releaseNode' on mouse button release. Called by
            mouse move actions while pressing right button.
            
            See 'moveSubtree' and 'moveTree'.
        -}
        moveNode :: Pos -> Action
        moveNode (x,y) = do
            treeposs <- readIORef treepossRef

            if null treeposs then labMag "Select a target node!"
            else do
                node <- readIORef nodeRef
                ctree <- readIORef ctreeRef

                let f p a col1 col2 = drawNode a $ if last treeposs <<= p
                                                   then col1 else col2
                case node of Just (z,p) -> do f p z red black; done
                             _ -> done
                -- (x,y) <- adaptPos pt
                case getSubtree (get ctree) x y of
                    Just (p,cu) -> do
                        let a = root cu
                        f p a cyan magenta
                        writeIORef nodeRef $ Just (a,p)
                    _ -> writeIORef nodeRef Nothing

        moveQuant = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               sig <- getSignature
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               let t = trees!!curr
                   p = emptyOrLast treeposs
                   u = getSubterm1 t p
                   msg = "MOVING DOWN A QUANTIFIER"
               writeIORef treesRef
                 $ updList trees curr $replace1 t p $ moveQdown sig u
               extendPT MoveQuant
               setProof True False msg [p] quantifierMoved
               clearAndDraw

       {- |
            Moves a subtree of a tree on the canvas. Click and hold the left
            mouse button over a subtree. Move the subtree to its new
            destination. When the mouse button is released the subtree will be
            inserted into the new position. It is initialized with
            'catchSubtree' on mouse button press and finished with
            'releaseSubtree' on mouse button release. Called by
            mouse move actions while pressing left button.
            
            See 'moveNode' and 'moveTree'.
        -}
        moveSubtree :: Pos -> Action
        moveSubtree pt@(x1,y1) = do
            isSubtree <- readIORef isSubtreeRef
            penpos <- readIORef penposRef

            when (just isSubtree && just penpos) $ do
                Just ct <- readIORef ctreeRef
                Just cu <- readIORef subtreeRef
                treeposs <- readIORef treepossRef
                firstMove <- readIORef firstMoveRef
                node <- readIORef nodeRef

                let (x0,y0) = get penpos
                    cu' = transTree2 (x1-x0,y1-y0) cu
                    p = last treeposs
                if firstMove && not (get isSubtree)
                    then drawTree cu ct black blue p
                    else drawTree cu ct white white p
                writeIORef firstMoveRef False
                writeIORef penposRef $ Just pt
                writeIORef subtreeRef $ Just cu'
                when (just node) $ drawNode (fst $ get node) black
                drawTree cu' ct red darkGreen p
                -- (x,y) <- adaptPos pt
                suptree <- readIORef suptreeRef
                case getSubtree (get suptree) x1 y1 of
                    Just (p,cu) -> do
                        let a = root cu
                        drawNode a magenta
                        writeIORef nodeRef $ Just (a,p)
                    _ -> writeIORef nodeRef Nothing
        
        {- |
            Moves the tree on the canvas. Click and hold the middle
            mouse button over the tree. Move the tree to its new
            destination. When the mouse button is released the tree will be
            inserted into the new position. It is initialized with
            'catchTree' on mouse button press and finished with
            'releaseTree' on mouse button release. Called by
            mouse move actions while pressing middle button.
            
            See 'moveNode' and 'moveSubtree'.
        -}
        moveTree :: Pos -> Action
        moveTree p@(x,y) = do
            isSubtree <- readIORef isSubtreeRef

            case isSubtree of
                 Just True -> moveSubtree p
                 Just _ -> do penpos <- readIORef penposRef
                              when (just penpos) $ do
                                   ctree <- readIORef ctreeRef
                                   let (x0,y0) = get penpos
                                       q@(i,j) = (x-x0,y-y0)
                                   draw $ transTree2 q $ get ctree
                                   modifyIORef cornerRef
                                        $ \corner -> (fst corner+i,snd corner+j)
                                   writeIORef penposRef $ Just p
                 _ -> done
        
        -- | Called by 'narrowBut'. Exported by public 'Epaint.Solver' method
        -- 'Epaint.narrow.
        narrow :: Action
        narrow = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
               str <- ent `gtkGet` entryText
               case parse pnat str of
                    Just limit -> narrow' limit True
                    _ -> case parse pnatSecs str of
                           Just n -> do
                                  modifyIORef timesRef $ \times -> (fst times,n)
                                  narrow' (-1) True
                           _ -> narrow' 1 False
       
        narrow' :: Int -> Bool -> Action
        narrow' limit sub = do
            trees <- readIORef treesRef
            curr <- readIORef currRef
            formula <- readIORef formulaRef
            constraints <- readIORef constraintsRef
            axioms <- readIORef axiomsRef
            treeposs <- readIORef treepossRef
            sig <- getSignature
            writeIORef ruleStringRef
                       $ if formula then "NARROWING" else "REWRITING"
            modifyIORef counterRef $ \counter -> upd counter 'd' 0
            let t = trees!!curr
                cls = filter (not . isSimpl) axioms
            if null treeposs then do
                extendPT $ Narrow limit True
                setTime
                narrowLoop sig cls 0 limit
            else if sub then do setTime; narrowSubtree t sig cls limit
                 else do
                    extendPT $ Narrow 0 False
                    narrowOrRewritePar t sig (Just $ -1) cls False treeposs

        -- used by narrow
        
        narrowLoop :: Sig -> [TermS] -> Int -> Int -> Action
        narrowLoop sig cls k limit
                | limit == 0 = finish k
                | True       = do
            trees <- readIORef treesRef
            curr <- readIORef currRef
            treeMode <- readIORef treeModeRef
            formula <- readIORef formulaRef
            simplifying <- readIORef simplifyingRef

            let t = trees!!curr
            case treeMode of
                "tree"
                    | formula ->
                        if isSol sig t then do
                            writeIORef solPositionsRef [0]
                            finishNar k
                        else do
                            joined <- readIORef joinedRef
                            writeIORef solPositionsRef []
                            if joined then mkStep t $ finish k
                            else case trees of [F "|" ts] -> split ts "summand"
                                               [F "&" ts] -> split ts "factor"
                                               _ -> mkStep t $ finish k
                    | True -> do
                        joined <- readIORef joinedRef
                        if joined then mkStep t $ finish k
                        else case trees of [F "<+>" ts] -> split ts "term"
                                           _ -> mkStep t $ finish k
                "summand"
                    | simplifying -> case t of F "|" ts -> actMore ts treeMode
                                               F "&" ts -> actMore ts "factor"
                                               _ -> actMore [t] "tree"
                    | null ts -> actMore [mkFalse] "tree"
                    | True    -> actMore ts treeMode
                                where t = simplifyFix sig $ mkDisjunct trees
                                      ts = mkSummands $ F "|" trees
                "factor"
                    | simplifying -> case t of F "|" ts -> actMore ts "summand"
                                               F "&" ts -> actMore ts treeMode
                                               _ -> actMore [t] "tree"
                    | null ts -> actMore [mkTrue] "tree"
                    | True    -> actMore ts treeMode
                                where t = simplifyFix sig $ mkConjunct trees
                                      ts = mkFactors $ F "&" trees
                _
                    | simplifying -> case t of F "<+>" ts -> actMore ts "term"
                                               _ -> actMore [t] "tree"
                    | null ts -> actMore [unit] "tree"
                    | True    -> actMore ts treeMode
                        where t = simplifyFix sig $ mkSum trees
                              ts = mkTerms $ F "<+>" trees
         where finish k = makeTrees sig >> finishNar k
               finishNar k = do
                    ruleString <- readIORef ruleStringRef
                    formula <- readIORef formulaRef
                    solPositions <- readIORef solPositionsRef
                    setProof True True ruleString [] $
                        finishedNar formula k ++ solved solPositions
                    setTreesFrame []
               mkStep t stop = do
                    formula <- readIORef formulaRef
                    narrowStep sig cls limit t proceed stop formula
               proceed t n vc = do
                    writeIORef varCounterRef vc
                    modifyIORef counterRef $ \counter -> upd counter 'd' k'
                    updateCurr t
                    narrowLoop sig cls k' (limit-n)
                    where k' = k+n
               split = actMore . map (dropnFromPoss 1)
               actMore ts mode = do
                    trees <- readIORef treesRef
                    curr <- readIORef currRef
                    formula <- readIORef formulaRef

                    let b n newTrees = newTrees || lg /= length trees
                                                || curr /= n
                        searchRedex (n:ns) = do
                            modifyIORef newTreesRef $ b n
                            writeIORef currRef n
                            mkStep (trees!!n) $ searchRedex ns
                        searchRedex _ = do
                            modifyIORef newTreesRef $ b 0
                            writeIORef currRef 0
                            finish k
                        ks = drop curr is++take curr is
                    writeIORef treesRef ts
                    modifyIORef counterRef $ \counter -> upd counter 't' lg
                    writeIORef treeModeRef $ if lg == 1 then "tree" else mode
                    writeIORef solPositionsRef
                        $ if formula then solPoss sig ts else []
                    solPositions <- readIORef solPositionsRef
                    searchRedex $ ks `minus` solPositions
                    where lg = length ts; is = indices_ ts

        -- used by narrow'

        narrowOrRewritePar :: TermS -> Sig -> Maybe Int -> [TermS] -> Bool
                           -> [[Int]] -> Action
        narrowOrRewritePar t sig k cls saveRedex ps = do
            varCounter <- readIORef varCounterRef
            formula <- readIORef formulaRef

            let f g = g t sig k cls saveRedex [] ps [] varCounter
            if formula || ps `subset` boolPositions sig t then f narrowPar
                                                          else f rewritePar
                                                          
        -- used by applyTheorem,narrow

        narrowPar :: TermS
                  -> Sig
                  -> Maybe Int
                  -> [TermS]
                  -> Bool
                  -> [TermS]
                  -> [[Int]]
                  -> [[Int]]
                  -> (String -> Int)
                  -> Action
        narrowPar t sig k cls saveRedex used (p:ps) qs vc =
            if p `notElem` noRefPoss t -- || isVarRoot sig redex
            then narrowPar t sig k cls saveRedex used ps qs vc
            else do
                matching <- readIORef matchingRef
                axioms <- readIORef axiomsRef
                rand <- readIORef randRef
                let b = matching > 1
                    apply at r = applyAxs cls1 cls3 axioms redex at r sig vc' b
                    applyR at r = applyAxsR cls1 cls3 axioms rand redex at r sig
                                             vc' b
                if isDefunct sig sym then case atomPosition sig t p of
                    Just (q,at,r) ->
                        if even matching then case apply at r of
                            (Backward reds vc,used') ->
                                proceed q mkDisjunct reds used' vc
                            (MatchFailure str,_) -> labMsg str
                            _ -> next
                        else case applyR at r of
                            (Backward reds vc,used',rand')-> do
                                writeIORef randRef rand'
                                proceed q mkDisjunct reds used' vc
                            (MatchFailure str,_,_) -> labMsg str
                            _ -> next
                    _ -> next
                else
                    if notnull p && isTerm sig redex then do
                        let q = init p
                        case (getSubterm t q,last p) of
                            (at@(F "->" [_,_]),0) ->
                                if even matching then case apply at [0] of
                                    (Backward reds vc,used')
                                     -> proceed q mkDisjunct reds used' vc
                                    (MatchFailure str,_) -> labMsg str
                                    _ -> next
                                else case applyR at [0] of
                                    (Backward reds vc,used',rand') -> do
                                        writeIORef randRef rand'
                                        proceed q mkDisjunct reds used' vc
                                    (MatchFailure str,_,_) -> labMsg str
                                    _ -> next
                            _ -> next
                    else
                        if isPred sig sym || isCopred sig sym then
                            if even matching then case apply redex [] of
                                (Backward reds vc,used') ->
                                    proceed p mkDisjunct reds used' vc
                                (Forward reds vc,used') ->
                                    proceed p mkConjunct reds used' vc
                                (MatchFailure str,_) ->
                                    labMsg str
                                _ -> next
                            else case applyR redex [] of
                                (Backward reds vc,used',rand') -> do
                                    writeIORef randRef rand'
                                    proceed p mkDisjunct reds used' vc
                                (Forward reds vc,used',rand') -> do
                                    writeIORef randRef rand'
                                    proceed p mkConjunct reds used' vc
                                (MatchFailure str,_,_) -> labMsg str
                                _ -> next
                        else next
         where redex = getSubterm t p; sym = getOp redex
               cls1 = filterClauses sig redex cls
               cls2 = if saveRedex then map copyRedex cls1 else cls1
               (cls3,vc') = renameApply sig t vc cls2
               proceed q f reds used' vc =
                         narrowPar (replace t q $ f reds) sig k cls saveRedex
                                   (used `join` used') ps (p:qs) vc
               next = narrowPar t sig k cls saveRedex used ps qs vc
               labMsg = labColorToPaint magback
        narrowPar _ _ k _ _ [] _ _ _ =
            labColorToPaint magback $ subtreesNarrowed k
        narrowPar t sig k _ _ used _ qs vc = do
            writeIORef varCounterRef vc
            maybeSimplify sig t
            makeTrees sig
            finish $ thApplied k
            where finish msg = do
                    modifyIORef counterRef $ \counter -> upd counter 'd' 1
                    setProof True True (applied b str) qs msg
                    setTreesFrame []
                  b = length used == 1
                  str = showFactors used
        
        -- | Used by 'narrowSubtree' and 'narrowLoop'.
        narrowStep :: Sig
                   -> [TermS]
                   -> Int
                   -> TermS
                   -> (TermS -> Int -> (String -> Int) -> Action)
                   -> Action
                   -> Bool
                   -> Action
        narrowStep sig cls limit t proceed stop nar = do
            times <- readIORef timesRef
            time <- getCPUTime
            let (time0,timeout) = times
                m = if limit < 0 then 1 else limit
            if mkSecs time0 time > timeout then stop
            else do
                matching <- readIORef matchingRef
                varCounter <- readIORef varCounterRef
                simplifying <- readIORef simplifyingRef
                axioms <- readIORef axiomsRef

                if even matching then do
                    refuting <- readIORef refutingRef

                    let (u,n,vc) = applyLoop t m varCounter cls axioms sig nar
                                              matching refuting simplifying
                    if n == 0 then stop else proceed u n vc
                else do
                    rand <- readIORef randRef
                    let (u,n,vc,rand') = applyLoopRandom rand t m varCounter cls
                                             axioms sig nar matching simplifying
                    writeIORef randRef rand'
                    if n == 0 then stop else proceed u n vc
        
        narrowSubtree :: TermS -> Sig -> [TermS] -> Int -> Action
        narrowSubtree t sig cls limit = do
            treeposs <- readIORef treepossRef
            let p = emptyOrLast treeposs
                u = getSubterm1 t p
                nar = isFormula sig u
                sn = subtreesNarrowed (Nothing :: Maybe Int)
                (str,str') = if nar then ("NARROWING",sn)
                                    else ("REWRITING",sn++onlyRew)
                proceed u n vc = do
                   simplifying <- readIORef simplifyingRef
                   let v = if simplifying then simplifyFix sig u else u
                   updateCurr $ replace1 t p v
                   writeIORef varCounterRef vc
                   extendPT $ Narrow limit True
                   modifyIORef counterRef $ \counter -> upd counter 'd' n
                   setProof True True str [p] $ appliedToSub (map toLower str) n
                   setTreesFrame []
                stop = labColorToPaint magback str'
            narrowStep sig cls limit u proceed stop nar
            
        -- used by narrow'

        -- | Called by menu item /negate for symbols/ from /axioms/ menu or
        -- by pressing @n@ on left label ('lab').
        negateAxioms :: Action
        negateAxioms = do
            str <- ent `gtkGet` entryText
            sig <- getSignature
            trees <- readIORef treesRef
            treeposs <- readIORef treepossRef
            curr <- readIORef currRef
            symbols <- readIORef symbolsRef
            let xs = if null trees || null treeposs then words str
                     else map (label $ trees!!curr) treeposs
                (ps,cps,_,_,_,_) = symbols
                ps1 = filter (isPred sig) $ meet xs ps
                cps1 = filter (isCopred sig) $ meet xs cps
            negateAxioms' ps1 cps1
        
        negateAxioms' :: [String] -> [String] -> Action
        negateAxioms' ps1 cps1 = do
            symbols <- readIORef symbolsRef
            axioms <- readIORef axiomsRef
            let (ps,cps,cs,ds,fs,hs) = symbols
                xs = ps1++cps1
                axs1 = noSimplsFor xs axioms
                ps2 = map mkComplSymbol cps1
                cps2 = map mkComplSymbol ps1
                str = complsAdded xs
                msg = init str ++ " (see " ++ tfield ++ ")."
            if null axs1 then
                labRed $ "There are no axioms for "++ showStrList xs
            else do
                writeIORef symbolsRef
                    (ps `join` ps2,cps `join` cps2,cs,ds,fs,hs)
                sig <- getSignature
                let axs2 = map (mkComplAxiom sig) axs1
                modifyIORef axiomsRef (++ axs2)
                enterFormulas axs2
                trees <- readIORef treesRef
                if null trees then labGreen msg
                else do
                    extendPT $ NegateAxioms ps1 cps1
                    setProof True False str [] msg
                    
        -- used by negateAxioms
        
        -- | Shows error message "@str@ cannot be stretched." on left label.
        -- Used by 'applyClause', 'applyCoinduction', 'applyInduction',
        -- 'createInvariant' and 'stretch'.
        notStretchable :: String -> Action
        notStretchable str = labRed $ str ++ " cannot be stretched."
        
        -- | Used by 'addClauses' and 'addSpec'.
        parseConjects :: Sig -> FilePath -> String -> Action
        parseConjects sig file conjs =
            case parseE (implication sig) conjs of
                Correct t -> do
                    let ts = if isConjunct t then subterms t else [t]
                    modifyIORef conjectsRef $ \conjects -> conjects `join` ts
                    labGreen $ newCls "conjectures" file
                p -> incorrect p conjs $ illformed "formula"
        
        -- | Used by 'addSigMap' and 'addSigMapT'.
        parseSigMap :: FilePath -> String -> Action
        parseSigMap file str = do
            signatureMap <- readIORef signatureMapRef
            sig <- getSignature
            sig' <- readIORef solveRef >>= getSignatureR
            case parseE (sigMap signatureMap sig sig') str of
                Correct f -> do
                    writeIORef signatureMapRef f
                    labGreen $ newSigMap file
                Partial f rest -> do
                    enterText $ showSignatureMap f $ check rest
                    labRed $ illformed "signature map"
                _ -> do
                    enterText str
                    labRed $ illformed "signature map"
        
        
        -- | Parses the text from text area and show it as a graph on the
        -- canvas. Called by button /parse up/ ('upBut') or by pressing the
        -- @Up@ on active text area ('tedit').
        parseText :: Action
        parseText = do
            numberedExps <- readIORef numberedExpsRef

            str <- ent `gtkGet` entryText
            let (exps, b) = numberedExps
            case parse intRanges str of
                Just ns | all (< length exps) ns -> do
                    ent `gtkSet` [ entryText := "" ]
                    let exps' = map (exps !!) ns
                    if b then enterTree True $ mkConjunct exps'
                         else enterTree False $ mkSum exps'
                _ -> do
                    str <- getTextHere
                    sig <- getSignature
                    case parseE (implication sig) str of
                        Correct t -> enterTree True t
                        _ -> case parseE (term sig) str of
                            Correct cl -> enterTree False cl
                            p -> incorrect p str $ illformed "term or formula"
        
        -- | Used by 'addSpec'.
        parseTerms :: Sig -> FilePath -> String -> Action
        parseTerms sig file ts =  case parseE (term sig) ts of
            Correct t -> do
                let ts = if isSum t then subterms t else [t]
                modifyIORef termsRef $ \terms -> ts `join` terms
                labGreen $ newCls "terms" file
            p -> incorrect p ts $ illformed "term"
        
        -- | Display the graph from canvas ('canv') as a text representation in
        -- the text area ('tedit'). Called by button /parse down/ ('downBut') or
        -- by pressing the @Down@ key on the active text area ('tedit').
        parseTree :: Action
        parseTree = do
            trees <- readIORef treesRef
            curr <- readIORef currRef
            fast <- readIORef fastRef
            treeposs <- readIORef treepossRef
            formula <- readIORef formulaRef

            if null trees then labBlue start
            else do
                let t = trees!!curr
                    enter _ _ [t] = enterText $ showTree fast t
                    enter b "" ts = if b then enter True "&" ts
                                         else enter False "<+>" ts
                    enter _ x ts  = enterText $ showTree fast $ F x ts
                if null treeposs
                then do enter formula "" [t]; labGreen treeParsed
                else do
                    sig <- getSignature
                    let ts@(u:us) = map (getSubterm1 t) treeposs
                        b = isFormula sig u
                    if null $ tail treeposs
                        then do enter b "" [u]; labGreen treeParsed
                        else if all (== b) $ map (isFormula sig) us
                                then do
                                    x <- ent `gtkGet` entryText
                                    enter b x $ addNatsToPoss ts
                                    labGreen $ init treeParsed ++ "s."
                                else labMag "Select either formulas or terms!"
        
        permuteSubtrees = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               let t = trees!!curr
                   p = emptyOrLast treeposs
               case getSubterm1 t p of
                    F x ts@(_:_:_) -> do
                         let n = length ts
                         modifyIORef permsRef
                           $ \perms -> upd perms n $ nextPerm $ perms n
                         perms <- readIORef permsRef
                         updateCurr $ replace1 t p $ F x $ map (ts!!) $ perms n
                         extendPT PermuteSubtrees
                         setProof (permutative x) False
                                  "PERMUTING THE SUBTREES" [p] permuted
                         drawCurr
                    _ -> done

        proofBackward = do
          restore <- readIORef restoreRef
          if restore then do oldTreeposs <- readIORef oldTreepossRef
                             writeIORef treepossRef oldTreeposs
                             writeIORef restoreRef False
                             drawCurr
          else do 
               checking <- readIORef checkingRef
               if checking then checkBackward
               else do proofPtr <- readIORef proofPtrRef
                       if proofPtr < 1 then labMag emptyProof
                       else do proof <- readIORef proofRef
                               let ps = peTreePoss $ proof!!proofPtr
                               modifyIORef proofPtrRef pred
                               proofPtr <- readIORef proofPtrRef
                               changeState proofPtr ps
                       proofTerm <- readIORef proofTermRef
                       proofTPtr <- readIORef proofTPtrRef
                       let n = searchback deriveStep $ take proofTPtr proofTerm
                       writeIORef proofTPtrRef $ if just n then get n else 0

        proofForward' = do
          checking <- readIORef checkingRef
          if checking then checkForward
          else do
               proofPtr <- readIORef proofPtrRef
               proofTerm <- readIORef proofTermRef
               let k = proofPtr+1
                   lg = length proofTerm
               proof <- readIORef proofRef
               if k >= length proof then labMag endOfProof else do
                         writeIORef proofPtrRef k
                         changeState k []
               proofTPtr <- readIORef proofTPtrRef
               when (proofTPtr < lg) $ do
                       proofTerm <- readIORef proofTermRef
                       let n = search deriveStep $ drop proofTPtr proofTerm
                       writeIORef proofTPtrRef $ if just n 
                                                  then proofTPtr+get n+1 else lg

        -- called by menu item /random labels/ from
        -- /transform selection/ menu or by pressing shift + L on active left
        -- lable ('lab').
        randomLabels :: Action
        randomLabels = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                str <- ent `gtkGet` entryText
                if null str then labRed "Enter labels!"
                else do
                    curr <- readIORef currRef
                    rand <- readIORef randRef
                    let (t,rand') = labelRandomly rand str $ trees!!curr
                    writeIORef treesRef $ updList trees curr t
                    writeIORef randRef rand'
                    extendPT RandomLabels
                    setProof False False "LABELING NODES" []
                        "The nodes have been labeled randomly."
                    drawCurr
        
        -- called by menu item /random tree/ from
        -- /transform selection/ menu or by pressing shift + @T@ on active left
        -- lable ('lab').
        randomTree :: Action
        randomTree = do
            str <- ent `gtkGet` entryText
            if null str then labRed "Enter labels!"
            else do
                rand <- readIORef randRef
                let (t,rand') = buildTreeRandomly rand str
                enterTree False t
                writeIORef randRef rand'
                extendPT RandomTree
                delay $ setProof False False "GENERATING A TREE" []
                                "A tree has been generated randomly."
        
        -- | Called by menu item /re-add/ from /specification/ menu.
        reAddSpec :: Action
        reAddSpec = do
            specfiles <- readIORef specfilesRef
            if null specfiles then labRed iniSpec
            else removeSpec >> addSpecWithBase (head specfiles)
        
        -- | Called by button /redraw/ ('clearS').
        redrawTree :: Action
        redrawTree = do
            treeposs <- readIORef treepossRef
            when (notnull treeposs) $ do
                writeIORef restoreRef True
            clearAndDraw

        reduceRegExp mode = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               sig <- getSignature
               trees <- readIORef treesRef
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               let ps = emptyOrAll treeposs
                   t = trees!!curr
                   ts = map (getSubterm t) ps
                   es = map (parseRE sig) ts
                   f (Just (e,_)) = showRE $ g e
                   g = case mode of 0 -> distributeReg
                                    1 -> reduceLeft
                                    _ -> reduceRight
               if any nothing es then labMag "Select regular expressions!"
               else do
                    updateCurr $ fold2 replace0 t ps $ map f es
                    extendPT $ ReduceRE mode
                    setProof False False "REDUCING THE REGULAR EXPRESSIONS" ps
                             regReduced
                    clearAndDraw

        refNodes = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else 
           do curr <- readIORef currRef
              treeposs <- readIORef treepossRef
              let t = trees!!curr
                  p:ps = emptyOrAll treeposs
                  f p = dropFromPoss p $ expand 0 t p
              if length treeposs < 2 
                 then labMag "Select at least two subterms!"
              else if all (eqTerm $ f p) $ map f ps then do
                      updateCurr $ reference t p ps
                      extendPT RefNodes
                      setProof True False "REFERENCING THE NODES" ps referenced
                      clearAndDraw
                   else labMag "Select roots of equal subterms!"

        -- | Finishes the 'moveNode' action. Called on right mouse button
        -- release on active canvas.
        releaseNode :: Action
        releaseNode = do
          treeposs <- readIORef treepossRef
          if null treeposs then labMag "Select a target node!"
          else do
              node <- readIORef nodeRef
              let p = last treeposs
              case node of
                   Just (_,q) | notnull q && p /= q -> do
                       trees <- readIORef treesRef
                       curr <- readIORef currRef
                       let t = replace0 (trees!!curr) q $ mkPos p
                       if p `elem` allPoss t then
                          do updateCurr t
                             let r = init q
                             extendPT ReleaseNode
                             setProof False False "INSERTING AN ARC" [r,p] $
                                                  arcInserted r p
                       else labRed $ show p ++ " does not exist!"
                       drawCurr
                       writeIORef nodeRef Nothing
                       canv `gtkSet` [ canvasCursor := LeftPtr ]
                   _ -> labMag "Select a non-root position!"
        
        -- | Finishes the 'moveSubtree' action. Called on left mouse button
        -- release on active canvas.
        releaseSubtree :: Action
        releaseSubtree = do
            isSubtree <- readIORef isSubtreeRef

            when (just isSubtree) $ do
                node <- readIORef nodeRef
                treeposs <- readIORef treepossRef
                subtree <- readIORef subtreeRef
                ctree <- readIORef ctreeRef

                let source = last treeposs
                    finish = do
                        drawTree (get subtree) (get ctree)
                            white white source
                        drawSubtrees
                case node of
                    Just (_,target) -> do
                        curr <- readIORef currRef
                        trees <- readIORef treesRef

                        let t = trees!!curr
                            u = getSubterm1 t source
                        if source == target then finish
                        else do
                            beep 
                            when (null target) $ changeMode u
                            replaceQuant u target
                            finishRelease (moveAndReplace t source t target)
                                source ReleaseSubtree
                    _ -> do
                        setTreeposs $ Remove source
                        finish
                resetCatch
        
        -- | Finishes the 'moveTree' action. Called on middle mouse button
        -- release on active canvas.
        releaseTree :: Action
        releaseTree = do
            isSubtree <- readIORef isSubtreeRef

            case isSubtree of
                Just True -> do
                    trees <- readIORef treesRef
                    curr <- readIORef currRef
                    treeposs <- readIORef treepossRef
                    varCounter <- readIORef varCounterRef
                    substitution <- readIORef substitutionRef
                    node <- readIORef nodeRef

                    let t = trees!!curr
                        p = last treeposs
                        u = getSubterm1 t p
                        z = 'z':show (varCounter "z")
                        (g,dom) = substitution
                        f t = finishRelease t p ReleaseTree
                    case node of
                        Just (_,q) -> when (p /= q) $ do
                            beep
                            f $ replace1 t q u
                        _ -> f $ replace0 t p $ V z
                    setSubst (g `andThen` for u z, dom `join1` z)
                    modifyIORef varCounterRef
                        $ \varCounter -> incr varCounter "z"
                    resetCatch
                Just False -> do
                    writeIORef penposRef Nothing
                    canv `gtkSet` [canvasCursor := LeftPtr ]
                    resetCatch
                _ -> done
        
        -- | Called by menu item /[remove in entry field].. for symbols/ from
        -- /axioms/ menu.
        removeAxiomsFor :: Action
        removeAxiomsFor = do
            str <- ent `gtkGet` entryText
            trees <- readIORef treesRef
            treeposs <- readIORef treepossRef
            axioms <- readIORef axiomsRef
            curr <- readIORef currRef
            let xs = if null trees || null treeposs then words str
                     else mapSet (label $ trees!!curr) treeposs
                axs = axiomsFor xs axioms
            if null axs then labRed $ noAxiomsFor xs
            else do
                writeIORef axiomsRef $ axioms `minus` axs
                axioms <- readIORef axiomsRef
                writeIORef simplRulesRef $ srules ["==","<==>"] axioms
                writeIORef transRulesRef $ srules ["->"] axioms
                labGreen $ axsRemovedFor xs
        
        -- | Called by menu item /remove in entry field/ from /axioms/ menu
        -- and menu items /[remove theorems].. in entry field/,
        -- /[remove conjects].. in entry field/
        -- and /[show conjects].. in entry field/ from menu /theorems/.
        removeClauses :: Int -> Action
        removeClauses n = do
            str <- ent `gtkGet` entryText
            numberedExps <- readIORef numberedExpsRef
            let (exps,_) = numberedExps
            case parse intRanges str of
                Just ns | all (< length exps) ns -> do
                    let ts = map (exps!!) ns
                    case n of
                      0 -> do
                          modifyIORef axiomsRef (`minus` ts)
                          axioms <- readIORef axiomsRef
                          writeIORef simplRulesRef $ srules ["==","<==>"] axioms
                          writeIORef transRulesRef $ srules ["->"] axioms
                          showAxioms True
                      1 -> do
                          modifyIORef theoremsRef (`minus` ts)
                          showTheorems True
                      2 -> do
                          modifyIORef conjectsRef (`minus` ts)
                          showConjects
                      _ -> do
                          modifyIORef termsRef (`minus` ts)
                          showTerms
                _ -> labMag enterNumbers
        
        -- | Called by menu item /remove conjects/ from menu /theorems/.
        removeConjects :: Action
        removeConjects = do
            writeIORef conjectsRef []
            labGreen "There are no conjectures."
        
        -- called by menu item /remove copies/ from menu /graph/.
        removeCopies :: Action
        removeCopies = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
              curr <- readIORef currRef
              treeposs <- readIORef treepossRef
              let t = trees!!curr
                  p = emptyOrLast treeposs
              if isHidden t || null p
              then labMag selectSub
              else do
                  writeIORef treesRef
                      $ updList trees curr $ removeAllCopies t p
                  extendPT RemoveCopies
                  setProof True False "REMOVING COPIES OF THE SUBTREE" [p]
                           copiesRemoved
                  clearAndDraw
        
        -- called by menu items /split cycles/ and
        -- /more tree arcs/ from menu /graph/.
        removeEdges :: Bool -> Action
        removeEdges b = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                curr <- readIORef currRef
                writeIORef treesRef $ updList trees curr $ f $ trees!!curr
                extendPT $ RemoveEdges b
                setProof False False "REMOVING EDGES" [] $ edgesRemoved b
                clearAndDraw
            where f = if b then removeCyclePtrs else moreTree

        -- called by menu item /remove node/ from menu /transform selection/.
        removeNode :: Action
        removeNode = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    p = emptyOrLast treeposs
                if isHidden t || null p
                    then labMag selectSub
                    else do
                        writeIORef treesRef
                            $ updList trees curr $ removeNonRoot t p
                        extendPT RemoveNode
                        setProof False False "REMOVING THE NODE" [p]
                                           "The selected node has been removed."
                        clearAndDraw
        
        -- called by menu item /remove other trees/ from tree menu.
        removeOthers :: Action
        removeOthers = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                treeMode <- readIORef treeModeRef
                if treeMode == "tree" then labGreen "There is only one tree."
                else do
                    curr <- readIORef currRef
                    modifyIORef solPositionsRef
                        $ \solPositions -> [0 | curr `elem` solPositions]
                    writeIORef treeModeRef "tree"
                    treeMode <- readIORef treeModeRef
                    writeIORef treesRef [trees!!curr]
                    modifyIORef counterRef $ \counter -> upd counter 't' 1
                    writeIORef currRef 0
                    extendPT RemoveOthers
                    setTreesFrame []
                    setProof (treeMode == "summand") False
                                 "REMOVING THE OTHER TREES" [] removedOthers
        
        -- called by menu item /remove path/ from menu
        -- /transform selection/ or by keypress @p@ on active left label
        -- ('lab').
        removePath :: Action
        removePath = do
            trees <- readIORef treesRef
            treeposs <- readIORef treepossRef
            if null trees || null treeposs then labMag selectSub
            else do
                curr <- readIORef currRef
                let p = last treeposs
                writeIORef treesRef
                    $ updList trees curr $ removeTreePath p $ trees!!curr
                extendPT RemovePath
                setProof False False "REMOVING THE PATH" [p]
                    ("The selected subtree and its ancestor"
                    ++ " nodes have been removed.")
                clearAndDraw
        
        -- | Called by menu item /remove map/ from menu /signature/.
        removeSigMap :: Action
        removeSigMap = do
            writeIORef signatureMapRef (id,[])
            labGreen iniSigMap
        
        -- | Used by 'reAddSpec'. Called by menu item /remove/ from menu
        -- /specification/.
        removeSpec :: Action
        removeSpec = do
            empty specfilesRef
            empty axiomsRef
            empty simplRulesRef
            empty transRulesRef
            empty theoremsRef
            empty conjectsRef
            empty termsRef
            writeIORef kripkeRef ([],[],[],[],[],[],[])
            writeIORef iniStatesRef []
            writeIORef noProcsRef 2
            writeIORef symbolsRef iniSymbols
            writeIORef signatureMapRef (id,[])
            where empty = flip writeIORef []
        
        -- called by menu item /remove/ from menu /substitution/.
        removeSubst :: Action
        removeSubst = do setSubst (V,[]); labGreen emptySubst
        
        -- called by menu item /remove/ from menu
        -- /transform selection/ or by pressing key @r@ with left label ('lab')
        -- active.
        removeSubtrees :: Action
        removeSubtrees = do
            trees <- readIORef treesRef
            curr <- readIORef currRef
            if null trees then labBlue start
            else do
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    lg = length trees
                    ps = if null treeposs then [[]] else minis (<<=) treeposs
                if ps == [[]] then
                    if lg < 2 then labRed "There is at most one tree."
                    else do
                        modifyIORef solPositionsRef
                            $ \solPositions -> shift curr solPositions
                        writeIORef treesRef $ context curr trees
                        modifyIORef counterRef $ \counter -> decr counter 't'
                        treeMode <- readIORef treeModeRef
                        let b = treeMode == "summand"
                        writeIORef treeModeRef
                            $ if lg == 2 then "tree" else treeMode
                        trees <- readIORef treesRef
                        writeIORef currRef
                            $ if curr < length trees then curr else 0
                        extendPT RemoveSubtrees 
                        setTreesFrame []
                        setProof b False "REMOVING THE CURRENT TREE" []
                            "The current tree has been removed."
                else if any null ps then labRed $ noApp "Subtree removal"
                    else do
                        sig <- getSignature
                        let qs = map init ps
                            q = head qs
                            u = getSubterm t q
                            r:rs = ps
                            b = last r == 0 && null rs && isImpl u && c ||
                                allEqual qs && (isDisjunct u && c ||
                                                isConjunct u && not c)
                            c = polarity True t q
                            t' = lshiftPos (foldl expandInto t ps) ps
                        simplifying <- readIORef simplifyingRef
                        writeIORef treesRef
                            $ updList trees curr $ if b && simplifying
                                                   then simplifyFix sig t'
                                                   else t'
                        extendPT RemoveSubtrees
                        setProof b True "REMOVING SUBTREES" ps removed
                        clearAndDraw
        
        -- | Called by menu item /remove theorems/ from menu /theorems/.
        removeTheorems :: Action
        removeTheorems = do
            writeIORef theoremsRef []
            labGreen "There are no theorems."
        
        -- | Called by menu item /rename/ from menu /substitution/.
        renameVar :: Action
        renameVar = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                str <- ent `gtkGet` entryText
                renameVar' str

        renameVar' :: String -> Action
        renameVar' str = do
            sig <- getSignature
            case parse (conjunct sig) str of
                Just (F "&" ts) -> proceed ts
                Just t -> proceed [t]
                _ -> labMag
                    "Enter a conjunction of equations between variables."
            where proceed ts =
                    case parseRenaming ts of
                        Just f -> do
                            trees <- readIORef treesRef
                            curr <- readIORef currRef
                            treeposs <- readIORef treepossRef
                            let t = trees!!curr
                                ps = emptyOrAll treeposs
                                ts = map (getSubterm t) ps
                                us = map (renameAll f) ts
                            writeIORef treesRef
                                $ updList trees curr $ fold2 replace t ps us
                            extendPT $ RenameVar str
                            setProof False False "RENAMING VARIABLES" ps
                                                "Variables have been renamed."
                            clearAndDraw
                        _ -> labMag "Enter equations between variables."
        
        -- used by renameVar
        
        -- | Called by menu item /label roots with entry/ from menu /graph/ or
        -- by pressing @l@ with left label ('lab') active.
        replaceNodes :: Action
        replaceNodes = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                str <- ent `gtkGet` entryText
                replaceNodes' $ unwords $ words str
        
        replaceNodes' :: String -> Action
        replaceNodes' x = do
            sig <- getSignature
            treeposs <- readIORef treepossRef
            let ps = emptyOrAll treeposs
                f p a = if p `elem` ps then x else a
                b = isFovar sig x
                chgV (F a []) | a == x && b     = V a
                chgV (V a)    | a == x && not b = leaf a
                chgV (F a ts) = F a $ map chgV ts
                chgV t        = t
            trees <- readIORef treesRef
            curr <- readIORef currRef
            updateCurr $ chgV $ mapTP f [] $ trees!!curr
            extendPT $ ReplaceNodes x
            drawCurr
            
        -- used by replaceNodes
        
        -- called from menu item
        -- /replace by tree of Solver@N@/ from menu /transform selection/.
        replaceOther :: Action
        replaceOther = do
            solve <- readIORef solveRef
            other <- getSolver solve
            tree <- getTreeR solve
            case tree of
                 Just t -> do treeposs <- readIORef treepossRef
                              let p = emptyOrLast treeposs
                              trees <- readIORef treesRef
                              curr <- readIORef currRef
                              updateCurr $ replace1 (trees!!curr) p t
                              extendPT ReplaceOther
                              setProof False False "REPLACING A SUBTREE" [p] $
                                       replaceIn other
                              clearAndDraw
                 _ -> labBlue $ startOther other
        
        -- | Used by 'instantiate' and 'releaseSubtree'.
        replaceQuant :: TermS -> [Int] -> Action
        replaceQuant u target = do
            trees <- readIORef treesRef
            curr <- readIORef currRef

            let t = trees!!curr
                x = label t target
            when (x /= root u)
                $ case isAny t x target of
                    Just q | polarity True t q -> replaceVar x u q
                    _ -> case isAll t x target of
                                Just q | polarity False t q -> replaceVar x u q
                                _ -> done

        -- | Called by menu item /replace by other sides of in/equations/
        -- from menu /transform selection/.
        replaceSubtrees :: Action
        replaceSubtrees = do
            treeposs <- readIORef treepossRef
            if null treeposs then labMag selectCorrectSubformula
            else do
                trees <- readIORef treesRef
                curr <- readIORef currRef
                let t = trees!!curr
                    p:ps = case treeposs of [p] -> [[],p]
                                            _ -> treeposs
                    u:us = map (getSubterm1 t) (p:ps)
                    ts = getOtherSides u p us ps
                maybe (labMag selectCorrectSubformula) (replaceSubtrees' ps) ts
        
        replaceSubtrees' :: [[Int]] -> [TermS] -> Action
        replaceSubtrees' ps ts = do
            sig <- getSignature
            extendPT $ ReplaceSubtrees ps ts
            trees <- readIORef treesRef
            curr <- readIORef currRef
            let t = fold2 replace1 (trees!!curr) ps ts
            maybeSimplify sig t
            makeTrees sig
            setTreesFrame []
            setProof True True "REPLACING THE SUBTREES" ps replacedTerm
            
        -- used by replaceSubtrees
        
        -- | Called by menu item /insert\/replace by text/ from menu
        -- /transform selection/ or by pressing @i@ while left lable ('lab') is
        -- active.
        replaceText :: Action
        replaceText = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do str <- getTextHere
                    replaceText' str
        
        replaceText' :: String -> Action
        replaceText' str = do
          sig <- getSignature
          treeposs <- readIORef treepossRef
          let ps = emptyOrAll treeposs
          case parseE (implication sig ++ term sig) str of
               Correct u -> finish u ps
               p -> incorrect p str $ illformed "term or formula"
          where finish u ps@(p:_) = do
                   trees <- readIORef treesRef
                   curr <- readIORef currRef
                   case changeTerm (trees!!curr) u ps of
                        Wellformed t -> do
                                   if null p then changeMode t else updateCurr t
                                   extendPT $ ReplaceText str
                                   setProof False False "REPLACING THE SUBTREES"
                                            ps textInserted
                                   clearAndDraw
                        Bad str -> labMag str
                        
        -- used by replaceText
        
        replaceVar :: String -> TermS -> [Int] -> Action
        replaceVar x u p = do
            trees <- readIORef treesRef
            curr <- readIORef currRef

            sig <- getSignature
            extendPT $ ReplaceVar x u p
            let t = trees!!curr
                F z [v] = getSubterm t p
                quant:xs = words z
                zs = xs `join` [ x | x <- frees sig u `minus` frees sig t
                               , nothing $ isAny t x p
                               , nothing $ isAll t x p
                               ]
                t1 = replace t p $ F (unwords $ quant:zs) [v>>>for u x]
            maybeSimplify sig t1
            makeTrees sig
            finish
            where str = showTerm0 u
                  msg = "SUBSTITUTING " ++ str ++ " FOR " ++ x
                  finish = do
                        setTreesFrame []
                        setProof True True msg [p]
                                         $ subMsg str x
        -- used by replaceQuant
        
        -- | Used by 'releaseSubtree' and 'releaseTree'.
        resetCatch :: Action
        resetCatch = do
            writeIORef nodeRef Nothing
            writeIORef penposRef Nothing
            writeIORef subtreeRef Nothing
            writeIORef suptreeRef Nothing
            writeIORef isSubtreeRef Nothing
            writeIORef firstMoveRef True
            canv `gtkSet` [ canvasCursor := LeftPtr ]
        
        resetLevel :: Action
        resetLevel = modifyIORef counterRef $ \counter -> upd counter 'c' 0

        -- called by menu item /reverse/ from menu /transform selection/.
        reverseSubtrees :: Action
        reverseSubtrees = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
              treeposs <- readIORef treepossRef
              if forsomeThereis (<<) treeposs treeposs
              then labMag "Select non-enclosing subtrees!"
              else do
                  curr <- readIORef currRef
                  let t = trees!!curr
                      ps = emptyOrAll treeposs
                      x = label t $ init $ head ps
                      b = allEqual (map init ps) && permutative x
                  case ps of
                      [p] -> do
                          let u = getSubterm t p
                              ps = succsInd p $ subterms u
                          finish t ps $ permutative $ root u
                      _ -> if any null ps
                           then labRed $ noApp "Subtree reversal"
                           else finish t ps b
          where finish t ps b = 
                   do updateCurr $ fold2 exchange t (f ps) $ f $ reverse ps
                      extendPT ReverseSubtrees
                      setProof b False "REVERSING THE LIST OF TREES" ps reversed
                      clearAndDraw
                   where f = take $ length ps`div`2
        
        -- | Used by 'narrowOrRewritePar'.
        rewritePar t sig k cls saveRedex used (p:ps) qs vc =
            if p `notElem` noRefPoss t -- || isVarRoot sig redex
            then rewritePar t sig k cls saveRedex used ps qs vc
            else do
                matching <- readIORef matchingRef
                axioms <- readIORef axiomsRef
                let cls1 = filterClauses sig redex $ filter unconditional cls
                    cls2 = if saveRedex then map copyRedex cls1 else cls1
                    (cls3,vc') = renameApply sig t vc cls2
                if even matching then
                    case applyAxsToTerm cls1 cls3 axioms redex sig vc of
                        (Sum reds vc,used') ->
                            rewritePar (replace t p $ mkSum reds) sig k cls
                                saveRedex (used `join` used') ps (p:qs) vc
                        _ -> rewritePar t sig k cls saveRedex used ps qs vc'
                else do
                    rand <- readIORef randRef
                    case applyAxsToTermR cls1 cls3 axioms rand redex sig vc of
                        (Sum reds vc,used',rand') -> do
                            writeIORef randRef rand'
                            rewritePar (replace t p $ mkSum reds) sig k cls
                                saveRedex (used `join` used') ps (p:qs) vc
                        _ -> rewritePar t sig k cls saveRedex used ps qs vc'
            where redex = getSubterm t p
        rewritePar t sig k cls saveRedex used _ qs vc =
            narrowPar t sig k cls saveRedex used [] qs vc
        
        -- | Used by 'checkProof' and 'stopRun'.
        runChecker :: Bool -> Action
        runChecker b = do
          when b $ do sp <- ent `gtkGet` entryText
                      let newSpeed = parse pnat sp
                      when (just newSpeed) $ writeIORef speedRef $ get newSpeed
                      checkingP <- readIORef checkingPRef
                      when (fst checkingP) $ setButton paint 3 runOpts
          runOpts (deriveBut, deriveButSignalRef)
          runProof <- runner $ do checkForward
                                  checkingP <- readIORef checkingPRef
                                  when (fst checkingP) showPicts
          writeIORef checkerRef runProof
          speed <- readIORef speedRef
          startRun runProof speed
          where runOpts (btn, cmd) = 
                                   do btn `gtkSet` [ buttonLabel := "stop run" ]
                                      replaceCommandButton cmd btn stopRun
        
        {- |
            Stores @str@ in a file. The file is stored in the programs user
            folder with the filename @file@. The filename is also prepend to
            the file as a comment.

            Used by 'saveSigMap', 'saveSpec', 'saveTree' and 'saveTrees'.
        -}
        saveFile :: FilePath -> String -> Action
        saveFile file str = do
            mkDir <$> home
            path <- userLib file
            writeFile path $ "-- " ++ file ++'\n':str
        
        -- | Called by button "save pic" ('saveBut').
        saveGraph dir = do
          dirPath <- pixpath dir
          let lg = length dir
              (prefix,suffix) = splitAt (lg-4) dir
          trees <- readIORef treesRef
          if null trees then labBlue start
          else if lg < 5 || suffix `notElem` words ".eps .png .gif" then do
                  trees <- readIORef treesRef
                  treeMode <- readIORef treeModeRef
                  fast <- readIORef fastRef
                  saveFile dir $ showTree fast $ joinTrees treeMode trees
                  labGreen $ saved "trees" dir
               else do
                    let f n = do
                              writeIORef currRef n
                              treeSlider `gtkSet` [rangeValue := fromIntegral n]
                              clearAndDraw
                              delay $ saveGraphDH True canv dir dirPath n
                    trees <- readIORef treesRef
                    case trees of
                      []  -> labBlue start
                      [_] -> do file <- savePic suffix canv dirPath
                                lab2 `gtkSet` [labelText := saved "tree" file]
                      _   -> do renewDir dirPath
                                saver <- runner2 f $ length trees-1
                                startRun saver 500
                                labGreen $ saved "trees" dirPath
            
        -- | Called by button "save pic to dir" ('saveDBut').
        saveGraphD :: Action
        saveGraphD = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do str <- ent `gtkGet` entryText
                  case str of 'p':str | just n -> writeIORef picNoRef $ get n
                                                  where n = parse nat str
                              _ -> done
                  picNo <- readIORef picNoRef
                  saveGraphDP True canv picNo

        saveGraphDP b screen n = do
          picDir <- readIORef picDirRef
          when (notnull picDir) $ do
            pp <- pixpath picDir
            saveGraphDH b screen picDir pp n
            modifyIORef picNoRef succ
        
        saveGraphDH :: Bool -> Canvas -> FilePath -> FilePath -> Int -> Action
        saveGraphDH b screen dir dirPath n = do
          mkHtml screen dir dirPath n
          let pic = if b then "tree" else "graph in the painter"
          lab2 `gtkSet` [labelText := saved pic $ mkFile dirPath n]

        -- used by 'draw' and 'saveGraphN'
       
        -- | Called by menu item /save proof to file/ from tree menu or by
        -- pressing key @s@ while left label ('lab') is active.
        saveProof :: Action
        saveProof = do
            proof <- readIORef proofRef
            if null proof then labMag "The proof is empty"
            else do
                trees <- readIORef treesRef
                solPositions <- readIORef solPositionsRef
                proofTerm <- readIORef proofTermRef
                -- TODO use filechooser widget instead.
                specfiles <- readIORef specfilesRef
                file <- ent `gtkGet` entryText
                filePath <- userLib $ head specfiles ++ '_':file
                let pfile = filePath ++ "P"
                    tfile = filePath ++ "T"
                write pfile $ '\n':showDeriv proof trees solPositions
                write tfile $ show proofTerm
                labGreen $ saved "proof" pfile ++ '\n':saved "proof term" tfile
            where write file str = writeFile file $ "-- " ++ file ++ '\n':str
        
        -- | Called by menu item /save map to file/ from menu /signature/.
        saveSigMap :: FilePath -> Action
        saveSigMap file = do
            signatureMap <- readIORef signatureMapRef
            saveFile file $ showSignatureMap signatureMap ""
            labGreen $ saved "signature map" file
        
        -- | Called by menu item /save to file/ from menu /specification/.
        saveSpec :: FilePath -> Action
        saveSpec file = do
            symbols <- readIORef symbolsRef
            axioms <- readIORef axiomsRef
            theorems <- readIORef theoremsRef
            conjects <- readIORef conjectsRef
            terms <- readIORef termsRef
            saveFile file $ showSignature (minus6 symbols iniSymbols)
                                    $ f "\naxioms:\n" showFactors axioms ++
                                      f "\ntheorems:\n" showFactors theorems ++
                                      f "\nconjects:\n" showFactors conjects ++
                                      f "\nterms:\n" showSum terms
            labGreen $ saved "specification" file
            where f str g cls = if null cls then "" else str ++ g cls
                
        -- | Called by all /[admit all simplifications and axioms] ../ menu
        -- items from menu /signature/.
        setAdmitted :: Bool -> Action
        setAdmitted block = do
            trees <- readIORef treesRef
            treeposs <- readIORef treepossRef
            str <- ent `gtkGet` entryText
            curr <- readIORef currRef
            setAdmitted' block $ if null trees || null treeposs then words str
                                 else map (label $ trees!!curr) treeposs
        
        -- | Called by /admit all simplifications and axioms/ from menu
        -- /signature/.
        setAdmitted' :: Bool -> [String] -> Action
        setAdmitted' block xs = do
            trees <- readIORef treesRef
            let msg = admitted block xs
            writeIORef constraintsRef (block,xs)
            if null trees then labGreen msg
            else do
                extendPT $ SetAdmitted block xs
                setProof True False "ADMIT" [] msg
        
        -- | Called by /collapse after simplify/ from menu
        -- /graph/.
        setCollapse :: Action
        setCollapse = do
            modifyIORef collSimplsRef not
            collSimpls <- readIORef collSimplsRef
            simplStrat <- readIORef simplStratRef
            let str = stratWord simplStrat
            stratBut `gtkSet`
              [buttonLabel := if collSimpls then str++"C" else str]
        
        -- | Used by 'buildSolve', 'checkForward', 'incrCurr',
        -- 'setCurrInSolve and 'simplify'.
        setCurr :: String -> Int -> Action
        setCurr msg n = do
            curr <- readIORef currRef
            if n /= curr then do
                writeIORef currRef n
                treeSlider `gtkSet` [ rangeValue := fromIntegral n ]
                setCurrInPaint paint n
                extendPT $ SetCurr msg n
                setProof True False "MOVED" [] msg
                clearAndDraw
            else labColorToPaint magback msg

        setCurrInSolve :: Int -> Action
        setCurrInSolve n = do
            trees <- readIORef treesRef
            when (n < length trees) $ setCurr newCurr n
            
        -- used by Epaint > remote
        
        setDeriveMode :: Action         -- used by buildSolve
        setDeriveMode = do
          checking <- readIORef checkingRef
          if checking then do
             checker <- readIORef checkerRef
             stopRun0 checker
             writeIORef checkingRef False
             isNew <- getNewCheck paint
             checkingP <- readIORef checkingPRef
             when (snd checkingP) $ do
                  setNewCheck paint
                  setButton paint 1 $ f "narrow/rewrite" narrow
                  setButton paint 2 $ f "simplify" simplify
                  setButton paint 3 $ \(btn,cmd) -> 
                                          do btn `gtkSet` [ buttonLabel := "" ]
                                             replaceCommandButton cmd btn $ done
             writeIORef checkingPRef (False,False)
             writeIORef speedRef 500
             quit `gtkSet` [ buttonLabel := "quit" ]
             replaceCommandButton quitSignalRef quit mainQuit
             simplifying <- readIORef simplifyingRef
             set $ if simplifying then "derive & simplify" else "derive"
          else do simplifying <- readIORef simplifyingRef
                  if simplifying then do writeIORef simplifyingRef False
                                         extendPT $ Simplifying False
                                         set "derive"
                                 else do writeIORef simplifyingRef True
                                         extendPT $ Simplifying True
                                         set "derive & simplify"
          where set str = do deriveBut `gtkSet` [ buttonLabel := str ]
                             replaceCommandButton deriveButSignalRef
                                                  deriveBut setDeriveMode
                f str act (btn,cmd) = 
                          do gtkSet btn [buttonLabel := str]
                             replaceCommandButton cmd btn $ do remote paint; act
                                                               showTreePicts

          -- Set font of text area ('tedit'), entry field ('ent'), left label
          -- ('lab') and right label ('lab2').
          -- Called by button 'fontBut' on font change.
        
        setFont :: FontDescription -> Action
        setFont fo = do
            writeIORef fontRef fo
            size <- fontDescriptionGetSize fo
            -- By changing the font size slider, setFontSize is called, which
            -- handles the font changing of the GUI elements.
            when (just size) $ fontSize `gtkSet` [rangeValue := get size]
            trees <- readIORef treesRef
            when (notnull trees) drawCurr
        
        {-  Set font size of text area ('tedit'), entry field ('ent'), left
            label ('lab') and right label ('lab2').
            Called by scale 'fontSize'.
        -}
        setFontSize :: Action
        setFontSize = do
            fo <- readIORef fontRef
            size <- fontSize `gtkGet` rangeValue
            fontDescriptionSetSize fo size
            fo' <- fontDescriptionCopy fo
            fontDescriptionSetFamily fo' "Monospace"
            widgetOverrideFont tedit $ Just fo'
            widgetOverrideFont ent $ Just fo'
            fontDescriptionSetFamily fo' "Sans"
            fontDescriptionSetStyle fo' StyleItalic
            widgetOverrideFont lab $ Just fo'
            widgetOverrideFont lab2 $ Just fo'
        
        -- | The @opts@ function sets the behavior of the forward button
        -- ('forwBut').
        -- Exported by public 'Epaint.Solver' method 'Epaint.setForw.
        
        setForw :: ButtonOpts -> Action
        setForw opts = opts (forwBut,forwButSignalRef) 
        {-
        The behavior of the setForw function changed with the port from
        O'Haskell/Tcl to GTK+. Originally @opts@ was a list of button options.
        Since GTK+ works different and the option system also was strongly mixed
        with the object oriented inheritance system, this function now takes a
        function as parameter, which handles the change in the button behavior.
        -}
        
        -- | Changes the picture interpreter. This determines how the painter is
        -- handling the graph on a call.
        -- Used by 'callEnum' and 'checkProof'. Called by interpreter button.
        
        setInterpreter :: String -> Action
        setInterpreter eval = do
          writeIORef picEvalRef eval
          interpreterLabel `gtkSet` [ labelLabel := eval ]
          str <- ent `gtkGet` entryText
          sig <- getSignature
          let drawFun = case parse (term sig) str of 
                             Just t | isDefunct sig $ fst $ unCurry t -> t
                             _ | str == "expand" -> leaf str
                               | True            -> leaf "id"
          writeIORef drawFunRef drawFun
          labGreen $ newInterpreter eval drawFun
        
        -- | Used by 'changeMode', 'setDeriveMode' and 'setTreeposs'. Called by
        -- button 'matchBut'.
        
        setNarrow chgMatch = do
          treeposs <- readIORef treepossRef
          trees <- readIORef treesRef
          curr <- readIORef currRef
          formula <- readIORef formulaRef
          sig <- getSignature
          matching <- readIORef matchingRef
          let nar = formula || notnull treeposs &&
                    treeposs `subset` boolPositions sig (trees!!curr)
              set str1 str2 = do
                      matchBut `gtkSet` [buttonLabel := str1]
                      randomBut `gtkSet` [buttonLabel := str2]
                      narrowBut `gtkSet`
                        [buttonLabel := if nar then "narrow" else "rewrite"]
              oldMatch = matching
          when (chgMatch == 1 && nar) $ do
                                       modifyIORef matchingRef
                                         $ \matching -> (matching+2) `mod` 4
                                       extendPT $ Matching oldMatch matching
          when (chgMatch == 2) $ do
                  modifyIORef matchingRef
                    $ \matching -> matching+if even matching then 1 else -1
                  extendPT $ Matching oldMatch matching
          case matching of
            0 -> set "match" "all"
            1 -> set "match" "random"
            2 -> set "unify" "all"
            _ -> set "unify" "random"
        
        setNewTrees :: [TermS] -> String -> Action
        setNewTrees ts typ = do
            writeIORef treesRef ts
            modifyIORef counterRef $ \counter -> upd counter 't' $ length ts
            writeIORef treeModeRef typ
            initialize [] "trees"
            setTreesFrame []

        setPicDir :: Bool -> Action
        setPicDir b = do
          dir <- ent `gtkGet` entryText
          writeIORef picDirRef $ if b || null dir then "picDir" else dir
          picDir <- readIORef picDirRef
          lab2 `gtkSet` [labelText := picDir ++ " is the current directory"]
          pp <- pixpath picDir
          mkDir pp
          writeIORef picNoRef 0

        setProof :: Bool -> Bool -> String -> [[Int]] -> String -> Action
        setProof correct simplPossible msg ps labMsg = do
          proof <- readIORef proofRef
          proofPtr <- readIORef proofPtrRef
          trees <- readIORef treesRef
          curr <- readIORef currRef
          counter <- readIORef counterRef
          ruleString <- readIORef ruleStringRef
          newTrees <- readIORef newTreesRef
          formula <- readIORef formulaRef
          matching <- readIORef matchingRef
          simplifying <- readIORef simplifyingRef
          refuting <- readIORef refutingRef
          treeMode <- readIORef treeModeRef
          varCounter <- readIORef varCounterRef
          solPositions <- readIORef solPositionsRef
          substitution <- readIORef substitutionRef
          newPreds <- readIORef newPredsRef
          joined <- readIORef joinedRef
          constraints <- readIORef constraintsRef
          fast <- readIORef fastRef
          simplStrat <- readIORef simplStratRef
          let oldProofElem = proof!!proofPtr
              n = counter 'd'
              msgAE = msg `elem` words "ADMIT REFUTE SAFE"
              msgSP = msg == "SPLIT"
              msgMV = msg == "MOVED" || msg == "JOIN"
              msgAD = take 4 msg == "ADDC"
              t = trees!!curr
              str = if msgAE then labMsg
                    else if msgSP
                         then labMsg ++ show (length trees) ++ ' ':treeMode ++
                              's':'.':showCurr fast t treeMode
                    else if msgMV then labMsg ++ showCurr fast t treeMode
                    else if msgAD then addAxsMsg msg
                    else if take 4 msg == "ADDI"
                         then showNew fast (length trees) t (addAxsMsg msg) n ps
                                      treeMode
                    else if newTrees
                         then showNew fast (length trees) t msg n ps treeMode
                    else showPre fast t msg n ps treeMode
              str0 = "\nThe axioms have been MATCHED against their redices."
                  `onlyif` matching < 2
              str1 = ("\nThe reducts have been simplified " ++
                      stratWord simplStrat ++ ".") `onlyif` simplifying
              str2 str = "\nFailure "++ str ++" have been removed."
                      `onlyif` refuting
              str3 =
                  if correct then case ruleString of
                                      "NARROWING" -> str0++str1++str2 "atoms"
                                      "REWRITING" -> str1++str2 "terms"
                                      _ -> str1 `onlyif` simplPossible
                  else "\nCAUTION: This step may be semantically incorrect!"
              (msgP,msgL) = if null str3 then (str,labMsg)
                                         else (str++'\n':str3,labMsg++str3)
              noChange = newTrees || msgAE || msgSP || msgMV || msgAD ||
                         trees /= peTrees oldProofElem ||
                         notnull msgL && head msgL == ' '
              msg1 = msgL ++ if noChange then ""
                                         else "\nThe "++ formString formula ++
                                              " has not been modified."
              u = joinTrees treeMode trees
              us = map (joinTrees treeMode . peTrees) proof
              pred =  search (== u) us
              cmsg = if noChange || nothing pred then ""
                     else "\nThe " ++ formString formula ++
                          " coincides with no. " ++ show (get pred)
              msg3 = msg1 ++ cmsg
          when (null ruleString || n > 0) $ do
             modifyIORef proofPtrRef succ
             proofPtr <- readIORef proofPtrRef
             perms <- readIORef permsRef
             axioms <- readIORef axiomsRef
             theorems <- readIORef theoremsRef
             newAxioms <- readIORef newAxiomsRef
             newTheorems <- readIORef newTheoremsRef
             let next = ProofElem
                      { peMsg = msgP ++ cmsg
                      , peMsgL = msg3
                      , peAxioms = axioms
                      , peTheorems = theorems
                      , peNewPreds = newPreds
                      , peNewAxioms = newAxioms
                      , peNewTheorems = newTheorems
                      , peTreeMode = treeMode
                      , peTrees = trees
                      , peTreePoss = ps
                      , peCurr = curr
                      , pePerms = perms
                      , peVarCounter = varCounter
                      , peSolPositions = solPositions
                      , peJoined = joined
                      , peSubstitution = substitution
                      , peConstraints = constraints
                      }
             modifyIORef proofRef
               $ \proof -> take proofPtr proof++[next]
          writeIORef newTreesRef False
          writeIORef ruleStringRef ""
          labColorToPaint greenback $ show proofPtr ++ ". " ++ msg3
        
        setQuit :: ButtonOpts -> Action
        setQuit opts = opts (quit, quitSignalRef)
        
        -- | Used by 'addSubst', 'changeState', 'initialize', 'releaseTree',
        -- 'removeSubst' and 'unifyAct'. Exported by public 'Epaint.Solver'
        -- method 'Epaint.setSubst.
        
        setSubst :: (String -> TermS,[String]) -> Action
        setSubst subst@(_,dom) = do
            setBackground applyBut $ if null dom then blueback else redback
            domMenu <- getMenu "domMenu" -- Note [DomMenu]
            containerForeach domMenu (containerRemove domMenu) -- Note [DomMenu]
            mapM_ (mkButF domMenu applySubstTo) dom
            writeIORef substitutionRef subst
        
        {- Note [DomMenu]
        ~~~~~~~~~~~~~~~~~
        
        Since Gtk+3 MenuButton is not implemented by Haskells gtk3 package,
        it is not possible to access the subToBut button. Instead the domMenu
        has become part of the glade file and will never be replaced. Instead
        of creating a new domMenu every time setSubst is called, all items
        are removed.
        -}

        -- | Used by 'showSubtreePicts', 'showTreePicts', 'simplify',
        -- 'enterTree and 'narrow''.
        setTime :: Action
        setTime = do
            (_, t) <- readIORef timesRef
            time <- getCPUTime
            writeIORef timesRef (time, t)
        
        -- | Used by 'catchSubtree', 'clearTreeposs', 'releaseSubtree',
        -- 'setSubtrees', 'setTreesFrame', 'showChanged' and 'unifyAct'.
        setTreeposs :: PossAct -> Action
        setTreeposs step = do
          treeposs <- readIORef treepossRef
          writeIORef oldTreepossRef treeposs
          writeIORef treepossRef $ case step of
                                  Add ps -> treeposs++ps
                                  Remove p -> treeposs`minus1`p
                                  Replace ps -> ps
          treeposs <- readIORef treepossRef
          oldTreeposs <- readIORef oldTreepossRef
          extendPT $ Mark oldTreeposs treeposs
          setNarrow 0
        
        -- | Used by 'simplify', 'splitTree', 'applyInd', 'applyTheorem',
        -- 'changeState', 'enterTree, 'narrowLoop', 'narrowPar',
        -- 'narrowSubtree', 'removeOthers', 'removeSubtrees',
        -- 'replaceSubtrees'', 'replaceVar' and 'setNewTrees'.
        setTreesFrame :: [[Int]] -> Action
        setTreesFrame ps = do
            trees <- readIORef treesRef
            treeMode <- readIORef treeModeRef
            curr <- readIORef currRef
            formula <- readIORef formulaRef

            let lg = length trees
                str = case treeMode of "tree" -> formString formula
                                       _ -> show lg ++ ' ':treeMode ++ "s"
            rangeSetRange treeSlider 0 $ fromIntegral (lg-1)
            treeSlider `gtkSet` [ widgetSensitive := True
                             , rangeValue := fromIntegral curr
                             ]
            setCurrInPaint paint curr
            termBut `gtkSet` [ labelText := str ]
            setTreeposs $ Replace ps
            drawCurr
        
        -- | Change varCounter state. Used by 'applyClause', 'applyCoinduction',
        -- 'applyTransitivity', 'compressAxioms', 'compressClauses',
        -- 'createInvariant', 'flattenImpl', 'showEqsOrGraph' and 'stretch'.
        setZcounter :: Int -> Action
        setZcounter n = modifyIORef varCounterRef
            $ \varCounter -> upd varCounter "z" n
        
        -- called by menu item /shift pattern to rhs/
        -- from menu /transform selection/.
        shiftPattern :: Action
        shiftPattern = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
              treeposs <- readIORef treepossRef
              curr <- readIORef currRef
              let [p,q] = case treeposs of [r] -> [[],r]; _ -> treeposs
                  r = drop (length p) q
                  t = trees!!curr
              if null treeposs || length treeposs > 2 || not (p << q)
              then labMag "Select a (conditional) equation and a pattern!"
              else do
                  sig <- getSignature
                  case makeLambda sig (getSubterm1 t p) r of
                       Just cl -> do
                                  updateCurr $ replace1 t p cl
                                  extendPT ShiftPattern
                                  setProof True False "SHIFTING A PATTERN" [[]]
                                           "A pattern has been shifted."
                                  clearAndDraw
                       _ -> labMag "The selected pattern cannot be shifted."
        
        -- called by menu item /move up quantifiers/
        -- from menu /transform selection/. 
        shiftQuants :: Action
        shiftQuants = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    ps = treeposs
                if null ps || any null ps then errorMsg
                else do
                    let qs = map init ps
                        ts = map (getSubterm1 t) ps
                        qvars = map (\t -> alls t++anys t) ts
                    if allEqual qs && any notnull qvars then do
                        sig <- getSignature
                        let q = head qs
                            u = getSubterm1 t q
                            x = root u
                        if isF u && x `elem` words "==> Not & |" then do
                            varCounter <- readIORef varCounterRef
                            let (as,es,v,vc) = moveUp sig varCounter x
                                                    (subterms u) $ map last ps
                                v' = simplifyFix sig v
                            finish (replace1 t q $ mkAll as $ mkAny es v') ps vc
                        else errorMsg
                    else errorMsg
            where finish t ps vc = do
                            updateCurr t
                            writeIORef varCounterRef vc
                            extendPT ShiftQuants
                            setProof True False "MOVING UP QUANTIFIERS" ps moved
                            clearAndDraw
                  errorMsg = labRed $ noApp "Move up quantifiers"
        
        -- Called by menu item /shift subformulas/ from menu
        -- /transform selection/. 
        shiftSubs :: Action
        shiftSubs = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                treeposs <- readIORef treepossRef
                if null treeposs || any null treeposs
                then labRed $ noApp "Shift subformulas"
                else shiftSubs' treeposs
        
        shiftSubs' :: [[Int]] -> Action
        shiftSubs' ps = do
            sig <- getSignature
            trees <- readIORef treesRef
            curr <- readIORef currRef
            case shiftSubformulas sig (trees!!curr) ps of
                Just t -> do
                    writeIORef treesRef $ updList trees curr t
                    extendPT $ ShiftSubs ps
                    setProof True False "SHIFTING SUBFORMULAS" ps shifted
                    clearAndDraw
                _ -> labRed $ noApp "Shift subformulas"
                
        -- used by shiftSubs
        
        -- | Used by 'removeClauses'. Called by menu items /show/ and
        -- /[show].. in text field of SolverN/ from menu /axioms/.
        showAxioms :: Bool -> Action
        showAxioms b = do
            axioms <- readIORef axiomsRef
            if null axioms then labGreen "There are no axioms."
            else if b then do enterFormulas axioms
                              labGreen $ see "axioms"
                      else do solve <- readIORef solveRef; bigWinR solve
                              enterFormulasR solve axioms
        
        -- | Called by menu item /[show].. for symbols/ from menu /axioms/ or by
        -- pressing button @x@ while left label ('lab') is active.
        showAxiomsFor :: Action
        showAxiomsFor = do
          str <- ent `gtkGet` entryText
          treeposs <- readIORef treepossRef
          trees <- readIORef treesRef
          curr <- readIORef currRef
          axioms <- readIORef axiomsRef
          let xs = if null trees || null treeposs && notnull str then words str
                   else mapSet (label $ trees!!curr) $ emptyOrAll treeposs
              axs = axiomsFor xs axioms
          if null axs then labRed $ noAxiomsFor xs
          else do enterFormulas axs
                  labGreen $ see $ "axioms for " ++ showStrList xs
        
        -- | Called by menu item /show changed/ from tree menu.
        
        showChanged :: Action
        showChanged = do
            proofPtr <- readIORef proofPtrRef
            if proofPtr <= 0 then labMag "The proof is empty."
            else do
                proof <- readIORef proofRef
                curr <- readIORef currRef
                writeIORef restoreRef True
                let proofElem = proof!!(proofPtr-1)
                    k = peCurr proofElem
                    ts = peTrees proofElem
                if k == curr then do
                    trees <- readIORef treesRef
                    let ps = changedPoss (ts!!k) (trees!!k)
                    setTreeposs $ Replace ps
                    drawCurr
                else labMag newCurr
        
        -- | Used by 'removeClauses'. Called by menu item /show conjects/ from
        -- menu /theorems/.
        
        showConjects :: Action
        showConjects = do
            conjects <- readIORef conjectsRef
            if null conjects then labGreen "There are no conjectures."
            else do enterFormulas conjects
                    labGreen $ see "conjectures"
        
        -- | Called by menu item /coordinates/ from menu /nodes/.
        
        showCoords :: Action
        showCoords = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                writeIORef restoreRef True
                curr <- readIORef currRef
                ctree <- readIORef ctreeRef
                drawThis "" (cTree (trees!!curr) $ get ctree) []
        
        -- | Called by menu item /cycle targets/ from menu /nodes/.
        
        showCycleTargets :: Action
        showCycleTargets = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                writeIORef restoreRef True
                trees <- readIORef treesRef
                curr <- readIORef currRef
                let t = trees!!curr
                drawThis "green" t $ cycleTargets t

        showFixPositions = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               writeIORef restoreRef True
               sig <- getSignature
               trees <- readIORef treesRef
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               let t = trees!!curr
                   p = emptyOrLast treeposs
               drawThis "green" t $ map (p++) $ labPoss isFix $ getSubterm t p

        -- | Called by menu item /greatest lower bound/ from menu /nodes/.
        
        showGlb :: Action
        showGlb = do
            treeposs <- readIORef treepossRef
            if null treeposs then labMag "Select subtrees!"
            else do
                writeIORef restoreRef True
                trees <- readIORef treesRef
                curr <- readIORef currRef
                drawThis "green" (trees!!curr) [glbPos treeposs]

        showKripke m = do
          sig <- getSignature
          let [sts0,labs,ats] = showSLA sig
          if null sts0 then labMag "The Kripke model is empty!"
          else do
               iniStates <- readIORef iniStatesRef
               let sts = if m < 5 then map show $ indices_ sts0 else sts0
                   pairs = mkPairs sts sts $ trans sig
                   trips = mkTrips sts labs sts $ transL sig
                   trGraph = if null iniStates then relToGraphAll pairs trips
                             else relToGraph pairs trips $ map f iniStates
                   f = if m < 5 then show . getInd (states sig) else showTerm0
                   atGraph =
                       if trGraph == emptyGraph then emptyGraph
                       else outGraph sts labs ats (out sig) (outL sig) trGraph
                   decorateTrGraph = do
                       trsOnCanvas <- readIORef trsOnCanvasRef
                       treeposs <- readIORef treepossRef
                       if trsOnCanvas && notnull treeposs then do
                          let f p a = if p `elem` treeposs && a `elem` sts
                                      then label atGraph p else a
                          trees <- readIORef treesRef
                          curr <- readIORef currRef
                          updateCurr $ mapTP f [] $ trees!!curr
                          writeIORef trsOnCanvasRef False
                          drawCurr
                       else labMag "Show state transitions first!"
                   paintGraph t = do
                       spread <- readIORef spreadRef
                       drawFun <- readIORef drawFunRef
                       let mkPict sizes = widgetTree sig sizes spread $
                                                     applyDrawFun sig drawFun t
                       pict <- runT $ mkPict sizes0
                       if nothing pict then labMag "There are no transitions."
                       else do
                           font <- readIORef fontRef
                           sizes <- mkSizes canv font $ stringsInPict $ get pict
                           spread <- readIORef spreadRef
                           pict <- runT $ mkPict sizes
                           curr <- readIORef currRef
                           callPaint paint [get pict] [curr] False curr "tree" 
                                     spread "white"
                   finish t = do
                       trees <- readIORef treesRef
                       if null trees then enterTree False t
                       else do
                            updateCurr t
                            extendPT ShowKripke
                            setProof False False "SHOWING A GRAPH" [[]] entered
                            clearAndDraw
               solve <- readIORef solveRef
               case m of 0 -> do finish trGraph; writeIORef trsOnCanvasRef True
                         1 -> decorateTrGraph
                         2 -> finish $ colorClasses sig trGraph
                         3 -> paintGraph trGraph
                         4 -> do bigWinR solve; enterTreeR solve False trGraph
                         5 -> do finish trGraph; writeIORef trsOnCanvasRef True
                         6 -> decorateTrGraph
                         7 -> finish $ colorClasses sig trGraph
                         8 -> paintGraph trGraph
                         9 -> do bigWinR solve; enterTreeR solve False trGraph
                         10 -> finish atGraph
                         11 -> paintGraph atGraph
                         _ -> do bigWinR solve; enterTreeR solve False atGraph

        -- | Called by all /show matrix/ menu items from menu /graph/.
        
        showMatrix mode = do
          trees <- readIORef treesRef
          if mode `elem` [0,5] && null trees then labBlue start
          else do
               sig <- getSignature
               treeposs <- readIORef treepossRef
               trees <- readIORef treesRef
               curr <- readIORef currRef
               let [sts,labs,ats] = showSLA sig
                   inds = map show $ indices_ sts
                   p:ps = emptyOrAll treeposs
                   t = getSubterm1 (trees!!curr) p
               let mkMat b  = case parseEqs t of        -- matrix from equations
                                   Just eqs -> f b $ eqsToGraphAll eqs
                                   _ -> f b t           -- matrix from graph
                   f True t = mat $ BoolMat dom1 dom2 pairs where
                              (dom1,dom2) = sortDoms pairs
                              pairs = deAssoc $ graphToRel labs t
                   f _ t    = mat $ ListMat dom1 dom2 trips where
                              (dom1,dom2) = sortDoms $ map (pr1 *** pr2) trips
                              trips = graphLToRel labs t
                   mkBM s s' tr = mat $ BoolMat (g fst) (g snd) pairs
                                  where pairs = deAssoc $ mkPairs s s' tr
                                        g pr = mkSet $ map pr pairs
                   mkLM s s' tr = mat $ ListMat s' labs' trips
                                  where trips = mkTrips s labs s' tr
                                        labs' = mkSet [x | (_,x,_:_) <- trips]
                   u = case mode of 0 -> mkMat True
                                    1 -> mkBM inds inds $ trans sig
                                    2 -> mkBM sts sts $ trans sig
                                    3 -> mkBM ats sts $ value sig
                                    4 -> mkBM sts ats $ out sig
                                    5 -> mkMat False
                                    6 -> mkLM inds inds $ transL sig
                                    7 -> mkLM sts sts $ transL sig
                                    8 -> mkLM ats sts $ valueL sig
                                    _ -> mkLM sts ats $ outL sig
               modifyIORef treesRef $ \ts -> updList ts curr $ replace1 t p u
               clearAndDraw
        
        -- called by all /(...) numbers/ menu items from /nodes/ menu
        
        showNumbers :: Int -> Action
        showNumbers m = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                writeIORef restoreRef True
                col <- ent `gtkGet` entryText
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    p = emptyOrLast treeposs
                    u = getSubterm1 t p
                    c = case parse color col of Just d -> d; _ -> black
                    (v,_) = order c label u
                drawThis "" (replace1 t p v) []
         where label (RGB 0 0 0) n = show n
               label c n           = show c++'$':show n
               order = case m of 1 -> levelTerm  -- "level numbers"
                                 2 -> preordTerm -- "preorder positions"
                                 3 -> heapTerm   -- "heap positions"
                                 _ -> hillTerm   -- "hill positions"
        
        showPicts :: Action             -- called by button paint
        showPicts = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               checking <- readIORef checkingRef
               if checking then do
                  modifyIORef checkingPRef $ \checkingP -> (True,snd checkingP)
                  isNew <- getNewCheck paint
                  if isNew then do buildPaint paint True
                                   setButton paint 3 runOpts
                                   showTreePicts
                           else showTreePicts
               else do treeposs <- readIORef treepossRef
                       if null treeposs then showTreePicts else showSubtreePicts
          where runOpts (btn,cmd) = do
                                  btn `gtkSet` [buttonLabel := "run proof"]
                                  replaceCommandButton cmd btn $ runChecker True
        
        showPolarities :: Action        -- called by button nodes > polarities
        showPolarities = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                writeIORef restoreRef True
                curr <- readIORef currRef
                let t = trees!!curr
                    ps = polTree True [] t
                drawThis "" (colorWith2 "green" "red" ps t) []
        
        showPositions :: Action         -- called by button nodes > positions
        showPositions = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                writeIORef restoreRef True
                curr <- readIORef currRef
                let t = trees!!curr
                drawThis "red" (mapT f $ posTree [] t) $ labPoss isPos t
            where f = unwords . map show
        
        showPreds :: Action             -- called by button nodes > predecessors
        showPreds = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                writeIORef restoreRef True
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    ps = concatMap (nodePreds t) $ emptyOrAll treeposs
                drawThis "green" t ps
        
        -- | Called by both /show proof/ menu items from tree menu.
        showProof :: Bool -> Action
        showProof b = do
            proof <- readIORef proofRef
            if null proof then labMag "The proof is empty."
            else do
                trees <- readIORef treesRef
                solPositions <- readIORef solPositionsRef
                let str = '\n':showDeriv proof trees solPositions
                if b then do enterText str; labGreen $ see "proof"
                     else do solve <- readIORef solveRef; bigWinR solve
                             enterTextR solve str
        
        -- called by both /show proof term/ menu items from tree menu.
        showProofTerm :: Action
        showProofTerm = do
          proofTerm <- readIORef proofTermRef
          if null proofTerm then labMag "The proof term is empty."
          else do labGreen $ see "proof term"
                  enterRef
        
        -- called by all /show relation/ menu items from menu /graph/.
        showRelation :: Int -> Action
        showRelation mode = do
          sig <- getSignature
          trees <- readIORef treesRef
          curr <- readIORef currRef
          treeposs <- readIORef treepossRef
          let [sts,labs,ats] = showSLA sig
              inds = map show $ indices_ sts
              t = trees!!curr
              p = emptyOrLast treeposs
              u = getSubterm1 t p
              f b = if null trees then labBlue start else act2 b labs t p u
          case mode of 0 -> f True
                       1 -> act1 $ mkRelConstsI inds inds $ trans sig
                       2 -> act1 $ mkRelConstsI sts sts $ trans sig
                       3 -> act1 $ mkRelConstsI ats sts $ value sig
                       4 -> act1 $ mkRelConstsI sts ats $ out sig
                       5 -> f False
                       6 -> act1 $ mkRel2ConstsI inds labs inds $ transL sig
                       7 -> act1 $ mkRel2ConstsI sts labs sts $ transL sig
                       8 -> act1 $ mkRel2ConstsI ats labs sts $ valueL sig
                       _ -> act1 $ mkRel2ConstsI sts labs ats $ outL sig
          where act1 ts = enterTree False $ h ts
                act2 b labs t p u = do
                       let v =  case parseEqs u of Just eqs -> eqsToGraphAll eqs
                                                   _ -> u
                       updateCurr $ replace1 t p $ h $
                                     if b then mkRelConsts $ graphToRel labs v
                                          else mkRel2Consts $ graphLToRel labs v
                       clearAndDraw
                g t@(F "()" ts) us = case last ts of F "[]" [] -> us
                                                     _ -> t:us
                h = mkList . foldr g []
        
        -- | Called by menu item /show sig/ from menu /signature/.
        showSig :: Action
        showSig = do
          symbols <- readIORef symbolsRef
          enterText $ showSignature (minus6 symbols iniSymbols) ""
          constraints <- readIORef constraintsRef
          let (block,xs) = constraints
          refuting <- readIORef refutingRef
          safeSimpl <- readIORef safeSimplRef
          labGreen $ see "signature" ++'\n':admitted block xs
                                      ++'\n':refuteMsg refuting
                                      ++'\n':safeMsg safeSimpl

        
        -- | Called by menu item /show map/ from menu /signature/.
        showSigMap :: Action
        showSigMap = do
            signatureMap <- readIORef signatureMapRef
            if null $ snd signatureMap then labGreen iniSigMap
            else do
                enterText $ showSignatureMap signatureMap ""
                labGreen $ see "signature map"
        
        -- | Called by menu item /[show].. solutions/ from menu /substitution/.
        showSolutions :: Action
        showSolutions = do
            sig <- getSignature
            formula <- readIORef formulaRef
            trees <- readIORef treesRef
            labGreen $ solved $ if formula then solPoss sig trees else []
        
        -- | Called by menu items /show/ and /[show].. in text field of SolverN/
        -- from menu /substitution/.
        showSubst :: Int -> Action
        showSubst mode = do
          (f,dom) <- readIORef substitutionRef
          let ts = substToEqs f dom
              typ = if length ts == 1 then "tree" else "factor"
          if null dom then labGreen emptySubst
          else do case mode of 0 -> do enterFormulas ts
                                       labGreen $ see "substitution"
                               1 -> do solve <- readIORef solveRef
                                       bigWinR solve; enterFormulasR solve ts
                               _ -> do solve <- readIORef solveRef
                                       bigWinR solve; setNewTreesR solve ts typ

        -- showSubtreePicts prepares selected subtrees of the current tree for 
        -- being displayed in the painter window and is used by showPicts.

        showSubtreePicts :: Action
        showSubtreePicts = do
          sig <- getSignature
          eval <- getInterpreter
          trees <- readIORef treesRef
          curr <- readIORef currRef
          treeposs <- readIORef treepossRef
          drawFun <- readIORef drawFunRef
          spread <- readIORef spreadRef
          let -- t = mapConsts chgDouble $ trees!!curr
              mkPicts sizes = map (f sizes) treeposs 
              f sizes = eval sizes spread . applyDrawFun sig drawFun
                                          . closeGraph (trees!!curr)
          font <- readIORef fontRef
          picts <- mapM runT $ mkPicts sizes0
          sizes <- mkSizes canv font $ concatMap (stringsInPict . getPict) picts
          setTime
          picts <- mapM runT $ mkPicts sizes
          picEval <- readIORef picEvalRef
          spread <- readIORef spreadRef
          back <- ent `gtkGet` entryText
          callPaint paint [concatMap getPict picts] [] True curr picEval spread
                    back

        -- | Called by menu item /successors/ from menu /nodes/.
        showSucs :: Action
        showSucs = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               writeIORef restoreRef True
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               let t = trees!!curr
               drawThis "green" t $ concatMap (nodeSucs t) $ emptyOrAll treeposs
        
        -- | Called by menu items /constructors/, /variables/ and
        -- /free variables/ from menu /nodes/.
        showSyms :: (Sig -> TermS -> [[Int]]) -> Action
        showSyms f = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                writeIORef restoreRef True
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                sig <- getSignature
                let t = trees!!curr
                    p = emptyOrLast treeposs
                drawThis "green" t $ map (p++) $ f sig $ getSubterm t p
        
        -- | Used by 'removeClauses'. Called by menu item /show terms/
        -- from menu /theorems/.
        showTerms :: Action
        showTerms = do
            terms <- readIORef termsRef
            if null terms then labGreen "There are no terms to be reduced."
            else do enterTerms terms
                    labGreen $ see "terms"
        
        -- | Used by 'removeClauses'. Called by menu items /show theorems/
        -- and /[show theorems].. in text field of SolverN/ from menu
        -- /theorems/.
        showTheorems :: Bool -> Action
        showTheorems b = do
            theorems <- readIORef theoremsRef
            if null theorems then labGreen "There are no theorems."
            else if b then do enterFormulas theorems
                              labGreen $ see "theorems"
                      else do solve <- readIORef solveRef; bigWinR solve
                              enterFormulasR solve theorems
        
        -- | Called by menu item /[show theorems].. for symbols/ from menu
        -- /theorems/.
        showTheoremsFor :: Action
        showTheoremsFor = do
            str <- ent `gtkGet` entryText
            trees <- readIORef treesRef
            treeposs <- readIORef treepossRef
            curr <- readIORef currRef
            theorems <- readIORef theoremsRef
            let xs = if null trees || null treeposs then words str
                     else map (label $ trees!!curr) treeposs
                cls = [thm | thm <- theorems, any (`isin` thm) xs]
            if null cls
            then labRed $ noTheoremsFor xs
            else do enterFormulas cls
                    labGreen $ see $ "theorems for " ++ showStrList xs
                
        -- showTreePicts prepares the actual sequence of trees for being 
        -- displayed in the painter window and is used by showPicts.

        showTreePicts :: Action
        showTreePicts = do
          sig  <- getSignature
          eval <- getInterpreter
          drawFun <- readIORef drawFunRef
          trees <- readIORef treesRef
          spread <- readIORef spreadRef
          let mkPicts sizes = map (f sizes) trees 
              f sizes = eval sizes spread . applyDrawFun sig drawFun
          font <- readIORef fontRef
          picts <- mapM runT $ mkPicts sizes0
          sizes <- mkSizes canv font $ concatMap (stringsInPict . getPict) picts
          setTime
          picts <- mapM runT $ mkPicts sizes
          curr <- readIORef currRef
          picEval <- readIORef picEvalRef
          spread <- readIORef spreadRef
          back <- gtkGet ent entryText
          callPaint paint (map getPict picts) (indices_ trees) False curr 
                    picEval spread back

        -- | Called by 'Epaint.Solver' and 'Epaint.Painter' buttons /simplifyDF/
        -- ('simplButD') and /simplifyBF/ ('simplButB'). Exported by public
        -- 'Epaint.Solver' method 'Epaint.simplify.
        simplify :: Action
        simplify = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do str <- ent `gtkGet` entryText
                    let act = simplify'
                    case parse pnat str of Just limit -> act limit True
                                           _ -> act 100 False

        simplify' :: Int -> Bool -> Action              -- used by simplify
        simplify' limit sub = do
          simplStrat <- readIORef simplStratRef
          writeIORef ruleStringRef $ "SIMPLIFYING " ++ stratWord simplStrat
          extendPT $ Simplify limit sub
          sig <- getSignature
          trees <- readIORef treesRef
          curr <- readIORef currRef
          treeposs <- readIORef treepossRef
          let t = trees!!curr
          if null treeposs then do
             treeMode <- readIORef treeModeRef
             formula <- readIORef formulaRef
             collSimpls <- readIORef collSimplsRef
             simplStrat <- readIORef simplStratRef
             solPositions <- readIORef solPositionsRef
             setTime
             let (u,n,cyclic) = simplifyLoop sig limit simplStrat t
                 v = if collSimpls then collapse False u else u
                 msg0 = "The " ++ (if treeMode == "tree" then formString formula
                                   else "previous " ++ treeMode)
                               ++ " is simplified."
                 msg = finishedSimpl n ++ solved solPositions ++
                     ("\nThe simplification became cyclically." `onlyif` cyclic)
             if n == 0 then do
                           modifyIORef counterRef $ \counter -> decr counter 't'
                           counter <- readIORef counterRef
                           if counter 't' > 0
                              then setCurr msg0 $ (curr+1) `mod` length trees
                           else do labMag treesSimplified
                                   labSolver paint treesSimplified
             else do updateCurr v
                     makeTrees sig
                     modifyIORef counterRef $ \counter -> upd counter 'd' n
                     ruleString <- readIORef ruleStringRef
                     setProof True False ruleString [] msg
                     setTreesFrame []
          else if sub then do simplStrat <- readIORef simplStratRef
                              simplifySubtree t sig limit simplStrat
                      else simplifyPar t sig treeposs []

        simplifyPar :: TermS -> Sig -> [[Int]] -> [[Int]] -> Action
        simplifyPar t sig (p:ps) qs =
            case simplifyOne sig t p of
                Just t -> simplifyPar t sig ps (p:qs)
                _ -> simplifyPar t sig ps qs
        simplifyPar _ _ [] [] = labColorToPaint magback
                   "The selected trees are simplified at their root positions."
        simplifyPar t _ _ qs = do
            updateCurr t
            modifyIORef counterRef $ \counter -> upd counter 'd' 1
            setProof True False "SIMPLIFYING THE SUBTREES" qs simplifiedPar
            clearAndDraw
        
        -- used by simplify'

        simplifySubtree :: TermS -> Sig -> Int -> Strategy -> Action
        simplifySubtree t sig limit strat = do
          treeposs <- readIORef treepossRef
          collSimpls <- readIORef collSimplsRef
          simplStrat <- readIORef simplStratRef
          let p = emptyOrLast treeposs
              (u,n,cyclic) = simplifyLoop sig limit strat $ getSubterm1 t p
              v = if collSimpls then collapse False u else u
              msg = appliedToSub "simplification" n ++
                    ("\nThe simplification became cyclical." `onlyif` cyclic)
          if n == 0 then labColorToPaint magback
              "The tree selected at last is simplified."
          else do updateCurr $ replace1 t p v
                  modifyIORef counterRef $ \counter -> upd counter 'd' n
                  ruleString <- readIORef ruleStringRef
                  setProof True False ruleString [p] msg
                  clearAndDraw
        
        skip = done

        -- called by menu item /specialize/ from menu /transform selection/.
        specialize :: Action
        specialize = do
            trees <- readIORef treesRef
            if null trees then labBlue start
            else do
                str <- ent `gtkGet` entryText
                (exps,b) <- readIORef numberedExpsRef
                case parse nat str of
                    k@(Just n) | n < length exps ->
                        if b then finish k $ exps!!n
                        else labMag $ enterTfield "formulas"
                    _ -> do str <- getTextHere
                            sig <- getSignature
                            case parseE (implication sig) str of
                                 Correct th -> finish Nothing th
                                 p -> incorrect p str $ illformed "formula"
          where finish k th = applyTheorem False k
                                  $ case th of F "Not" [th] -> mkHorn mkFalse th
                                               _ -> mkCoHorn mkTrue th
        
        -- called by button /split\/join/ ('splitBut').
        splitTree :: Action
        splitTree = do
          trees <- readIORef treesRef
          when (notnull trees) $ do
              sig <- getSignature
              extendPT SplitTree
              joined <- readIORef joinedRef
              if joined then do
                  writeIORef joinedRef False
                  splitBut `gtkSet` [ buttonLabel := "join" ]
                  makeTrees sig
                  setTreesFrame []
                  setProof True False "SPLIT" [] "The tree has been split."
              else do
                  writeIORef joinedRef True
                  splitBut `gtkSet` [ buttonLabel := "split" ]
                  treeMode <- readIORef treeModeRef
                  trees <- readIORef treesRef
                  let t = joinTrees treeMode trees
                  writeIORef treeModeRef "tree"
                  writeIORef treesRef [t]
                  writeIORef currRef 0
                  modifyIORef counterRef $ \counter -> upd counter 't' 1
                  formula <- readIORef formulaRef
                  writeIORef solPositionsRef [0 | formula && isSol sig t]
                  setTreesFrame []
                  setProof True False "JOIN" [] "The trees have been joined."
 
        stateEquiv :: Action
        stateEquiv = do
          sig <- getSignature
          let f (i,j) = mkTup [states sig!!i,states sig!!j]
          enterTree False $ mkList $ map f $ bisim sig 
        
        -- | Called by 'deriveBut' if it shows /stop run/. The 'deriveBut' is
        -- set to /stop run/ when 'runChecker' is called. 
        
        stopRun :: Action
        stopRun = do
          checking <- readIORef checkingRef
          when checking $ do checker <- readIORef checkerRef
                             stopRun0 checker
                             runOpts (deriveBut,deriveButSignalRef)
          checkingP <- readIORef checkingPRef
          when (fst checkingP) $ setButton paint 3 runOpts
          where runOpts (btn,cmd) = 
                          do btn `gtkSet` [ buttonLabel := "run proof" ]
                             replaceCommandButton cmd btn $ runChecker True
        
        -- |called by all /stretch/ menu items from /transform selection/ menu.
        stretch :: Bool -> Action
        stretch conc = do
           trees <- readIORef treesRef
           if null trees then labBlue start
           else do
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               let t = trees!!curr
                   p = emptyOrLast treeposs
                   u = getSubterm t p
                   (f,step,str) =
                      if conc then (stretchConc,StretchConclusion,"CONCLUSION")
                              else (stretchPrem,StretchPremise,"PREMISE")
               case preStretch conc (const True) u of
                    Just (_,varps) -> do
                                varCounter <- readIORef varCounterRef
                                let (v,n) = f (varCounter "z") varps u
                                updateCurr $ replace t p v
                                setZcounter n
                                extendPT step
                                setProof True False ("STRETCHING THE "++str) [p] 
                                                    stretched
                                clearAndDraw
                    _ -> notStretchable $ "The "++str
        
        -- called by menu item /subsume/ from menu /transform selection/.
        subsumeSubtrees :: Action
        subsumeSubtrees = do
            treeposs <- readIORef treepossRef
            if length treeposs /= 2 || any null treeposs
            then labMag "Select two proper subtrees!"
            else do
                trees <- readIORef treesRef
                curr <- readIORef currRef
                let t = trees!!curr
                    ps@[p,q] = treeposs
                    prem = getSubterm t p
                    conc = getSubterm t q
                    r = init p
                    s = init q
                    u = getSubterm t r
                sig <- getSignature
                if subsumes sig prem conc then
                   if r == s then
                      if isImpl u then do updateCurr $ replace0 t r mkTrue
                                          finish ps "premise"
                      else if isConjunct u then do
                              let u' = F "&" $ context (last q) $ subterms u
                              updateCurr $ replace1 t r u'
                              finish ps "factor"
                      else if isDisjunct u then do
                              let u' = F "|" $ context (last p) $ subterms u
                              updateCurr $ replace t r u'
                              finish ps "summand"
                      else labGreen msg
                   else labGreen msg
                else labRed "The selected trees are not subsumable."
            where msg = "The selected trees are subsumable."
                  finish ps str = do
                            extendPT SubsumeSubtrees
                            setProof True False "SUBSUMPTION" ps $ subsumed str
                            clearAndDraw
        
        -- | Sitch state varibale 'fastRef' and alternate 'fastBut' label
        -- between "fast" and "slow". Called by 'fastBut'.
        switchFast :: Action
        switchFast = do
            modifyIORef fastRef not
            fast <- readIORef fastRef
            fastBut `gtkSet`
              [buttonLabel := if fast then "indented text" else "flowing text"]

        switchRefute = do
          modifyIORef refutingRef not
          refuting <- readIORef refutingRef
          extendPT $ Refuting refuting
          refuting <- readIORef refutingRef
          let msg = refuteMsg refuting
          setProof True False "REFUTE" [] msg
          refuteBut <- readIORef refuteButRef
          refuteBut `gtkSet` [menuItemLabel := msg]

        -- | Alternate between safe and unsafe equation removal. Called by menu
        -- item /safe\/unsafe equation removal/ from menu /signature/.
        switchSafe :: Action
        switchSafe = do
          modifyIORef safeSimplRef not
          safeSimpl <- readIORef safeSimplRef
          extendPT $ SafeSimpl safeSimpl
          safeSimpl <- readIORef safeSimplRef
          let msg = safeMsg safeSimpl
          setProof True False "SAFE" [] msg
          safeBut <- readIORef safeButRef
          safeBut `gtkSet` [menuItemLabel := msg]

        transformGraph mode = do
          trees <- readIORef treesRef
          if null trees then labBlue start
          else do
               sig <- getSignature
               trees <- readIORef treesRef
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               varCounter <- readIORef varCounterRef
               let t = trees!!curr
                   p:ps = emptyOrAll treeposs
                   newRoot = length treeposs == 1 && notnull p
                   vcz = varCounter "z"
                   (eqs,n) = graphToEqs vcz t p
                   labs = map showTerm0 $ labels sig
                   u = getSubterm1 t p
                   pairs = graphToRel labs t
                   trips = graphLToRel labs t
                   g = relToGraph pairs trips [label t p]
                   new = if isSum t
                         then joinGraphs $ updList (subterms t) (p!!0) g else g
                   act n p u = do
                               updateCurr $ replace1 t p u
                               when (mode == 3) $ setZcounter n
                               extendPT $ Transform mode
                               setProof False False "TRANSFORMING THE GRAPH" [p]
                                        transformed
                               clearAndDraw
               case mode of
                    0 -> case parseColl parsePair u of
                              Just pairs@(_:_)
                                -> act 0 p $ relToGraphAll pairs []
                              _ -> case parseColl parseTrip u of
                                   Just trips@(_:_)
                                     -> act 0 p $ relToGraphAll [] trips
                                   _ -> case parseEqs u of
                                        Just eqs -> act 0 p $ eqsToGraphAll eqs
                                        _ -> if newRoot then act 0 [] new
                                             else labRed "Select new root!"
                    1 -> case parseColl parsePair u of
                              Just rel@(_:_)              -- build iterative eqs
                                -> do
                                   let (eqs,n) = relToEqs vcz rel []
                                   act n p $ eqsTerm eqs
                              _ -> case parseColl parseTrip u of
                                        Just rel@(_:_)
                                          -> do
                                             let (eqs,n) = relToEqs vcz [] rel
                                             act n p $ eqsTerm eqs
                                        _ -> act n p $ eqsTerm eqs
                    b -> act 0 p $ collapse (b == 2) u
                            
        updateCurr :: TermS -> Action
        updateCurr t = do curr <- readIORef currRef
                          modifyIORef treesRef $ \trees -> updList trees curr t

        -- | Used by 'buildUnifier' and 'unifyOther'.
        unifyAct :: TermS -> TermS -> TermS -> TermS -> [Int] -> [Int] -> Action
        unifyAct u u' t t' p q = do
            writeIORef restoreRef True
            sig <- getSignature
            case unify True sig [] V u u' t t' p q of
                Def (f,True) -> do
                    let xs = frees sig u `join` frees sig u'
                        dom = domSub xs f
                    if null dom then labGreen $ unifiedT ++ emptySubst
                    else if any hasPos $ map f dom then labRed posInSubst
                         else do
                               setSubst (f,dom)
                               labGreen $ unifiedT ++ "See substitution > show."
                Def (_,False) -> labRed partialUnifier
                BadOrder -> labRed noUnifier
                Circle p q -> labRed $ circle p q
                NoPos p -> do
                    setTreeposs $ Replace [p]
                    drawCurr
                    labRed dangling
                NoUni -> labRed noUnifier
                OcFailed x -> labRed $ ocFailed x
        
        -- | Called by menu item /unify with tree of SolverN/ from menu
        -- /transform selection/.
        unifyOther :: Action
        unifyOther = do
            solve <- readIORef solveRef
            tree <- getTreeR solve
            case tree of
                Just t -> do treeposs <- readIORef treepossRef
                             trees <- readIORef treesRef
                             curr <- readIORef currRef
                             let p = emptyOrLast treeposs
                                 t' = trees!!curr
                                 u = getSubterm t' p
                             unifyAct t u t t' [] p
                _ -> do other <- getSolver solve
                        labBlue $ startOther other
        
        -- called by menu item /unify/ from menu /transform selection/.
        unifySubtrees :: Action
        unifySubtrees = do
          treeposs <- readIORef treepossRef
          if length treeposs /= 2 || any null treeposs
             then labMag "Select two proper subtrees!"
          else do
            sig <- getSignature
            trees <- readIORef treesRef
            curr <- readIORef currRef
            treeposs <- readIORef treepossRef
            let t = trees!!curr
                [p,q] = treeposs
                select = getSubterm1 t
                xs = sigVars sig t
            if init p == init q then
               case unifyS sig xs (select p) $ select q of
                    Just f -> do let (zs,ps) = quantPoss t $ domSub xs f
                                     ts = zipWith g zs ps
                                     g x p = t>>>restrict ((anys+++alls) u) f
                                             where t = select p
                                                   u = select $ init p
                                     result = fold2 replace1 t ps ts
                                 updateCurr result
                                 extendPT UnifySubtrees
                                 treeposs <- readIORef treepossRef
                                 setProof True False "SUBTREE UNIFICATION"
                                          treeposs $ unified "subtree"
                                 clearAndDraw
                    _ -> labRed noUnifier
            else labMag "Select subtrees with the same predecessor!"

    return Solver {addSpec         = addSpec,
                   backWin         = backWin,
                   bigWinR         = bigWin,
                   buildSolve      = buildSolve,
                   checkInSolver   = checkInSolver,
                   drawCurr        = drawCurr,
                   enterTextR      = enterText,
                   enterFormulasR  = enterFormulas,
                   enterTreeR      = enterTree,
                   getEntry        = getEntry',
                   getSolver       = return this,
                   getText         = getTextHere,
                   getFont         = readIORef fontRef,
                   getPicNo        = readIORef picNoRef,
                   getSignatureR   = getSignature,
                   getTreeR        = getTree,
                   isSolPos        = \n -> elem n <$> readIORef solPositionsRef,
                   labBlueR        = labBlue,
                   labRedR         = labRed,
                   labGreenR       = labGreen,
                   narrow          = narrow,
                   proofBackward   = proofBackward,
                   proofForward    = proofForward',
                   saveGraphDP     = saveGraphDP,
                   setCurrInSolve  = setCurrInSolve,
                   setForw         = setForw,
                   setQuit         = setQuit,
                   setInterpreterR = setInterpreter,
                   setNewTreesR    = setNewTrees,
                   setSubst        = setSubst,
                   showPicts       = showPicts,
                   simplify        = simplify,
                   stopRun         = stopRun}

-- ENUMERATOR messages

badConstraint :: String
badConstraint = "The constraint is not well-formed."

howMany :: (Eq a, Num a, Show a) => a -> String -> String -> String
howMany 1 object ""     = "There is one " ++ object ++ "."
howMany 1 object constr = "There is one " ++ object ++ " satisfying " ++ constr
                           ++ "."
howMany n object ""     = "There are " ++ show n ++ " " ++ object ++ "s."
howMany n object constr = "There are " ++ show n ++ " " ++ object ++
                             "s satisfying " ++ constr ++ "."

none :: String -> String -> String
none object "" = "There is no " ++ object ++ "."
none object c  = "There is no " ++ object ++ " satisfying " ++ c ++ "."

startEnum :: String -> String
startEnum object = (init $ enterTfield str) ++
                   (case object of "palindrome" -> "!"
                                   _ -> more)
      where str = case object of
                  "palindrome" -> "a sequence of strings"
                  "alignment" -> "two sequences of strings separated by blanks"
                  "dissection"
                    -> "the breadth > 0 and the height > 0 of a rectangle"
                  _ -> "the length of a list"
            more = "\nand a constraint into the entry field (see the manual)!"

data Enumerator = Enumerator
                   {buildEnum :: String -> (String -> String -> Bool) -> Action}
                   
enumerator :: IORef Solver -> Template Enumerator
enumerator solveRef = do
    objectRef <- newIORef ""
    complRef <- newIORef $ const2 False

    return $
        let buildEnum' obj f = do
                writeIORef objectRef obj
                writeIORef complRef f
                solve <- readIORef solveRef
                labBlueR solve $ startEnum obj
                setForw solve $ \(btn, cmd) -> do
                    btn `gtkSet` [ buttonLabel := "go" ]
                    setBackground btn redback
                    replaceCommandButton cmd btn $ getInput obj
                setQuit solve $ \(quit, signal) -> do
                  quit `gtkSet` [ buttonLabel := "quit " ++ obj]
                  replaceCommandButton signal quit finish
 
            finish = do
                solve <- readIORef solveRef
                labBlueR solve start
                setForw solve $ \(btn, cmd) -> do
                    btn `gtkSet` [ buttonLabel := "--->" ]
                    setBackground btn greenback
                    solve <- readIORef solveRef
                    replaceCommandButton cmd btn $ proofForward solve
                setQuit solve $ \(quit, signal) -> do
                    quit `gtkSet` [ buttonLabel := "quit" ]
                    replaceCommandButton signal quit mainQuit
                setInterpreterR solve $ "tree"
                    
            getInput "alignment" = do
                solve <- readIORef solveRef
                str <- getText solve
                constr <- getEntry solve
                let global = notnull constr && head constr == 'g'
                    (xs,ys) = break (== '\n') str
                if null ys then
                   labRedR solve $ enterTfield "two sequences of strings"
                else do compl <- readIORef complRef
                        showResult constr $ map (alignToTerm . compress) $
                                   mkAlign global (words xs) (words ys) compl
            getInput "palindrome" = do
                solve <- readIORef solveRef
                compl <- readIORef complRef
                str <- getText solve
                showResult "" $ map (alignToTerm . compress)
                              $ mkPali (words str) compl
            getInput "dissection" = do
                solve <- readIORef solveRef
                str <- getText solve
                case parse size str of
                     Just (b,h) -> do 
                        constr <- getEntry solve
                        case parse (disjunct sig) constr of
                          Just t -> case dissConstr b h t of
                                      Just (c,ns,c') -> showResult (showEnum t)
                                                        $ mkDissects c c' ns b h
                                      _ -> labRedR solve badConstraint
                          _ -> labRedR solve badConstraint
                     _ -> labBlueR solve $ enterTfield "two numbers > 0"
                where size = do b <- token pnat; h <- token pnat; return (b,h)
            getInput _ = do
                solve <- readIORef solveRef
                str <- getText solve
                case parse (token pnat) str of
                     Just n | n > 1 -> do
                        constr <- getEntry solve
                        case parse (disjunct sig) constr of
                             Just t -> case partConstr t of
                                       Just c -> showResult (showEnum t)
                                                 $ mkPartitions c n t
                                       _ -> labRedR solve badConstraint
                             _ -> labRedR solve badConstraint
                     _ -> labBlueR solve $ enterTfield "a number > 1"

            showResult constr terms = do
                solve <- readIORef solveRef
                object <- readIORef objectRef
                if null terms then labGreenR solve $ none object constr
                else do let n = length terms
                            typ = if n == 1 then "tree" else "term"
                        setNewTreesR solve terms typ
                        labGreenR solve $ howMany n object constr
        in Enumerator {buildEnum = buildEnum'}

  where sig = predSig $ words "alter area bal brick eqarea eqout factor hei" ++
                        words "hori levmin levmax sizes sym out vert"

        alignToTerm :: Align_ String -> TermS
        alignToTerm t = case t of
                        Compl x y t -> F "compl" [V x,alignToTerm t,V y]
                        Equal_ s t -> F "equal" $ alignToTerm t:map V s
                        Ins s t -> F "insert" $ alignToTerm t:map V s
                        Del s t -> F "delete" $ alignToTerm t:map V s
                        End s -> F "end" $ map V s

        showEnum t = showSummands (mkSummands t) `minus`" \n"
