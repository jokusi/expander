{-|
Module      : Ecom
Description : TODO
Copyright   : (c) Peter Padawitz, September 2018
                  Jos Kusiek, September 2018
License     : BSD3
Maintainer  : (padawitz peter)@(edu udo)
Stability   : experimental
Portability : portable

Ecom contains the main program, the solver and the enumerator.
-}
module Ecom where

import Prelude ()
import qualified Base.Haskell as Haskell
import Base.System
import Eterm
import Epaint
import Esolve

initialFont :: String
initialFont = sansSerif ++ " 18"

data PossAct = Add [[Int]] | Remove [Int] | Replace [[Int]]

-- * __Proofs__

data ProofElem = ProofElem
    { peMsg, peMsgL, peTreeMode :: String
    , peTrees               :: [TermS]
    , peTreePoss            :: [[Int]]
    , peCurr                :: Int
    , pePerms               :: Int -> [Int]
    , peVarCounter          :: String -> Int
    , peNewPreds            :: ([String],[String])
    , peSolPositions        :: [Int]
    , peSubstitution        :: (SubstS,[String])
    , peConstraints         :: (Bool,[String])
    , peJoined, peSafe        :: Bool
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
showNew fast k t msg n ps tm = preceding msg ps tm n ++ show k ++ tm ++ "s." ++
                               showCurr fast t tm

showPre :: Bool -> TermS -> String -> Int -> [[Int]] -> String -> String
showPre fast t msg n ps tm = preceding msg ps tm n ++ "\n\n" ++ showTree fast t

preceding :: String -> [[Int]] -> String -> Int -> String
preceding msg ps tm n = if take 3 msg `elem` words "BUI MIN"
                        then msg ++ " leads to "
                        else msg ++ str1 ++ showPS ps ++ tm ++ "s" ++
                             (str2 `onlyif` nrs) ++ " leads to "
    where str1 = if last msg == '\n' then "" else " "
          str2 = " (" ++ if n == 1 then "one step)" else show n++ " steps)"
          nrs = take 3 msg `elem` words "NAR REW SIM"
          showPS []  = ("to " `ifnot` nrs) ++ "the preceding "
          showPS ps = "at positions" ++ concatMap f ps ++ "\nof the preceding "
          f p = '\n':show p `minus1` ' '

-- * __Proof term__ functions

addStep :: [Step] -> Step -> [Step]
addStep pt@(_:_) step = case (step,last pt) of
                             (DeriveMode _ _,DeriveMode _ _) -> init pt++[step]
                             (Mark _,Mark _) -> init pt++[step]
                             (Match _,Match _) -> init pt++[step]
                             _ -> pt++[step]
addStep _ step        = [step]

deriveStep :: Step -> Bool
deriveStep step = case step of DeriveMode _ _ -> False
                               Mark _                -> False
                               Match _        -> False
                               _                -> True

command :: Parser Step
command = concat [do symbol "AddAxioms"; axs <- list linearTerm
                     return $ AddAxioms axs,
                  do symbol "ApplySubst"; return ApplySubst,
                  do symbol "ApplySubstTo"; x <- token quoted
                     t <- enclosed linearTerm; return $ ApplySubstTo x t,
                  do symbol "ApplyTransitivity"; return ApplyTransitivity,
                  do symbol "BuildKripke"; m <- token int
                     return $ BuildKripke m,
                  do symbol "BuildRE"; return BuildRE,
                  do symbol "CollapseStep"; return CollapseStep,
                  do symbol "ComposePointers"; return ComposePointers,
                  do symbol "CopySubtrees"; return CopySubtrees,
                  do symbol "CreateIndHyp"; return CreateIndHyp,
                  do symbol "CreateInvariant"; b <- token bool
                     return $ CreateInvariant b,
                  do symbol "DecomposeAtom"; return DecomposeAtom,
                  do symbol "DeriveMode"; s <- token bool; r <- token bool
                     return $ DeriveMode s r,
                  do symbol "EvaluateTrees"; return EvaluateTrees,
                  do symbol "ExpandTree"; b <- token bool; n <- token int
                     return $ ExpandTree b n,
                  do symbol "FlattenImpl"; return FlattenImpl,
                  do symbol "Generalize"; cls <- list linearTerm
                     return $ Generalize cls,
                  do symbol "Induction"; b <- token bool; n <- token int
                     return $ Induction b n,
                  do symbol "Mark"; ps <- list $ list int; return $ Mark ps,
                  do symbol "Match"; n <- token int; return $ Match n,
                  do symbol "Minimize"; return Minimize,
                  do symbol "ModifyEqs"; m <- token int; return $ ModifyEqs m,
                  do symbol "Narrow"; limit <- token int; sub <- token bool
                     return $ Narrow limit sub,
                  do symbol "NegateAxioms"; ps <- list quoted
                     cps <- list quoted; return $ NegateAxioms ps cps,
                  do symbol "RandomLabels"; return RandomLabels,
                  do symbol "RandomTree"; return RandomTree,
                  do symbol "ReduceRE"; m <- token int; return $ ReduceRE m,
                  do symbol "ReleaseNode"; return ReleaseNode,
                  do symbol "ReleaseSubtree"; return ReleaseSubtree,
                  do symbol "ReleaseTree"; return ReleaseTree,
                  do symbol "RemoveCopies"; return RemoveCopies,
                  do symbol "RemoveEdges"; b <- token bool
                     return $ RemoveEdges b,
                  do symbol "RemoveNode"; return RemoveNode,
                  do symbol "RemoveOthers"; return RemoveOthers,
                  do symbol "RemovePath"; return RemovePath,
                  do symbol "RemoveSubtrees"; return RemoveSubtrees,
                  do symbol "RenameVar"; x <- token quoted
                     return $ RenameVar x,
                  do symbol "ReplaceNodes"; x <- token quoted
                     return $ ReplaceNodes x,
                  do symbol "ReplaceOther"; return ReplaceOther,
                  do symbol "ReplaceSubtrees"; ps <- list $ list int
                     ts <- list linearTerm; return $ ReplaceSubtrees ps ts,
                  do symbol "ReplaceText"; x <- token quoted
                     return $ ReplaceText x,
                  do symbol "ReplaceVar"; x <- token quoted
                     u <- enclosed linearTerm; p <- list int
                     return $ ReplaceVar x u p,
                  do symbol "ReverseSubtrees"; return ReverseSubtrees,
                  do symbol "SafeEqs"; return SafeEqs,
                  do symbol "SetAdmitted"; block <- token bool
                     xs <- list quoted; return $ SetAdmitted block xs,
                  do symbol "SetCurr"; msg <- token quoted; n <- token int
                     return $ SetCurr msg n,
                  do symbol "ShiftPattern"; return ShiftPattern,
                  do symbol "ShiftQuants"; return ShiftQuants,
                  do symbol "ShiftSubs"; ps <- list $ list int
                     return $ ShiftSubs ps,
                  do symbol "Simplify"; depthfirst <- token bool
                     limit <- token int; sub <- token bool
                     return $ Simplify depthfirst limit sub,
                  do symbol "SplitTree"; return SplitTree,
                  do symbol "SubsumeSubtrees"; return SubsumeSubtrees,
                  do symbol "Theorem"; b <- token bool
                     th <- enclosed linearTerm; return $ Theorem b th,
                  do symbol "Transform"; m <- token int; return $ Transform m,
                  do symbol "UnifySubtrees"; return UnifySubtrees]

linearTerm :: Parser (Term String)
linearTerm =   concat [do symbol "F"; x <- token quoted; ts <- list linearTerm
                          return $ F x ts,
                       do symbol "V"; x <- token quoted; return $ V x]

-- * __Solver__ messages

start :: String
start = "Welcome to Expander3 (November 5, 2018)"

startOther :: String -> String
startOther solve = "Load and parse a term or formula in " ++ solve ++ "!"

applied :: Bool -> String -> String
applied b str = "Applying the " ++ s ++ str ++ "\n\n"
          where s = if b then if '!' `elem` str then "induction hypothesis\n\n"
                                                else "theorem\n\n"
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

admitted :: Bool -> [String] -> String
admitted True []  = "All simplifications are admitted."
admitted block xs = (if block then "All simplifications except those for "
                              else "Only simplifications for ") ++
                    showStrList xs ++ " are admitted."

axsRemovedFor :: Show a => a -> String
axsRemovedFor xs = "The axioms for " ++ showStrList xs ++ " have been removed."

check :: String -> String
check rest = "\n--CHECK FROM HERE:\n" ++ rest

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

complsAdded :: Show t => [t] -> String
complsAdded xs = "Axioms for the complement" ++ str ++ showStrList xs ++
                  " have been added."
                 where str = case xs of [_] -> " of "; _ -> "s of "

concCallsPrem :: String
concCallsPrem
            = "Some conclusion contains the root of the corresponding premise."

creatingInvariant :: String -> Term String -> String
creatingInvariant str ax
       = str ++ " for the iterative program\n\n" ++ showTree False ax ++ "\n\n"

edgesRemoved :: Bool -> String
edgesRemoved True = "Cycles have been removed."
edgesRemoved _    = "Forward arcs have been turned into tree edges."

dangling :: String
dangling = "The highlighted subtree cannot be removed from its position " ++
           "because a pointer points to it."

emptyProof :: String
emptyProof = "The proof is empty."

emptySubst :: String
emptySubst = "The substitution is empty."

emptyPicDir :: String
emptyPicDir = "The picture directory is empty."

endOfProof :: String
endOfProof = "The end of the derivation has been reached."

enterNumber :: String
enterNumber = "Enter the number of a formula shown in the text field!"

enterNumbers :: String
enterNumbers = "Enter numbers of formulas shown in the text field!"

eqInverted :: String
eqInverted = "The selected equation has been inverted."

equationRemoval :: Bool -> String
equationRemoval safe = "Equation removal is " ++ if safe then "safe."
                                                          else "unsafe."

eqsButMsg :: Bool -> String
eqsButMsg safe = (if safe then "safe" else "unsafe") ++ " equation removal"

eqsModified :: String
eqsModified = "The selected regular equations have been modified."

evaluated :: String
evaluated = "The selected trees have been evaluated."

expanded :: String
expanded = "The selected trees have been expanded."

extendedSubst :: String
extendedSubst =
        "The equations in the text field have been added to the substitution."

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
              " in the text field."

illformed :: String
illformed = "The term or formula in the text field is not well-formed."

illformedF :: String
illformedF = "The formula in the text field is not well-formed."

illformedS :: String
illformedS = "The substitution in the text field is not well-formed."

illformedSig :: String
illformedSig = "The signature in the text field is not well-formed."

illformedSM :: String
illformedSM = "The signature map in the text field is not well-formed."

illformedT :: String
illformedT = "The term in the text field is not well-formed."

indApplied :: String -> String
indApplied str = str ++ " has been applied to the selected formulas."

indHypsCreated :: Show a => [a] -> String
indHypsCreated [x] = "The induction variable is " ++ showStr x ++
                     ".\nInduction hypotheses have been added to the theorems."
                     ++ "\nGive axioms for the induction ordering >>!"

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
    show' labs "label" ++ " has been built from the " ++ g mode
    where f 0 = "cycle-free"; f 1 = "pointer-free"; f _ = ""
          g 3 = "current graph."; g 4 = "regular expression."; g _ = "axioms."

kripkeMsg = "BUILDING A KRIPKE MODEL"
    
leavesExpanded :: String
leavesExpanded = "The selected trees have been expanded at their leaves."

levelMsg :: (Eq a, Num a, Show a) => a -> String
levelMsg i = "The current tree has been collapsed at " ++
              (if i == 0 then "leaf level." else " the " ++ show (i+1) ++
              " lowest levels.")

loaded :: String -> String
loaded file = file ++ " has been loaded into the text field."

minimized n = "The Kripke model has been minimized. It has " ++ 
              show' n "states."

moved :: String
moved = "The selected quantifiers have been moved to the parent node."

newCls :: String -> String -> String
newCls cls file = "The " ++ cls ++ " in " ++ file ++ " have been added."

newCurr :: String
newCurr = "The tree slider has been moved."

newInterpreter :: String -> String -> String
newInterpreter eval draw = eval ++" is the actual widget-term interpreter. "++
                           (if null draw then "No draw function" else draw) ++
                           " is applied before painting."

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

pointersComposed :: String
pointersComposed = "The pointers in the selected trees have been composed."

posInSubst :: String
posInSubst = "There is a pointer in a substitution."

proofLoaded :: String -> String
proofLoaded file = "The proof term has been loaded from " ++ file ++ "."

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
reversed = "The list of selected trees has been reversed."

see :: String -> String
see str = "See the " ++ str ++ " in the text field."

selectCorrectSubformula :: String
selectCorrectSubformula = "Select an implication, a conjunction or a " ++
                          "disjunction and subterms to be replaced!"

selectSub :: String
selectSub = "Select a proper non-hidden subtree!"

shifted :: String
shifted =
     "The selected subformulas have been shifted to the premise or conclusion."

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
textInserted
           = "The tree in the text field replaces/precedes the selected trees."

transformed :: String
transformed = "The selected graph has been transformed."

transitivityApplied :: String
transitivityApplied
              = "The transitivity axiom has been applied to the selected atoms."

treeParsed :: String
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

enumerators :: [String]
enumerators  = words "alignment palindrome dissection" ++ ["level partition",
                     "preord partition","heap partition","hill partition"]

interpreters :: [String]
interpreters = words "tree widgets overlay matrices" ++
               ["matrix solution","linear equations","level partition",
                "preord partition","heap partition","hill partition"]

specfiles1 :: [String]
specfiles1 =
  words "abp account align auto1 auto2 base bool bottle bottleac bottlef" ++
  words "btree cobintree coin coregs cse cycle dna echo echoac election" ++
  words "factflow flowers FP gauss graphs hanoi hanoilab hinze infbintree" ++
  words "kino knight kripke1 kripke2"

specfiles2 :: [String]
specfiles2 =
  words "lazy lift liftlab list listeval listrev log log4 lr1 lr2 micro" ++
  words "modal mutex mutexco mutexquad nat NATths needcoind newman obdd" ++ 
  words "obst partn penroseS phil philac polygons prims prog puzzle queens"

specfiles3 :: [String]
specfiles3 =
  words "regeqs relalg relalgdb relalgp robot ROBOTacts sendmore set" ++
  words "shelves simpl stack STACKimpl STACKimpl2 stream trans0 trans1" ++
  words "trans2 turtles widgets zip"

{-
pictsOf "bottle" sig                = (solPic sig widgets,False)
pictsOf "robot" sig                = (solPic sig widgets,False)
pictsOf "ROBOTacts" sig            = (solPic sig widgets,False)
pictsOf "queens" sig               = (solPic sig matrix,False)
pictsOf "knight" sig               = (solPic sig matrix,False)
pictsOf ('g':'a':'u':'s':'s':_) _ = (searchPic linearEqs,False)
pictsOf _ _                              = (searchPic widgets,False)
-}
-- * the __Solver__ template

solver :: String -> IORef Solver -> Enumerator -> Painter -> Template Solver
solver this solveRef enum paint = do
    builder <- loadGlade "Solver"
    let getObject :: GObjectClass cls => (GObject -> cls) -> String -> IO cls
        getObject = builderGetObject builder
        getButton = getObject castToButton
        getMenuItem   = getObject castToMenuItem
        getMenu   = getObject castToMenu
    
    win <- getObject castToWindow "win"
    backBut <- getButton "backBut"
    canv <- canvas
    scrollCanv <- getObject castToScrolledWindow "scrollCanv"
    --close <- newIORef $ error "ref close"
    deriveBut <- getButton "deriveBut"
    treeSlider <- getObject castToScale "treeSlider"
    ent <- getObject castToEntry "ent"
    fontSize <- getObject castToScale "fontSize"
    fastBut <- getButton "fastBut"
    randomBut <- getButton "randomBut"
    forwBut <- getButton "forwBut"
    hideBut <- getButton "hideBut"
    interpreterLabel <- getObject castToLabel "interpreterLabel"
    lab <- getObject castToLabel "lab"
    matchBut <- getButton "matchBut"
    narrowBut <- getButton "narrowBut"
    safeButRef <- newIORef undefined
    simplButD <- getButton "simplButD"
    simplButB <- getButton "simplButB"
    splitBut <- getButton "splitBut"
    tedit <- getObject castToTextView "tedit"
    termBut <- getObject castToLabel "termBut"
    lab2 <- getObject castToLabel "lab2"
    treeSize <- getObject castToScale "treeSize"
    subToBut <- getButton "subToBut"
    quit <- getButton "quit"

    fontRef <- newIORef $ error "fontRef undefined"

    -- Signals
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
    -- osciRef <- newIORef Nothing

    fastRef <- newIORef False
    firstMoveRef <- newIORef True
    formulaRef <- newIORef True
    showStateRef <- newIORef True
    joinedRef <- newIORef True
    safeRef <- newIORef True
    wtreeRef <- newIORef True
    firstClickRef <- newIORef True

    checkingRef <- newIORef False
    checkingPRef <- newIORef False
    simplifyingRef <- newIORef False
    refutingRef <- newIORef False
    collSimplsRef <- newIORef False
    newTreesRef <- newIORef False
    restoreRef <- newIORef False

    canvSizeRef <- newIORef (0,0)
    cornerRef <- newIORef (30,20)
    counterRef <- newIORef $ const 0
    currRef <- newIORef 0
    -- curr1Ref <- newIORef 0
    matchingRef <- newIORef 0
    proofPtrRef <- newIORef 0
    proofTPtrRef <- newIORef 0
    picNoRef <- newIORef 0
    stateIndexRef <- newIORef 0

    axiomsRef <- newIORef []
    checkersRef <- newIORef []
    conjectsRef <- newIORef []
    indClausesRef <- newIORef []
    matchTermRef <- newIORef []
    oldTreepossRef <- newIORef []
    proofRef <- newIORef []
    proofTermRef <- newIORef []
    refuteTermRef <- newIORef []
    ruleStringRef <- newIORef []
    simplRulesRef <- newIORef []
    simplTermRef <- newIORef []
    solPositionsRef <- newIORef []
    specfilesRef <- newIORef []
    termsRef <- newIORef []
    theoremsRef <- newIORef []
    transRulesRef <- newIORef []
    treepossRef <- newIORef []
    treesRef <- newIORef []

    numberedExpsRef <- newIORef ([],True)
    constraintsRef <- newIORef (True,[])

    drawFunRef <- newIORef ""
    picEvalRef <- newIORef "tree"
    picDirRef <- newIORef "picDir"

    signatureMapRef <- newIORef (id,[])
    newPredsRef <- newIORef nil2
    partRef <- newIORef (id,[])
    proofStepRef <- newIORef ApplySubst
    substitutionRef <- newIORef (V,[])
    treeModeRef <- newIORef "tree"
    symbolsRef <- newIORef iniSymbols
    randRef <- newIORef seed
    sizeStateRef <- newIORef sizes0
    spreadRef <- newIORef (10,30)
    timesRef <- newIORef (0,300)
    speedRef <- newIORef 500
    varCounterRef <- newIORef $ const 0
    chgPermRef <- newIORef False
    permsRef <- newIORef $ \n -> [0..n-1]
    kripkeRef <- newIORef ([],[],[],[],[],[],[])



    let mkSub :: Menu -> String -> Request Menu
        mkSub m text = cascade m text menuOpt{ font = font12 }
        
        mkBut :: Menu -> String -> Action -> Request MenuItem
        mkBut m text cmd = do
          item <- menuItemNewWithLabel text
          addContextClass item "font12"
          item `on` menuItemActivated $ cmd
          menuShellAppend m item
          item `gtkSet` [ widgetVisible := True ]
          return item
        mkButF m cmd file = mkBut m file $ cmd file
        

        -- | Initializes and shows the Solver GUI. Main 'Solver' function that
        -- has to be called first.
        buildSolve' :: Action
        buildSolve' = do
          icon <- iconPixbuf
          win `gtkSet` [ windowTitle := this
                    , windowIcon := Just icon
                    , windowDefaultWidth := 1200
                    , windowDefaultHeight := 820
                    ]

          let da = getDrawingArea canv
          widgetAddEvents  da [ButtonMotionMask]
          da `on` buttonPressEvent $ do
              button <- eventButton
              pt <- round2 <$> eventCoordinates
              lift $ case button of
                  LeftButton -> catchSubtree pt
                  MiddleButton -> catchTree pt
                  RightButton -> catchNode pt
                  _ -> return ()
              return False
          da `on` motionNotifyEvent $ do
              lift $ do
                  dw <- widgetGetParentWindow da
                  (_, x, y, modifier) <- drawWindowGetPointerPos dw
                  let pt = (x, y)
                      button = Haskell.find (`elem` [Button1, Button2, Button3])
                                    modifier
                  case button of
                      Just Button1 -> moveSubtree pt
                      Just Button2 -> moveTree pt
                      Just Button3 -> moveNode pt
                      _ -> return ()
              return False
          da `on` buttonReleaseEvent $ do
              button <- eventButton
              lift $ case button of
                  LeftButton -> releaseSubtree
                  MiddleButton -> releaseTree
                  RightButton -> releaseNode
                  _ -> return ()
              return False

          let takeCurr = do
                  curr1 <- truncate <$> (treeSlider `gtkGet` rangeValue)
                  setCurr newCurr curr1
          treeSlider `on` valueChanged $ takeCurr
          
          widgetOverrideFont ent
              =<< Just <$> fontDescriptionFromString (monospace ++ " 18")
          ent `on` keyPressEvent $ do
              name <- unpack <$> eventKeyName
              lift $ case name of
                  "Up" -> getFileAnd $ loadText True
                  "Down" -> getFileAnd saveTree
                  "Right" -> applyClause False False False
                  "Left" -> applyClause False True False
                  "Return" -> getFileAnd addSpecWithBase
                  _ -> return ()
              return False

          font <- fontDescriptionFromString initialFont
          writeIORef fontRef font

          hideBut `on` buttonActivated $ hideOrShow
          
          widgetOverrideFont lab =<< Just <$> labFont
          setBackground lab blueback
          lab `gtkSet` [ labelLabel := start ]
          lab `on` keyPressEvent $ do
              name <- unpack <$> eventKeyName
              lift $ case name of
                  "c" -> copySubtrees
                  "i" -> replaceText
                  "l" -> replaceNodes
                  "L" -> randomLabels
                  "n" -> negateAxioms
                  "o" -> removeNode
                  "p" -> removePath
                  "r" -> removeSubtrees
                  "s" -> saveProof
                  "T" -> randomTree
                  "v" -> reverseSubtrees
                  "d" -> setPicDir False
                  "x" -> showAxiomsFor
                  "Left" -> incrCurr False
                  "Right" -> incrCurr True
                  _ -> return ()
              return False

          widgetOverrideFont lab2 =<< Just <$> labFont
          setBackground lab2 blueback

          widgetModifyFont tedit
              =<< Just <$> fontDescriptionFromString "Courier 12"

          tedit `on` keyPressEvent $ do
              name <- unpack <$> eventKeyName
              lift $ case name of
                  "Up" -> parseText
                  "Down" -> parseTree
                  _ -> return ()
              return False

          matchBut `on` buttonActivated $ setNarrow True False
          randomBut `on` buttonActivated $ setNarrow False True
          
          narrowBut `gtkSet` [ buttonLabel := "" ]
          narrowBut `on` buttonActivated $ narrow'

          backButSignal <- backBut `on` buttonActivated $ backProof
          writeIORef backButSignalRef backButSignal

          writeIORef forwButSignalRef
              =<< (forwBut `on` buttonActivated $ forwProof')

          picEval <- readIORef picEvalRef
          spread <- readIORef spreadRef
          setEval paint picEval spread
          
          setPicDir True

          
          buildSolve1

        -- | Second half of 'buildSolve''.
        buildSolve1 :: Action
        buildSolve1 = do
          solve <- readIORef solveRef
          other <- getSolver solve

          deriveButSignal <- deriveBut `on` buttonActivated $ setDeriveMode
          writeIORef deriveButSignalRef deriveButSignal
          minusBut <- getButton "minusBut"
          minusBut `on` buttonActivated $ incrEntry False
          plusBut <- getButton "plusBut"
          plusBut `on` buttonActivated $ incrEntry True
          paintBut <- getButton "paintBut"
          paintBut `on` buttonActivated $ showPicts'
          downBut <- getButton "downBut"
          downBut `on` buttonActivated $ parseTree
          upBut <- getButton "upBut"
          upBut `on` buttonActivated $ parseText
          clearS <- getButton "clearS"
          clearS `on` buttonActivated $ redrawTree
          clearT <- getButton "clearT"
          clearT `on` buttonActivated $ do
              clearText
              writeIORef numberedExpsRef ([],True)
          quitSignal <- quit `on` buttonActivated $ mainQuit
          writeIORef quitSignalRef quitSignal
          saveBut <- getButton "saveBut"
          saveBut `on` buttonActivated $ getFileAnd saveGraph
          saveDBut <- getButton "saveDBut"
          saveDBut `on` buttonActivated $ saveGraphD
          dirBut <- getButton "dirBut"
          dirBut `on` buttonActivated $ setPicDir False
          simplButD `on` buttonActivated $ simplify' True
          simplButB `on` buttonActivated $ simplify' False
          fastBut `on` buttonActivated $ switchFast
          splitBut `on` buttonActivated $ splitTree

          axsMenu <- getMenu "axsMenu"
          mkBut axsMenu "show axioms" $ showAxioms True
          mkBut axsMenu (".. in text field of "++ other) $ showAxioms False
          mkBut axsMenu ".. for symbols (x)" showAxiomsFor
          subMenu <- mkSub axsMenu "add"
          createSub 0 subMenu
          mkBut axsMenu "combine for symbol" $ compressAxioms True
          mkBut axsMenu ".. in entry field" compressClauses
          mkBut axsMenu "invert for symbol" $ compressAxioms False
          mkBut axsMenu "negate for symbols (n)" negateAxioms
          mkBut axsMenu "Kleene axioms for symbols" kleeneAxioms
          mkBut axsMenu "remove in entry field" $ removeClauses 0
          mkBut axsMenu ".. for symbols" removeAxiomsFor
          
          
          fontBut <- getObject castToFontButton "fontBut"
          fontBut `gtkSet` [ fontButtonUseSize  := False
                        , fontButtonFontName := initialFont
                        ]
          fontBut `onFontSet` do
              fd <- fontDescriptionFromString
                  =<< (fontBut `gtkGet` fontButtonFontName :: IO String)
              setFont fd
          
          Just size <- fontDescriptionGetSize =<< readIORef fontRef
          fontSize `gtkSet` [ rangeValue := size ]
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
          mkBut graphMenu "collapse after simplify" setCollapse
          mkBut graphMenu "collapse -->" $ transformGraph 0
          mkBut graphMenu "collapse level" collapseStep
          mkBut graphMenu "collapse <--" $ transformGraph 1
          mkBut graphMenu "remove copies" removeCopies
          mkBut graphMenu "show graph" $ transformGraph 2
          let mkMenu m n1 n2 n3 n4 = do
                 mkBut m "here" $ cmd n1
                 mkBut m "with state equivalence" $ cmd n2
                 mkBut m "in painter" (do initCanvas; cmd n3)
                 mkBut m ("in "++ other) $ cmd n4
                 where cmd = showTransOrKripke
          subMenu <- mkSub graphMenu "of transitions"
          mkMenu subMenu 0 1 2 3
          subMenu <- mkSub graphMenu "of labelled transitions"
          mkMenu subMenu 4 5 6 7
          let mkMenu m n1 n2 n3 = do
                 mkBut m "here" $ cmd n1
                 mkBut m "in painter" (do initCanvas; cmd n2)
                 mkBut m ("in "++ other) $ cmd n3
                 where cmd = showTransOrKripke
          subMenu <- mkSub graphMenu "of Kripke model"
          mkMenu subMenu 8 9 10
          subMenu <- mkSub graphMenu "of labelled Kripke model"
          mkMenu subMenu 11 12 13
          mkBut graphMenu "build iterative equations" $ transformGraph 3
          mkBut graphMenu "connect equations" $ modifyEqs 0
          let mkMenu m cmd n1 n2 n3 n4 = do
                  mkBut m "of canvas" $ cmd n1
                  mkBut m "of transitions" $ cmd n2
                  mkBut m "of atom values" $ cmd n3
                  mkBut m "of output" $ cmd n4
          subMenu <- mkSub graphMenu "show Boolean matrix"
          mkMenu subMenu (\x -> initCanvas >> showMatrix x) 6 0 1 2
          subMenu <- mkSub graphMenu "show list matrix"
          mkMenu subMenu (\x -> initCanvas >> showMatrix x) 7 3 4 5
          subMenu <- mkSub graphMenu "show binary relation"
          mkMenu subMenu showRelation 6 0 1 2
          subMenu <- mkSub graphMenu "show ternary relation"
          mkMenu subMenu showRelation 7 3 4 5
          
          treeMenu <- getMenu "treeMenu"
          subMenu <- mkSub treeMenu "call enumerator"
          mapM_ (mkButF subMenu callEnum) enumerators
          mkBut treeMenu "remove other trees" removeOthers
          mkBut treeMenu "show changed" showChanged
          mkBut treeMenu "show proof" $ showProof True
          mkBut treeMenu (".. in text field of "++ other) $ showProof False
          mkBut treeMenu "save proof to file (s)" saveProof
          mkBut treeMenu "show proof term" $ showProofTerm True
          mkBut treeMenu (".. in text field of "++ other) $ showProofTerm False
          mkBut treeMenu "check proof term from file" $ checkProofF False
          mkBut treeMenu ".. in painter" $ checkProofF True
          mkBut treeMenu ".. from text field" $ checkProofT False
          mkBut treeMenu ".. in painter" $ checkProofT True
          mkBut treeMenu "create induction hypotheses" createIndHyp
          mkBut treeMenu "save tree to file" $ getFileAnd saveTree
          mkBut treeMenu "load text from file" $ getFileAnd $ loadText True
          mkBut treeMenu (".. in text field of "++ other) $ getFileAnd 
                                                          $ loadText False
          mkBut treeMenu "permute factors/summands" permuteGoal
          
          nodesMenu <- getMenu "nodesMenu"
          mkBut nodesMenu "greatest lower bound" showGlb
          mkBut nodesMenu "predecessors" showPreds
          mkBut nodesMenu "successors" showSucs
          mkBut nodesMenu "constructors" $ showSyms constrPositions
          mkBut nodesMenu "values" showVals
          mkBut nodesMenu "variables" $ showSyms varPositions
          mkBut nodesMenu "free variables" $ showSyms freePositions
          mkBut nodesMenu "label roots with entry (l)" replaceNodes
          mkBut nodesMenu "polarities" showPolarities
          mkBut nodesMenu "positions" showPositions
          mkBut nodesMenu "level numbers" $ showNumbers 1
          mkBut nodesMenu "preorder numbers" $ showNumbers 2
          mkBut nodesMenu "heap numbers" $ showNumbers 3
          mkBut nodesMenu "hill numbers" $ showNumbers 4
          mkBut nodesMenu "coordinates" showCoords
          mkBut nodesMenu "cycle targets" showCycleTargets
          
          interpreterMenu <- getMenu "interpreterMenu"
          mapM_ (mkButF interpreterMenu setInterpreter') interpreters

          sigMenu <- getMenu "sigMenu"
          mkBut sigMenu "admit all simplifications" $ setAdmitted' True []
          mkBut sigMenu ".. except for symbols" $ setAdmitted True
          mkBut sigMenu ".. for symbols" $ setAdmitted False
          but <- mkBut sigMenu (eqsButMsg False) switchSafe
          writeIORef safeButRef but
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
          mkBut streeMenu "stretch premise" $ stretch True
          mkBut streeMenu "stretch conclusion" $ stretch False
          mkBut streeMenu "instantiate" instantiate
          mkBut streeMenu "unify" unifySubtrees
          mkBut streeMenu "generalize" generalize
          mkBut streeMenu "specialize" specialize
          mkBut streeMenu "decompose atom" decomposeAtom
          mkBut streeMenu "replace by other sides of in/equations"
                  replaceSubtrees
          mkBut streeMenu "use transitivity" applyTransitivity
          subMenu <- mkSub streeMenu "apply clause"
          mkBut subMenu "Left to right (Left)" $ applyClause False False False
          mkBut subMenu ".. and save redex" $ applyClause False False True
          mkBut subMenu "Left to right lazily" $ applyClause True False False
          mkBut subMenu ".. and save redex" $ applyClause True False True
          mkBut subMenu "Right to left (Right)" $ applyClause False True False
          mkBut subMenu ".. and save redex" $ applyClause False True True
          mkBut subMenu "Right to left lazily" $ applyClause True True False
          mkBut subMenu ".. and save redex" $ applyClause True True True
          mkBut streeMenu "move up quantifiers" shiftQuants
          mkBut streeMenu "shift subformulas" shiftSubs
          mkBut streeMenu "coinduction" $ startInd False
          mkBut streeMenu "induction" $ startInd True
          mkBut streeMenu "create Hoare invariant" $ createInvariant True
          mkBut streeMenu "create subgoal invariant" $ createInvariant False
          mkBut streeMenu "flatten (co-)Horn clause" flattenImpl
          mkBut streeMenu "shift pattern to rhs" shiftPattern
          mkBut streeMenu ("replace by tree of "++ other) replaceOther
          mkBut streeMenu ("unify with tree of "++ other) unifyOther
          mkBut streeMenu "build unifier" buildUnifier
          mkBut streeMenu "subsume" subsumeSubtrees
          mkBut streeMenu "evaluate" evaluateTrees
          mkBut streeMenu "copy (c)" copySubtrees
          mkBut streeMenu "remove (r)" removeSubtrees
          mkBut streeMenu "remove node (o)" removeNode
          mkBut streeMenu "reverse (v)" reverseSubtrees
          mkBut streeMenu "insert/replace by text (i)" replaceText
          mkBut streeMenu "random labels (L)" randomLabels
          mkBut streeMenu "random tree (T)" randomTree
          mkBut streeMenu "remove path (p)" removePath

          subsMenu <- getMenu "subsMenu"
          mkBut subsMenu "add from text field" addSubst
          mkBut subsMenu "apply" applySubst
          mkBut subsMenu "rename" renameVar
          mkBut subsMenu "remove" removeSubst
          mkBut subsMenu "show" $ showSubst True
          mkBut subsMenu (".. in text field of "++ other) $ showSubst False
          mkBut subsMenu (".. on canvas of "++ other) showSubstCanv
          mkBut subsMenu ".. solutions" showSolutions

          specMenu <- getMenu "specMenu"
          mkBut specMenu "re-add" reAddSpec
          mkBut specMenu "remove"
                $ do removeSpec; labGreen' $ iniSpec++iniSigMap
          mkBut specMenu "set pic directory (t)" $ setPicDir False
          mkBut specMenu "build Kripke model" $ buildKripke 2
          mkBut specMenu ".. from current graph" $ buildKripke 3
          mkBut specMenu ".. from regular expression" $ buildKripke 4
          mkBut specMenu ".. cycle-free" $ buildKripke 0
          mkBut specMenu ".. pointer-free" $ buildKripke 1
          mkBut specMenu "state equivalence" stateEquiv
          mkBut specMenu "minimize" minimize
          mkBut specMenu "build regular expression" buildRegExp
          mkBut specMenu "distribute regular expression" $ reduceRegExp 0
          mkBut specMenu "reduce left-folded regular expression"$ reduceRegExp 1
          mkBut specMenu ".. right-folded regular expression" $ reduceRegExp 2
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
          mkBut thsMenu (".. in text field of "++ other) $ showTheorems False
          mkBut thsMenu ".. for symbols" showTheoremsFor
          mkBut thsMenu "remove theorems" removeTheorems
          mkBut thsMenu ".. in entry field" $ removeClauses 1
          subMenu <- mkSub thsMenu "add theorems"
          createSub 1 subMenu
          mkBut thsMenu "show terms" showTerms
          mkBut thsMenu "show conjects" showConjects
          mkBut thsMenu ".. in entry field" $ removeClauses 3
          mkBut thsMenu "remove conjects" removeConjects
          mkBut thsMenu ".. in entry field" $ removeClauses 2
          mkBut thsMenu "show induction hypotheses" showIndClauses
          subMenu <- mkSub thsMenu "add conjects"
          createSub 2 subMenu

          treeSize `on` valueChanged $ drawNewCurr
          
          horBut <- getObject castToScale "horBut"
          horBut `on` valueChanged $ do
              val <- truncate <$> horBut `gtkGet` rangeValue
              blowHor val
              drawNewCurr
          
          verBut <- getObject castToScale "verBut"
          verBut `on` valueChanged $ do
              val <- truncate <$> verBut `gtkGet` rangeValue
              blowVer val
              drawShrinked            

          -- Scroll support for canvas
          containerAdd scrollCanv $ getDrawingArea canv
          changeCanvasBackground white

          win `on` deleteEvent $ lift mainQuit >> return False
          widgetShowAll win

-- end of buildSolve

-- The other methods of solver are listed in alphabetical order:

        -- | Used by 'addClauses' and 'addSpec''.
        addAxioms :: TermS -> String -> Action
        addAxioms t file = do
          sig <- getSignature
          let axs = if isConjunct t then subterms t else [t]
              cls = filter (not . isAxiom sig) axs
          if null cls then do
                           writeIORef solPositionsRef []
                           modifyIORef axiomsRef $ \axioms -> axioms `join` axs
                           modifyIORef simplRulesRef $ \simplRules
                               -> simplRules ++ trips ["==","<==>"] axs
                           modifyIORef transRulesRef $ \transRules
                               -> transRules ++ trips ["->"] axs
                           labGreen' $ newCls "axioms" file
          else do
              enterFormulas' cls
              labRed' "The clauses in the text field are not axioms."

        -- | Used by 'createClsMenu'.
        addClauses :: Int -> FilePath -> Action
        addClauses treetype file = do
            str <- if text then getTextHere else lookupLibs file
            let str' = removeComment 0 str
                file' = if text then "the text field" else file
            sig <- getSignature
            case treetype of
                0 -> case parseE (implication sig) str' of
                        Correct t -> addAxioms t file'
                        p -> incorrect p str' illformedF
                1 -> case parseE (implication sig) str' of
                        Correct t -> addTheorems t file'
                        p -> incorrect p str' illformedF
                _ -> parseConjects sig file' str'
            where text = null file

        addNamedAxioms :: Action
        addNamedAxioms = do
          trees <- readIORef treesRef
          if null trees then labBlue' start
          else do
               str <- ent `gtkGet` entryText
               sig <- getSignature
               trees <- readIORef treesRef
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               let pars = words str
                   b par = par `elem` words "refl symm tran" ||
                           ((sig&isConstruct) ||| (sig&isDefunct)) (init par) &&
                           just (parse digit [last par])
                   t = trees!!curr
                   p = emptyOrLast treeposs
                   pars' = filter b pars
                   axs = case getSubterm t p of
                              F equiv [_,_] -> congAxs equiv pars'
                              _ -> []
               if null pars'
                  then labRed' "Enter axiom names into the entry field."
                  else if null axs then
                          labRed' "Select a binary relation in the current tree."
                       else addNamedAxioms' axs

        addNamedAxioms' axs = do
          modifyIORef axiomsRef $ \axioms -> axioms `join` axs
          modifyIORef indClausesRef $ \indClauses -> indClauses `join` axs
          enterFormulas' axs
          setProofTerm $ AddAxioms axs
          let msg = "Adding\n\n" ++ showFactors axs ++
                    "\n\nto the axioms and applying nothing"
          setProof True False msg [] $ newCls "axioms" "the text field"

        -- | Called by menu items /STACK2IMPL/ and /from file/ from menu
        -- /signature/.
        addSigMap :: FilePath -> IO ()
        addSigMap file = do
            str <- lookupLibs file
            parseSigMap file $ removeComment 0 str

        -- | Called by menu items /from text field/ and /from file/ from menu
        -- /signature/.
        addSigMapT :: Action
        addSigMapT = do
            str <- getTextHere
            parseSigMap "the text field" str

        -- | Adds a specification from file. Used by 'addSpecWithBase',
        -- 'parseSig'. Exported by public 'Epaint.Solver' method
        -- 'Epaint.addSpec'.
        addSpec' :: Bool -> FilePath -> Action
        addSpec' b file = do
            checking <- readIORef checkingRef
            when (not checking) $ do
                when b $ modifyIORef specfilesRef $ \specfiles -> file:specfiles
                str <- get
                if null str then labRed' $ file ++ " is not a file name."
                else do
                    let (sig,axs,ths,conjs,ts) = splitSpec $ removeComment 0 str
                        act1 = do
                            sig <- getSignature
                            if onlySpace axs then act2 sig
                            else case parseE (implication sig) axs of
                                    Correct t -> do
                                        addAxioms t file'
                                        delay $ act2 sig
                                    p -> incorrect p axs illformedF
                        act2 sig =
                            if onlySpace ths then act3 sig
                            else case parseE (implication sig) ths of
                                Correct t -> do
                                    addTheorems t file'
                                    delay $ act3 sig
                                p -> incorrect p ths illformedF
                        act3 sig =
                            if onlySpace conjs then act4 sig
                            else do
                                parseConjects sig file' conjs
                                delay $ act4 sig
                        act4 sig =
                            if onlySpace ts then delay $ return ()
                            else parseTerms sig file' ts
                    if onlySpace sig then act1
                    else do
                        parseSig file' sig
                        delay act1
         where (file',get) = if null file then ("the text field",getTextHere)
                                          else (file,lookupLibs file)
               onlySpace = all (`elem` " \t\n")
        
        -- | Adds base specification first, then loads specification from
        -- given file by calling 'addSpec''. Used by multiple entries from
        -- the "specification" menu. Pressing "Reteurn" in entry field is
        -- equal to menu item "specification"->"add"->"from file (Return)".
        addSpecWithBase :: FilePath -> Action
        addSpecWithBase spec = do
          addSpec' True "base"
          when (spec /= "base") $ addSpec' True spec
        
        -- | Adds substitutions. Called by menu item
        -- /add from text field/ from menu /substitution/.
        addSubst :: Action
        addSubst = do
            str <- getTextHere
            sig <- getSignature
            case parseE (conjunct sig) str of
                Correct t ->
                    if hasPos t then labRed' posInSubst
                    else case eqsToSubst $ mkFactors t of
                        Just (f,dom) -> do
                            (g,xs) <- readIORef substitutionRef
                            setSubst' (g `andThen` f, xs `join` dom)
                            labGreen' extendedSubst
                        _ -> labRed' illformedS
                p -> incorrect p str illformedS
        
        -- | Used by 'enterFormulas'', 'enterTerms', 'enterText'' and
        -- 'enterPT''.
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

        -- | Add theorems from file. Used by 'addClauses', 'addSpec''
        -- and /from SolverN/ menu items created by 'createClsMenu'.
        addTheorems :: TermS -> FilePath -> Action
        addTheorems t file = do
            -- sig <- getSignature
            modifyIORef theoremsRef $ \theorems ->
                theorems `join` if isConjunct t then subterms t else [t]
            labGreen' $ newCls "theorems" file
        
        -- | Called by menu item /apply clause/ from menu /transform selection/.
        applyClause :: Bool -> Bool -> Bool -> Action
        applyClause lazy invert saveRedex = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                str <- ent `gtkGet` entryText
                numberedExps <- readIORef numberedExpsRef
                let (exps,b) = numberedExps
                case parse nat str of
                    k@(Just n) | n < length exps
                      -> if b then if lazy then stretchAndApply k $ exps!!n
                                           else finish k $ exps!!n
                        else labMag "Enter formulas into the text field!"
                    _ -> do
                        str <- getTextHere
                        sig <- getSignature
                        case parseE (implication sig) str of
                              Correct cl | lazy -> stretchAndApply Nothing cl
                                         | True -> finish Nothing cl
                              p -> incorrect p str illformedF
          where stretchAndApply k cl = do
                 varCounter <- readIORef varCounterRef
                 let zNo = varCounter "z"
                 case preStretch True (const True) cl of
                      Just (_,varps) -> do
                                        setZcounter n; finish k clp
                                        where (clp,n) = stretchPrem zNo varps cl
                      _ -> case preStretch False (const True) cl of
                                Just (_,varps) -> do setZcounter n; finish k clc
                                        where (clc,n) = stretchConc zNo varps cl
                                _ -> notStretchable "The left-hand side"
                finish k cl = applyTheorem saveRedex k $
                                          if invert then invertClause cl else cl

        
        -- | Used by 'checkForward' and 'startInd'.
        applyCoinduction :: Int -> Action
        applyCoinduction limit = do
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
              str = "COINDUCTION"
              g = stretchConc $ varCounter "z"
              getAxioms = flip noSimplsFor axioms
              h x = if x `elem` fst newPreds then getPrevious x else x
              conjs@(conj:_) = map (mapT h) $ map (getSubterm t) qs
              f = preStretch False (sig&isCopred)
          if notnull qs && any null ps then labRed' $ noApp str
          else if null ps && universal sig t p conj
                 then case f conj of
                      Just (x,varps)
                        -> do
                           let (conj',k) = g varps conj; axs = getAxioms [x]
                           setZcounter k
                           applyInd limit False str [conj'] [x] axs t p []
                      _ -> notStretchable "The conclusion"
                 else if allEqual rs && isConjunct u && universal sig t r u then
                         case mapM f conjs of
                         Just symvarpss
                           -> do
                              let (xs,varpss) = unzip symvarpss
                                  (conjs',ks) = unzip $ zipWith g varpss conjs
                                  ys = mkSet xs; axs = getAxioms ys
                              modifyIORef varCounterRef
                                $ \varCounter -> updMax varCounter "z" ks
                              applyInd limit False str conjs' ys axs t r $
                                                       restInd (subterms u) qs
                         _ -> notStretchable "Some conclusion"
                      else labRed' $ noApp str


        
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
          if all noQuantsOrConsts ts && polarity True t pred && isDisjunct u &&
             all (isProp sig ||| isAnyQ) (sucTerms u qs)
             then finishDisCon k False True ts prem redices t ps pred qs sig msg
          else labRed' $ noAppT k
        applyDisCon k (F "<===" [F "&" ts,prem]) redices t ps sig msg = do
          let pred = glbPos ps
              u = getSubterm t pred
              qs = map (restPos pred) ps
          if all noQuantsOrConsts ts && polarity True t pred && isConjunct u && 
             all (isProp sig ||| isAllQ) (sucTerms u qs)
            then finishDisCon k False False ts prem redices t ps pred qs sig msg
          else labRed' $ noAppT k
        applyDisCon k (F "===>" [F "&" ts,conc]) redices t ps sig msg = do
          let pred = glbPos ps
              u = getSubterm t pred
              qs = map (restPos pred) ps
          if all noQuantsOrConsts ts && polarity False t pred && isConjunct u &&
             all (isProp sig ||| isAllQ) (sucTerms u qs)
             then finishDisCon k True True ts conc redices t ps pred qs sig msg
          else labRed' $ noAppT k
        applyDisCon k (F "===>" [F "|" ts,conc]) redices t ps sig msg = do
          let pred = glbPos ps
              u = getSubterm t pred
              qs = map (restPos pred) ps
          if all noQuantsOrConsts ts && polarity False t pred && isDisjunct u &&
             all (isProp sig ||| isAnyQ) (sucTerms u qs)
             then finishDisCon k True False ts conc redices t ps pred qs sig msg
          else labRed' $ noAppT k
        
        -- Used by 'applyCoinduction' and 'applyInduction'.
        applyInd :: Int -> Bool -> String -> [TermS] -> [String] -> [TermS]
                 -> TermS -> [Int] -> [TermS] -> Action
        applyInd limit ind str conjs indsyms axs t p rest = do
          sig <- getSignature
          varCounter <- readIORef varCounterRef
          (nps,ncps) <- readIORef newPredsRef
          let syms = if ind then ncps else nps
              vc1 = decrVC varCounter syms
              indsyms' = indsyms `join` map getPrevious syms
              (f,vc2) = renaming vc1 indsyms'
              axs0 = map mergeWithGuard axs
              (axs1,vc3) = iterate h (axs0,vc2)!!limit
              h (axs,vc) = applyToHeadOrBody sig (((`elem` indsyms') .) . label)
                                                 False axs0 axs vc
              newAxs = map mkAx conjs
              mkAx (F x [t,u]) = F x [g t,u]
              mkAx _           = error "applyInd"
              -- g replaces a logical predicate r by f(r) and an equation
              -- h(t)=u with h in xs by the logical atom f(h)(t,u).
              g eq@(F "=" [F x ts,u]) = if x `elem` indsyms'
                                        then F (f x) $ ts++[u] else eq
              g (F x ts)              = F (f x) $ map g ts
              g t                     = t
              rels = map f indsyms'
              (ps',cps') = if ind then ([],rels) else (rels,[])
          (ps,cps,cs,ds,fs,hs) <- readIORef symbolsRef
          writeIORef symbolsRef (ps `join` ps',cps `join` cps',cs,ds,fs,hs)
          writeIORef newPredsRef (nps `join` ps',ncps `join` cps')
          sig <- getSignature
          let (cls,vc4) = applyToHeadOrBody sig (const2 True) True newAxs
                                                (map g axs1) vc3
              conj = mkConjunct cls
              xs = [x | x <- frees sig conj, noExcl x]
              u = replace t p $ mkConjunct $ mkAll xs conj:rest
              msg = "Adding\n\n" ++ showFactors newAxs ++
                 "\n\nto the axioms and applying " ++ str ++ " wrt\n\n"
                 ++ showFactors axs1 ++ "\n\n"
          modifyIORef indClausesRef (`join` newAxs)
          modifyIORef axiomsRef (`join` newAxs)
          writeIORef varCounterRef vc4
          writeIORef proofStepRef $ Induction ind limit
          maybeSimplify sig u
          makeTrees sig
          proofStep <- readIORef proofStepRef
          setProofTerm proofStep
          setTreesFrame []
          setProof True True msg [p] $ indApplied str
        
        -- | Used by 'checkForward' and 'startInd'.
        applyInduction :: Int -> Action
        applyInduction limit = do
            trees <- readIORef treesRef
            curr <- readIORef currRef
            treeposs <- readIORef treepossRef
            varCounter <- readIORef varCounterRef
            let t = trees!!curr
                qs@(p:ps) = emptyOrAll treeposs
                rs@(r:_) = map init qs
                u = getSubterm t r
                str = "FIXPOINT INDUCTION"
                g = stretchPrem $ varCounter "z"
            if notnull qs && any null ps then labRed' $ noApp str
            else do
                sig <- getSignature
                newPreds <- readIORef newPredsRef
                let h (F x ts) = if x `elem` snd newPreds
                                 then if isPred sig z then F z ts
                                      else mkEq (F z $ init ts) $ last ts
                                 else F x $ map h ts where z = getPrevious x
                    h t               = t
                    conjs@(conj:_) = map (h . getSubterm t) qs
                    f = preStretch True $ isPred sig ||| isDefunct sig
                    getAxioms ks xs = unzip . map g . noSimplsFor xs
                      where g = flatten (maximum ks) $ filter (isDefunct sig) xs
                if null ps && universal sig t p conj
                then case f conj of
                        Just (x,varps) -> do
                            axioms <- readIORef axiomsRef
                            let (conj',k) = g varps conj
                                (axs,ms) = getAxioms [k] [x] axioms
                            modifyIORef varCounterRef $ \varCounter ->
                                updMax varCounter "z" ms
                            applyInd limit True str [conj'] [x] axs t p []
                        _ -> notStretchable "The premise"
                else
                    if allEqual rs && isConjunct u && universal sig t r u
                    then case mapM f conjs of
                        Just symvarpss -> do
                            axioms <- readIORef axiomsRef
                            let (xs,varpss) = unzip symvarpss
                                (conjs',ks) = unzip $ zipWith g varpss conjs
                                ys = mkSet xs; (axs,ms) = getAxioms ks ys axioms
                            modifyIORef varCounterRef $ \varCounter ->
                                updMax varCounter "z" ms
                            applyInd limit True str conjs' ys axs t r $
                                     restInd (subterms u) qs
                        _ -> notStretchable "Some premise"
                    else labRed' $ noApp str
        
        -- | Called by menu item /apply map/ from menu /signature/.
        applySigMap :: Action
        applySigMap = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                signatureMap <- readIORef signatureMapRef
                curr <- readIORef currRef
                formula <- readIORef formulaRef
                solve <- readIORef solveRef
                other <- getSolver solve
                sig <- getSignature
                sig' <- getSignatureR solve
                case applySignatureMap sig sig' (fst signatureMap) $ trees!!curr
                    of Just t -> do bigWin solve; enterTree solve formula t
                       _ -> labRed' $ sigMapError other
        
        -- | Called by menu item /apply/ from menu /substitution/.
        applySubst :: Action
        applySubst = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                -- sig <- getSignature
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
                setProofTerm ApplySubst
                setProof False False msg ps subsAppliedToAll
                clearTreeposs; drawCurr'
        
        -- | Used by 'setSubst''.
        applySubstTo :: String -> Action
        applySubstTo x = do
            trees <- readIORef treesRef
            substitution <- readIORef substitutionRef

            if null trees then labBlue' start
                          else applySubstTo' x $ fst substitution x
        
        -- | Used by 'applySubstTo' and 'checkForward'.
        applySubstTo' :: String -> TermS -> Action
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
                    Just q
                        | polarity False t q -> finish (q++[0]) t sig msg True
                    _ -> finish p t sig msg False
            where finish p t sig msg b = do
                    curr <- readIORef currRef

                    modifyIORef treesRef $ \trees -> updList trees curr t'
                    setProofTerm $ ApplySubstTo x v
                    drawThis t' (map (p++) $ freeXPositions sig x u) "green"
                    setProof b False msg [p] $ subsAppliedTo x
                    (f,dom) <- readIORef substitutionRef
                    setSubst' (upd f x $ V x, dom `minus1` x)
                    where t' = replace t p $ u>>>for v x
                          u = getSubterm t p
        
        -- | Used by 'checkForward', 'specialize' and 'applyClause'.
        applyTheorem :: Bool -> Maybe Int -> TermS -> Action
        applyTheorem saveRedex k th = do
            sig <- getSignature
            writeIORef proofStepRef $ Theorem saveRedex th
            trees <- readIORef treesRef
            curr <- readIORef currRef
            treeposs <- readIORef treepossRef
            varCounter <- readIORef varCounterRef
            let t = trees!!curr
                ps = emptyOrAll treeposs
                redices = map (getSubterm t) ps
                n = length ps
                ([th'],vc) =
                    renameApply [if saveRedex then copyRedex th else th]
                                            sig t varCounter
                f t (redex:rest) (p:ps) qs vc
                            = case applySingle th' redex t p sig vc of
                                        Just (t,vc) -> f t rest ps (p:qs) vc
                                        _ -> f t rest ps qs vc
                f _ _ _ [] _  = labRed' $ notUnifiable k
                f t _ _ qs vc = do
                            writeIORef varCounterRef vc
                            maybeSimplify sig t
                            makeTrees sig
                            finish qs
                str = showTree False $ case th of
                    F "===>" [F "True" [],th] -> th
                    F "<===" [F "False" [],th] -> mkNot sig th
                    _ -> th
                finish qs = do
                    proofStep <- readIORef proofStepRef
                    setProofTerm proofStep
                    setTreesFrame []
                    setProof True True (applied True str) qs
                                           $ thApplied k
            when (nothing k) $ enterText' str
            if isTaut th then do
                writeIORef varCounterRef vc
                f t redices ps [] vc
            else
                if n > 1 && isDisCon th && n == noOfComps th
                then do
                    writeIORef varCounterRef vc
                    applyDisCon k th' redices t ps sig $ applied True str
                else
                  if saveRedex || isSimpl th || all (correctPolarity t) ps
                     then if isAxiom sig th then
                             narrowOrRewritePar t sig k [th] saveRedex ps
                          else if isTheorem th then do
                                                    writeIORef varCounterRef vc
                                                    f t redices ps [] vc 
                                               else labRed' $ noTheorem k
                     else labRed' $ noAppT k
            where correctPolarity t p = isHornT th && b || isCoHornT th && not b
                                     where b = polarity True t p
        
        -- | Used by 'checkForward'. Called by menu item
        -- /use transitivity/ from menu /transform selection/.
        applyTransitivity :: Action
        applyTransitivity = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    ps = emptyOrAll treeposs
                    redices = map (getSubterm1 t) ps
                case redices of
                    F x [l,r]:_ -> do
                        varCounter <- readIORef varCounterRef
                        let p:qs = ps
                            n = varCounter "z"
                            z = 'z':show n
                            n' = n+1
                        if transitive x && null qs && polarity True t p then do
                            let u = anyConj [z] [F x [l,V z],F x [V z,r]]
                            curr <- readIORef currRef
                            modifyIORef treesRef $ \trees ->
                                updList trees curr $ replace1 t p u
                            setZcounter n'
                        else do
                            let z' = 'z':show n'
                                u | qs == [p ++ [0]]
                                    = anyConj [z] [mkEq l $ V z, F x [V z, r]]
                                  | qs == [p ++ [1]]
                                    = anyConj [z] [F x [l, V z], mkEq (V z) r]
                                  | otherwise
                                    = anyConj [z, z'] [mkEq l $ V z
                                                      , F x [V z, V z']
                                                      , mkEq (V z') r]
                            curr <- readIORef currRef
                            modifyIORef treesRef $ \trees ->
                                updList trees curr $ replace1 t p u
                            setZcounter $ n'+1
                        finish ps
                    _ ->
                        if any null ps then labMag "Select proper subtrees!"
                        else do
                            let qs = map init ps
                                q = head qs
                                u = getSubterm t q
                            if allEqual qs && isConjunct u then
                                case transClosure redices of
                                    Just v ->
                                        if polarity False t q then do
                                            let us = v:removeTerms (subterms u)
                                                        redices
                                                t' = replace1 t q
                                                    $ mkConjunct us
                                            curr <- readIORef currRef
                                            modifyIORef treesRef $ \trees ->
                                                updList trees curr t'
                                            finish ps
                                        else labRed' $ noApp "Transitivity"
                                    _ -> labMag "Select composable atoms!"
                            else labRed' $ noApp "Transitivity"
            where anyConj xs = mkAny xs . F "&"
                  finish ps = do
                        setProofTerm ApplyTransitivity
                        setProof True False "TRANSITIVITY" ps
                            transitivityApplied
                        clearTreeposs; drawCurr'

        -- | Called by button "<---" ('backBut') or keypress "Up" while left
        -- label ('lab') is active.
        backProof :: Action
        backProof = do
            restore <- readIORef restoreRef
            if restore then do
                oldTreeposs <- readIORef oldTreepossRef
                writeIORef treepossRef oldTreeposs
                writeIORef restoreRef False
                drawCurr'
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
        
        -- | Minimize solver window. Exported by public 'Epaint.Solver' method
        -- 'Epaint.backWin'.
        backWin' :: Action
        backWin' = windowIconify  win
        
        -- | Bring solver window to front, even if minimized. Exported by public
        -- 'Epaint.Solver' method 'Epaint.bigWin'.
        bigWin' :: Action
        bigWin' = windowDeiconify  win >> windowPresent  win
        
        -- | Used by slider horBut.
        blowHor :: Int -> Action
        blowHor i = do
            modifyIORef spreadRef $ \spread -> (i,snd spread)
            picEval <- readIORef picEvalRef
            spread <- readIORef spreadRef
            setEval paint picEval spread
        
        -- | Used by slider verBut.
        blowVer :: Int -> Action
        blowVer i = do
            modifyIORef spreadRef $ \spread -> (fst spread,i)
            picEval <- readIORef picEvalRef
            spread <- readIORef spreadRef
            setEval paint picEval spread
        
        {-
            | Builds a Kripke model based on the given @mode@.
            0 -> cycle free
            1 -> pointer-free
            2 -> normal
            3 -> rebuild last one
            4 -> from current graph
            Used by 'checkForward' and multiple entries from "specification"
            menu.
        -}
        buildKripke :: Int -> Action
        buildKripke 3 = do                              -- from current graph
          trees <- readIORef treesRef
          if null trees then labBlue' start
          else do
            curr <- readIORef currRef
            let t = trees!!curr
                (states',atoms',rules') = graphToTransRules t
            changeSimpl "states" $ mkList states'
            changeSimpl "atoms" $ mkList atoms'
            changeSimpl "labels" $ mkList []
            writeIORef transRulesRef rules'
            writeIORef kripkeRef (states',atoms',[],[],[],[],[])
            sig <- getSignature
            let (rs1,_) = rewriteSig sig (sig&states)
                (rs2,_) = rewriteSig sig (sig&atoms)
                tr = pairsToInts states' rs1 states'
                va = pairsToInts states' rs2 atoms'
            writeIORef kripkeRef (states',atoms',[],tr,[],va,[])
            delay $ setProof True False kripkeMsg []
                     $ kripkeBuilt 3 0 (length states') 0 $ length atoms'

        buildKripke 4 = do                            -- from regular expression
          trees <- readIORef treesRef
          if null trees then labBlue' start
          else do
               sig <- getSignature
               trees <- readIORef treesRef
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               let t = trees!!curr
                   p = emptyOrLast treeposs
               case parseRE sig $ getSubterm t p of
                 Just (e,as) -> do
                    let (_,nda) = regToAuto e
                        as' = as `minus1` "eps"
                        (sts,delta) = powerAuto nda as' 
                        finals = searchAll (elem 1) sts
                        mkTerm = mkList . map mkConst
                        f (st,a) = (mkPair (mkTerm st) $ leaf a,[],
                                    mkTerm $ delta st a)
                        states' = map mkTerm sts
                        labels' = map leaf as'
                        atom' = leaf "final"
                    changeSimpl "states" $ mkList states'
                    changeSimpl "atoms" $ mkList [atom']
                    changeSimpl "labels" $ mkList labels'
                    writeIORef transRulesRef $ map f $ prod2 sts as'
                    writeIORef kripkeRef (states',[atom'],labels',[],[],[],[])
                    sig <- getSignature
                    let (_,rsL) = rewriteSig sig (sig&states)
                        trL = tripsToInts states' labels' rsL states'
                    writeIORef kripkeRef
                      (states',[atom'],labels',[],trL,[finals],[])
                    delay $ setProof True False kripkeMsg []
                          $ kripkeBuilt 4 0 (length sts) (length as') 1
                 _ -> labMag "Select a regular expression!"

        buildKripke mode = do
          trees <- readIORef treesRef
          when (null trees) $ enterTree' False $ V""
          str <- ent `gtkGet` entryText
          sig <- getSignature
          let noProcs = if (sig&isDefunct) "procs" 
                           then case parse pnat str of Just n -> n; _ -> 0
                           else 0
          when (noProcs > 0) $ changeSimpl "procs" $ mkConsts [0..noProcs-1]
          simplRules <- readIORef simplRulesRef
          let iniStates = [t | (F "states" _,_,t) <- simplRules]
          changeSimpl "states" $ if null iniStates then mkList [] 
                                                   else head iniStates
          delay $ buildKripke1 mode noProcs

        buildKripke1 mode noProcs = do
          sig <- getSignature
          let simplify x = case simplifyIter sig $ leaf x of F "[]" ts -> ts
                                                             _ -> []
              [states,atoms',labels] = map simplify
                $ words "states atoms labels"
          writeIORef kripkeRef (states,atoms',labels,[],[],[],[])
          changeSimpl "states" $ mkList states
          changeSimpl "atoms"  $ mkList atoms'
          changeSimpl "labels" $ mkList labels
          
          sig <- getSignature
          let (states,rs,rsL) = rewriteStates sig mode
              tr  = pairsToInts states rs states
              trL = tripsToInts states labels rsL states
          writeIORef kripkeRef (states,atoms',labels,tr,trL,[],[])
          changeSimpl "states" $ mkList states
          delay $ buildKripke2 mode noProcs states atoms' labels tr trL
        
        buildKripke2 mode noProcs states atoms' labels tr trL = do
          sig <- getSignature
          let (rs,rsL) = rewriteSig sig (sig&atoms)
              va  = pairsToInts states rs atoms'
              vaL = tripsToInts states labels rsL atoms'
          writeIORef kripkeRef (states,atoms',labels,tr,trL,va,vaL)
          delay $ setProof True False kripkeMsg []
                $ kripkeBuilt mode noProcs (length states) (length labels)
                $ length atoms'
        
        buildRegExp = do
          trees <- readIORef treesRef
          if null trees then labBlue' start
          else do
               str <- ent `gtkGet` entryText
               sig <- getSignature
               let finish start = do
                      trees <- readIORef treesRef
                      curr <- readIORef currRef
                      writeIORef treesRef
                        $ updList trees curr $ showRE $ autoToReg sig start
                      setProofTerm BuildRE
                      setProof False False "BUILDING A REGULAR EXPRESSION" []
                                           regBuilt
                      clearTreeposs; drawCurr'
               case parse (term sig) str of
                    Just start | start `elem` (sig&states) -> finish start
                    _ -> do
                         trees <- readIORef treesRef
                         curr <- readIORef currRef
                         treeposs <- readIORef treepossRef
                         let start = label (trees!!curr) $ emptyOrLast treeposs
                         case parse (term sig) $ takeWhile (/= ':') start of
                              Just start | start `elem` (sig&states)
                                -> finish start
                              _ -> labRed' "Enter or select an initial state!"
        
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
            writeIORef wtreeRef False
            writeIORef matchingRef 0
            matchBut `gtkSet` [ buttonLabel := "match" ]
            splitBut `gtkSet` [ buttonLabel := "join" ]
            setBackground matchBut blueback
            mapM_ (`setBackground` blueback)
                [deriveBut,narrowBut,simplButD,simplButB]
            clearTreeposs
            setInterpreter' obj
            sig <- getSignature
            let ts = case simplifyIter sig $ F "compl" [] of F "[]" us -> us
                                                             _ -> []
                compl = curry $ setToFun $ zipWith f (evens ts) $ odds ts
                      where f t u = (showTerm0 t,showTerm0 u)
            (enum&buildEnum) obj $ if obj `elem` ["alignment","palindrome"]
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
                    _ -> return ()
        
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
                            setTreeposs (Add [p])
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
        
        -- | Changes the background of the canvas area.
        changeCanvasBackground :: Color -> Action
        changeCanvasBackground c@(RGB r g b) = do
            let f n = fromIntegral $ n * 256
                (r', g' , b') = (f r, f g, f b)
            canv `gtkSet` [ canvasBackground := c ]
            widgetModifyBg scrollCanv StateNormal $ gtkColor r' g' b'
        
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
                setNarrow False False
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
            safe <- readIORef safeRef
            joined <- readIORef joinedRef
            safeBut <- readIORef safeButRef

            let proofElem = proof!!ptr
            writeIORef treesRef $ peTrees proofElem
            modifyIORef counterRef $ \counter -> upd counter 't' $ length trees
            writeIORef treeModeRef $ peTreeMode proofElem
            writeIORef currRef $ peCurr proofElem
            writeIORef permsRef $ pePerms proofElem
            writeIORef varCounterRef $ peVarCounter proofElem
            writeIORef newPredsRef $ peNewPreds proofElem
            writeIORef solPositionsRef $ peSolPositions proofElem
            writeIORef constraintsRef $ peConstraints proofElem
            writeIORef joinedRef $ peJoined proofElem
            writeIORef safeRef $ peSafe proofElem
            setTreesFrame ps
            setSubst' (peSubstitution proofElem)
            labGreen' (peMsgL proofElem)
            safeBut `gtkSet` [ menuItemLabel := eqsButMsg $ not safe ]
            splitBut `gtkSet` [ buttonLabel := if joined then "split" else "join" ]
        
        -- | Used by 'backProof'.
        checkBackward :: Action
        checkBackward = do
            proofTPtr <- readIORef proofTPtrRef
            proofTerm <- readIORef proofTermRef

            if proofTPtr < 1 then do
                labMag emptyProof
                labSolver paint emptyProof
                enterPT' proofTPtr proofTerm
            else do
                modifyIORef proofTPtrRef pred
                proofTPtr <- readIORef proofTPtrRef
                case proofTerm!!proofTPtr of
                    Mark _ -> do
                        writeIORef treepossRef []
                        drawCurr'
                    Match _ -> do
                        modifyIORef matchTermRef init
                        matchTerm <- readIORef matchTermRef
                        writeIORef matchingRef $ last matchTerm
                    DeriveMode _ _ -> do
                        modifyIORef simplTermRef init
                        simplTerm <- readIORef simplTermRef
                        writeIORef simplifyingRef $ last simplTerm
                        modifyIORef refuteTermRef init
                        refuteTerm <- readIORef refuteTermRef
                        writeIORef refutingRef $ last refuteTerm
                    NegateAxioms ps1 cps1 -> do
                        proofPtr <- readIORef proofPtrRef
                        (ps,cps,cs,ds,fs,hs) <- readIORef symbolsRef

                        writeIORef symbolsRef
                            (minus ps ps2,minus cps cps2,cs,ds,fs,hs)
                        modifyIORef axiomsRef
                            $ \axioms -> axioms `minus` axs axioms
                        when (proofPtr > 0) $ do
                            proof <- readIORef proofRef
                            modifyIORef proofPtrRef pred
                            proofPtr <- readIORef proofPtrRef
                            labColorToPaint greenback (peMsgL (proof!!proofPtr))
                        where ps2 = map mkComplSymbol cps1
                              cps2 = map mkComplSymbol ps1
                              axs = noSimplsFor (ps2++cps2)
                    _ -> do
                        proofPtr <- readIORef proofPtrRef
                        when (proofPtr > 0) $ do
                            proof <- readIORef proofRef
                            modifyIORef proofPtrRef pred
                            proofPtr <- readIORef proofPtrRef
                            changeState proofPtr $ peTreePoss (proof!!proofPtr)
                enterPT' proofTPtr proofTerm
        
        -- | Used by 'forwProof'' and 'runChecker'.
        checkForward :: Action
        checkForward = do
            proofTPtr <- readIORef proofTPtrRef
            proofTerm <- readIORef proofTermRef
            if proofTPtr >= length proofTerm then do
                labMag endOfProof
                labSolver paint endOfProof
                enterPT' proofTPtr proofTerm
            else do
                proofPtr <- readIORef proofPtrRef
                let step = proofTerm!!proofTPtr
                    k = proofPtr+1
                proof <- readIORef proofRef
                when (deriveStep step && k < length proof)
                    $ writeIORef proofPtrRef k
                case step of
                    AddAxioms axs -> addNamedAxioms' axs
                    ApplySubst -> applySubst
                    ApplySubstTo x t -> applySubstTo' x t
                    ApplyTransitivity -> applyTransitivity
                    BuildKripke m -> buildKripke m
                    BuildRE -> buildRegExp
                    CollapseStep -> collapseStep
                    ComposePointers -> composePointers
                    CopySubtrees -> copySubtrees
                    CreateIndHyp -> createIndHyp
                    CreateInvariant b -> createInvariant b
                    DecomposeAtom -> decomposeAtom
                    DeriveMode s r -> do
                        writeIORef simplifyingRef s
                        writeIORef refutingRef r
                        modifyIORef simplTermRef $ \simplTerm -> simplTerm++[s]
                        modifyIORef refuteTermRef
                            $ \refuteTerm -> refuteTerm++[r]
                    EvaluateTrees -> evaluateTrees
                    ExpandTree b n -> expandTree' b n
                    FlattenImpl -> flattenImpl
                    Generalize cls -> generalize' cls
                    Induction True n -> applyInduction n
                    Induction _ n -> applyCoinduction n
                    Mark ps -> do
                        writeIORef treepossRef ps
                        drawCurr'
                    Match n -> do
                        writeIORef matchingRef n
                        modifyIORef matchTermRef $ \matchTerm -> matchTerm++[n]
                    Minimize -> minimize
                    ModifyEqs m -> modifyEqs m
                    Narrow limit sub -> narrow'' limit sub
                    NegateAxioms ps cps -> negateAxioms' ps cps
                    RandomLabels -> randomLabels
                    RandomTree -> randomTree
                    ReduceRE m -> reduceRegExp m
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
                    SafeEqs -> switchSafe
                    SetAdmitted block xs -> setAdmitted' block xs
                    SetCurr msg n -> setCurr msg n
                    Simplify depthfirst limit sub
                                  -> simplify'' depthfirst limit sub
                    ShiftPattern -> shiftPattern
                    ShiftQuants -> shiftQuants
                    ShiftSubs ps -> shiftSubs' ps
                    SplitTree -> splitTree
                    StretchConclusion -> stretch False
                    StretchPremise -> stretch True
                    SubsumeSubtrees -> subsumeSubtrees
                    Theorem b th -> applyTheorem b Nothing th
                    Transform m -> transformGraph m
                    UnifySubtrees -> unifySubtrees
                modifyIORef proofTPtrRef succ
                enterPT' proofTPtr proofTerm
        
        -- | Exported by public 'Epaint.Solver' method 'Epaint.checkInSolver'.
        checkInSolver' :: Action
        checkInSolver' = writeIORef checkingPRef False
        
        -- | Used by 'checkProofF' and 'checkProofT'.
        checkProof :: String -> FilePath -> Action
        checkProof pterm file = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else case parse (list command) $ removeComment 0 pterm of
              Just pt@(DeriveMode s r:Match m:_) -> do
                curr <- readIORef currRef
                fast <- readIORef fastRef
                checkingP <- readIORef checkingPRef
                writeIORef proofTermRef pt
                writeIORef proofTPtrRef 2
                enterPT' 2 pt
                writeIORef simplifyingRef s
                writeIORef simplTermRef [s]
                writeIORef refutingRef r
                writeIORef refuteTermRef [r]
                writeIORef matchingRef m
                writeIORef matchTermRef [m]
                writeIORef treepossRef [[]]
                initialize [] $ showTree fast $ trees!!curr
                quit `gtkSet` [ buttonLabel := "stop check" ]
                setBackground quit redback
                replaceCommandButton quitSignalRef quit setDeriveMode
                labGreen' $ proofLoaded file
                when (not checkingP) $ setInterpreter' "tree"
                runChecker False
              _ -> labRed' $ "There is no proof term in " ++ file ++ "."
        
        -- | Called by check proof options in tree menu.
        checkProofF :: Bool -> Action
        checkProofF inPainter = do
            str <- ent `gtkGet` entryText
            case words str of
                [file,sp] -> do
                    pterm <- lookupLibs file
                    writeIORef checkingRef True
                    writeIORef checkingPRef inPainter
                    let newSpeed = parse pnat sp
                    when (just newSpeed)
                       $ writeIORef speedRef $ get newSpeed
                    checkProof pterm file
                [file] -> do
                    pterm <- lookupLibs file
                    writeIORef checkingRef True
                    writeIORef checkingPRef inPainter
                    checkProof pterm file
                _ -> labMag "Enter a file name!"
        
        -- | Called by check proof options in tree menu.
        checkProofT :: Bool -> Action
        checkProofT inPainter = do
            pterm <- getTextHere
            writeIORef checkingRef True
            writeIORef checkingPRef inPainter
            sp <- ent `gtkGet` entryText
            let newSpeed = parse pnat sp
            when (just newSpeed) $ writeIORef speedRef $ get newSpeed
            checkProof pterm "the text field"
        
        -- | Used by many 'Epaint.Solver' methods.
        clearTreeposs :: Action
        clearTreeposs = setTreeposs $ Replace []
        
        -- | Used by 'enterFormulas'', 'enterTerms', 'enterText'' and
        -- 'enterPT''. Called by "remove text" button.
        clearText :: Action
        clearText = do
            buffer <- tedit `gtkGet` textViewBuffer
            buffer `gtkSet` [ textBufferText := "" ]
        
        -- | Used by 'checkForward'. Called by menu item /collapse level/
        -- from /graph/ menu.
        collapseStep :: Action
        collapseStep = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                counter <- readIORef counterRef
                part <- readIORef partRef
                let t = trees!!curr
                    p = emptyOrLast treeposs
                    u = getSubterm1 t p
                    n = counter 'c'
                    (v,part') = collapseLoop True (u,part) n
                    setPr = setProof True False "COLLAPSING THE SUBTREE" [p]
                setProofTerm CollapseStep
                if u == v then do
                    setPr collapsed
                    clearTreeposs
                    modifyIORef counterRef $ \counter -> upd counter 'c' 0
                    writeIORef partRef (id,[])
                else do
                    curr <- readIORef currRef
                    modifyIORef treesRef
                        $ \trees -> updList trees curr $ replace1 t p v
                    setPr $ levelMsg n
                    drawCurr'
                    modifyIORef counterRef $ \counter -> incr counter 'c'
                    writeIORef partRef part'
        
        -- | Used by 'checkForward'. Called by menu item /compose pointers/
        -- from /graph/ menu. 
        composePointers :: Action
        composePointers = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                -- sig <- getSignature
                let t = trees!!curr
                    ps = emptyOrAll treeposs
                    ts = map (composePtrs . getSubterm1 t) ps
                writeIORef treesRef
                    $ updList trees curr $ fold2 replace1 t ps ts
                setProofTerm ComposePointers
                setProof True False "COMBINING THE POINTERS OF THE TREES" ps
                   pointersComposed
                drawCurr'
        
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
            then
                if null axs then labRed' $ noAxiomsFor [x]
                else do
                    varCounter <- readIORef varCounterRef
                    let (th,k) = compressAll b sig (varCounter "z") axs
                    modifyIORef theoremsRef $ \theorems -> th:theorems
                    setZcounter k
                    enterFormulas' [th]
                    labGreen' $ newCls "theorems" "the text field"
            else
                labMag "Enter a predicate, a defined function or a copredicate!"
        
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
                        let i = varCounter "z"
                            (th,k) = combineOne sig i ks (exps!!n) exps
                        modifyIORef theoremsRef $ \theorems -> th:theorems
                        setZcounter k
                        enterFormulas' [th]
                        labGreen' $ newCls "theorems" "the text field"
                    else labMag "Enter clauses into the text field!"
                _ -> labMag $ enterNumber ++ " Enter argument positions!"
        
        -- | Used by 'checkForward'. Called by menu item /copy/ from menu
        -- /transform selection/ or by pressing key @c@ on left label.
        copySubtrees :: Action
        copySubtrees = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                treeposs <- readIORef treepossRef
                curr <- readIORef currRef
                let ps = emptyOrAll treeposs
                    t = trees!!curr
                if any null ps then labMag "Select proper subtrees!"
                else do
                    writeIORef treesRef $ updList trees curr $ copy ps t
                    setProofTerm CopySubtrees
                    let b = all idempotent $ map (label t . init) ps
                    setProof b False "COPYING THE SUBTREES" ps
                                        "The selected tree have been copied."
                    drawCurr'
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
        
        -- | Used by 'checkForward'. Called by menu item
        -- /create induction hypotheses/ from tree menu.
        createIndHyp :: Action
        createIndHyp = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                treeposs <- readIORef treepossRef
                if null treeposs then labMag "Select induction variables!"
                else do
                    curr <- readIORef currRef
                    let t = trees!!curr
                        xs = map (label t) treeposs
                    sig <- getSignature
                    if all (isFovar sig) xs &&
                       and (zipWith (isAllOrFree t) xs treeposs)
                    then do
                        let f x = V $ if x `elem` xs then '!':x else x
                            g f = mkTup $ map f xs
                            hyps = mkIndHyps t $ F ">>" [g f,g V]
                        modifyIORef treesRef $ \trees -> updList trees curr $
                            mkAll (frees sig t `minus` xs) $ t>>>f
                        writeIORef indClausesRef hyps
                        modifyIORef theoremsRef $ \theorems -> hyps++theorems
                        setProofTerm CreateIndHyp
                        setProof True False "SELECTING INDUCTION VARIABLES"
                            treeposs $ indHypsCreated xs
                        clearTreeposs
                        drawCurr'
                    else labMag "Select induction variables!"
        
        -- | Used by 'checkForward'. Called by create invariant menu items from
        -- /transform selection/ menu.
        createInvariant :: Bool -> Action
        createInvariant b = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
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
                if i > -1 && universal sig t p conj
                then case preStretch True (isDefunct sig) conj of
                    Just (f,varps) -> do
                        varCounter <- readIORef varCounterRef
                        case stretchPrem (varCounter "z") varps conj of
                            (F "===>" [F "=" [F _ xs,d],conc],m) -> do
                                let lg = length xs
                                if i < lg
                                then do
                                    axioms <- readIORef axiomsRef
                                    case derivedFun sig f xs i lg axioms of
                                        -- ax is f(xs)=loop(take i xs++inits)
                                        Just (loop,inits,ax)-> do
                                            let n = m+length inits
                                                (as,bs) = splitAt (lg-i) xs
                                                cs = map newVar [m..n-1]
                                                u = mkInvs b loop as bs
                                                        cs inits d conc
                                            curr <- readIORef currRef
                                            modifyIORef treesRef $ \trees ->
                                                updList trees curr
                                                    $ replace t p u
                                            setZcounter n
                                            setProofTerm $ CreateInvariant b
                                            setProof True False
                                                (creatingInvariant str ax)
                                                [p] $ invCreated b
                                            clearTreeposs; drawCurr'
                                        _ -> labRed' $ f
                                                ++ " is not a derived function."
                                else labRed' $ wrongArity f lg
                            _ -> labRed' concCallsPrem
                    _ -> notStretchable "The premise"
                else labRed' $ noApp str
            where str = if b then "HOARE INVARIANT CREATION"
                        else "SUBGOAL INVARIANT CREATION"
        
        -- | Creates sub menus for /specification/ menu. Used by 'buildSolve1'.
        createSpecMenu :: Bool -> Menu -> Action
        createSpecMenu add m = do
            mapM_ (mkButF m cmd) specfiles1
            mkBut m (if add then "from file (Return)" else "from file")
                    $ getFileAnd cmd
            when add
              $ Haskell.void $ mkBut m "from text field" $ addSpecWithBase ""
            subMenu <- mkSub m "more"
            mapM_ (mkButF subMenu cmd) specfiles2
            subMenu <- mkSub subMenu "more"
            mapM_ (mkButF subMenu cmd) specfiles3
            return ()
            where cmd = if add then addSpecWithBase else loadText True

        createSub mode menu = do
          mkBut menu "from file" $ getFileAnd $ addClauses mode
          mkBut menu "from text field" $ addClauses mode ""
          when (mode == 0) $ do
            mkBut menu "from entry field" addNamedAxioms; return ()
          solve <- readIORef solveRef
          other <- getSolver solve
          mkBut menu ("from "++ other) $ do tree <- (solve&getTree)
                                            case tree of
                                                Just t
                                                  -> addTheorems t other
                                                _ -> labBlue' $ startOther other
          return ()

        -- | Used by 'checkForward'. Called by /decompose atom/ menu item
        -- from /transform selection/ menu.
        decomposeAtom :: Action
        decomposeAtom = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    p = emptyOrLast treeposs
                    b = polarity True t p
                    F x [l,r] = getSubterm1 t p
                    finish u = do
                        curr <- readIORef currRef
                        modifyIORef treesRef $ \trees ->
                            updList trees curr $ replace1 t p u
                        setProofTerm DecomposeAtom
                        setProof True False "DECOMPOSING THE ATOM" [p]
                            atomDecomposed
                        clearTreeposs; drawCurr'
                sig <- getSignature
                case x of
                    "=" | b -> finish $ splitEq sig l r
                    "=/=" | not b -> finish $ splitNeq sig l r
                    _ -> labRed' atomNotDecomposed
        
        delay :: Action -> Action
        delay = gtkDelay 100
        
        -- | Used by 'drawPointer', 'drawShrinked', 'drawThis', 'moveTree' and
        -- 'setInterpreter'.
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
            -- when (notnull treeDir)
            --     $ delay 100 $ saveGraphD' treeDir =<< readIORef picNoRef
          where bds (n,w) (a,(x,y)) pss = (x-x',y-y'):(x+x',y+y'):concat pss
                               where (x',y') = (nodeWidth w a,n`div`2)
        
        {- |
            Draws a line from position @(x, y)@ to the position of the root node
            of the tree @ct@ in color @color@. The font size that has been set
            is substracted from the line. This is used by 'drawTree' and
            'drawTree2' to draw the edges of a function graph.
        -}
        drawArc :: Pos -> TermSP -> Color -> Action
        drawArc (x,y) ct color =
            when (not $ isPos a) $ do
                font <- readIORef fontRef

                (above,below) <- getTextHeight canv font
                line canv [(x,y+below),(x',y'-above)]
                    $ lineOpt{ lineFill = color }
                return ()
            where (a,(x',y')) = root ct
        
        {- |
            Draw current tree. Used by all functions that (re-)draw the current
            tree. Called by font size button on change. Exported by public
            'Epaint.Solver' method 'Epaint.drawCurr'.
        -}
        drawCurr' :: Action
        drawCurr' = do
            trees <- readIORef treesRef
            curr <- readIORef currRef

            drawThis (trees!!curr) [] ""
        
        -- | Called if 'horBut' or 'treeSlider' is changed.
        drawNewCurr :: Action
        drawNewCurr = do
            trees <- readIORef treesRef
            when (notnull trees) drawCurr'
        
        -- | Draws a single text node. Used by 'drawTree', 'drawTree2',
        -- 'moveNode', 'moveSubtree' and 'catchNode'.
        drawNode :: (String, Pos) -> Color -> Action
        drawNode (a,p) c =
            when (not $ isPos a) $ do
                font <- readIORef fontRef

                canvasText canv p textOpt{ textFont = Just font
                                         , textFill = c'
                                         , textJustify = CenterAlign
                                         }
                    (delQuotes a)
                return ()
         where c' = case parse colPre a of Just (c,_) -> c; _ -> c
        
        -- | Used by 'drawTree'.
        drawPointer :: TermSP -> Color -> [Int] -> Pos -> [Int] -> Action
        drawPointer ct ac p mid@(x,y) q = do
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
                draw path color = (canv&line) path lineOpt{ lineFill = color
                                                          , lineArrow = Just Last
                                                          , lineSmooth = True
                                                          }

        -- | Called on change by 'verBut'.
        drawShrinked :: Action
        drawShrinked = do
            trees <- readIORef treesRef
            corner <- readIORef cornerRef
            spread <- readIORef spreadRef
            ctree <- readIORef ctreeRef
            when (notnull trees)
                $ draw $ shrinkTree (snd corner) (snd spread) $ get ctree
        
        -- | Used by 'releaseSubtree', 'setSubtrees' and 'catchSubtree'.
        drawSubtrees :: Action
        drawSubtrees = do
            Just ct <- readIORef ctreeRef
            treeposs <- readIORef treepossRef
            oldTreeposs <- readIORef oldTreepossRef

            drawTree3 ct ct black blue red darkGreen [] treeposs
                $ minis (<<=) $ treeposs `join` oldTreeposs
        
        -- | Used by 'applySubstTo'', 'drawCurr'', 'showCoords',
        -- 'showCycleTargets', 'showGlb', 'showNumbers', 'showPolarities',
        -- 'showPositions', 'showPreds', 'showSucs', 'showSyms' and 'showVals'.
        drawThis :: TermS -> [[Int]] -> String -> Action
        drawThis t ps col = do
            showState <- readIORef showStateRef
            treeposs <- readIORef treepossRef
            maxHeap <- getMaxHeap
            font <- readIORef fontRef
            spread <- readIORef spreadRef
            corner <- readIORef cornerRef

            let qs = if showState then [] else treeposs
                u = cutTree maxHeap (colHidden t) ps col qs
            sizes@(_,w) <- mkSizes canv font $ nodeLabels u
            writeIORef sizeStateRef sizes
            draw $ coordTree w spread corner u
            return ()

        {- |
            @drawTree ct ct nc ac []@ draws the nodes of @ct@ in color @nc@ and
            the arcs of @ct@ in color @ac@. Used by 'draw', 'drawTree2',
            'moveSubtree' and 'releaseSubtree'.
        -}
        drawTree :: TermSP -- ^ ct
                 -> TermSP -- ^ ct
                 -> Color -- ^ nc
                 -> Color -- ^ ac
                 -> [Int]
                 -> Action
        drawTree (F cx@(_,q) cts) ct nc ac p = do
            drawNode cx nc
            drawTrees cts $ succsInd p cts
            where drawTrees (ct':cts) (p:ps) = do
                            drawArc q ct' ac
                            drawTree ct' ct nc ac p
                            drawTrees cts ps
                  drawTrees _ _ = return ()
        drawTree (V cx@(a,q)) ct nc ac p
            | isPos a = drawPointer ct ac p q $ getPos a
            | True    = drawNode cx nc

        {- |
            @drawTree2 ct ct nc ac nc' ac' [] qs@ draws the nested ones among
            the subtrees at positions @qs@ alternately in (text,line)-colors
            (@nc@,@ac@) and (@nc'@,@ac'@). Used by 'draw' and 'drawTree3'.
        -}
        drawTree2 :: TermSP -- ^ ct
                  -> TermSP -- ^ ct
                  -> Color -- ^ nc
                  -> Color -- ^ ac
                  -> Color -- ^ nc'
                  -> Color -- ^ ac'
                  -> [Int]
                  -> [[Int]] -- ^ qs
                  -> Action
        drawTree2 ct@(V _) ct0 nc ac nc' ac' p qs
            | p `elem` qs = drawTree ct ct0 nc' ac' p
            | True      = drawTree ct ct0 nc ac p
        drawTree2 (F cx@(_,q) cts) ct nc ac nc' ac' p qs
            | p `elem` qs = do
                drawNode cx nc'
                drawTrees2 q cts nc' ac' nc ac ps
            | True      = do
                drawNode cx nc
                drawTrees2 q cts nc ac nc' ac' ps
                    where ps = succsInd p cts
                          drawTrees2 q (ct':cts) nc ac nc' ac' (p:ps) = do
                                        drawArc q ct' ac
                                        drawTree2 ct' ct nc ac nc' ac' p qs
                                        drawTrees2 q cts nc ac nc' ac' ps
                          drawTrees2 _ _ _ _ _ _ _ = return ()

        {- |
            @drawTree3 ct .. rs@ applies @drawTree2 ct ..@ to the subtrees of
            @ct@ at positions @rs@. Used by 'drawSubtrees'.
        -}
        drawTree3 :: TermSP -- ^ ct
                  -> TermSP -- ^ ct
                  -> Color -- ^ nc
                  -> Color -- ^ ac
                  -> Color -- ^ nc'
                  -> Color -- ^ ac'
                  -> [Int]
                  -> [[Int]] -- ^ qs
                  -> [[Int]] -- ^ rs
                  -> Action
        drawTree3 ct' ct nc ac nc' ac' p qs rs
            | any (<<= p) rs
                = drawTree2 ct' ct nc ac nc' ac' p qs
        drawTree3 (V _) _ _ _ _ _ _ _ _ = return ()
        drawTree3 (F (_,q) cts) ct nc ac nc' ac' p qs rs
            = drawTrees3 q cts nc ac nc' ac' ps
            where ps = succsInd p cts
                  drawTrees3 q (ct':cts) nc ac nc' ac' (p:ps) = do
                        drawTree3 ct' ct nc ac nc' ac' p qs rs
                        drawTrees3 q cts nc ac nc' ac' ps
                  drawTrees3 _ _ _ _ _ _ _ = return ()
        
        -- Show formulas in textfield. Exported by public
        -- 'Epaint.Solver' method 'Epaint.enterFormulas'.
        enterFormulas' :: [TermS] -> Action
        enterFormulas' fs = do
            checking <- readIORef checkingRef
            when (not checking) $ do
                clearText
                addText $ lines $ showFactors fs
                writeIORef numberedExpsRef (fs,True)

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
        enterText' :: String -> Action
        enterText' str = do
            checking <- readIORef checkingRef
            when (not checking) $ do
                clearText
                addText $ lines str
                writeIORef numberedExpsRef ([],True)
        
        
        {- | 
            Show pointer in textfield. Used by 'checkBackward', 'checkForward',
            'checkProof', 'setDeriveMode' and 'showProofTerm'. Exported by
            public 'Epaint.Solver' method 'Epaint.enterPT'.
        -}
        enterPT' :: Int -> [Step] -> Action
        enterPT' n pt = do
            clearText
            addText $ lines $ show $ addPtr n pt
            where addPtr 0 (step:pt) = POINTER step:pt
                  addPtr n (step:pt) = step:addPtr (n-1) pt
                  addPtr _ pt        = pt
        
        {- |
            Show tree in canvas. Used by 'initCanvas', 'parseText',
            'randomTree', 'showEqsOrGraph' and 'showRelation'. Exported by
            public 'Epaint.Solver' method 'Epaint.enterTree'.
        -}
        enterTree' :: Bool -> TermS -> Action
        enterTree' b t = do
            simplifying <- readIORef simplifyingRef
            refuting <- readIORef refutingRef
            fast <- readIORef fastRef

            setTime
            writeIORef matchingRef 0
            matching <- readIORef matchingRef
            matchBut `gtkSet` [ buttonLabel := "match" ]
            writeIORef formulaRef b
            writeIORef treeModeRef "tree"
            writeIORef treesRef [t]
            modifyIORef counterRef $ \counter -> upd counter 't' 1
            writeIORef proofTermRef
                [DeriveMode simplifying refuting, Match matching]
            writeIORef proofTPtrRef 2
            clearTreeposs
            sig <- getSignature
            makeTrees sig
            initialize (sigVars sig t) $ showTree fast t
            setTreesFrame []
            labGreen' $ objects++str
         where objects = if b then "Formulas" else "Terms"
               str = " are displayed on the canvas."
        
        -- | Used by 'checkForward'. Called by "evaluate" menu item
        -- from "transform selection" menu.
        evaluateTrees :: Action
        evaluateTrees = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                sig <- getSignature
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    ps = emptyOrAll treeposs
                    ts = map (evaluate sig . getSubterm1 t) ps
                writeIORef treesRef
                    $ updList trees curr $ fold2 replace1 t ps ts
                setProofTerm EvaluateTrees
                setProof True False "EVALUATING THE TREES" ps evaluated
                drawCurr'
        
        -- | Called by expand menu items from
        -- "graph" menu.
        expandTree :: Bool -> Action
        expandTree b = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                limit <- ent `gtkGet` entryText
                expandTree' b $ case parse pnat limit of Just n -> n; _ -> 0
        
        -- | Used by 'expandTree' and 'checkForward'.
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
            setProofTerm $ ExpandTree b limit
            setProof True False "EXPANDING THE SUBTREES" ps $
                expanded ++ circlesUnfolded limit
            clearTreeposs; drawCurr'
        
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
            varCounter <- readIORef varCounterRef
            case applyMany b c ts reduct redices t ps pred qs sig varCounter of
                Just (t,vc) -> do
                    maybeSimplify sig t
                    writeIORef varCounterRef vc
                    proofStep <- readIORef proofStepRef
                    setProofTerm proofStep
                    setProof True True msg ps $ thApplied k
                    clearTreeposs; drawCurr'
                _ -> labRed' $ notUnifiable k
        
        -- | Used by 'releaseSubtree' and 'releaseTree'.
        finishRelease :: TermS -> [Int] -> Step -> Action
        finishRelease t p step = do
            trees <- readIORef treesRef
            curr <- readIORef currRef

            writeIORef treesRef $ updList trees curr t
            setProofTerm step
            clearTreeposs; drawCurr'
            setProof False False "REPLACING THE SUBTREE" [p]
                                 "The selected tree has been replaced."
        
        -- | Used by 'checkForward'. Called by /flatten (co-)Horn clause/ menu
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
                setProofTerm FlattenImpl
                setProof True False "FLATTENING" [[]] flattened
                clearTreeposs; drawCurr'
        
        -- | Used by 'setDeriveMode' and 'stopRun''. Called by keypress @Up@ on
        -- left label ('lab').  Exported by public 'Epaint.Solver' method
        -- 'Epaint.forwProof'.
        forwProof' :: Action
        forwProof' = do
            checking <- readIORef checkingRef
            if checking then checkForward
            else do
                proofPtr <- readIORef proofPtrRef
                proofTerm <- readIORef proofTermRef
                proof <- readIORef proofRef
                let k = proofPtr+1
                    lg = length proofTerm
                if k >= length proof then labMag endOfProof
                else do
                    writeIORef proofPtrRef k
                    changeState k []
                proofTPtr <- readIORef proofTPtrRef
                when (proofTPtr < lg) $ do
                    let n = search deriveStep $ drop proofTPtr proofTerm
                    modifyIORef proofTPtrRef $ \proofTPtr
                        -> if just n then proofTPtr + get n+1 else lg
        
        -- | Called by /generalize/ menu item
        -- from /transform selection/ menu.
        generalize :: Action
        generalize = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    p = emptyOrLast treeposs
                    cl = getSubterm t p
                sig <- getSignature
                if isTerm sig cl then labRed' "Select a formula!"
                else do
                    str <- ent `gtkGet` entryText
                    numberedExps <- readIORef numberedExpsRef
                    let (exps,b) = numberedExps
                    case parse intRanges str of
                        Just ns | all (< length exps) ns ->
                            if b then generalizeEnd t p cl $ map (exps!!) ns
                            else labMag "Enter formulas into the text field!"
                        _ -> do
                            str <- getTextHere
                            case parseE (implication sig) str of
                                Correct cl' -> generalizeEnd t p cl [cl']
                                p -> incorrect p str illformedF
        
        -- | Used by 'checkForward'. 
        generalize' :: [TermS] -> Action
        generalize' cls = do
            trees <- readIORef treesRef
            curr <- readIORef currRef
            treeposs <- readIORef treepossRef
            let t = trees!!curr
                p = emptyOrLast treeposs
            generalizeEnd t p (getSubterm t p) cls
        
        -- | Used by 'generalize' and 'generalize''.
        generalizeEnd :: TermS -> [Int] -> TermS -> [TermS] -> Action
        generalizeEnd t p cl cls = do
            curr <- readIORef currRef
            modifyIORef treesRef $ \trees ->
                updList trees curr $ replace t p $ f $ cl:cls
            enterFormulas' cls
            setProofTerm $ Generalize cls
            setProof True False "GENERALIZING" [p] generalized
            clearTreeposs; drawCurr'
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
        
        -- | Exported by public 'Epaint.Solver' method 'Epaint.getFont'.
        getFont' :: Request FontDescription
        getFont' = readIORef fontRef
        
        -- | Used by 'showSubtreePicts' and 'showTreePicts'.
        getInterpreter = do
          sig <- getSignature
          picEval <- readIORef picEvalRef
          return $ case picEval of 
                        "tree"               -> widgetTree sig
                        "matrices"           -> searchPic matrix
                        "matrix solution"    -> solPic sig matrix
                        "linear equations"   -> linearEqs
                        "level partition"    -> searchPic (partition 0)
                        "preord partition"   -> searchPic (partition 1)
                        "heap partition"     -> searchPic (partition 2)
                        "hill partition"     -> searchPic (partition 3)
                        "alignment"          -> searchPic alignment
                        "palindrome"         -> searchPic alignment
                        "dissection"         -> searchPic dissection
                        _                    -> searchPic (widgets sig black)
        
        -- | Get value of 'treeSize' scale. Used by 'drawThis'.
        getMaxHeap :: Request Int
        getMaxHeap = truncate <$> (treeSize `gtkGet` rangeValue)
        
        getPicNo' = readIORef picNoRef

        -- | Used by most other 'Epaint.Solver' functions. Exported by public
        -- 'Epaint.Solver' method 'Epaint.getSignatureR'.
        getSignature :: Request Sig
        getSignature = do
            (ps,cps,cs,ds,fs,hs) <- readIORef symbolsRef
            (sts,ats,labs,tr,trL,va,vaL) <- readIORef kripkeRef
            simplRules <- readIORef simplRulesRef
            transRules <- readIORef transRulesRef
            (block,xs) <- readIORef constraintsRef
            safe <- readIORef safeRef

            return $ let
              isPred'       = (`elem` ps)  ||| projection
              isCopred'     = (`elem` cps) ||| projection
              isConstruct'  = (`elem` cs)  ||| just . parse int
                              ||| just . parse real
                              ||| just . parse quoted
                              ||| just . parse (strNat "inj")
              isDefunct'    = (`elem` ds) ||| projection
              isFovar'      = (`elem` fs) . base
              isHovar'      = (`elem` (map fst hs)) . base
              hovarRel' x y = isHovar' x &&
                  case lookup (base x) hs of
                      Just es@(_:_) -> isHovar' y || y `elem` es
                      _ -> not $ isFovar' y
              blocked' x = if block then z `elem` xs else z `notElem` xs
                        where z = head $ words x
              safeEqs' = safe; simpls' = simplRules
              transitions' = transRules
              states' = sts; atoms' = ats; labels' = labs; trans' = tr
              transL' = trL; value' = va; valueL' = vaL
              base = pr1 . splitVar
             in Sig
                { isPred      = isPred'
                , isCopred    = isCopred'
                , isConstruct = isConstruct'
                , isDefunct   = isDefunct'
                , isFovar     = isFovar'
                , isHovar     = isHovar'
                , blocked     = blocked'
                , hovarRel    = hovarRel'
                , simpls      = simpls'
                , transitions = transitions'
                , states      = states'
                , atoms       = atoms'
                , labels      = labels'
                , trans       = trans'
                , value       = value'
                , transL      = transL'
                , valueL      = valueL'
                , safeEqs     = safeEqs'
                }

        -- | Returns name of this solver object. Exported by public
        -- 'Epaint.Solver' method 'Epaint.getSolver'.
        getSolver' :: Request String
        getSolver' = return this
        
        getSpread' :: Request Pos
        getSpread' = readIORef spreadRef
        
        -- | Returns content of text area. Used by 'addClauses',
        -- 'addSigMapT', 'addSpec'', 'addSubst', 'applyClause', 'checkProofT',
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
        getTree' :: Request (Maybe TermS)
        getTree' = do
            trees <- readIORef treesRef
            if null trees then do
                labBlue' start
                return Nothing
            else do
                curr <- readIORef currRef
                return $ Just $ trees!!curr
        
        -- | Called by button "hide" ('hideBut').
        hideOrShow :: Action
        hideOrShow = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                drawCurr'
                modifyIORef showStateRef not
                showState <- readIORef showStateRef
                hideBut `gtkSet`
                    [ buttonLabel := if showState then "hide" else "show" ]
        
        -- | Minimize solver window. Exported by public 'Epaint.Solver' method
        -- 'Epaint.iconify'.
        iconify' :: Action
        iconify' = windowIconify win
        
        -- | Handles incorrect parser results. Used by 'addClauses', 'addSpec'',
        -- 'addSubst', 'applyClause', 'generalize', 'instantiate',
        -- 'parseConjects', 'parseText', 'parseTerms', 'replaceText'' and
        -- 'specialize'.
        incorrect :: Parse TermS -> String -> String -> Action
        incorrect p str error = do
            case p of
                Partial t rest -> enterText' $ showTree False t ++ check rest
                _ -> enterText' str
            labRed' error
        
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
        
        -- | Used by all menu items /[show graph].. in painter/ and
        -- /[show matrix].. of (...)/ from /graph/ menu.
        initCanvas :: Action
        initCanvas = do
            trees <- readIORef treesRef
            when (null trees)
                $ enterTree' False $ F "see painter" []
                -- delay 100 $ return ()
        
        -- | Used by 'checkProof', 'enterTree'' and 'setNewTrees''.
        initialize :: [String] -> String -> Action
        initialize vars str = do
          symbols@(ps,cps,cs,ds,fs,hs) <- readIORef symbolsRef
          (nps,ncps) <- readIORef newPredsRef
          let (ps',cps') = (ps `minus` nps,cps `minus` ncps)
          constraints@(block,xs) <- readIORef constraintsRef
          treeMode <- readIORef treeModeRef
          trees <- readIORef treesRef
          varCounter <- readIORef varCounterRef
          safe <- readIORef safeRef
          joined <- readIORef joinedRef
          indClauses <- readIORef indClausesRef

          writeIORef symbolsRef (ps',cps',cs,ds,fs,hs)
          modifyIORef axiomsRef $ \axioms -> removeTerms axioms indClauses
          modifyIORef theoremsRef
              $ \theorems -> removeTerms theorems indClauses
          writeIORef indClausesRef []
          writeIORef newPredsRef nil2
          writeIORef solPositionsRef []
          writeIORef varCounterRef
            $ iniVC $ ps'++cps'++cs++ds++fs++map fst hs++vars
          setSubst' (V,[])
          writeIORef partRef (id,[])
          writeIORef chgPermRef False
          writeIORef permsRef $ \n -> [0..n-1]
          varCounter <- readIORef varCounterRef
          perms <- readIORef permsRef
          writeIORef proofRef
              [ ProofElem
                  { peMsg = "Derivation of\n\n"++str++
                                      '\n':'\n':admitted block xs++
                                      '\n':equationRemoval safe
                  , peMsgL = ""
                  , peTreeMode = treeMode
                  , peTrees = trees
                  , peTreePoss = []
                  , peCurr = 0
                  , peVarCounter = varCounter
                  , pePerms = perms
                  , peNewPreds = nil2
                  , peSolPositions = []
                  , peSubstitution = (V,[])
                  , peConstraints = constraints
                  , peJoined = joined
                  , peSafe = safe
                  }
              ]
          writeIORef proofPtrRef 0
          writeIORef counterRef $ const 0
          writeIORef currRef 0
        
        -- | Called by menu item /instantiate/ from /transform selection/ menu
        instantiate :: Action
        instantiate = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                sig <- getSignature
                str <- ent `gtkGet` entryText
                let str' = removeComment 0 str
                case parseE (term sig) str' of
                    Correct t -> do
                        treeposs <- readIORef treepossRef
                        replaceQuant t (emptyOrLast treeposs)
                        labRed' notInstantiable
                    p -> incorrect p str' illformedT
        
        -- | Exported by public 'Epaint.Solver' method 'Epaint.isSolPos'.
        isSolPos' :: Int -> Request Bool
        isSolPos' n = elem n <$> readIORef solPositionsRef
        
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
            if copred || isPred sig x  then do
                axioms <- readIORef axiomsRef
                let axs = noSimplsFor [x] axioms
                if null axs then labRed' $ noAxiomsFor [x]
                else do
                    varCounter <- readIORef varCounterRef
                    symbols <- readIORef symbolsRef
                    let i = V $ 'i':show (varCounter "i")
                        (axs',k) = f sig x axs i $ varCounter "z"
                        (ps,cps,cs,ds,fs,hs) = symbols
                        ps' = x:(x++"Loop"):ps
                    writeIORef symbolsRef (ps',cps`minus1`x,cs,ds,fs,hs)
                    modifyIORef axiomsRef
                        $ \axioms -> axioms `minus` axs `join` axs'
                    modifyIORef varCounterRef
                        $ \varCounter -> upd (incr varCounter "i") "z" k
                    enterFormulas' axs'
                    labGreen' $ if copred then newPredicate str1 str2 x
                                else newPredicate str2 str1 x
            else labMag "Enter either a predicate or a copredicate!"
            where (str1,str2) = ("copredicate","predicate")
        
        -- | Shows @str@ in the left label ('lab') and set the label background
        -- to blue. Exported by public 'Epaint.Solver' method 'Epaint.labBlue'.
        labBlue' :: String -> Action
        labBlue' str = labColor str blueback

        -- | Shows @str@ in left label ('lab') and set the label background to
        -- @col@. Used by 'labBlue'', 'labColorToPaint', 'labGreen'', 'labMag'
        -- and  'labRed''.
        labColor :: String -> Background -> Action
        labColor str col = do
            lab `gtkSet` [ labelText := str ]
            setBackground lab col
        
        -- | Used by 'checkBackward', 'narrowPar', 'narrowSubtree', 'setCurr',
        -- 'setProof', 'simplifyPar' and 'simplifySubtree'.
        labColorToPaint :: Background -> String -> Action
        labColorToPaint col str = do
            labColor str col
            labSolver paint str
        
        {- unused
        labColorToPaintT col str = do
            (time0,_) <-  readIORef timesRef
            if time0 == 0 then labColor str col
            else do
                time <- getCPUTime
                writeIORef timesRef (0,300)
                labColor (str++'\n':show (mkSecs time0 time)++" sec") col
            labSolver paint str
        -}
        
        -- | Shows @str@ in the left label and set the label background to green.
        -- Exported by public 'Epaint.Solver' method 'Epaint.labGreen'.
        labGreen' :: String -> Action
        labGreen' = flip labColor greenback
        
        -- | Shows @str@ in the left label and set the label background to
        -- magenta.
        labMag :: String -> Action
        labMag = flip labColor magback
        
        -- | Shows @str@ in the left label and set the label background to a
        -- pulsating red.
        -- Exported by public 'Epaint.Solver' method 'Epaint.labRed'.
        labRed' :: String -> Action
        labRed' = flip labColor redpulseback
        
        -- | Lookup @file@ and load content into text area.
        -- Called by all menu items in "load text" submenu from tree menu and
        -- "specification" menu.
        loadText :: Bool -> FilePath -> Action
        loadText b file = do
          str <- lookupLibs file
          if null str then labRed' $ file ++ " is not a file name."
                      else if b then do
                                  enterText' str
                                  labGreen' $ loaded file
                                else do
                                  solve <- readIORef solveRef
                                  solve&bigWin
                                  (solve&enterText) str
        
        -- | Used by 'applyInd', 'applyTheorem', 'enterTree'', 'narrowLoop',
        -- 'narrowPar', 'replaceSubtrees'', 'replaceVar', 'simplify''' and
        -- 'splitTree'.
        makeTrees :: Sig -> Action
        makeTrees sig = do
          treeMode <- readIORef treeModeRef
          trees <- readIORef treesRef
          case treeMode of
           "tree"    -> do
                        joined <- readIORef joinedRef
                        if joined then return ()
                        else case trees of
                             [t@(F "|" _)]   -> do
                                                writeIORef solPositionsRef []
                                                split (mkSummands t) "summand"
                             [t@(F "&" _)]   -> do
                                                writeIORef solPositionsRef []
                                                split (mkFactors t) "factor"
                             [t@(F "<+>" _)] -> split (mkTerms t) "term"
                             _               -> return ()
           "summand" -> if null ts then actMore [mkFalse] "tree"
                                   else actMore ts treeMode
                        where ts = mkSummands $ F "|" trees
           "factor"  -> if null ts then actMore [mkTrue] "tree"
                                   else actMore ts treeMode
                        where ts = mkFactors $ F "&" trees
           _         -> if null ts then actMore [unit] "tree"
                                   else actMore ts treeMode
                        where ts = mkTerms $ F "<+>" trees

         where split = actMore . map dropHeadFromPoss
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
                    writeIORef solPositionsRef
                        $ if formula then solPoss sig ts
                                     else []
                    where lg = length ts
        
        -- | Used by 'applyInd', 'applyTheorem', 'finishDisCon', 'narrowPar',
        -- 'replaceSubtrees'' and 'replaceVar'.
        maybeSimplify :: Sig -> TermS -> Action
        maybeSimplify sig t = do
            trees <- readIORef treesRef
            curr <- readIORef currRef
            simplifying <- readIORef simplifyingRef

            writeIORef treesRef $ updList trees curr
                $ if simplifying then simplifyIter sig t else t
        
        -- | Used by 'checkForward'. Called by menu item "minimize" from
        -- "specification" menu.
        minimize :: Action
        minimize = do
          sig <- getSignature
          simplRules <- readIORef simplRulesRef
          when (notnull (sig&states)) $ do
             let (states,tr,trL,va,vaL) = mkQuotient sig
             writeIORef kripkeRef
                $ (states,(sig&atoms),(sig&labels),tr,trL,va,vaL)
             changeSimpl "states" $ mkList states
             setProofTerm Minimize
             setProof True False "MINIMIZING THE KRIPKE MODEL" [] $ minimized 
                                 $ length states
        
        modifyEqs m = do
          trees <- readIORef treesRef
          if null trees then labBlue' start
          else do
               sig <- getSignature
               trees <- readIORef treesRef
               curr <- readIORef currRef
               treeposs <- readIORef treepossRef
               let t = trees!!curr
                   p:ps = emptyOrAll treeposs
                   u = getSubterm1 t p
                   act p u = do
                       writeIORef treesRef $ updList trees curr $ replace1 t p u
                       setProofTerm $ ModifyEqs m
                       setProof False False "MODIFYING THE EQUATIONS" [p] $
                                            eqsModified
                       clearTreeposs; drawCurr'
               case m of 0 -> case parseEqs u of
                                   Just eqs -- from equations to equations
                                     -> do
                                        let t = connectEqs eqs
                                        firstClick <- readIORef firstClickRef
                                        if firstClick
                                           then do
                                             act p t
                                             writeIORef substitutionRef
                                               (const t,[])
                                             writeIORef firstClickRef False
                                           else do
                                             (f,_) <- readIORef substitutionRef
                                             let u = eqsToGraphs $ f ""
                                             act p u
                                             writeIORef substitutionRef (V,[])
                                             writeIORef firstClickRef True
                                   _ -> labMag "Select iterative equations!"
                         1 -> case parseEqs u of
                                   Just eqs -> act p $ eqsTerm
                                                     $ autoEqsToRegEqs sig eqs
                                   _ -> labMag "Select iterative equations!"
                         2 -> case parseEqs u of
                                   Just eqs | just v -> act [] $ get v
                                              where v = substituteVars t eqs ps
                                   _ -> labMag instantiateVars
                         _ -> case parseIterEq u of
                                  Just (Equal x t) | just e
                                    -> act p $ mkEq (V x) $ showRE $ fst $ get e
                                       where e = solveRegEq sig x t
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
        moveNode (x, y) = do
            treeposs <- readIORef treepossRef

            if null treeposs then labMag "Select a target node!"
            else do
                node <- readIORef nodeRef
                ctree <- readIORef ctreeRef

                let f p a col1 col2 = drawNode a $ if last treeposs <<= p
                                                   then col1 else col2
                case node of Just (z,p) -> do f p z red black; return ()
                             _ -> return ()
                -- (x,y) <- adaptPos pt
                case getSubtree (get ctree) x y of
                    Just (p,cu) -> do
                        let a = root cu
                        f p a cyan magenta
                        writeIORef nodeRef $ Just (a,p)
                    _ -> writeIORef nodeRef Nothing
        
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
                Just _ -> do
                    penpos <- readIORef penposRef

                    when (just penpos) $ do
                        ctree <- readIORef ctreeRef

                        let (x0,y0) = get penpos
                            q@(i,j) = (x-x0,y-y0)
                        draw $ transTree2 q $ get ctree
                        modifyIORef cornerRef
                            $ \corner -> (fst corner+i,snd corner+j)
                        writeIORef penposRef $ Just p
                _ -> return ()
        
        -- | Called by 'narrowBut'. Exported by public 'Epaint.Solver' method
        -- 'Epaint.narrow'.
        narrow' :: Action
        narrow' = do
            trees <- readIORef treesRef

            if null trees then labBlue' start
            else do
                str <- ent `gtkGet` entryText
                case parse pnat str of
                    Just limit -> narrow'' limit True
                    _ -> case parse pnatSecs str of
                            Just n -> do
                                modifyIORef timesRef $ \times -> (fst times,n)
                                narrow'' (-1) True
                            _ -> narrow'' 1 False
        
        -- | Used by 'checkForward' and 'narrow''.
        narrow'' :: Int -> Bool -> Action
        narrow'' limit sub = do
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
                writeIORef proofStepRef $ Narrow limit True
                setTime
                narrowLoop sig cls 0 limit
            else if sub then do setTime; narrowSubtree t sig cls limit
                 else do
                    writeIORef proofStepRef $ Narrow 0 False
                    narrowOrRewritePar t sig (Just $ -1) cls False treeposs
        
        -- | Used by 'narrow'''.
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
                                where t = simplifyIter sig $ mkDisjunct trees
                                      ts = mkSummands $ F "|" trees
                "factor"
                    | simplifying -> case t of F "|" ts -> actMore ts "summand"
                                               F "&" ts -> actMore ts treeMode
                                               _ -> actMore [t] "tree"
                    | null ts -> actMore [mkTrue] "tree"
                    | True    -> actMore ts treeMode
                                where t = simplifyIter sig $ mkConjunct trees
                                      ts = mkFactors $ F "&" trees
                _
                    | simplifying -> case t of F "<+>" ts -> actMore ts "term"
                                               _ -> actMore [t] "tree"
                    | null ts -> actMore [unit] "tree"
                    | True    -> actMore ts treeMode
                        where t = simplifyIter sig $ mkSum trees
                              ts = mkTerms $ F "<+>" trees
         where finish k = makeTrees sig >> finishNar k
               finishNar k = do
                    proofStep <- readIORef proofStepRef
                    ruleString <- readIORef ruleStringRef
                    formula <- readIORef formulaRef
                    solPositions <- readIORef solPositionsRef

                    setProofTerm proofStep
                    setProof True True ruleString [] $
                        finishedNar formula k ++ solved solPositions
                    setTreesFrame []
               mkStep t stop = do
                    formula <- readIORef formulaRef
                    narrowStep sig cls limit t proceed stop formula
               proceed t n vc = do
                    curr <- readIORef currRef
                    writeIORef varCounterRef vc
                    modifyIORef counterRef $ \counter -> upd counter 'd' k'
                    modifyIORef treesRef $ \trees -> updList trees curr t
                    narrowLoop sig cls k' (limit-n)
                    where k' = k+n
               split = actMore . map dropHeadFromPoss
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

        -- | Used by 'applyTheorem' and 'narrow''.
        narrowOrRewritePar :: TermS
                           -> Sig
                           -> Maybe Int
                           -> [TermS]
                           -> Bool
                           -> [[Int]]
                           -> Action
        narrowOrRewritePar t sig k cls saveRedex ps = do
            varCounter <- readIORef varCounterRef
            formula <- readIORef formulaRef

            let f g = g t sig k cls saveRedex [] ps [] varCounter
            if formula || ps `subset` boolPositions sig t then f narrowPar
                                                          else f rewritePar
        
        -- | Used by 'rewritePar'.
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
            if p `notElem` positions t --- || isVarRoot sig redex
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
               (cls3,vc') = renameApply cls2 sig t vc
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
                    proofStep <- readIORef proofStepRef
                    setProofTerm proofStep
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
                                              matching simplifying refuting
                    if n == 0 then stop else proceed u n vc
                else do
                    rand <- readIORef randRef
                    let (u,n,vc,rand') = applyLoopRandom rand t m varCounter cls
                                             axioms sig nar matching simplifying
                    writeIORef randRef rand'
                    if n == 0 then stop else proceed u n vc
        
        -- | Used by 'narrow'''.
        narrowSubtree :: TermS -> Sig -> [TermS] -> Int -> Action
        narrowSubtree t sig cls limit = do
            treeposs <- readIORef treepossRef

            let p = emptyOrLast treeposs
                u = getSubterm t p
                nar = isFormula sig u
                sn = subtreesNarrowed (Nothing :: Maybe Int)
                (str,str') = if nar then ("NARROWING",sn)
                                    else ("REWRITING",sn++onlyRew)
                proceed u n vc = do
                    simplifying <- readIORef simplifyingRef
                    curr <- readIORef currRef

                    let v = if simplifying then simplifyIter sig u else u
                    modifyIORef treesRef
                        $ \trees -> updList trees curr $ replace t p v
                    writeIORef varCounterRef vc
                    setProofTerm $ Narrow limit True
                    modifyIORef counterRef $ \counter -> upd counter 'd' n
                    setProof True True str [p]
                        $ appliedToSub (map toLower str) n
                    setTreesFrame []
                stop = labColorToPaint magback str'
            narrowStep sig cls limit u proceed stop nar
        
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
        
        -- | Used by 'checkForward' and 'negateAxioms'.
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
                msg = init str ++ " (see the text field)."
            if null axs1 then
                labRed' $ "There are no axioms for "++ showStrList xs
            else do
                writeIORef symbolsRef
                    (ps `join` ps2,cps `join` cps2,cs,ds,fs,hs)
                sig <- getSignature
                let axs2 = map (mkComplAxiom sig) axs1
                modifyIORef axiomsRef (`join` axs2)
                enterFormulas' axs2
                trees <- readIORef treesRef
                if null trees then labGreen' msg
                else do
                    setProofTerm $ NegateAxioms ps1 cps1
                    setProof True False str [] msg
        
        -- | Shows error message "@str@ cannot be stretched." on left label.
        -- Used by 'applyClause', 'applyCoinduction', 'applyInduction',
        -- 'createInvariant' and 'stretch'.
        notStretchable :: String -> Action
        notStretchable str = labRed' $ str ++ " cannot be stretched."
        
        -- | Used by 'addClauses' and 'addSpec''.
        parseConjects :: Sig -> FilePath -> String -> Action
        parseConjects sig file conjs =
            case parseE (implication sig) conjs of
                Correct t -> do
                    let ts = if isConjunct t then subterms t else [t]
                    modifyIORef conjectsRef $ \conjects -> conjects `join` ts
                    labGreen' $ newCls "conjectures" file
                p -> incorrect p conjs illformed
        
        -- | Used by 'addSpec''.
        parseSig :: FilePath -> String -> Action
        parseSig file str = do
            (ps,cps,cs,ds,fs,hs) <- readIORef symbolsRef
            let syms = ps++cps++cs++ds++fs++map fst hs
            case parseE (signature ([],ps,cps,cs,ds,fs,hs)) str of
                Correct (specs,ps,cps,cs,ds,fs,hs) -> do
                    writeIORef symbolsRef (ps,cps,cs,ds,fs,hs)
                    symbols <- readIORef symbolsRef
                    specfiles <- readIORef specfilesRef
                    
                    let finish = do
                          writeIORef varCounterRef $ iniVC syms
                          labGreen' $ newSig file
                    mapM_ (addSpec' False) $ specs `minus` specfiles
                    delay finish
                Partial (_,ps,cps,cs,ds,fs,hs) rest -> do
                    enterText' $ showSignature (ps,cps,cs,ds,fs,hs) $ check rest
                    labRed' illformedSig
                _ -> do
                    enterText' str
                    labRed' illformedSig
        
        -- | Used by 'addSigMap' and 'addSigMapT'.
        parseSigMap :: FilePath -> String -> Action
        parseSigMap file str = do
            signatureMap <- readIORef signatureMapRef
            sig <- getSignature
            sig' <- getSignatureR =<< readIORef solveRef
            case parseE (sigMap signatureMap sig sig') str of
                Correct f -> do
                    writeIORef signatureMapRef f
                    labGreen' $ newSigMap file
                Partial f rest -> do
                    enterText' $ showSignatureMap f $ check rest
                    labRed' illformedSM
                _ -> do
                    enterText' str
                    labRed' illformedSM
        
        
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
                    if b then enterTree' True $ mkConjunct exps'
                         else enterTree' False $ mkSum exps'
                _ -> do
                    str <- getTextHere
                    sig <- getSignature
                    case parseE (term sig) str of
                        Correct t -> enterTree' False t
                        _ -> case parseE (implication sig) str of
                            Correct cl -> enterTree' True cl
                            p -> incorrect p str illformed
        
        -- | Used by 'addSpec''.
        parseTerms :: Sig -> FilePath -> String -> Action
        parseTerms sig file ts =  case parseE (term sig) ts of
            Correct t -> do
                let ts = if isSum t then subterms t else [t]
                modifyIORef termsRef $ \terms -> ts `join` terms
                labGreen' $ newCls "terms" file
            p -> incorrect p ts illformed
        
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

            if null trees then labBlue' start
            else do
                let t = trees!!curr
                    enter _ _ [t] = enterText' $ showTree fast t
                    enter b "" ts = if b then enter True "&" ts
                                         else enter False "<+>" ts
                    enter _ x ts  = enterText' $ showTree fast $ F x ts
                if null treeposs
                then do enter formula "" [t]; labGreen' treeParsed
                else do
                    sig <- getSignature
                    let ts@(u:us) = map (getSubterm1 t) treeposs
                        b = isFormula sig u
                    if null $ tail treeposs
                        then do enter b "" [u]; labGreen' treeParsed
                        else if all (== b) $ map (isFormula sig) us
                                then do
                                    x <- ent `gtkGet` entryText
                                    enter b x $ addNatsToPoss ts
                                    labGreen' $ init treeParsed ++ "s."
                                else labMag "Select either formulas or terms!"
        
        permuteGoal = writeIORef chgPermRef True

        -- | Used by 'checkForward'. Called by menu item /random labels/ from
        -- /transform selection/ menu or by pressing shift + L on active left
        -- lable ('lab').
        randomLabels :: Action
        randomLabels = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                str <- ent `gtkGet` entryText
                if null str then labRed' "Enter labels!"
                else do
                    curr <- readIORef currRef
                    rand <- readIORef randRef
                    let (t,rand') = labelRandomly rand str $ trees!!curr
                    writeIORef treesRef $ updList trees curr t
                    writeIORef randRef rand'
                    setProofTerm RandomLabels
                    setProof False False "LABELING NODES" []
                        "The nodes have been labeled randomly."
                    drawCurr'
        
        -- | Used by 'checkForward'. Called by menu item /random tree/ from
        -- /transform selection/ menu or by pressing shift + @T@ on active left
        -- lable ('lab').
        randomTree :: Action
        randomTree = do
            str <- ent `gtkGet` entryText
            if null str then labRed' "Enter labels!"
            else do
                rand <- readIORef randRef
                let (t,rand') = buildTreeRandomly rand str
                enterTree' False t
                writeIORef randRef rand'
                setProofTerm RandomTree
                delay $ setProof False False "GENERATING A TREE" []
                                "A tree has been generated randomly."
        
        -- | Called by menu item /re-add/ from /specification/ menu.
        reAddSpec :: Action
        reAddSpec = do
            specfiles <- readIORef specfilesRef
            if null specfiles then labRed' iniSpec
            else removeSpec >> addSpecWithBase (head specfiles)
        
        -- | Called by button /redraw/ ('clearS').
        redrawTree :: Action
        redrawTree = do
            treeposs <- readIORef treepossRef
            when (notnull treeposs) $ do
                writeIORef restoreRef True
                clearTreeposs
            drawCurr'

        reduceRegExp mode = do
          trees <- readIORef treesRef
          if null trees then labBlue' start
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
                   g = case mode of 0 -> distribute
                                    1 -> reduceLeft
                                    _ -> reduceRight

               if any nothing es then labMag "Select regular expressions!"
               else do
                    modifyIORef treesRef
                      $ \trees -> updList trees curr
                                  $ fold2 replace0 t ps $ map f es
                    setProofTerm $ ReduceRE mode
                    setProof False False "REDUCING THE REGULAR EXPRESSIONS"
                                         ps regReduced
                    clearTreeposs; drawCurr'

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

                        let t = replace (trees!!curr) q $ mkPos p
                        if p `elem` allPoss t
                            then do
                                modifyIORef treesRef
                                    $ \trees -> updList trees curr t
                                let r = init q
                                setProofTerm ReleaseNode
                                setProof False False "INSERTING AN ARC"
                                                [r,p] $ arcInserted r p
                            else labRed' dangling
                        drawCurr'
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
                            finishRelease
                                (replace2 t source t target)
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
                        _ -> f $ replace t p $ V z
                    setSubst' (g `andThen` for u z, dom `join1` z)
                    modifyIORef varCounterRef
                        $ \varCounter -> incr varCounter "z"
                    resetCatch
                Just False -> do
                    writeIORef penposRef Nothing
                    canv `gtkSet` [canvasCursor := LeftPtr ]
                    resetCatch
                _ -> return ()
        
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
                     else mkSet $ map (label $ trees!!curr) treeposs
                axs = clausesFor xs axioms
            if null axs then labRed' $ noAxiomsFor xs
            else do
                writeIORef axiomsRef $  removeTerms axioms axs
                axioms <- readIORef axiomsRef
                writeIORef simplRulesRef $ trips ["==","<==>"] axioms
                writeIORef transRulesRef $ trips ["->"] axioms
                labGreen' $ axsRemovedFor xs
        
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
                          modifyIORef axiomsRef
                              $ \axioms -> removeTerms axioms ts
                          axioms <- readIORef axiomsRef
                          writeIORef simplRulesRef $ trips ["==","<==>"] axioms
                          writeIORef transRulesRef $ trips ["->"] axioms
                          showAxioms True
                      1 -> do
                          modifyIORef theoremsRef
                              $ \theorems -> removeTerms theorems ts
                          showTheorems True
                      2 -> do
                          modifyIORef conjectsRef
                              $ \conjects -> removeTerms conjects ts
                          showConjects
                      _ -> do
                          modifyIORef termsRef
                              $ \terms -> removeTerms terms ts
                          showTerms
                _ -> labMag enterNumbers
        
        -- | Called by menu item /remove conjects/ from menu /theorems/.
        removeConjects :: Action
        removeConjects = do
            writeIORef conjectsRef []
            writeIORef indClausesRef []
            labGreen' $ "There are neither conjectures nor "
                ++ "induction hypotheses."
        
        -- | Used by 'checkForward'. Called by menu item /remove copies/
        -- from menu /graph/.
        removeCopies :: Action
        removeCopies = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
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
                    setProofTerm RemoveCopies
                    setProof True False "REMOVING COPIES of the subtree" [p]
                                      copiesRemoved
                    clearTreeposs; drawCurr'
        
        -- | Used by 'checkForward'. Called by menu items /split cycles/ and
        -- /more tree arcs/ from menu /graph/.
        removeEdges :: Bool -> Action
        removeEdges b = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                curr <- readIORef currRef
                writeIORef treesRef $ updList trees curr $ f $ trees!!curr
                setProofTerm $ RemoveEdges b
                setProof False False "REMOVING EDGES" [] $ edgesRemoved b
                clearTreeposs; drawCurr'
            where f = if b then removeCyclePtrs else moreTree
        
        -- | Used by 'checkForward'. Called by menu item /remove node/ from menu
        -- /transform selection/.
        removeNode :: Action
        removeNode = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
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
                        setProofTerm RemoveNode
                        setProof False False "REMOVING THE NODE" [p]
                                           "The selected node has been removed."
                        clearTreeposs; drawCurr'
        
        -- | Used by 'checkForward'. Called by menu item /remove other trees/
        -- from tree menu.
        removeOthers :: Action
        removeOthers = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                treeMode <- readIORef treeModeRef
                if treeMode == "tree" then labGreen' "There is only one tree."
                else do
                    curr <- readIORef currRef
                    modifyIORef solPositionsRef
                        $ \solPositions -> [0 | curr `elem` solPositions]
                    writeIORef treeModeRef "tree"
                    treeMode <- readIORef treeModeRef
                    writeIORef treesRef [trees!!curr]
                    modifyIORef counterRef $ \counter -> upd counter 't' 1
                    writeIORef currRef 0
                    setProofTerm RemoveOthers
                    setTreesFrame []
                    setProof (treeMode == "summand") False
                                 "REMOVING THE OTHER TREES" [] removedOthers
        
        -- | Used by 'checkForward'. Called by menu item /remove path/ from menu
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
                setProofTerm RemovePath
                setProof False False "REMOVING THE PATH" [p]
                    ("The selected subtree and its ancestor"
                    ++ " nodes have been removed.")
                clearTreeposs; drawCurr'
        
        -- | Called by menu item /remove map/ from menu /signature/.
        removeSigMap :: Action
        removeSigMap = do
            writeIORef signatureMapRef (id,[])
            labGreen' iniSigMap
        
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
            writeIORef symbolsRef iniSymbols
            writeIORef signatureMapRef (id,[])
            where empty = flip writeIORef []
        
        -- | Called by menu item /remove/ from menu /substitution/.
        removeSubst :: Action
        removeSubst = do setSubst' (V,[]); labGreen' emptySubst
        
        -- | Used by 'checkForward'. Called by menu item /remove/ from menu
        -- /transform selection/ or by pressing key @r@ with left label ('lab')
        -- active.
        removeSubtrees :: Action
        removeSubtrees = do
            trees <- readIORef treesRef
            curr <- readIORef currRef
            if null trees then labBlue' start
            else do
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    lg = length trees
                    ps = if null treeposs then [[]] else minis (<<=) treeposs
                if ps == [[]] then
                    if lg < 2 then labRed' "There is at most one tree."
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
                        setProofTerm RemoveSubtrees
                        setTreesFrame []
                        setProof b False "REMOVING THE CURRENT TREE" []
                            "The current tree has been removed."
                else if any null ps then labRed' $ noApp "Subtree removal"
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
                                                   then simplifyIter sig t'
                                                   else t'
                        setProofTerm RemoveSubtrees
                        setProof b True "REMOVING SUBTREES" ps removed
                        clearTreeposs; drawCurr'
        
        -- | Called by menu item /remove theorems/ from menu /theorems/.
        removeTheorems :: Action
        removeTheorems = do
            writeIORef theoremsRef []
            labGreen' "There are no theorems."
        
        -- | Called by menu item /rename/ from menu /substitution/.
        renameVar :: Action
        renameVar = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                str <- ent `gtkGet` entryText
                renameVar' str
        
        -- | Used by 'checkForward' and 'renameVar'.
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
                            setProofTerm (RenameVar str)
                            setProof False False "RENAMING VARIABLES" ps
                                                "Variables have been renamed."
                            clearTreeposs; drawCurr'
                        _ -> labMag "Enter equations between variables."
        
        -- | Called by menu item /label roots with entry/ from menu /graph/ or
        -- by pressing @l@ with left label ('lab') active.
        replaceNodes :: Action
        replaceNodes = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                x <- ent `gtkGet` entryText
                if null x then labRed' "The entry field is empty."
                else replaceNodes' x
        
        -- | Used by 'checkForward' and 'replaceNodes'.
        replaceNodes' :: String -> Action
        replaceNodes' x = do
            sig <- getSignature
            trees <- readIORef treesRef
            curr <- readIORef currRef
            treeposs <- readIORef treepossRef
            let t = trees!!curr
                ps = emptyOrAll treeposs
                ts = map (changeRoot . getSubterm t) ps
                new = if isFovar sig x then V x else F x []
                changeRoot (V _)    = new
                changeRoot (F _ []) = new
                changeRoot (F _ ts) = F x ts
                changeRoot t        = t
            writeIORef treesRef $ updList trees curr $ fold2 replace0 t ps ts
            setProofTerm $ ReplaceNodes x; drawCurr'
            setProof False False "REPLACING NODES" ps $ nodesReplaced x
        
        -- | Used by 'checkForward'. Called from menu item
        -- /replace by tree of Solver@N@/ from menu /transform selection/.
        replaceOther :: Action
        replaceOther = do
            solve <- readIORef solveRef
            other <- getSolver solve
            tree <- getTree solve
            case tree of
                Just t -> do
                    treeposs <- readIORef treepossRef
                    curr <- readIORef currRef
                    let p = emptyOrLast treeposs
                    modifyIORef treesRef $ \trees
                        -> updList trees curr $ replace1 (trees!!curr) p t
                    setProofTerm ReplaceOther
                    setProof False False "REPLACING A SUBTREE" [p]
                        $ replaceIn other
                    clearTreeposs; drawCurr'
                _ -> labBlue' $ startOther other
        
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
                                _ -> return ()

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
                    p:ps = case treeposs of [p] -> [[],p]; _ -> treeposs
                    u:us = map (getSubterm1 t) (p:ps)
                    ts = getOtherSides u p us ps
                maybe (labMag selectCorrectSubformula) (replaceSubtrees' ps) ts
        
        -- | Used by 'checkForward' and 'replaceSubtrees'.
        replaceSubtrees' :: [[Int]] -> [TermS] -> Action
        replaceSubtrees' ps ts = do
            sig <- getSignature
            writeIORef proofStepRef $ ReplaceSubtrees ps ts
            trees <- readIORef treesRef
            curr <- readIORef currRef
            let t = fold2 replace1 (trees!!curr) ps ts
            maybeSimplify sig t
            makeTrees sig
            finish ps
            where msg = "REPLACING THE SUBTREES"
                  finish ps = do
                    proofStep <- readIORef proofStepRef
                    setProofTerm proofStep
                    setTreesFrame []
                    setProof True True msg ps replacedTerm
        
        -- | Called by menu item /insert\/replace by text/ from menu
        -- /transform selection/ or by pressing @i@ while left lable ('lab') is
        -- active.
        replaceText :: Action
        replaceText = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                str <- getTextHere
                replaceText' str
        
        -- | Used by 'checkForward' and 'replaceText'.
        replaceText' :: String -> Action
        replaceText' str = do
            sig <- getSignature
            treeposs <- readIORef treepossRef
            let ps = emptyOrAll treeposs
            case parseE (term sig) str of
                Correct u -> finish u ps
                _ -> case parseE (implication sig) str of
                        Correct u -> finish u ps
                        p -> incorrect p str illformed
            where finish u ps@(p:_) = do
                    trees <- readIORef treesRef
                    curr <- readIORef currRef
                    case changeTerm (trees!!curr) u ps of
                        Wellformed t -> do
                            if null p then changeMode t
                            else writeIORef treesRef $ updList trees curr t
                            setProofTerm $ ReplaceText str
                            setProof False False "REPLACING THE SUBTREES" ps
                                     textInserted
                            clearTreeposs; drawCurr'
                        Bad str -> labMag str
        
        -- | Used by 'checkForward'.
        replaceVar :: String -> TermS -> [Int] -> Action
        replaceVar x u p = do
            trees <- readIORef treesRef
            curr <- readIORef currRef

            sig <- getSignature
            writeIORef proofStepRef $ ReplaceVar x u p
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
                        setProofTerm =<< readIORef proofStepRef
                        setTreesFrame []
                        setProof True True msg [p]
                                         $ subMsg str x
        
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
        
        -- | Used by 'checkForward'. Called by menu item /reverse/ from menu
        -- /transform selection/.
        reverseSubtrees :: Action
        reverseSubtrees = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
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
                             then labRed' $ noApp "Subtree reversal"
                             else finish t ps b
            where finish t ps b = do
                    curr <- readIORef currRef
                    modifyIORef treesRef $ \trees ->
                        updList trees curr $ fold2 exchange t (f ps) $ f
                            $ reverse ps
                    setProofTerm ReverseSubtrees
                    setProof b False "REVERSING THE SUBTREES" ps reversed
                    clearTreeposs; drawCurr'
                    where f = take $ length ps`div`2
        
        -- | Used by 'narrowOrRewritePar'.
        rewritePar :: TermS
                   -> Sig
                   -> Maybe Int
                   -> [TermS]
                   -> Bool
                   -> [TermS]
                   -> [[Int]]
                   -> [[Int]]
                   -> (String -> Int)
                   -> Action
        rewritePar t sig k cls saveRedex used (p:ps) qs vc =
            if p `notElem` positions t --- || isVarRoot sig redex
            then rewritePar t sig k cls saveRedex used ps qs vc
            else do
                matching <- readIORef matchingRef
                axioms <- readIORef axiomsRef
                let cls1 = filterClauses sig redex $ filter unconditional cls
                    cls2 = if saveRedex then map copyRedex cls1 else cls1
                    (cls3,vc') = renameApply cls2 sig t vc
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
        
        -- | Used by 'checkProof' and 'stopRun''.
        runChecker :: Bool -> Action
        runChecker b = do
            when b $ do
              sp <- ent `gtkGet` entryText
              let newSpeed = parse pnat sp
              when (just newSpeed) $ writeIORef speedRef $ get newSpeed
            skipOpts backBut backButSignalRef
            skipOpts forwBut forwButSignalRef
            runOpts deriveBut deriveButSignalRef
            runProof <- runner checkForward
            speed <- readIORef speedRef
            startRun runProof speed
            let act = do checkForward
                         showTreePicts
            showTreePicts
            setButtons paint skipOpts skipOpts runOpts
            runProofP <- runner act
            startRun runProofP speed
            writeIORef checkersRef [runProof,runProofP]
            where skipOpts btn cmd = do
                    btn `gtkSet` [ buttonLabel := "" ]
                    setBackground btn redback
                    replaceCommandButton cmd btn $ return ()
                  runOpts btn cmd = do
                    btn `gtkSet` [ buttonLabel := "stop run" ]
                    setBackground btn redback
                    replaceCommandButton cmd btn stopRun'
        
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
        saveGraph :: FilePath -> Action
        saveGraph dir = do
          dirPath <- pixpath dir
          let f n = do writeIORef currRef n
                       treeSlider `gtkSet` [rangeValue := fromIntegral n]
                       clearTreeposs
                       drawCurr'
                       delay $ saveGraphDH True canv dir dirPath n
          trees <- readIORef treesRef
          case trees of []  -> labBlue' start
                        [_] -> if length dir < 5 then
                                  labMag "Enter a file name!"
                               else do
                                 let suffix = drop (length dir-4) dir
                                 dirPath <- pixpath dir -- ohaskell where
                                 file <- savePic suffix canv dirPath
                                 lab2 `gtkSet` [labelText := saved "tree" file]
                        _   -> do
                               renewDir dirPath
                               saver <- runner2 f $ length trees-1
                               (saver&startRun) 500
                               labGreen' $ saved "trees" dirPath
            
        -- | Called by button "save pic to dir" ('saveDBut').
        saveGraphD :: Action
        saveGraphD = do
          trees <- readIORef treesRef
          if null trees then labBlue' start
          else do
               str <- ent `gtkGet` entryText
               case parse nat str of Just n -> writeIORef picNoRef n
                                     _ -> return ()
               picNo <- readIORef picNoRef
               saveGraphDP' True canv picNo
        
        saveGraphDP' b screen n = do
          picDir <- readIORef picDirRef
          when (notnull picDir) $ do
            pp <- pixpath picDir
            saveGraphDH b screen picDir pp n
            modifyIORef picNoRef succ
        
        -- | Used by 'draw' and 'saveGraphN'.
        saveGraphDH :: Bool -> Canvas -> FilePath -> FilePath -> Int -> Action
        saveGraphDH b screen dir dirPath n = do
          mkHtml screen dir dirPath n
          let pic = if b then "tree" else "graph in the painter"
          lab2 `gtkSet` [ labelText := saved pic $ mkFile dirPath n]
        
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
                file <- ent `gtkGet` entryText
                filePath <- userLib file
                let pfile = filePath ++ "P"
                    tfile = filePath ++ "T"
                write pfile $ '\n':showDeriv proof trees solPositions
                write tfile $ show proofTerm
                labGreen' $ saved "proof" pfile ++ '\n':saved "proof term" tfile
            where write file str = writeFile file $ "-- " ++ file ++ '\n':str
        
        -- | Called by menu item /save map to file/ from menu /signature/.
        saveSigMap :: FilePath -> Action
        saveSigMap file = do
            signatureMap <- readIORef signatureMapRef
            saveFile file $ showSignatureMap signatureMap ""
            labGreen' $ saved "signature map" file
        
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
            labGreen' $ saved "specification" file
            where f str g cls = if null cls then "" else str ++ g cls
        
        -- | Called  by pressing key @Down@ while entry field ('ent') is active.
        saveTree :: FilePath -> Action
        saveTree file = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                treeMode <- readIORef treeModeRef
                fast <- readIORef fastRef
                saveFile file $ showTree fast $ joinTrees treeMode trees
                labGreen' $ saved "trees" file
        
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
            if null trees then labGreen' msg
            else do
                setProofTerm $ SetAdmitted block xs
                setProof True False "ADMITTED" [] msg
        
        -- | Called by /collapse after simplify/ from menu
        -- /graph/.
        setCollapse :: Action
        setCollapse = do
            modifyIORef collSimplsRef not
            collSimpls <- readIORef collSimplsRef
            simplButD `gtkSet`[ buttonLabel := if collSimpls then "simplifyDC"
                                            else "simplifyD"]
            simplButB `gtkSet` [ buttonLabel :=  if collSimpls then "simplifyBC"
                                              else "simplifyB"]
        
        -- | Used by 'buildSolve'', 'checkForward', 'incrCurr',
        -- 'setCurrInSolve'' and 'simplify'''.
        setCurr :: String -> Int -> Action
        setCurr msg n = do
            curr <- readIORef currRef

            if n /= curr then do
                writeIORef currRef n
                treeSlider `gtkSet` [ rangeValue := fromIntegral n ]
                setCurrInPaint paint n
                setProofTerm $ SetCurr msg n
                setProof True False "MOVED" [] msg
                clearTreeposs
                drawCurr'
            else labColorToPaint magback msg

        -- | Exported by public 'Epaint.Solver' method 'Epaint.setCurrInSolve'.
        setCurrInSolve' :: Int -> Action
        setCurrInSolve' n = do
            trees <- readIORef treesRef
            when (n < length trees) $ setCurr newCurr n
        
        -- | Used by 'buildSolve''.
        setDeriveMode :: Action
        setDeriveMode = do
            checking <- readIORef checkingRef

            if checking then do
                proofTPtr <- readIORef proofTPtrRef
                proofPtr <- readIORef proofPtrRef
                simplifying <- readIORef simplifyingRef
                refuting <- readIORef refutingRef
                checkers <- readIORef checkersRef

                mapM_ stopRun0 checkers
                writeIORef checkingRef False
                writeIORef speedRef 500
                backBut `gtkSet` [ buttonLabel := "<---" ]
                replaceCommandButton backButSignalRef backBut backProof
                forwBut `gtkSet` [ buttonLabel := "--->" ]
                replaceCommandButton forwButSignalRef forwBut forwProof'
                case (simplifying,refuting) of (True,True)  -> dsr
                                               (True,_)     -> ds
                                               (False,True) -> dr
                                               _ -> set' "derive"
                quit `gtkSet` [ buttonLabel := "quit" ]
                replaceCommandButton quitSignalRef quit mainQuit
                setNarrow False False
                setButtons paint (f "narrow/rewrite" narrow')
                                 (f "simplifyD" $ simplify' True)
                                 (f "simplifyB" $ simplify' False)
                modifyIORef proofTermRef
                    $ \proofTerm -> take proofTPtr proofTerm
                proofTerm <- readIORef proofTermRef
                enterPT' proofTPtr proofTerm
                modifyIORef proofRef $ \proof -> take (proofPtr+1) proof
            else do
                simplifying <- readIORef simplifyingRef
                refuting <- readIORef refutingRef

                case (simplifying,refuting) of
                    (False,False) -> do writeIORef simplifyingRef True; ds
                    (True,False) -> do writeIORef refutingRef True; dsr
                    (True,_) -> do writeIORef simplifyingRef False; dr
                    _ -> do writeIORef refutingRef False; set' "derive"
                simplifying <- readIORef simplifyingRef
                refuting <- readIORef refutingRef
                setProofTerm $ DeriveMode simplifying refuting
         where f str act btn cmd = do
                    btn `gtkSet` [ buttonLabel := str ]
                    replaceCommandButton cmd btn $ do
                        remote paint
                        act
                        showTreePicts
               set' str = do
                    deriveBut `gtkSet` [ buttonLabel := str ]
                    replaceCommandButton deriveButSignalRef
                        deriveBut setDeriveMode
               ds = set' "derive & simplify"
               dr = set' "derive & refute"
               dsr = set' "derive & simplify & refute"
        
        {- |
            Set font of text area ('tedit'), entry field ('ent'), left label
            ('lab') and right label ('lab2').
            Called by button 'fontBut' on font change.
        -}
        setFont :: FontDescription -> Action
        setFont fo = do
            writeIORef fontRef fo
            size <- fontDescriptionGetSize fo
            -- By changing the font size slider, setFontSize is called, which
            -- handles the font changing of the GUI elements.
            when (just size) $ fontSize `gtkSet` [ rangeValue := get size]
            trees <- readIORef treesRef
            when (notnull trees) drawCurr'
        
        {- |
            Set font size of text area ('tedit'), entry field ('ent'), left
            label ('lab') and right label ('lab2').
            Called by scale 'fontSize'.
        -}
        setFontSize :: Action
        setFontSize = do
            fo <- readIORef fontRef
            size <- fontSize `gtkGet` rangeValue
            fontDescriptionSetSize fo size
            fo' <- fontDescriptionCopy fo
            fontDescriptionSetFamily fo' monospace
            widgetOverrideFont tedit $ Just fo'
            widgetOverrideFont ent $ Just fo'
            fontDescriptionSetFamily fo' sansSerif
            fontDescriptionSetStyle fo' StyleItalic
            widgetOverrideFont lab $ Just fo'
            widgetOverrideFont lab2 $ Just fo'
        
        -- | The @opts@ function sets the behavior of the forward button
        -- ('forwBut').
        -- Exported by public 'Epaint.Solver' method 'Epaint.setForw'.
        setForw' :: (Button -> IORef (ConnectId Button) -> Action) -> Action
        setForw' opts = opts forwBut forwButSignalRef -- Note [setForw]
        
        {- Note [setForw]
        ~~~~~~~~~~~~~~~~~
        The behavior of the setForw' function changed with the port from
        O'Haskell/Tcl to GTK+. Originally @opts@ was a list of button options.
        Since GTK+ works different and the option system also was strongly mixed
        with the object oriented inheritance system, this function now takes a
        function as parameter, which handles the change in the button behavior.
        -}
        
        -- | Changes the picture interpreter. This determines how the painter is
        -- handling the graph on a call.
        -- Used by 'callEnum' and 'checkProof'. Called by interpreter button.
        setInterpreter' :: String -> Action
        setInterpreter' eval = do
            sig <- getSignature
            writeIORef wtreeRef $ take 4 eval == "tree"
            writeIORef picEvalRef eval
            interpreterLabel `gtkSet` [ labelLabel := eval ]
            spread <- readIORef spreadRef
            setEval paint eval spread
            draw <- ent `gtkGet` entryText
            writeIORef drawFunRef
              $  if draw == "text" || (sig&isDefunct) draw then draw else ""
            drawFun <- readIORef drawFunRef
            labGreen' $ newInterpreter eval drawFun
        
        -- | Used by 'changeMode', 'setDeriveMode' and 'setTreeposs'. Called by
        -- button 'matchBut'.
        setNarrow :: Bool -> Bool -> Action
        setNarrow chgMatch chgRandom = do
          treeposs <- readIORef treepossRef
          trees <- readIORef treesRef
          curr <- readIORef currRef
          formula <- readIORef formulaRef

          sig <- getSignature
          let nar = formula || notnull treeposs &&
                          treeposs `subset` boolPositions sig (trees!!curr)
              set' str1 str2 = do
                matchBut `gtkSet` [ buttonLabel := str1 ]
                randomBut `gtkSet` [ buttonLabel := str2 ]
                narrowBut `gtkSet`
                  [ buttonLabel := if nar then "narrow" else "rewrite"]
          when (chgMatch && nar) $ do
              modifyIORef matchingRef
                  $ \matching -> (matching+2) `mod` 4
              matching <- readIORef matchingRef
              setProofTerm $ Match matching
          matching <- readIORef matchingRef
          
          when chgRandom $ do
            modifyIORef matchingRef $ \matching ->
              if even matching then matching+1 
                               else matching-1
            matching <- readIORef matchingRef
            setProofTerm $ Match matching
          matching <- readIORef matchingRef
          case matching of
            0 -> set' "match" "all"
            1 -> set' "match" "random"
            2 -> set' "unify" "all"
            _ -> set' "unify" "random"
        
        -- | Exported by public 'Epaint.Solver' method 'Epaint.setNewTrees'.
        setNewTrees' :: [TermS] -> String -> Action
        setNewTrees' ts typ = do
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
          lab2 `gtkSet` [ labelText := picDir ++ " is the current directory"]
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
          safe <- readIORef safeRef
          constraints <- readIORef constraintsRef
          fast <- readIORef fastRef

          let oldProofElem = proof!!proofPtr
              t = trees!!curr
              n = counter 'd'
              msgAE = msg == "ADMITTED" || msg == "EQS"
              msgSP = msg == "SPLIT"
              msgMV = msg == "MOVED" || msg == "JOIN"
              str | msgAE     = labMsg
                  | msgSP     = labMsg ++ show (length trees)
                                   ++ ' ':treeMode ++ "s."
                                   ++ showCurr fast t treeMode
                  | msgMV     = labMsg ++ showCurr fast t treeMode
                  | newTrees  = showNew fast (length trees) t msg n ps treeMode
                  | otherwise = showPre fast t msg n ps treeMode
              str0 = "\nThe axioms have been MATCHED against their redices."
                  `onlyif` matching < 2
              str1 = "\nThe reducts have been simplified."
                  `onlyif` simplifying
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
              msg1 = msgL ++ if newTrees || msgAE || msgSP || msgMV ||
                                notnull msgL && head msgL == ' ' ||
                                trees /= (oldProofElem&peTrees)
                     then "" else "\nCAUTION: The "++ formString formula
                                            ++" has not been modified."
              u = joinTrees treeMode trees
              us = map (joinTrees treeMode . peTrees) proof
              cycle = search (eqTerm u) us
              cmsg = "\nThe entire goal coincides with no. " ++ show (get cycle)
              (msg2,msg3) = if just cycle then (msgP++cmsg,msg1++cmsg)
                                          else (msgP,msg1)
          when (null ruleString || n > 0) $ do
             modifyIORef proofPtrRef succ
             proofPtr <- readIORef proofPtrRef
             perms <- readIORef permsRef
             let next = ProofElem
                      { peMsg = msg2
                      , peMsgL = msg3
                      , peTreeMode = treeMode
                      , peTrees = trees
                      , peTreePoss = ps
                      , peCurr = curr
                      , pePerms = perms
                      , peVarCounter = varCounter
                      , peNewPreds = newPreds
                      , peSolPositions = solPositions
                      , peSubstitution = substitution
                      , peSafe = safe
                      , peConstraints = constraints
                      , peJoined = joined
                      }
             modifyIORef proofRef
               $ \proof -> take proofPtr proof++[next]
             chgPerm <- readIORef chgPermRef
             case u of F x ts@(_:_:_) | chgPerm && just cycle
                                                && x `elem` words "| &"
                         -> do
                            let n = length ts
                            modifyIORef permsRef
                              $ \perms -> upd perms n $ nextPerm $ perms n
                            writeIORef treesRef [F x [ts!!i | i <- perms n]]
                                  -- [F x $ tail ts++[head ts]]
                                  -- [F x $ reverse ts]
                            writeIORef currRef 0
                       _ -> return ()
       -- else picNo := picNo-1
          writeIORef newTreesRef False
          writeIORef ruleStringRef ""
          labColorToPaint greenback $ show proofPtr ++ ". " ++ msg3
        
        setProofTerm :: Step -> Action
        setProofTerm step = do
            checking <- readIORef checkingRef
            proofTPtr <- readIORef proofTPtrRef
            proofTerm <- readIORef proofTermRef

            when (not checking) $ do
                let pt = if proofTPtr+1 < length proofTerm
                               then take proofTPtr proofTerm else proofTerm
                writeIORef proofTermRef $ addStep pt step
                writeIORef proofTPtrRef $ length proofTerm
        
        setQuit' :: (Button -> IORef (ConnectId Button) -> Action) -> Action
        setQuit' opts = opts quit quitSignalRef

        
        -- | Used by 'addSubst', 'changeState', 'initialize', 'releaseTree',
        -- 'removeSubst' and 'unifyAct'. Exported by public 'Epaint.Solver'
        -- method 'Epaint.setSubst'.
        setSubst' :: (String -> TermS,[String]) -> Action
        setSubst' subst@(_,dom) = do
            setBackground subToBut $ if null dom then blueback else redback
            domMenu <- getMenu "domMenu" -- Note [DomMenu]
            containerForeach domMenu (containerRemove domMenu) -- Note [DomMenu]
            mapM_ (mkButF domMenu applySubstTo) dom
            writeIORef substitutionRef subst
        
        {- Note [DomMenu]
        ~~~~~~~~~~~~~~~~~
        
        Since Gtk+3 MenuButton is not implemented by Haskells gtk3 package,
        it is not possible to access the subToBut button. Instead the domMenu
        has become part of the glade file and will never be replaced. Instead
        of creating a new domMenu every time setSubst' is called, all items
        are removed.
        -}
        
        {- unused
        -- | Called by button "set" ('subBut').
        setSubtrees :: Action
        setSubtrees = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                str <- ent `gtkGet` entryText
                curr <- readIORef currRef
                let f = natToLabel $ posTree [] $ trees!!curr
                case parse intRanges str of
                    Just ns | all (just . f) ns -> do
                        let qs = map get $ map f ns
                        treeposs <- readIORef treepossRef
                        setTreeposs $ Add $ qs `minus` treeposs
                        drawSubtrees
                        labGreen' $ case qs of
                                   [q] -> "The tree at position " ++ show q ++
                                          " has been selected."
                                   _ -> "The trees at position " ++
                                        init (tail $ show qs `minus1` ' ') ++
                                        " have been selected."
                    _ -> labMag "Enter tree positions in heap order!"
        -}
        
        -- | Used by 'showSubtreePicts', 'showTreePicts', 'simplify''',
        -- 'enterTree'' and 'narrow'''.
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

            setProofTerm $ Mark treeposs
            setNarrow False False
        
        -- | Used by 'simplify''', 'splitTree', 'applyInd', 'applyTheorem',
        -- 'changeState', 'enterTree'', 'narrowLoop', 'narrowPar',
        -- 'narrowSubtree', 'removeOthers', 'removeSubtrees',
        -- 'replaceSubtrees'', 'replaceVar' and 'setNewTrees''.
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
            drawCurr'
        
        -- | Change varCounter state. Used by 'applyClause', 'applyCoinduction',
        -- 'applyTransitivity', 'compressAxioms', 'compressClauses',
        -- 'createInvariant', 'flattenImpl', 'showEqsOrGraph' and 'stretch'.
        setZcounter :: Int -> Action
        setZcounter n = modifyIORef varCounterRef
            $ \varCounter -> upd varCounter "z" n
        
        -- | Used by 'checkForward'. Called by menu item /shift pattern to rhs/
        -- from menu /transform selection/.
        shiftPattern :: Action
        shiftPattern = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
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
                            curr <- readIORef currRef
                            modifyIORef treesRef $ \trees ->
                                updList trees curr $ replace1 t p cl
                            setProofTerm ShiftPattern
                            setProof True False "SHIFTING A PATTERN" [[]]
                                "A pattern has been shifted."
                            clearTreeposs; drawCurr'
                        _ -> labMag "The selected pattern cannot be shifted."
        
        -- | Used by 'checkForward'. Called by menu item /move up quantifiers/
        -- from menu /transform selection/. 
        shiftQuants :: Action
        shiftQuants = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
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
                                v' = simplifyIter sig v
                            finish (replace1 t q $ mkAll as $ mkAny es v') ps vc
                        else errorMsg
                    else errorMsg
            where finish t ps vc = do
                        curr <- readIORef currRef
                        modifyIORef treesRef $ \trees -> updList trees curr t
                        writeIORef varCounterRef vc
                        setProofTerm ShiftQuants
                        setProof True False "MOVING UP QUANTIFIERS" ps moved
                        clearTreeposs; drawCurr'
                  errorMsg = labRed' $ noApp "Move up quantifiers"
        
        -- Called by menu item /shift subformulas/ from menu
        -- /transform selection/. 
        shiftSubs :: Action
        shiftSubs = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                treeposs <- readIORef treepossRef
                if null treeposs || any null treeposs
                then labRed' $ noApp "Shift subformulas"
                else shiftSubs' treeposs
        
        -- | Used by 'checkForward' and 'shiftSubs'.
        shiftSubs' :: [[Int]] -> Action
        shiftSubs' ps = do
            sig <- getSignature
            trees <- readIORef treesRef
            curr <- readIORef currRef
            case shiftSubformulas sig (trees!!curr) ps of
                Just t -> do
                    writeIORef treesRef $ updList trees curr t
                    setProofTerm $ ShiftSubs ps
                    setProof True False "SHIFTING SUBFORMULAS" ps shifted
                    clearTreeposs; drawCurr'
                _ -> labRed' $ noApp "Shift subformulas"
        
        -- | Used by 'removeClauses'. Called by menu items /show/ and
        -- /[show].. in text field of SolverN/ from menu /axioms/.
        showAxioms :: Bool -> Action
        showAxioms b = do
            axioms <- readIORef axiomsRef
            if null axioms then labGreen' "There are no axioms."
            else
                if b then do
                    enterFormulas' axioms
                    labGreen' $ see "axioms"
                else do
                    solve <- readIORef solveRef
                    bigWin solve
                    enterFormulas solve axioms
        
        -- | Called by menu item /[show].. for symbols/ from menu /axioms/ or by
        -- pressing button @x@ while left label ('lab') is active.
        showAxiomsFor :: Action
        showAxiomsFor = do
            str <- ent `gtkGet` entryText
            treeposs <- readIORef treepossRef
            trees <- readIORef treesRef
            curr <- readIORef currRef
            axioms <- readIORef axiomsRef
            let ps = emptyOrAll treeposs
                xs = if null trees || null treeposs && notnull str
                     then words str
                     else mkSet $ map (label $ trees!!curr) ps
                axs = clausesFor xs axioms
            if null axs then labRed' $ noAxiomsFor xs
            else do
                enterFormulas' axs
                labGreen' $ see $ "axioms for " ++ showStrList xs
        
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
                    drawCurr'
                else labMag newCurr
        
        -- | Used by 'removeClauses'. Called by menu item /show conjects/ from
        -- menu /theorems/.
        showConjects :: Action
        showConjects = do
            conjects <- readIORef conjectsRef
            if null conjects then labGreen' "There are no conjectures."
            else do
                enterFormulas' conjects
                labGreen' $ see "conjectures"
        
        -- | Called by menu item /coordinates/ from menu /nodes/.
        showCoords :: Action
        showCoords = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                writeIORef restoreRef True
                curr <- readIORef currRef
                ctree <- readIORef ctreeRef
                drawThis (cTree (trees!!curr) $ get ctree) [] ""
        
        -- | Called by menu item /cycle targets/ from menu /nodes/.
        showCycleTargets :: Action
        showCycleTargets = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                writeIORef restoreRef True
                curr <- readIORef currRef
                let t = trees!!curr
                drawThis t (cycleTargets t) "green"
        
        -- | Called by menu item /greatest lower bound/ from menu /nodes/.
        showGlb :: Action
        showGlb = do
            treeposs <- readIORef treepossRef
            if null treeposs then labMag "Select subtrees!"
            else do
                writeIORef restoreRef True
                trees <- readIORef treesRef
                curr <- readIORef currRef
                drawThis (trees!!curr) [glbPos treeposs] "green"
        
        -- | Called by menu item /show induction hypotheses/ from menu
        -- /theorems/.
        showIndClauses :: Action
        showIndClauses = do
            indClauses <- readIORef indClausesRef
            if null indClauses
            then labGreen' "There are no induction hypotheses."
            else do
                enterFormulas' indClauses
                labGreen' $ see "induction hypotheses"
        
        -- | Called by all /show matrix/ menu items from menu /graph/.
        showMatrix :: Int -> Action
        showMatrix m = do
          kripke <- readIORef kripkeRef
          treeposs <- readIORef treepossRef
          trees <- readIORef treesRef
          curr <- readIORef currRef
          spread <- readIORef spreadRef
          sig <- getSignature
          let [sts,ats,labs] 
                  = map (map showTerm0) [sig&states,sig&atoms,sig&labels]
              p:ps = emptyOrAll treeposs
              t = getSubterm1 (trees!!curr) p
              f = if null ps then id else drop $ length p
              is = [i | [i,1] <- map f ps]
          pict <- runT $ matrix sizes0 spread t
          let u = case m of 0 -> Hidden $ BoolMat sts sts
                                        $ deAssoc0 $ mkPairs sts sts (sig&trans)
                            1 -> Hidden $ BoolMat ats sts
                                        $ deAssoc0 $ mkPairs ats sts (sig&value)
                            2 -> Hidden $ BoolMat sts ats
                                        $ deAssoc0 $ mkPairs sts ats $ out sig
                            3 -> Hidden $ ListMat sts (labs' trips) $ trips
                                 where
                                   trips = mkTriples sts labs sts (sig&transL)
                            4 -> Hidden $ ListMat ats (labs' trips) $ trips
                                 where
                                   trips = mkTriples ats labs sts (sig&valueL)
                            5 -> Hidden $ ListMat sts (labs' trips) $ trips
                                 where trips = mkTriples sts labs ats $ outL sig
                            _ -> case parseEqs t of
                                    Just eqs -> mat m $ eqsToGraph is eqs
                                    _ -> if just pict then t else mat m t
          pict <- runT $ matrix sizes0 spread u
          if m > 5 && null trees then labBlue' start
          else
              if nothing pict then labMag "The matrix is empty."
              else do
                  font <- readIORef fontRef
                  sizes <- mkSizes canv font $ stringsInPict $ get pict
                  fast <- readIORef fastRef
                  spread <- readIORef spreadRef
                  setEval paint "" spread
                  Just pict <- runT $ matrix sizes spread u
                  curr <- readIORef currRef
                  callPaint paint [pict] [curr] False True curr "white"
          where labs' trips = mkSet [x | (_,x,_:_) <- trips]
                mat 6 t = Hidden $ BoolMat dom1 dom2 ps
                          where ps = deAssoc0 $ graphToRel t
                                (dom1,dom2) = sortDoms ps
                mat _ t = Hidden $ ListMat dom1 dom2 ts
                         where ts = graphToRel2 (evenNodes t) t
                               (dom1,dom2) = sortDoms $ map (pr1 *** pr2) ts
        
        -- | Called by all /(...) numbers/ menu items from /nodes/ menu.
        showNumbers :: Int -> Action
        showNumbers m = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
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
                drawThis (replace1 t p v) [] ""
         where label (RGB 0 0 0) n = show n
               label c n           = show c++'_':show n
               order = case m of 1 -> levelTerm -- "level numbers"
                                 2 -> preordTerm -- "preorder positions"
                                 3 -> heapTerm -- "heap positions"
                                 _ -> hillTerm -- "hill positions"
        
        -- | Called by button /paint/ ('paintBut'). Exported by public
        -- 'Epaint.Solver' method 'Epaint.showPicts'.
        showPicts' :: Action
        showPicts' = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                checking <- readIORef checkingRef
                if checking then do
                    writeIORef checkingPRef True
                    showTreePicts
                else do
                    treeposs <- readIORef treepossRef
                    if null treeposs then showTreePicts
                    else showSubtreePicts
        
        -- | Called by menu item /polarities/ from menu /nodes/.
        showPolarities :: Action
        showPolarities = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                writeIORef restoreRef True
                curr <- readIORef currRef
                let t = trees!!curr
                    ps = polTree True [] t
                drawThis (colorWith2 "green" "red" ps t) [] ""
        
        -- | Called by menu item /positions/ from menu /nodes/.
        showPositions :: Action
        showPositions = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                writeIORef restoreRef True
                curr <- readIORef currRef
                let t = trees!!curr
                drawThis (mapT f $ posTree [] t) (pointers t) "red"
            where f = unwords . map show
        
        -- | Called by menu item /predecessors/ from menu /nodes/.
        showPreds :: Action
        showPreds = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                writeIORef restoreRef True
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    ps = concatMap (nodePreds t) $ emptyOrAll treeposs
                drawThis t ps "green"
        
        -- | Called by both /show proof/ menu items from tree menu.
        showProof :: Bool -> Action
        showProof b = do
            proof <- readIORef proofRef
            if null proof then labMag "The proof is empty."
            else do
                trees <- readIORef treesRef
                solPositions <- readIORef solPositionsRef
                let str = '\n':showDeriv proof trees solPositions
                if b then do enterText' str; labGreen' $ see "proof"
                     else do
                        solve <- readIORef solveRef
                        bigWin solve
                        enterText solve str
        
        -- | Called by both /show proof term/ menu items from tree menu.
        showProofTerm :: Bool -> Action
        showProofTerm b = do
            proofTerm <- readIORef proofTermRef
            if null proofTerm then labMag "The proof term is empty."
            else do
                proofTPtr <- readIORef proofTPtrRef
                if b then do
                    enterPT' proofTPtr proofTerm
                    labGreen' $ see "proof term"
                else do
                    solve <- readIORef solveRef
                    bigWin solve
                    enterPT solve proofTPtr proofTerm
        
        -- | Used by 'checkForward'. Called by all /show relation/ menu items
        -- from menu /graph/.
        showRelation :: Int -> Action
        showRelation m = do
            kripke <- readIORef kripkeRef
            trees <- readIORef treesRef
            curr <- readIORef currRef
            treeposs <- readIORef treepossRef
            sig <- getSignature
            let [sts,ats,labs] 
                    = map (map showTerm0) [sig&states,sig&atoms,sig&labels]
                t = trees!!curr
                p:ps = emptyOrAll treeposs
                u = getSubterm1 t p
                f = if null ps then id else drop $ length p
                is = [i | [i,1] <- map f ps]
            case m of
               0 -> act1 $ mkRelConstsI sts sts (sig&trans) 
               1 -> act1 $ mkRelConstsI ats sts (sig&value)
               2 -> act1 $ mkRelConstsI sts ats $ out sig
               3 -> act1 $ mkRel2ConstsI sts labs sts (sig&transL)
               4 -> act1 $ mkRel2ConstsI ats labs sts (sig&valueL)
               5 -> act1 $ mkRel2ConstsI sts labs ats $ outL sig
               _ -> if null trees then labBlue' start
                    else act2 t p $ case parseEqs u of
                                         Just eqs -> eqsToGraph is eqs
                                         _ -> u
         where act1 ts = enterTree' False $ h ts
               act2 t p u = do
                    curr <- readIORef currRef
                    modifyIORef treesRef $ \trees ->
                        updList trees curr $ replace1 t p $ h $ f m u
                    clearTreeposs; drawCurr'
                    where f 6 = mkRelConsts . graphToRel
                          f _ = mkRel2Consts . graphToRel2 (evenNodes u)
               g t@(F "()" ts) us = case last ts of F "[]" [] -> us
                                                    _ -> t:us
               h = mkList . foldr g []
        
        -- | Called by menu item /show sig/ from menu /signature/.
        showSig :: Action
        showSig = do
          symbols <- readIORef symbolsRef
          constraints <- readIORef constraintsRef
          safe <- readIORef safeRef

          enterText' $ showSignature (minus6 symbols iniSymbols) ""
          let (block,xs) = constraints
          labGreen' $ see "signature" ++ '\n':admitted block xs
                                      ++ '\n':equationRemoval safe

        
        -- | Called by menu item /show map/ from menu /signature/.
        showSigMap :: Action
        showSigMap = do
            signatureMap <- readIORef signatureMapRef
            if null $ snd signatureMap then labGreen' iniSigMap
            else do
                enterText' $ showSignatureMap signatureMap ""
                labGreen' $ see "signature map"
        
        -- | Called by menu item /[show].. solutions/ from menu /substitution/.
        showSolutions :: Action
        showSolutions = do
            sig <- getSignature
            formula <- readIORef formulaRef
            trees <- readIORef treesRef
            labGreen' $ solved $ if formula then solPoss sig trees else []
        
        -- | Called by menu items /show/ and /[show].. in text field of SolverN/
        -- from menu /substitution/.
        showSubst :: Bool -> Action
        showSubst b = do
            (f,dom) <- readIORef substitutionRef
            let fs = substToEqs f dom
            if null dom then labGreen' emptySubst
            else if b then do
                enterFormulas' fs
                labGreen' $ see "substitution"
            else do
                solve <- readIORef solveRef
                bigWin solve
                enterFormulas solve fs
        
        -- | Called by menu item /[show].. on canvas of SolverN/ from menu
        -- /substitution/.
        showSubstCanv :: Action
        showSubstCanv = do
            (f,dom) <- readIORef substitutionRef
            let ts = substToEqs f dom
                typ = if length ts == 1 then "tree" else "factor"
            if null dom then labGreen' emptySubst
            else do
                solve <- readIORef solveRef
                bigWin solve
                setNewTrees solve ts typ
        
        -- | Used by 'showPicts''.
        showSubtreePicts :: Action
        showSubtreePicts = do
            sig <- getSignature
            eval <- getInterpreter
            str <- ent `gtkGet` entryText
            trees <- readIORef treesRef
            curr <- readIORef currRef
            treeposs <- readIORef treepossRef
            drawFun <- readIORef drawFunRef
            spread <- readIORef spreadRef
            let t = trees!!curr
                ts = applyDrawFun sig drawFun str $ map (closedSub t) treeposs
                picts = map (eval sizes0 spread) ts
            picts <- mapM runT picts
            font <- readIORef fontRef
            sizes <- mkSizes canv font
                      $ concatMap (stringsInPict . getJust) picts
            fast <- readIORef fastRef
            setTime
            back <- ent `gtkGet` entryText
            spread <- readIORef spreadRef
            let picts = map (eval sizes spread) ts
            picts <- mapM runT picts
            (paint&callPaint) [concatMap getJust picts] [] True True curr back
        
        -- | Called by menu item /successors/ from menu /nodes/.
        showSucs :: Action
        showSucs = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                writeIORef restoreRef True
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                drawThis t
                    (concatMap (nodeSucs t) $ emptyOrAll treeposs) "green"
        
        -- | Called by menu items /constructors/, /variables/ and
        -- /free variables/ from menu /nodes/.
        showSyms :: (Sig -> TermS -> [[Int]]) -> Action
        showSyms f = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                writeIORef restoreRef True
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                sig <- getSignature
                let t = trees!!curr
                    p = emptyOrLast treeposs
                drawThis t (map (p++) $ f sig $ getSubterm t p) "green"
        
        -- | Used by 'removeClauses'. Called by menu item /show terms/
        -- from menu /theorems/.
        showTerms :: Action
        showTerms = do
            terms <- readIORef termsRef
            if null terms then labGreen' "There are no terms to be reduced."
            else do
                enterTerms terms
                labGreen' $ see "terms"
        
        -- | Used by 'removeClauses'. Called by menu items /show theorems/
        -- and /[show theorems].. in text field of SolverN/ from menu
        -- /theorems/.
        showTheorems :: Bool -> Action
        showTheorems b = do
            theorems <- readIORef theoremsRef
            if null theorems then labGreen' "There are no theorems."
            else
                if b then do
                    enterFormulas' theorems
                    labGreen' $ see "theorems"
                else do
                    solve <- readIORef solveRef
                    bigWin solve
                    enterFormulas solve theorems
        
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
                cls = clausesFor xs theorems
            if null cls
            then labRed' $ "There are no theorems for " ++ showStrList xs ++ "."
            else do
                enterFormulas' cls
                labGreen' $ see $ "theorems for " ++ showStrList xs
        
        showTransOrKripke m = do
          sig <- getSignature
          str <- ent `gtkGet` entryText
          varCounter <- readIORef varCounterRef
          let [sts,ats,labs] = map (map showTerm0)
                                   [sig&states,sig&atoms,sig&labels]
              vcz = varCounter "z"
              (eqs,zn)    = relToEqs vcz $ mkPairs sts sts (sig&trans)
              (eqsL,zn')  = relLToEqs zn $ mkTriples sts labs sts (sig&transL)
              trGraph     = eqsToGraph [] eqs
              trGraphL    = eqsToGraph [] eqsL
              atGraph     = if all null (sig&trans) then emptyGraph
                            else outGraph sts ats (out sig) trGraph
              atGraphL    = if null (sig&labels) then emptyGraph
                            else outGraphL sts labs ats (out sig) (outL sig)
                                                                  trGraphL
              inPainter t = do
                           drawFun <- readIORef drawFunRef
                           let u = head $ applyDrawFun sig drawFun str [t]
                           spread <- readIORef spreadRef
                           pict <-  (widgetTree sig sizes0 spread u)&runT
                           if nothing pict then labMag "The tree is empty."
                           else do
                                font <- readIORef fontRef
                                sizes <- mkSizes canv font $ stringsInPict $ get pict
                                (paint&setEval) "tree" spread
                                pict <- (widgetTree sig sizes spread u)&runT
                                curr <- readIORef currRef
                                (paint&callPaint) [get pict] [curr] False True
                                                             curr "white"

          setZcounter zn'
          solve <- readIORef solveRef
          case m of 0  -> enterTree' False trGraph
                    1  -> enterTree' False $ colorClasses sig trGraph
                    2  -> inPainter trGraph
                    3  -> do (solve&bigWin); (solve&enterTree) False trGraph
                    4  -> enterTree' False trGraphL
                    5  -> enterTree' False $ colorClasses sig trGraphL
                    6  -> inPainter trGraphL
                    7  -> do (solve&bigWin); (solve&enterTree) False trGraphL
                    8  -> enterTree' False atGraph
                    9  -> inPainter atGraph
                    10 -> do (solve&bigWin); (solve&enterTree) False atGraph
                    11 -> enterTree' False atGraphL
                    12 -> inPainter atGraphL
                    _  -> do (solve&bigWin); (solve&enterTree) False atGraphL

        -- | Used by 'stopRun'', 'runChecker', 'setDeriveMode' and 'showPicts''.
        showTreePicts :: Action
        showTreePicts = do                          -- without transformer:
            sig <- getSignature
            eval <- getInterpreter                 -- getInterpreter
            str <- ent `gtkGet` entryText
            drawFun <- readIORef drawFunRef
            trees <- readIORef treesRef
            spread <- readIORef spreadRef
            let ts = applyDrawFun sig drawFun str trees
                picts = map (eval sizes0 spread) ts
            picts <- mapM runT picts           -- return ()
            font <- readIORef fontRef
            sizes <- mkSizes canv font
                      $ concatMap (stringsInPict . getJust) picts
            fast <- readIORef fastRef
            setTime
            back <- ent `gtkGet` entryText
            checkingP <- readIORef checkingPRef
            checking <- readIORef checkingRef
            curr <- readIORef currRef
            let picts = map (eval sizes spread) ts
            picts <- mapM runT picts           -- return ()
            (paint&callPaint) (map getJust picts) (indices_ ts) False 
                              (checkingP || not checking) curr back
        
        -- | Called by menu item /values/ from menu /nodes/.
        showVals :: Action
        showVals = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                writeIORef restoreRef True
                curr <- readIORef currRef
                let t = trees!!curr
                drawThis t (valPositions t) "green"
        
        -- | Called by 'Epaint.Solver' and 'Epaint.Painter' buttons /simplifyDF/
        -- ('simplButD') and /simplifyBF/ ('simplButB'). Exported by public
        -- 'Epaint.Solver' method 'Epaint.simplify'.
        simplify' :: Bool -> Action
        simplify' depthfirst = do
            trees <- readIORef treesRef

            if null trees then labBlue' start
            else do
                str <- ent `gtkGet` entryText
                let act = simplify'' depthfirst
                case parse pnat str of Just limit -> act limit True
                                       _ -> act 100 False
        
        -- | Used by 'checkForward' and 'simplify''.
        simplify'' :: Bool -> Int -> Bool -> Action
        simplify'' depthfirst limit sub = do
            trees <- readIORef treesRef
            curr <- readIORef currRef
            treeposs <- readIORef treepossRef

            writeIORef ruleStringRef "SIMPLIFYING"
            writeIORef proofStepRef $ Simplify depthfirst limit sub
            sig <- getSignature
            let t = trees!!curr
            if null treeposs then do
                treeMode <- readIORef treeModeRef
                formula <- readIORef formulaRef
                collSimpls <- readIORef collSimplsRef

                setTime
                let (u,n) = simplifyLoop sig depthfirst limit t
                    v = if collSimpls then collapse True u else u
                    msg = "The "
                        ++ (if treeMode == "tree" then formString formula
                            else "previous " ++ treeMode) ++ " is simplified."
                if n == 0 then do
                    modifyIORef counterRef $ \counter -> decr counter 't'
                    counter <- readIORef counterRef
                    if counter 't' > 0
                    then setCurr msg $ (curr+1) `mod` length trees
                    else do
                        labMag treesSimplified
                        labSolver paint treesSimplified
                else do
                    proofStep <- readIORef proofStepRef
                    ruleString <- readIORef ruleStringRef
                    solPositions <- readIORef solPositionsRef

                    modifyIORef treesRef $ \trees -> updList trees curr v
                    makeTrees sig
                    setProofTerm proofStep
                    modifyIORef counterRef $ \counter -> upd counter 'd' n
                    setProof True False ruleString []
                        $ finishedSimpl n++solved solPositions
                    setTreesFrame []
            else if sub then simplifySubtree t sig depthfirst limit
                        else simplifyPar t sig treeposs []
        
        -- | Used by 'simplify'''.
        simplifyPar :: TermS -> Sig -> [[Int]] -> [[Int]] -> Action
        simplifyPar t sig (p:ps) qs =
            case simplifyOne sig t p of
                Just t -> simplifyPar t sig ps (p:qs)
                _ -> simplifyPar t sig ps qs
        simplifyPar _ _ [] [] = labColorToPaint magback
                   "The selected trees are simplified at their root positions."
        simplifyPar t _ _ qs = do
            curr <- readIORef currRef
            proofStep <- readIORef proofStepRef
            modifyIORef treesRef $ \trees -> updList trees curr t
            setProofTerm proofStep
            modifyIORef counterRef $ \counter -> upd counter 'd' 1
            setProof True False "SIMPLIFYING THE SUBTREES" qs simplifiedPar
            clearTreeposs; drawCurr'
        
        -- | Used by 'simplify'''.
        simplifySubtree :: TermS -> Sig -> Bool -> Int -> Action
        simplifySubtree t sig depthfirst limit = do
            treeposs <- readIORef treepossRef
            collSimpls <- readIORef collSimplsRef
            let p = emptyOrLast treeposs
                (u,n) = simplifyLoop sig depthfirst limit $ getSubterm t p
                v = if collSimpls then collapse True u else u
            if n == 0 then labColorToPaint magback
                "The tree selected at last is simplified."
            else do
                curr <- readIORef currRef
                proofStep <- readIORef proofStepRef
                ruleString <- readIORef ruleStringRef
                modifyIORef treesRef
                    $ \trees -> updList trees curr $ replace1 t p v
                setProofTerm proofStep
                modifyIORef counterRef $ \counter -> upd counter 'd' n
                setProof True False ruleString [p] $
                                         appliedToSub "simplification" n
                clearTreeposs; drawCurr'
        
        -- | Called by menu item /specialize/ from menu /transform selection/.
        specialize :: Action
        specialize = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                str <- ent `gtkGet` entryText
                (exps,b) <- readIORef numberedExpsRef
                case parse nat str of
                    k@(Just n) | n < length exps ->
                        if b then finish k $ exps!!n
                        else labMag "Enter formulas into the text field!"
                    _ -> do
                        str <- getTextHere
                        sig <- getSignature
                        case parseE (implication sig) str of
                            Correct th -> finish Nothing th
                            p -> incorrect p str illformedF
            where finish k th = applyTheorem False k $
                                    case th of F "Not" [th] -> mkHorn mkFalse th
                                               _ -> mkCoHorn mkTrue th
        
        -- | Used by 'checkForward'. Called by button /split\/join/
        -- ('splitBut').
        splitTree :: Action
        splitTree = do
            trees <- readIORef treesRef
            when (notnull trees) $ do
                joined <- readIORef joinedRef

                sig <- getSignature
                setProofTerm SplitTree
                if joined then do
                    writeIORef joinedRef False
                    splitBut `gtkSet` [ buttonLabel := "join" ]
                    makeTrees sig
                    setTreesFrame []
                    setProof True False "SPLIT" []
                             "The tree has been split into "
                else do
                    treeMode <- readIORef treeModeRef
                    formula <- readIORef formulaRef

                    writeIORef joinedRef True
                    splitBut `gtkSet` [ buttonLabel := "split" ]
                    let t = joinTrees treeMode trees
                    writeIORef treeModeRef "tree"
                    writeIORef treesRef [t]
                    modifyIORef counterRef $ \counter -> upd counter 't' 1
                    writeIORef currRef 0
                    writeIORef solPositionsRef [0 | formula && isSol sig t]
                    setTreesFrame []
                    setProof True False "JOIN" [] "The trees have been joined."
        
        -- | Called by menu items /coinduction/ and /induction/ from menu
        -- /transform selection/.
        startInd :: Bool -> Action
        startInd ind = do
          trees <- readIORef treesRef
          if null trees then labBlue' start
          else do
               str <- ent `gtkGet` entryText
               let pars = words str
               case pars of
                    ["ext",limit] | just k
                      -> do
                         let n = get k
                         if ind then applyInduction n else applyCoinduction n
                         where k = parse pnat limit
                    _ -> if ind then applyInduction 0 else applyCoinduction 0
        
        stateEquiv :: Action
        stateEquiv = do
          sig <- getSignature
          let f (i,j) = mkTup [(sig&states)!!i,(sig&states)!!j]
          enterTree' False $ mkList $ map f $ bisim sig 
        
        -- | Called by 'deriveBut' if it shows /stop run/. The 'deriveBut' is
        -- set to /stop run/ when 'runChecker' is called. Exported by public
        -- 'Epaint.Solver' method 'Epaint.stopRun'.
        stopRun' :: Action
        stopRun' = do
            checking <- readIORef checkingRef
            checkers <- readIORef checkersRef
            when checking $ do
                mapM_ stopRun0 checkers
                backBut `gtkSet` [ buttonLabel := "<---" ]
                replaceCommandButton backButSignalRef backBut backProof
                forwBut `gtkSet` [ buttonLabel := "--->" ]
                replaceCommandButton forwButSignalRef forwBut forwProof'
                runOpts deriveBut deriveButSignalRef
                setButtons paint backOpts forwOpts runOpts
            where backOpts btn cmd = do
                    btn `gtkSet` [ buttonLabel := "<---" ]
                    replaceCommandButton cmd btn $ actInPaint backProof
                  forwOpts btn cmd = do
                    btn `gtkSet` [ buttonLabel := "--->" ]
                    replaceCommandButton cmd btn $ actInPaint forwProof'
                  runOpts btn cmd = do
                    btn `gtkSet` [ buttonLabel := "run proof" ]
                    setBackground btn redback
                    replaceCommandButton cmd btn $ runChecker True
                  actInPaint act = do act; showTreePicts
        
        -- | Used by 'checkForward'. Called by all /stretch/ menu items from
        -- /transform selection/ menu.
        stretch :: Bool -> Action
        stretch prem = do
            trees <- readIORef treesRef
            if null trees then labBlue' start
            else do
                curr <- readIORef currRef
                treeposs <- readIORef treepossRef
                let t = trees!!curr
                    p = emptyOrLast treeposs
                    u = getSubterm t p
                    (f,pt,str) =
                            if prem then (stretchPrem,StretchPremise,"PREMISE")
                            else (stretchConc,StretchConclusion,"CONCLUSION")
                case preStretch prem (const True) u of
                    Just (_,varps) -> do
                        varCounter <- readIORef varCounterRef
                        let (v,n) = f (varCounter "z") varps u
                        curr <- readIORef currRef
                        modifyIORef treesRef
                            $ \trees -> updList trees curr $ replace t p v
                        setZcounter n
                        setProofTerm pt
                        setProof True False ("STRETCHING THE "++str)
                            [p] stretched
                        clearTreeposs; drawCurr'
                    _ -> notStretchable $ "The "++str
        
        -- | Used by 'checkForward'. Called by menu item /subsume/ from menu
        -- /transform selection/.
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
                        if isImpl u then do
                            curr <- readIORef currRef
                            modifyIORef treesRef $ \trees ->
                                updList trees curr $ replace t r mkTrue
                            finish ps "premise"
                        else if isConjunct u then do
                            let u' = F "&" $ context (last q) $ subterms u
                            curr <- readIORef currRef
                            modifyIORef treesRef $ \trees ->
                                updList trees curr $ replace1 t r u'
                            finish ps "factor"
                        else if isDisjunct u then do
                            let u' = F "|" $ context (last p) $ subterms u
                            curr <- readIORef currRef
                            modifyIORef treesRef $ \trees ->
                                updList trees curr $ replace t r u'
                            finish ps "summand"
                        else labGreen' msg
                    else labGreen' msg
                else labRed' "The selected trees are not subsumable."
            where msg = "The selected trees are subsumable."
                  finish ps str = do
                            setProofTerm SubsumeSubtrees
                            setProof True False "SUBSUMPTION" ps $ subsumed str
                            clearTreeposs; drawCurr'
        
        -- | Sitch state varibale 'fastRef' and alternate 'fastBut' label
        -- between "fast" and "slow". Called by 'fastBut'.
        switchFast :: Action
        switchFast = do
            modifyIORef fastRef not
            fast <- readIORef fastRef
            fastBut `gtkSet` [ buttonLabel := if fast then "indented text"
                                                   else "continuous text" ]
        
        -- | Alternate between safe and unsafe equation removal. Called by menu
        -- item /safe\/unsafe equation removal/ from menu /signature/.
        switchSafe :: Action
        switchSafe = do
            modifyIORef safeRef not
            safe <- readIORef safeRef
            safeBut <- readIORef safeButRef
            setProofTerm SafeEqs
            setProof True False "EQS" [] $ equationRemoval $ not safe
            safeBut `gtkSet` [ menuItemLabel := eqsButMsg safe]

        transformGraph mode = do
          trees <- readIORef treesRef
          if null trees then labBlue' start
          else do
               sig <- getSignature
               trees <- readIORef treesRef
               curr <- readIORef currRef
               varCounter <- readIORef varCounterRef
               treeposs <- readIORef treepossRef
               let t = trees!!curr
                   vcz = varCounter "z"
                   relToEqs1 = relToEqs vcz . deAssoc1
                   relToEqs3 = relLToEqs vcz . deAssoc3
                   p:ps = emptyOrAll treeposs
                   u = getSubterm1 t p
                   (q,f,r) = if null ps then ([],id,p)
                                        else (p,drop $ length p,head ps)
                   (eqs,zn) = graphToEqs vcz (getSubterm1 t q) $ f r
                   is = [i | [i,1] <- map f ps]
                   x = label t r
                   act zn p u = do
                                   writeIORef treesRef
                                     $ updList trees curr $ replace1 t p u
                                   when (mode == 3) $ setZcounter zn
                                   setProofTerm $ Transform mode
                                   setProof False False "TRANSFORMING THE GRAPH"
                                                        [p] $ transformed
                                   clearTreeposs; drawCurr'
               case mode of 0 -> act 0 p $ collapse True u
                            1 -> act 0 p $ collapse False u
                            2 -> case parseColl parseConsts2 u of
                                 Just rel -- from pairs to a graph
                                   -> do
                                      let (eqs,zn) = relToEqs1 rel
                                      act zn p $ eqsToGraphx x eqs
                                 _ -> case parseColl parseConsts3 u of
                                      Just rel -- from triples to a graph
                                        -> do
                                           let (eqs,zn) = relToEqs3 rel
                                           act zn p $ eqsToGraphx x eqs
                                      _ -> case parseEqs u of
                                           Just eqs -- from equations to a graph
                                             -> act vcz p $ eqsToGraph is eqs
                                           _ -> -- from a graph to a graph
                                             act vcz q $ eqsToGraphx x eqs
                            _ -> case parseColl parseConsts2 u of
                                 Just rel -- from pairs to equations
                                   -> do
                                      let (eqs,zn) = relToEqs1 rel
                                      act zn p $ eqsTerm eqs
                                 _ -> case parseColl parseConsts3 u of
                                      Just rel -- from triples to equations
                                        -> do
                                           let (eqs,zn) = relToEqs3 rel
                                           act zn p $ eqsTerm eqs
                                      _ -> -- from a graph to equations
                                           act vcz p $ eqsTerm eqs

        -- | Used by 'buildUnifier' and 'unifyOther'.
        unifyAct :: TermS -> TermS -> TermS -> TermS -> [Int] -> [Int] -> Action
        unifyAct u u' t t' p q = do
            writeIORef restoreRef True
            sig <- getSignature
            case unify u u' t t' p q V sig [] of
                Def (f,True) -> do
                    let xs = frees sig u ++ frees sig u'
                        dom = domSub xs f
                    if null dom then labGreen' $ unifiedT ++ emptySubst
                    else
                        if any hasPos $ map f dom then labRed' posInSubst
                        else do
                            setSubst' (f,dom)
                            labGreen' $ unifiedT ++ "See substitution > show."
                Def (_,False) -> labRed' partialUnifier
                BadOrder -> labRed' noUnifier
                Circle p q -> labRed' $ circle p q
                NoPos p -> do
                    setTreeposs $ Replace [p]
                    drawCurr'
                    labRed' dangling
                NoUni -> labRed' noUnifier
                OcFailed x -> labRed' $ ocFailed x
        
        -- | Called by menu item /unify with tree of SolverN/ from menu
        -- /transform selection/.
        unifyOther :: Action
        unifyOther = do
            solve <- readIORef solveRef
            tree <- getTree solve
            case tree of
                Just t -> do
                    treeposs <- readIORef treepossRef
                    trees <- readIORef treesRef
                    curr <- readIORef currRef
                    let p = emptyOrLast treeposs
                        t' = trees!!curr
                        u = getSubterm t' p
                    unifyAct t u t t' [] p
                _ -> do
                    other <- getSolver solve
                    labBlue' $ startOther other
        
        -- | Used by 'checkForward'. Called by menu item /unify/ from menu
        -- /transform selection/.
        unifySubtrees :: Action
        unifySubtrees = do
            treeposs <- readIORef treepossRef
            if length treeposs /= 2 || any null treeposs
            then labMag "Select two proper subtrees!"
            else do
                trees <- readIORef treesRef
                curr <- readIORef currRef
                let t = trees!!curr
                    ps@[p,q] = treeposs
                    u = getSubterm1 t p
                    u' = getSubterm1 t q
                    r = init p
                    v = getSubterm1 t r
                    b = polarity True t r
                if r == init q then do
                    sig <- getSignature
                    if isConjunct v && b then do
                        let xs = if null r then []
                                 else anys $ getSubterm1 t $ init r
                        case unifyS sig xs u u' of
                            Just f -> do
                                let us = map (>>>f) $ init $ subterms v
                                    t' = replace1 t r $ mkConjunct us
                                curr <- readIORef currRef
                                modifyIORef treesRef $ \trees ->
                                    updList trees curr t'
                                setProofTerm UnifySubtrees
                                setProof True False "FACTOR UNIFICATION" ps
                                       $ unified "factor"
                                clearTreeposs; drawCurr'
                            _ -> labRed' noUnifier
                    else
                        if isDisjunct v && not b then do
                            let xs = if null r then []
                                            else alls $ getSubterm1 t $ init r
                            case unifyS sig xs u u' of
                                Just f -> do
                                    let us = map (>>>f) $ init $ subterms v
                                        t' = replace1 t r $ mkDisjunct us
                                    curr <- readIORef currRef
                                    modifyIORef treesRef $ \trees ->
                                        updList trees curr t'
                                    setProofTerm UnifySubtrees
                                    setProof True False "SUMMAND UNIFICATION" ps
                                            $ unified "summand"
                                    clearTreeposs; drawCurr'
                                _ -> labRed' noUnifier
                        else labRed' $ noApp "Subtree unification"
                else labMag "Select subtrees with the same predecessor!"
        
    return Solver
        { addSpec         = addSpec'
        , backWin         = backWin'
        , bigWin          = bigWin'
        , checkInSolver   = checkInSolver'
        , drawCurr        = drawCurr'
        , forwProof       = forwProof'
        , showPicts       = showPicts'
        , stopRun         = stopRun'
        , buildSolve      = buildSolve'
        , enterPT         = enterPT'
        , enterText       = enterText'
        , enterFormulas   = enterFormulas'
        , enterTree       = enterTree'
        , getEntry        = getEntry'
        , getSolver       = getSolver'
        , getSpread       = getSpread'
        , getText         = getTextHere
        , getFont         = getFont'
        , getPicNo        = getPicNo'
        , getSignatureR   = getSignature
        , getTree         = getTree'
        , isSolPos        = isSolPos'
        , labBlue         = labBlue'
        , labRed          = labRed'
        , labGreen        = labGreen'
        , narrow          = narrow'
        , saveGraphDP     = saveGraphDP'
        , setCurrInSolve  = setCurrInSolve'
        , setForw         = setForw'
        , setQuit         = setQuit'
        , setInterpreter  = setInterpreter'
        , setNewTrees     = setNewTrees'
        , setSubst        = setSubst'
        , simplify        = simplify'
        , iconify         = iconify'
        }


-- * __Enumerator__ messages

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
startEnum object = "Enter " ++ str ++ " into the text field" ++
                   (case object of "palindrome" -> "!"; _ -> more)
      where str = case object of
                  "palindrome" -> "a sequence of strings"
                  "alignment" -> "two sequences of strings separated by blanks"
                  "dissection"
                    -> "the breadth > 0 and the height > 0 of a rectangle"
                  _ -> "the length of a list"
            more = "\nand a constraint into the entry field (see the manual)!"

-- * the __enumerator__ template

data Enumerator = Enumerator
    { buildEnum :: String -> (String -> String -> Bool) -> Action }

enumerator :: IORef Solver -> Template Enumerator
enumerator solveRef = do
    objectRef <- newIORef ""
    complRef <- newIORef $ const2 False

    return $
        let buildEnum' obj f = do
                writeIORef objectRef obj
                writeIORef complRef f
                solve <- readIORef solveRef
                labBlue solve $ startEnum obj
                setForw solve $ \btn cmd -> do
                    btn `gtkSet` [ buttonLabel := "go" ]
                    setBackground btn redback
                    replaceCommandButton cmd btn $ getInput obj
                solve&setQuit $ \quit signal -> do
                  quit `gtkSet` [ buttonLabel := "quit " ++ obj]
                  replaceCommandButton signal quit finish
                  

            finish = do
                solve <- readIORef solveRef
                labBlue solve start
                setForw solve $ \btn cmd -> do
                    btn `gtkSet` [ buttonLabel := "--->" ]
                    setBackground btn greenback
                    solve <- readIORef solveRef
                    replaceCommandButton cmd btn (forwProof solve)
                solve&setQuit $ \quit signal -> do
                  quit `gtkSet` [ buttonLabel := "quit" ]
                  replaceCommandButton signal quit mainQuit
                solve&setInterpreter $ "tree"
                    
            getInput "alignment" = do
                solve <- readIORef solveRef
                str <- getText solve
                constr <- getEntry solve
                let global = notnull constr && head constr == 'g'
                    (xs,ys) = break (== '\n') str
                if null ys then labRed solve
                        "Enter TWO sequences of strings into the entry field!"
                else do
                    compl <- readIORef complRef
                    showResult constr $ map (alignToTerm . compress)
                        $ mkAlign global (words xs) (words ys) compl
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
                                Just (c,ns,c')
                                  -> showResult (showEnum t)
                                    $ mkDissects c c' ns b h
                                _ -> labRed solve badConstraint
                            _ -> labRed solve badConstraint
                    _ -> labBlue solve
                            "Enter two numbers > 0 into the text field!"
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
                                    _ -> labRed solve badConstraint
                            _ -> labRed solve badConstraint
                    _ -> labBlue solve "Enter a number > 1 into the text field!"

            showResult constr terms = do
                solve <- readIORef solveRef
                object <- readIORef objectRef
                if null terms
                then labGreen solve $ none object constr
                else do let n = length terms
                            typ = if n == 1 then "tree" else "term"
                        setNewTrees solve terms typ
                        labGreen solve $ howMany n object constr
        in Enumerator
            { buildEnum = buildEnum'
            }

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

