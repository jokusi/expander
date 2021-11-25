module SpecificationTest (tests) where

import Test.Framework
import Test.Framework.Providers.HUnit
import Test.HUnit

import qualified Base.System as Base
import Base.Gui hiding
  (Cmd,Action,Request,readIORef,writeIORef,modifyIORef,newIORef,IORef,done)
import qualified Base.Gui as Base
import Eterm
import Esolve
import Ecom

import Control.Monad (void, msum, when, unless, filterM)
import Control.Monad.State (StateT)
import qualified Control.Monad.State as State
import Data.Maybe (isJust, fromJust, isNothing, fromMaybe)
import Data.List (isSuffixOf, isInfixOf, isPrefixOf, sort)
import Prelude hiding ((++),concat)
import System.Directory
import System.FilePath


tests =  test_all_specifications

mkSpecTest name = testCase name $ loadSpec name

isSpecification :: FilePath -> Bool
isSpecification file = all (not . ($ file))
    [ hasExtension
    , isInfixOf "proof"
    , isInfixOf "code"
    , isInfixOf "term"
    , isInfixOf "RR"
    , isSuffixOf "T"
    , isSuffixOf "P"
    , isSuffixOf "C"
    , isSuffixOf "R"
    , isSuffixOf "G"
    , isSuffixOf "W"
    , isSuffixOf "Pic"
    , isPrefixOf "["
    ]

-- generated with "script/fails.hs"
isKnownFailure :: FilePath -> Bool
isKnownFailure file = all (/= file) ["mutexAlt", "rhpytree","raintabB","rot","rainpie","rainpoly","quad","yinyang","rainrect2","polysG4","graph10","rainpyt","crossing1","nemos","listsols","parity","polysG6","recttabAS","rainpoly3","transIn","polysG1","rainpoly2","rainpytl","EXwait","partn","rotnew","flashpoly","rainsnow3","factor3-4-6-2","lr2run","joins","evensmorse","kripke4","mapiter2","fib01","topempty","STACK2IMPL","btree","tgraph","flashplait","pulse","hanoiAlt","mapziptup","lr1run","fruit","gettup","poppush","iterloop","rects","light","oddszip","tree","graph7","rects0","graph6","infbintree","auto1", "partflattenN","solver","recttabA","PAFLall","part1","flash","recttabB","rainpie3","natstream","rainplait2","toppush","testnew5","polar","safe","AFcrit","robotGraph","reqs","knight","recttabBS","rotplait","shuttle","graph5","rotweetysh","lift","flashsnow","trans2sols","morsef","mergePalt","shuttle3","rotweety","flashshine","waveG","gear","wave","natloop","dissW","rainpyt3","rects4","STACKconjs","KNIGHTsols","kinotest","zipmorse","rainrect","puzzle","tweetynet","LRaltRun","queens5solM","snake","rotgrow","showtest1","mapiter1","notfairblink2","robot80-120","distestG","polysG10","rectangle","polysG3","rainpoly2-1","SOL1tree","paths","roturt","rotweety3","invinv","cbau2-0","quad2","states","pytree2","maploop0","graph8","rainpie2","rainplait","matrix","polysG7","set","SOLSPICT2","rotwave","polysG9","rainrectld","rainsnow2","transDesc","iterate","product","lr2Act","flash2","copyrem","shuttle2","SolverCG","relalgdb","testgrow","hanoiLab","cobintree","five2","part2","five","echo3","notfairblink","polytab","maploop","mats","lightsnow","graph3","rects2","decagon","palindrome","pushcomp","solspict","rainpoly5","logConj1","rainpie5","liftAlt","rframe","factor6-6-6-2","iter1iter2","logConj0","sum","rainsnow","rotpoly","updeq","rects3","plaits","pulse2","natloopN","primes6","shuttles","cpic1","graph4","morseinv2","pairs","rainpytd","needcoind","queens5sol","coregs","rainsnow1","distest2-2","rainplait3","showtest2","shuttles2","monad","polysG8","drei","band","rotweety2","graph9","pytree3","rainpoly3-1","part3","flash0","tattooG","mutexquad","snakes","popempty","shine","rotmat","mapfact","cpic2","kinotest2","fern2-12-1-1","hanoi","coin","mutexco","rainpyt2","rainpyt2l","LRalt","polysG2","quad3","PUSHCOMP2","tattoo4","quad1","pytree1","pascal4","fahrplan","Notsorted","rainplait4","sortperm","logConj2","eqtest","SOLSPICT1","natstreamSol","hanoiActs","rainpyt2d","sendmore","morseinv","primes5","colorhull"]

-- IORef emulation
type Cmd a = StateT SolverState IO a
type Action = Cmd ()
type Request a = Cmd a

data IORef a = IORef
  { getter :: SolverState -> a
  , setter :: a -> SolverState -> SolverState
  }

readIORef :: IORef a -> Request a
readIORef ref = do
  st <- State.get
  return $ getter ref st

writeIORef :: IORef a -> a -> Action
writeIORef ref a = do
  st <- State.get
  State.put $ setter ref a st

modifyIORef :: IORef a -> (a -> a) -> Action
modifyIORef ref f = do
  st <- State.get
  let a = getter ref st
  State.put $ setter ref a st


-- State
-- In: "    (.+)Ref <- newIORef (.+)"
-- Out: "  , $1Ref_ :: $2"
data SolverState = SolverState
  { ctreeRef_ :: (Maybe ())
  , nodeRef_ :: (Maybe ())
  , penposRef_ :: (Maybe ())
  , subtreeRef_ :: (Maybe ())
  , isSubtreeRef_ :: (Maybe ())
  , suptreeRef_ :: (Maybe ())
  , osciRef_ :: (Maybe ())

  , formulaRef_ :: Bool
  , joinedRef_ :: Bool
  , safeSimplRef_ :: Bool
  , firstMoveRef_ :: Bool
  , showStateRef_ :: Bool
  , firstClickRef_ :: Bool

  , fastRef_ :: Bool
  , checkingRef_ :: Bool
  , checkingPRef_ :: (Bool,Bool)
  , refutingRef_ :: Bool
  , simplifyingRef_ :: Bool
  , collSimplsRef_ :: Bool
  , newTreesRef_ :: Bool
  , restoreRef_ :: Bool
  , trsOnCanvasRef_ :: Bool

  , axiomsRef_ :: [TermS]
  , theoremsRef_ :: [TermS]
  , conjectsRef_ :: [TermS]
  , newAxiomsRef_ :: [()]
  , newTheoremsRef_ :: [()]
  , oldTreepossRef_ :: [()]
  , proofRef_ :: [()]
  , proofTermRef_ :: [()]
  , ruleStringRef_ :: [()]
  , simplRulesRef_ :: [(TermS, [TermS], TermS)]
  , solPositionsRef_ :: [Int]
  , specfilesRef_ :: [String]
  , termsRef_ :: [TermS]
  , transRulesRef_ :: [(TermS, [TermS], TermS)]
  , treepossRef_ :: [()]
  , treesRef_ :: [()]
  , iniStatesRef_ :: [TermS]
  
  , kripkeRef_ :: ([TermS],[TermS],[TermS],[[Int]],[[[Int]]],[[Int]],[[[Int]]])

  , canvSizeRef_ :: (Int,Int)
  , cornerRef_ :: (Int,Int)
  , currRef_ :: Int
  -- , curr1Ref_ :: Int
  , matchingRef_ :: Int
  , noProcsRef_ :: Int
  , proofPtrRef_ :: Int
  , proofTPtrRef_ :: Int
  , picNoRef_ :: Int
  , simplStratRef_ :: Strategy

  , numberedExpsRef_ :: ([()],Bool)
  , constraintsRef_ :: (Bool,[String])

  , drawFunRef_ :: TermS
  , picEvalRef_ :: String
  , picDirRef_ :: String

  , signatureMapRef_ :: (() -> (),[()])
  , newPredsRef_ :: ([()],[()])
  , partRef_ :: (() -> (),[()])
  , substitutionRef_ :: (() -> Term (), [()])
  , treeModeRef_ :: String
  , symbolsRef_ :: ([String], [String], [String], [String], [String], [(String,[String])])
  , randRef_ :: Int
  , sizeStateRef_ :: Sizes
  , spreadRef_ :: (Int,Int)
  , timesRef_ :: (Int,Int)
  , speedRef_ :: Int
  , counterRef_ :: (Int -> Int)
  , varCounterRef_ :: VarCounter
  , permsRef_ :: (Int -> [Int])

  -- additional refs to emulate gui
  , _teditTextRef_ :: String
  }

-- Attributes
-- Out: "$1Ref = IORef $1Ref_ (\a st -> st{ $1Ref_ = a})"
ctreeRef = IORef ctreeRef_ (\a st -> st{ ctreeRef_ = a})
nodeRef = IORef nodeRef_ (\a st -> st{ nodeRef_ = a})
penposRef = IORef penposRef_ (\a st -> st{ penposRef_ = a})
subtreeRef = IORef subtreeRef_ (\a st -> st{ subtreeRef_ = a})
isSubtreeRef = IORef isSubtreeRef_ (\a st -> st{ isSubtreeRef_ = a})
suptreeRef = IORef suptreeRef_ (\a st -> st{ suptreeRef_ = a})
osciRef = IORef osciRef_ (\a st -> st{ osciRef_ = a})

formulaRef = IORef formulaRef_ (\a st -> st{ formulaRef_ = a})
joinedRef = IORef joinedRef_ (\a st -> st{ joinedRef_ = a})
safeSimplRef = IORef safeSimplRef_ (\a st -> st{ safeSimplRef_ = a})
firstMoveRef = IORef firstMoveRef_ (\a st -> st{ firstMoveRef_ = a})
showStateRef = IORef showStateRef_ (\a st -> st{ showStateRef_ = a})
firstClickRef = IORef firstClickRef_ (\a st -> st{ firstClickRef_ = a})

fastRef = IORef fastRef_ (\a st -> st{ fastRef_ = a})
checkingRef = IORef checkingRef_ (\a st -> st{ checkingRef_ = a})
checkingPRef = IORef checkingPRef_ (\a st -> st{ checkingPRef_ = a})
refutingRef = IORef refutingRef_ (\a st -> st{ refutingRef_ = a})
simplifyingRef = IORef simplifyingRef_ (\a st -> st{ simplifyingRef_ = a})
collSimplsRef = IORef collSimplsRef_ (\a st -> st{ collSimplsRef_ = a})
newTreesRef = IORef newTreesRef_ (\a st -> st{ newTreesRef_ = a})
restoreRef = IORef restoreRef_ (\a st -> st{ restoreRef_ = a})
trsOnCanvasRef = IORef trsOnCanvasRef_ (\a st -> st{ trsOnCanvasRef_ = a})

axiomsRef = IORef axiomsRef_ (\a st -> st{ axiomsRef_ = a})
theoremsRef = IORef theoremsRef_ (\a st -> st{ theoremsRef_ = a})
conjectsRef = IORef conjectsRef_ (\a st -> st{ conjectsRef_ = a})
newAxiomsRef = IORef newAxiomsRef_ (\a st -> st{ newAxiomsRef_ = a})
newTheoremsRef = IORef newTheoremsRef_ (\a st -> st{ newTheoremsRef_ = a})
oldTreepossRef = IORef oldTreepossRef_ (\a st -> st{ oldTreepossRef_ = a})
proofRef = IORef proofRef_ (\a st -> st{ proofRef_ = a})
proofTermRef = IORef proofTermRef_ (\a st -> st{ proofTermRef_ = a})
ruleStringRef = IORef ruleStringRef_ (\a st -> st{ ruleStringRef_ = a})
simplRulesRef = IORef simplRulesRef_ (\a st -> st{ simplRulesRef_ = a})
solPositionsRef = IORef solPositionsRef_ (\a st -> st{ solPositionsRef_ = a})
specfilesRef = IORef specfilesRef_ (\a st -> st{ specfilesRef_ = a})
termsRef = IORef termsRef_ (\a st -> st{ termsRef_ = a})
transRulesRef = IORef transRulesRef_ (\a st -> st{ transRulesRef_ = a})
treepossRef = IORef treepossRef_ (\a st -> st{ treepossRef_ = a})
treesRef = IORef treesRef_ (\a st -> st{ treesRef_ = a})
iniStatesRef = IORef iniStatesRef_ (\a st -> st{ iniStatesRef_ = a})

kripkeRef = IORef kripkeRef_ (\a st -> st{ kripkeRef_ = a})

canvSizeRef = IORef canvSizeRef_ (\a st -> st{ canvSizeRef_ = a})
cornerRef = IORef cornerRef_ (\a st -> st{ cornerRef_ = a})
currRef = IORef currRef_ (\a st -> st{ currRef_ = a})
-- curr1Ref = IORef -- curr1Ref_ (\a st -> st{ -- curr1Ref_ = a})
matchingRef = IORef matchingRef_ (\a st -> st{ matchingRef_ = a})
noProcsRef = IORef noProcsRef_ (\a st -> st{ noProcsRef_ = a})
proofPtrRef = IORef proofPtrRef_ (\a st -> st{ proofPtrRef_ = a})
proofTPtrRef = IORef proofTPtrRef_ (\a st -> st{ proofTPtrRef_ = a})
picNoRef = IORef picNoRef_ (\a st -> st{ picNoRef_ = a})
simplStratRef = IORef simplStratRef_ (\a st -> st{ simplStratRef_ = a})

numberedExpsRef = IORef numberedExpsRef_ (\a st -> st{ numberedExpsRef_ = a})
constraintsRef = IORef constraintsRef_ (\a st -> st{ constraintsRef_ = a})

drawFunRef = IORef drawFunRef_ (\a st -> st{ drawFunRef_ = a})
picEvalRef = IORef picEvalRef_ (\a st -> st{ picEvalRef_ = a})
picDirRef = IORef picDirRef_ (\a st -> st{ picDirRef_ = a})

signatureMapRef = IORef signatureMapRef_ (\a st -> st{ signatureMapRef_ = a})
newPredsRef = IORef newPredsRef_ (\a st -> st{ newPredsRef_ = a})
partRef = IORef partRef_ (\a st -> st{ partRef_ = a})
substitutionRef = IORef substitutionRef_ (\a st -> st{ substitutionRef_ = a})
treeModeRef = IORef treeModeRef_ (\a st -> st{ treeModeRef_ = a})
symbolsRef = IORef symbolsRef_ (\a st -> st{ symbolsRef_ = a})
randRef = IORef randRef_ (\a st -> st{ randRef_ = a})
sizeStateRef = IORef sizeStateRef_ (\a st -> st{ sizeStateRef_ = a})
spreadRef = IORef spreadRef_ (\a st -> st{ spreadRef_ = a})
timesRef = IORef timesRef_ (\a st -> st{ timesRef_ = a})
speedRef = IORef speedRef_ (\a st -> st{ speedRef_ = a})
counterRef = IORef counterRef_ (\a st -> st{ counterRef_ = a})
varCounterRef = IORef varCounterRef_ (\a st -> st{ varCounterRef_ = a})
permsRef = IORef permsRef_ (\a st -> st{ permsRef_ = a})

_teditTextRef = IORef _teditTextRef_ (\a st -> st{ _teditTextRef_ = a})

-- Out: "  $2"
initSolverState :: SolverState
initSolverState = SolverState
  Nothing
  Nothing
  Nothing
  Nothing
  Nothing
  Nothing
  Nothing

  True
  True
  True
  True
  True
  True

  False
  False
  (False,False)
  False
  False
  False
  False
  False
  False

  []
  []
  []
  []
  []
  []
  []
  []
  []
  []
  []
  []
  []
  []
  []
  []
  []

  ([],[],[],[],[],[],[])

  (0,0)
  (30,20)
  0
  -- 0 -- Gtk does not need this
  0
  2
  0
  0
  0
  PA

  ([],True)
  (True,[])

  (leaf "id")
  "tree"
  "picDir"

  (id,[])
  nil2
  (id,[])
  (V,[])
  "tree"
  iniSymbols
  seed
  sizes0
  (10,30)
  (0,300)
  500
  (const 0)
  (const 0)
  (\n -> [0..n-1])

  ""


-- modified functions
lookupLibs :: FilePath -> Cmd String
lookupLibs = State.liftIO . Base.lookupLibs

-- builtinLibDir :: Cmd FilePath
-- builtinLibDir = State.liftIO . Base.builtinLibDir

done :: Action
done = return ()

delay :: a -> a
delay = id

enterFormulas :: [TermS] -> Action
enterFormulas _ = return ()

enterText :: String -> Action
enterText _ = return ()

getTextHere :: Request String
getTextHere = readIORef _teditTextRef

incorrect :: Parse TermS -> String -> String -> Action
incorrect _ _ error = labRed error

labGreen :: String -> Action
labGreen _ = return ()

labRed :: String -> Action
labRed = State.liftIO . assertFailure . ("Expander error message: "++)

-- extracted solver functions with state
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

addSpecWithBase :: FilePath -> Action
addSpecWithBase spec = do
  addSpec True "base"
  unless (spec == "base") $ addSpec True spec

addTheorems :: TermS -> FilePath -> Action
addTheorems t file = do
    modifyIORef theoremsRef $ \theorems ->
        theorems `join` if isConjunct t then subterms t else [t]
    labGreen $ newCls "theorems" file

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


parseConjects :: Sig -> FilePath -> String -> Action
parseConjects sig file conjs =
    case parseE (implication sig) conjs of
        Correct t -> do
            let ts = if isConjunct t then subterms t else [t]
            modifyIORef conjectsRef $ \conjects -> conjects `join` ts
            labGreen $ newCls "conjectures" file
        p -> incorrect p conjs $ illformed "formula"

parseTerms :: Sig -> FilePath -> String -> Action
parseTerms sig file ts =  case parseE (term sig) ts of
    Correct t -> do
        let ts = if isSum t then subterms t else [t]
        modifyIORef termsRef $ \terms -> ts `join` terms
        labGreen $ newCls "terms" file
    p -> incorrect p ts $ illformed "term"



-- test functions
loadSpec :: String -> IO ()
loadSpec spec = State.evalStateT (addSpecWithBase spec) initSolverState

test_all_specifications = buildTest $ do
    dir <- Base.builtinLibDir
    list <- listDirectory dir
    listOfFiles <- filterM (doesFileExist . (dir </>)) list
    let listOfSpecs
            = Data.List.sort
            $ filter isKnownFailure
            $ filter isSpecification listOfFiles
        listOfTests = map mkSpecTest listOfSpecs
        tests = testGroup "specifications" listOfTests
    return tests

