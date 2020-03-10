module SpecificationTest (tests) where

import Test.Framework
import Test.Framework.Providers.HUnit
import Test.HUnit

import Base.System (lookupLibs,builtinLibDir)
import Base.Gui hiding (Cmd,Action,Request,set,get)
import qualified Base.Gui as Base
import qualified Graphics.UI.Gtk as Gtk (get,set)
import Eterm
import Esolve
import Ecom

import Control.Monad (void, msum, when, unless, filterM)
import Data.IORef
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

-- State
-- In: "     (.+)Ref <- newIORef (.+)"
-- Out: "  , $1Ref_ :: IORef ()"
data SolverState = SolverState
  { ctreeRef_ :: IORef (Maybe ())
  , nodeRef_ :: IORef (Maybe ())
  , penposRef_ :: IORef (Maybe ())
  , subtreeRef_ :: IORef (Maybe ())
  , isSubtreeRef_ :: IORef (Maybe ())
  , suptreeRef_ :: IORef (Maybe ())
  -- , osciRef_ :: IORef (Maybe ())

  , formulaRef_ :: IORef Bool
  , joinedRef_ :: IORef Bool
  , safeRef_ :: IORef Bool
  , firstMoveRef_ :: IORef Bool
  , showStateRef_ :: IORef Bool
  , firstClickRef_ :: IORef Bool

  , fastRef_ :: IORef Bool
  , checkingRef_ :: IORef Bool
  , checkingPRef_ :: IORef (Bool,Bool)
  , simplifyingRef_ :: IORef Bool
  , refutingRef_ :: IORef Bool
  , collSimplsRef_ :: IORef Bool
  , newTreesRef_ :: IORef Bool
  , restoreRef_ :: IORef Bool

  , canvSizeRef_ :: IORef (Int,Int)
  , cornerRef_ :: IORef (Int,Int)
  , currRef_ :: IORef Int
  -- , curr1Ref_ :: IORef Int
  , matchingRef_ :: IORef Int
  , noProcsRef_ :: IORef Int
  , proofPtrRef_ :: IORef Int
  , proofTPtrRef_ :: IORef Int
  , picNoRef_ :: IORef Int
  , stateIndexRef_ :: IORef Int
  , simplStratRef_ :: IORef Strategy

  , axiomsRef_ :: IORef [TermS]
  , conjectsRef_ :: IORef [TermS]
  , indClausesRef_ :: IORef [()]
  , matchTermRef_ :: IORef [()]
  , oldTreepossRef_ :: IORef [()]
  , proofRef_ :: IORef [()]
  , proofTermRef_ :: IORef [()]
  , refuteTermRef_ :: IORef [()]
  , ruleStringRef_ :: IORef [()]
  , simplRulesRef_ :: IORef [(TermS, [TermS], TermS)]
  , simplTermRef_ :: IORef [()]
  , solPositionsRef_ :: IORef [Int]
  , specfilesRef_ :: IORef [String]
  , stratTermRef_ :: IORef [()]
  , termsRef_ :: IORef [TermS]
  , theoremsRef_ :: IORef [TermS]
  , transRulesRef_ :: IORef [(TermS, [TermS], TermS)]
  , treepossRef_ :: IORef [()]
  , treesRef_ :: IORef [()]

  , numberedExpsRef_ :: IORef ([()],Bool)
  , constraintsRef_ :: IORef (Bool,[String])

  , drawFunRef_ :: IORef String
  , picEvalRef_ :: IORef String
  , picDirRef_ :: IORef String

  , signatureMapRef_ :: IORef (() -> (),[()])
  , newPredsRef_ :: IORef ([()],[()])
  , partRef_ :: IORef (() -> (),[()])
  , substitutionRef_ :: IORef (() -> Term (), [()])
  , treeModeRef_ :: IORef String
  , symbolsRef_ :: IORef ([String], [String], [String], [String], [String], [(String,[String])])
  , randRef_ :: IORef Int
  , sizeStateRef_ :: IORef Sizes
  , spreadRef_ :: IORef (Int,Int)
  , timesRef_ :: IORef (Int,Int)
  , speedRef_ :: IORef Int
  , counterRef_ :: IORef (Int -> Int)
  , varCounterRef_ :: IORef VarCounter
  , permsRef_ :: IORef (Int -> [Int])
  , kripkeRef_ :: IORef ([TermS],[TermS],[TermS],[[Int]],[[[Int]]],[[Int]],[[[Int]]])

  -- additional refs to emulate gui
  , _teditTextRef_ :: IORef String
  }

-- Attributes
-- Out: "$1Ref = newAttr (\st -> readIORef ($1Ref_ st)) (\st -> writeIORef ($1Ref_ st))"
ctreeRef = newAttr (\st -> readIORef (ctreeRef_ st)) (\st -> writeIORef (ctreeRef_ st))
nodeRef = newAttr (\st -> readIORef (nodeRef_ st)) (\st -> writeIORef (nodeRef_ st))
penposRef = newAttr (\st -> readIORef (penposRef_ st)) (\st -> writeIORef (penposRef_ st))
subtreeRef = newAttr (\st -> readIORef (subtreeRef_ st)) (\st -> writeIORef (subtreeRef_ st))
isSubtreeRef = newAttr (\st -> readIORef (isSubtreeRef_ st)) (\st -> writeIORef (isSubtreeRef_ st))
suptreeRef = newAttr (\st -> readIORef (suptreeRef_ st)) (\st -> writeIORef (suptreeRef_ st))
-- osciRef = newAttr (\st -> readIORef (-- osciRef_ st)) (\st -> writeIORef (-- osciRef_ st))

formulaRef = newAttr (\st -> readIORef (formulaRef_ st)) (\st -> writeIORef (formulaRef_ st))
joinedRef = newAttr (\st -> readIORef (joinedRef_ st)) (\st -> writeIORef (joinedRef_ st))
safeRef = newAttr (\st -> readIORef (safeRef_ st)) (\st -> writeIORef (safeRef_ st))
firstMoveRef = newAttr (\st -> readIORef (firstMoveRef_ st)) (\st -> writeIORef (firstMoveRef_ st))
showStateRef = newAttr (\st -> readIORef (showStateRef_ st)) (\st -> writeIORef (showStateRef_ st))
firstClickRef = newAttr (\st -> readIORef (firstClickRef_ st)) (\st -> writeIORef (firstClickRef_ st))

fastRef = newAttr (\st -> readIORef (fastRef_ st)) (\st -> writeIORef (fastRef_ st))
checkingRef = newAttr (\st -> readIORef (checkingRef_ st)) (\st -> writeIORef (checkingRef_ st))
checkingPRef = newAttr (\st -> readIORef (checkingPRef_ st)) (\st -> writeIORef (checkingPRef_ st))
simplifyingRef = newAttr (\st -> readIORef (simplifyingRef_ st)) (\st -> writeIORef (simplifyingRef_ st))
refutingRef = newAttr (\st -> readIORef (refutingRef_ st)) (\st -> writeIORef (refutingRef_ st))
collSimplsRef = newAttr (\st -> readIORef (collSimplsRef_ st)) (\st -> writeIORef (collSimplsRef_ st))
newTreesRef = newAttr (\st -> readIORef (newTreesRef_ st)) (\st -> writeIORef (newTreesRef_ st))
restoreRef = newAttr (\st -> readIORef (restoreRef_ st)) (\st -> writeIORef (restoreRef_ st))

canvSizeRef = newAttr (\st -> readIORef (canvSizeRef_ st)) (\st -> writeIORef (canvSizeRef_ st))
cornerRef = newAttr (\st -> readIORef (cornerRef_ st)) (\st -> writeIORef (cornerRef_ st))
currRef = newAttr (\st -> readIORef (currRef_ st)) (\st -> writeIORef (currRef_ st))
-- curr1Ref = newAttr (\st -> readIORef (-- curr1Ref_ st)) (\st -> writeIORef (-- curr1Ref_ st))
matchingRef = newAttr (\st -> readIORef (matchingRef_ st)) (\st -> writeIORef (matchingRef_ st))
noProcsRef = newAttr (\st -> readIORef (noProcsRef_ st)) (\st -> writeIORef (noProcsRef_ st))
proofPtrRef = newAttr (\st -> readIORef (proofPtrRef_ st)) (\st -> writeIORef (proofPtrRef_ st))
proofTPtrRef = newAttr (\st -> readIORef (proofTPtrRef_ st)) (\st -> writeIORef (proofTPtrRef_ st))
picNoRef = newAttr (\st -> readIORef (picNoRef_ st)) (\st -> writeIORef (picNoRef_ st))
stateIndexRef = newAttr (\st -> readIORef (stateIndexRef_ st)) (\st -> writeIORef (stateIndexRef_ st))
simplStratRef = newAttr (\st -> readIORef (simplStratRef_ st)) (\st -> writeIORef (simplStratRef_ st))

axiomsRef = newAttr (\st -> readIORef (axiomsRef_ st)) (\st -> writeIORef (axiomsRef_ st))
conjectsRef = newAttr (\st -> readIORef (conjectsRef_ st)) (\st -> writeIORef (conjectsRef_ st))
indClausesRef = newAttr (\st -> readIORef (indClausesRef_ st)) (\st -> writeIORef (indClausesRef_ st))
matchTermRef = newAttr (\st -> readIORef (matchTermRef_ st)) (\st -> writeIORef (matchTermRef_ st))
oldTreepossRef = newAttr (\st -> readIORef (oldTreepossRef_ st)) (\st -> writeIORef (oldTreepossRef_ st))
proofRef = newAttr (\st -> readIORef (proofRef_ st)) (\st -> writeIORef (proofRef_ st))
proofTermRef = newAttr (\st -> readIORef (proofTermRef_ st)) (\st -> writeIORef (proofTermRef_ st))
refuteTermRef = newAttr (\st -> readIORef (refuteTermRef_ st)) (\st -> writeIORef (refuteTermRef_ st))
ruleStringRef = newAttr (\st -> readIORef (ruleStringRef_ st)) (\st -> writeIORef (ruleStringRef_ st))
simplRulesRef = newAttr (\st -> readIORef (simplRulesRef_ st)) (\st -> writeIORef (simplRulesRef_ st))
simplTermRef = newAttr (\st -> readIORef (simplTermRef_ st)) (\st -> writeIORef (simplTermRef_ st))
solPositionsRef = newAttr (\st -> readIORef (solPositionsRef_ st)) (\st -> writeIORef (solPositionsRef_ st))
specfilesRef = newAttr (\st -> readIORef (specfilesRef_ st)) (\st -> writeIORef (specfilesRef_ st))
stratTermRef = newAttr (\st -> readIORef (stratTermRef_ st)) (\st -> writeIORef (stratTermRef_ st))
termsRef = newAttr (\st -> readIORef (termsRef_ st)) (\st -> writeIORef (termsRef_ st))
theoremsRef = newAttr (\st -> readIORef (theoremsRef_ st)) (\st -> writeIORef (theoremsRef_ st))
transRulesRef = newAttr (\st -> readIORef (transRulesRef_ st)) (\st -> writeIORef (transRulesRef_ st))
treepossRef = newAttr (\st -> readIORef (treepossRef_ st)) (\st -> writeIORef (treepossRef_ st))
treesRef = newAttr (\st -> readIORef (treesRef_ st)) (\st -> writeIORef (treesRef_ st))

numberedExpsRef = newAttr (\st -> readIORef (numberedExpsRef_ st)) (\st -> writeIORef (numberedExpsRef_ st))
constraintsRef = newAttr (\st -> readIORef (constraintsRef_ st)) (\st -> writeIORef (constraintsRef_ st))

drawFunRef = newAttr (\st -> readIORef (drawFunRef_ st)) (\st -> writeIORef (drawFunRef_ st))
picEvalRef = newAttr (\st -> readIORef (picEvalRef_ st)) (\st -> writeIORef (picEvalRef_ st))
picDirRef = newAttr (\st -> readIORef (picDirRef_ st)) (\st -> writeIORef (picDirRef_ st))

signatureMapRef = newAttr (\st -> readIORef (signatureMapRef_ st)) (\st -> writeIORef (signatureMapRef_ st))
newPredsRef = newAttr (\st -> readIORef (newPredsRef_ st)) (\st -> writeIORef (newPredsRef_ st))
partRef = newAttr (\st -> readIORef (partRef_ st)) (\st -> writeIORef (partRef_ st))
substitutionRef = newAttr (\st -> readIORef (substitutionRef_ st)) (\st -> writeIORef (substitutionRef_ st))
treeModeRef = newAttr (\st -> readIORef (treeModeRef_ st)) (\st -> writeIORef (treeModeRef_ st))
symbolsRef = newAttr (\st -> readIORef (symbolsRef_ st)) (\st -> writeIORef (symbolsRef_ st))
randRef = newAttr (\st -> readIORef (randRef_ st)) (\st -> writeIORef (randRef_ st))
sizeStateRef = newAttr (\st -> readIORef (sizeStateRef_ st)) (\st -> writeIORef (sizeStateRef_ st))
spreadRef = newAttr (\st -> readIORef (spreadRef_ st)) (\st -> writeIORef (spreadRef_ st))
timesRef = newAttr (\st -> readIORef (timesRef_ st)) (\st -> writeIORef (timesRef_ st))
speedRef = newAttr (\st -> readIORef (speedRef_ st)) (\st -> writeIORef (speedRef_ st))
counterRef = newAttr (\st -> readIORef (counterRef_ st)) (\st -> writeIORef (counterRef_ st))
varCounterRef = newAttr (\st -> readIORef (varCounterRef_ st)) (\st -> writeIORef (varCounterRef_ st))
permsRef = newAttr (\st -> readIORef (permsRef_ st)) (\st -> writeIORef (permsRef_ st))
kripkeRef = newAttr (\st -> readIORef (kripkeRef_ st)) (\st -> writeIORef (kripkeRef_ st))

_teditTextRef = newAttr (\st -> readIORef (_teditTextRef_ st)) (\st -> writeIORef (_teditTextRef_ st))

-- Out: "  <*> newIORef $2"
initSolverState :: IO SolverState
initSolverState = SolverState
  <$> newIORef Nothing
  <*> newIORef Nothing
  <*> newIORef Nothing
  <*> newIORef Nothing
  <*> newIORef Nothing
  <*> newIORef Nothing
  -- <*> newIORef Nothing

  <*> newIORef True
  <*> newIORef True
  <*> newIORef True
  <*> newIORef True
  <*> newIORef True
  <*> newIORef True

  <*> newIORef False
  <*> newIORef False
  <*> newIORef (False,False)
  <*> newIORef False
  <*> newIORef False
  <*> newIORef False
  <*> newIORef False
  <*> newIORef False

  <*> newIORef (0,0)
  <*> newIORef (30,20)
  <*> newIORef 0
  -- <*> newIORef 0
  <*> newIORef 0
  <*> newIORef 0
  <*> newIORef 0
  <*> newIORef 0
  <*> newIORef 0
  <*> newIORef 0
  <*> newIORef PA

  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []
  <*> newIORef []

  <*> newIORef ([],True)
  <*> newIORef (True,[])

  <*> newIORef ""
  <*> newIORef "tree"
  <*> newIORef "picDir"

  <*> newIORef (id,[])
  <*> newIORef nil2
  <*> newIORef (id,[])
  <*> newIORef (V,[])
  <*> newIORef "tree"
  <*> newIORef iniSymbols
  <*> newIORef seed
  <*> newIORef sizes0
  <*> newIORef (10,30)
  <*> newIORef (0,300)
  <*> newIORef 500
  <*> (newIORef $ const 0)
  <*> (newIORef $ const 0)
  <*> (newIORef $ \n -> [0..n-1])
  <*> newIORef ([],[],[],[],[],[],[])

  <*> newIORef ""

-- modified types
type Cmd a = SolverState -> IO a
type Action = Cmd ()
type Request a = Cmd a


-- extracted solver functions with state
addAxioms :: TermS -> String -> Action
addAxioms t file sST = do
  sig <- getSignature sST
  let axs = if isConjunct t then subterms t else [t]
      cls = filter (not . (isAxiom sig ||| isSimpl)) axs
  if null cls
    then do
      sST `Gtk.set`
        [ solPositionsRef := []
        , axiomsRef :~ \axioms -> axioms `join` axs
        , simplRulesRef :~ \simplRules -> simplRules ++ trips ["==","<==>"] axs
        , transRulesRef :~ \transRules -> transRules ++ trips ["->"] axs
        ]
      labGreen' $ newCls "axioms" file
    else do
        enterFormulas' cls
        labRed' "The clauses in the text field are not axioms."


      --   -- | Used by 'createClsMenu'.
      --   addClauses :: Int -> FilePath -> Action
      --   addClauses treetype file = do
      --       str <- if text then getTextHere else lookupLibs file
      --       let str' = removeComment 0 str
      --           file' = if text then "the text field" else file
      --       sig <- getSignature
      --       case treetype of
      --           0 -> case parseE (implication sig) str' of
      --                   Correct t -> addAxioms t file'
      --                   p -> incorrect p str' illformedF
      --           1 -> case parseE (implication sig) str' of
      --                   Correct t -> addTheorems t file'
      --                   p -> incorrect p str' illformedF
      --           _ -> parseConjects sig file' str'
      --       where text = null file

      --   addNamedAxioms :: Action
      --   addNamedAxioms = do
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else do
      --          str <- ent `gtkGet` entryText
      --          sig <- getSignature
      --          trees <- readIORef treesRef
      --          curr <- readIORef currRef
      --          treeposs <- readIORef treepossRef
      --          let pars = words str
      --              b par = par `elem` words "refl symm tran" ||
      --                      ((sig&isConstruct) ||| (sig&isDefunct)) (init par) &&
      --                      just (parse digit [last par])
      --              t = trees!!curr
      --              p = emptyOrLast treeposs
      --              pars' = filter b pars
      --              axs = case getSubterm t p of
      --                         F equiv [_,_] -> congAxs equiv pars'
      --                         _ -> []
      --          if null pars'
      --             then labRed' "Enter axiom names into the entry field."
      --             else if null axs then
      --                     labRed' "Select a binary relation in the current tree."
      --                  else addNamedAxioms' axs

      --   addNamedAxioms' axs = do
      --     modifyIORef axiomsRef $ \axioms -> axioms `join` axs
      --     modifyIORef indClausesRef $ \indClauses -> indClauses `join` axs
      --     enterFormulas' axs
      --     extendPT False False False False $ AddAxioms axs
      --     let msg = "Adding\n\n" ++ showFactors axs ++
      --               "\n\nto the axioms and applying nothing"
      --     setProof True False msg [] $ newCls "axioms" "the text field"

      --   -- | Called by menu items /STACK2IMPL/ and /from file/ from menu
      --   -- /signature/.
      --   addSigMap :: FilePath -> IO ()
      --   addSigMap file = do
      --       str <- lookupLibs file
      --       parseSigMap file $ removeComment 0 str

      --   -- | Called by menu items /from text field/ and /from file/ from menu
      --   -- /signature/.
      --   addSigMapT :: Action
      --   addSigMapT = do
      --       str <- getTextHere
      --       parseSigMap "the text field" str

addSpec' :: Bool -> FilePath -> Action
addSpec' b file sST = do
    checking <- sST `Gtk.get` checkingRef
    when (not checking) $ do
        when b $ sST `Gtk.set` [ specfilesRef :~ \specfiles -> file:specfiles]
        str <- get
        if null str then labRed' $ file ++ " is not a file name."
        else do
            let (sig,axs,ths,conjs,ts) = splitSpec $ removeComment 0 str
                act1 :: Base.Action
                act2,act3,act4 :: Sig -> Base.Action
                act1 = do
                    sig <- getSignature sST
                    if onlySpace axs then act2 sig
                    else case parseE (implication sig) axs of
                            Correct t -> do
                                addAxioms t file' sST
                                delay $ act2 sig
                            p -> incorrect p axs illformedF
                act2 sig =
                    if onlySpace ths then act3 sig
                    else case parseE (implication sig) ths of
                        Correct t -> do
                            addTheorems t file' sST
                            delay $ act3 sig
                        p -> incorrect p ths illformedF
                act3 sig =
                    if onlySpace conjs then act4 sig
                    else do
                        parseConjects sig file' conjs sST
                        delay $ act4 sig
                act4 sig =
                    if onlySpace ts then delay $ return ()
                    else parseTerms sig file' ts sST
            if onlySpace sig then act1
            else do
                  (ps,cps,cs,ds,fs,hs) <- sST `Gtk.get` symbolsRef
                  let syms = ps++cps++cs++ds++fs++map fst hs
                  case parseE (signature ([],ps,cps,cs,ds,fs,hs)) sig of
                      Correct (specs,ps,cps,cs,ds,fs,hs)
                        -> do
                          sST `Gtk.set` [ symbolsRef := (ps,cps,cs,ds,fs,hs)]
                          let finish = do
                                sST `Gtk.set` [ varCounterRef := iniVC syms]
                                labGreen' $ newSig file'
                                delay act1
                          specfiles <- sST `Gtk.get` specfilesRef
                          mapM_ (flip (addSpec' False) sST)
                            $ specs `minus` specfiles
                          delay finish
                      Partial (_,ps,cps,cs,ds,fs,hs) rest
                        -> do
                            enterText' $ showSignature (ps,cps,cs,ds,fs,hs)
                                      $ check rest
                            labRed' illformedSig
                      _ -> do
                            enterText' sig
                            labRed' illformedSig
  where (file',get) = if null file then ("the text field",getTextHere sST)
                                  else (file,lookupLibs file)
        onlySpace = all (`elem` " \t\n")
        
addSpecWithBase :: FilePath -> Action
addSpecWithBase spec sST = do
  addSpec' True "base" sST
  when (spec == "base") $ do addSpec' True spec sST
                             mapM_ act w
  where act x = do
          simplRules <- sST `Gtk.get` simplRulesRef
          when (nothing $ search ((== x) . root . pr1) simplRules)
            $ sST `Gtk.set`
            [ simplRulesRef :~ \simplRules -> (leaf x,[],mkList []):simplRules]
        w = words "states labels atoms"
        
      --   -- | Adds substitutions. Called by menu item
      --   -- /add from text field/ from menu /substitution/.
      --   addSubst :: Action
      --   addSubst = do
      --       str <- getTextHere
      --       sig <- getSignature
      --       case parseE (conjunct sig) str of
      --           Correct t ->
      --               if hasPos t then labRed' posInSubst
      --               else case eqsToSubst $ mkFactors t of
      --                   Just (f,dom) -> do
      --                       (g,xs) <- readIORef substitutionRef
      --                       setSubst' (g `andThen` f, xs `join` dom)
      --                       labGreen' extendedSubst
      --                   _ -> labRed' illformedS
      --           p -> incorrect p str illformedS
        
      --   -- | Used by 'enterFormulas'', 'enterTerms', 'enterText'' and
      --   -- 'enterRef'.
      --   addText :: [String] -> Action
      --   addText ls = do
      --       buffer <- tedit `gtkGet` textViewBuffer
      --       end <- textBufferGetEndIter buffer
      --       textBufferInsert buffer end text
      --    where addNo :: Int -> [String] -> [String]
      --          addNo _ []               = []
      --          addNo n ([]:ls)          = []:addNo n ls
      --          -- addNo 0 ((' ':l):ls)     = (" 0> " ++ l):addNo 1 ls
      --          -- addNo n ((' ':l):ls)     = ("    " ++ l):addNo n ls
      --          -- addNo n (('.':l):ls)     = ("   ." ++ l):addNo n ls
      --          addNo n (l:ls) | n < 10  = (' ':' ':show n ++ '>':l):f n
      --                         | n < 100 = (' ':show n ++ '>':l):f n
      --                         | True    = (show n ++ '>':l):f n
      --                                     where f n = addNo (n+1) ls
      --          split []                  = []
      --          split l | length l <= 85 = [l]
      --                  | True           = take 85 l:split ('.':drop 85 l)
      --          text = unlines $ addNo 0 $ concatMap split ls

addTheorems :: TermS -> FilePath -> Action
addTheorems t file sST = do
    -- sig <- getSignature
    sST `Gtk.set`
      [ theoremsRef :~
          \theorems -> theorems `join` if isConjunct t then subterms t else [t]
      ]
    labGreen' $ newCls "theorems" file
        
      --   -- | Called by menu item /apply clause/ from menu /transform selection/.
      --   applyClause :: Bool -> Bool -> Bool -> Action
      --   applyClause lazy invert saveRedex = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           str <- ent `gtkGet` entryText
      --           numberedExps <- readIORef numberedExpsRef
      --           let (exps,b) = numberedExps
      --           case parse nat str of
      --               k@(Just n) | n < length exps
      --                 -> if b then if lazy then stretchAndApply k $ exps!!n
      --                                      else finish k $ exps!!n
      --                   else labMag "Enter formulas into the text field!"
      --               _ -> do
      --                   str <- getTextHere
      --                   sig <- getSignature
      --                   case parseE (implication sig) str of
      --                         Correct cl | lazy -> stretchAndApply Nothing cl
      --                                    | True -> finish Nothing cl
      --                         p -> incorrect p str illformedF
      --     where stretchAndApply k cl = do
      --            varCounter <- readIORef varCounterRef
      --            let zNo = varCounter "z"
      --            case preStretch True (const True) cl of
      --                 Just (_,varps) -> do
      --                                   setZcounter n; finish k clp
      --                                   where (clp,n) = stretchPrem zNo varps cl
      --                 _ -> case preStretch False (const True) cl of
      --                           Just (_,varps) -> do setZcounter n; finish k clc
      --                                   where (clc,n) = stretchConc zNo varps cl
      --                           _ -> notStretchable "The left-hand side"
      --           finish k cl = applyTheorem saveRedex k $
      --                                     if invert then invertClause cl else cl

        
      --   -- | Used by 'checkForward' and 'startInd'.
      --   applyCoinduction :: Int -> Action
      --   applyCoinduction limit = do
      --     sig <- getSignature
      --     trees <- readIORef treesRef
      --     curr <- readIORef currRef
      --     treeposs <- readIORef treepossRef
      --     varCounter <- readIORef varCounterRef
      --     axioms <- readIORef axiomsRef
      --     newPreds <- readIORef newPredsRef
      --     let t = trees!!curr
      --         qs@(p:ps) = emptyOrAll treeposs
      --         rs@(r:_) = map init qs
      --         u = getSubterm t r
      --         str = "COINDUCTION"
      --         g = stretchConc $ varCounter "z"
      --         getAxioms = flip noSimplsFor axioms
      --         h x = if x `elem` fst newPreds then getPrevious x else x
      --         conjs@(conj:_) = map (mapT h) $ map (getSubterm t) qs
      --         f = preStretch False (sig&isCopred)
      --     if notnull qs && any null ps then labRed' $ noApp str
      --     else if null ps && universal sig t p conj
      --            then case f conj of
      --                 Just (x,varps)
      --                   -> do
      --                      let (conj',k) = g varps conj; axs = getAxioms [x]
      --                      setZcounter k
      --                      applyInd limit False str [conj'] [x] axs t p []
      --                 _ -> notStretchable "The conclusion"
      --            else if allEqual rs && isConjunct u && universal sig t r u then
      --                    case mapM f conjs of
      --                    Just symvarpss
      --                      -> do
      --                         let (xs,varpss) = unzip symvarpss
      --                             (conjs',ks) = unzip $ zipWith g varpss conjs
      --                             ys = mkSet xs; axs = getAxioms ys
      --                         modifyIORef varCounterRef
      --                           $ \varCounter -> updMax varCounter "z" ks
      --                         applyInd limit False str conjs' ys axs t r $
      --                                                  restInd (subterms u) qs
      --                    _ -> notStretchable "Some conclusion"
      --                 else labRed' $ noApp str


        
      --   -- | Used by 'applyTheorem'.
      --   applyDisCon :: Maybe Int -> TermS -> [TermS] -> TermS -> [[Int]] -> Sig
      --               -> String -> Action
      --   applyDisCon k (F "|" ts) redices t ps sig msg =
      --       applyDisCon k (F "<===" [F "|" ts,mkTrue]) redices t ps sig msg
      --   applyDisCon k (F "&" ts) redices t ps sig msg =
      --       applyDisCon k (F "<===" [F "&" ts,mkTrue]) redices t ps sig msg
      --   applyDisCon k (F "<===" [F "|" ts,prem]) redices t ps sig msg = do
      --     let pred = glbPos ps
      --         u = getSubterm t pred
      --         qs = map (restPos pred) ps
      --     if all noQuantsOrConsts ts && polarity True t pred && isDisjunct u &&
      --        all (isProp sig ||| isAnyQ) (sucTerms u qs)
      --        then finishDisCon k False True ts prem redices t ps pred qs sig msg
      --     else labRed' $ noAppT k
      --   applyDisCon k (F "<===" [F "&" ts,prem]) redices t ps sig msg = do
      --     let pred = glbPos ps
      --         u = getSubterm t pred
      --         qs = map (restPos pred) ps
      --     if all noQuantsOrConsts ts && polarity True t pred && isConjunct u && 
      --        all (isProp sig ||| isAllQ) (sucTerms u qs)
      --       then finishDisCon k False False ts prem redices t ps pred qs sig msg
      --     else labRed' $ noAppT k
      --   applyDisCon k (F "===>" [F "&" ts,conc]) redices t ps sig msg = do
      --     let pred = glbPos ps
      --         u = getSubterm t pred
      --         qs = map (restPos pred) ps
      --     if all noQuantsOrConsts ts && polarity False t pred && isConjunct u &&
      --        all (isProp sig ||| isAllQ) (sucTerms u qs)
      --        then finishDisCon k True True ts conc redices t ps pred qs sig msg
      --     else labRed' $ noAppT k
      --   applyDisCon k (F "===>" [F "|" ts,conc]) redices t ps sig msg = do
      --     let pred = glbPos ps
      --         u = getSubterm t pred
      --         qs = map (restPos pred) ps
      --     if all noQuantsOrConsts ts && polarity False t pred && isDisjunct u &&
      --        all (isProp sig ||| isAnyQ) (sucTerms u qs)
      --        then finishDisCon k True False ts conc redices t ps pred qs sig msg
      --     else labRed' $ noAppT k
        
      --   -- Used by 'applyCoinduction' and 'applyInduction'.
      --   applyInd :: Int -> Bool -> String -> [TermS] -> [String] -> [TermS]
      --            -> TermS -> [Int] -> [TermS] -> Action
      --   applyInd limit ind str conjs indsyms axs t p rest = do
      --     sig <- getSignature
      --     varCounter <- readIORef varCounterRef
      --     (nps,ncps) <- readIORef newPredsRef
      --     let syms = if ind then ncps else nps
      --         vc1 = decrVC varCounter syms
      --         indsyms' = indsyms `join` map getPrevious syms
      --         (f,vc2) = renaming vc1 indsyms'
      --         axs0 = map mergeWithGuard axs
      --         (axs1,vc3) = iterate h (axs0,vc2)!!limit
      --         h (axs,vc) = applyToHeadOrBody sig (((`elem` indsyms') .) . label)
      --                                            False axs0 axs vc
      --         newAxs = map mkAx conjs
      --         mkAx (F x [t,u]) = F x [g t,u]
      --         mkAx _           = error "applyInd"
      --         -- g replaces a logical predicate r by f(r) and an equation
      --         -- h(t)=u with h in xs by the logical atom f(h)(t,u).
      --         g eq@(F "=" [F x ts,u]) = if x `elem` indsyms'
      --                                   then F (f x) $ ts++[u] else eq
      --         g (F x ts)              = F (f x) $ map g ts
      --         g t                     = t
      --         rels = map f indsyms'
      --         (ps',cps') = if ind then ([],rels) else (rels,[])
      --     (ps,cps,cs,ds,fs,hs) <- readIORef symbolsRef
      --     writeIORef symbolsRef (ps `join` ps',cps `join` cps',cs,ds,fs,hs)
      --     writeIORef newPredsRef (nps `join` ps',ncps `join` cps')
      --     sig <- getSignature
      --     let (cls,vc4) = applyToHeadOrBody sig (const2 True) True newAxs
      --                                           (map g axs1) vc3
      --         conj = mkConjunct cls
      --         xs = [x | x <- frees sig conj, noExcl x]
      --         u = replace t p $ mkConjunct $ mkAll xs conj:rest
      --         msg = "Adding\n\n" ++ showFactors newAxs ++
      --            "\n\nto the axioms and applying " ++ str ++ " wrt\n\n"
      --            ++ showFactors axs1 ++ "\n\n"
      --     modifyIORef indClausesRef (`join` newAxs)
      --     modifyIORef axiomsRef (`join` newAxs)
      --     writeIORef varCounterRef vc4
      --     extendPT False False True True $ Induction ind limit
      --     maybeSimplify sig u
      --     makeTrees sig
      --     setTreesFrame []
      --     setProof True True msg [p] $ indApplied str
        
      --   -- | Used by 'checkForward' and 'startInd'.
      --   applyInduction :: Int -> Action
      --   applyInduction limit = do
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       treeposs <- readIORef treepossRef
      --       varCounter <- readIORef varCounterRef
      --       let t = trees!!curr
      --           qs@(p:ps) = emptyOrAll treeposs
      --           rs@(r:_) = map init qs
      --           u = getSubterm t r
      --           str = "FIXPOINT INDUCTION"
      --           g = stretchPrem $ varCounter "z"
      --       if notnull qs && any null ps then labRed' $ noApp str
      --       else do
      --           sig <- getSignature
      --           newPreds <- readIORef newPredsRef
      --           let h (F x ts) = if x `elem` snd newPreds
      --                            then if isPred sig z then F z ts
      --                                 else mkEq (F z $ init ts) $ last ts
      --                            else F x $ map h ts where z = getPrevious x
      --               h t               = t
      --               conjs@(conj:_) = map (h . getSubterm t) qs
      --               f = preStretch True $ isPred sig ||| isDefunct sig
      --               getAxioms ks xs = unzip . map g . noSimplsFor xs
      --                 where g = flatten (maximum ks) $ filter (isDefunct sig) xs
      --           if null ps && universal sig t p conj
      --           then case f conj of
      --                   Just (x,varps) -> do
      --                       axioms <- readIORef axiomsRef
      --                       let (conj',k) = g varps conj
      --                           (axs,ms) = getAxioms [k] [x] axioms
      --                       modifyIORef varCounterRef $ \varCounter ->
      --                           updMax varCounter "z" ms
      --                       applyInd limit True str [conj'] [x] axs t p []
      --                   _ -> notStretchable "The premise"
      --           else
      --               if allEqual rs && isConjunct u && universal sig t r u
      --               then case mapM f conjs of
      --                   Just symvarpss -> do
      --                       axioms <- readIORef axiomsRef
      --                       let (xs,varpss) = unzip symvarpss
      --                           (conjs',ks) = unzip $ zipWith g varpss conjs
      --                           ys = mkSet xs; (axs,ms) = getAxioms ks ys axioms
      --                       modifyIORef varCounterRef $ \varCounter ->
      --                           updMax varCounter "z" ms
      --                       applyInd limit True str conjs' ys axs t r $
      --                                restInd (subterms u) qs
      --                   _ -> notStretchable "Some premise"
      --               else labRed' $ noApp str
        
      --   -- | Called by menu item /apply map/ from menu /signature/.
      --   applySigMap :: Action
      --   applySigMap = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           signatureMap <- readIORef signatureMapRef
      --           curr <- readIORef currRef
      --           formula <- readIORef formulaRef
      --           solve <- readIORef solveRef
      --           other <- getSolver solve
      --           sig <- getSignature
      --           sig' <- getSignatureR solve
      --           case applySignatureMap sig sig' (fst signatureMap) $ trees!!curr
      --               of Just t -> do bigWin solve; enterTree solve formula t
      --                  _ -> labRed' $ sigMapError other
        
      --   -- | Called by menu item /apply/ from menu /substitution/.
      --   applySubst :: Action
      --   applySubst = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           -- sig <- getSignature
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           substitution <- readIORef substitutionRef
      --           let t = trees!!curr
      --               (g,dom) = substitution
      --               f t p = replace t p $ getSubterm t p>>>g
      --               ts = substToEqs g dom
      --               ps = emptyOrAll treeposs
      --               msg = "The substitution\n\n" ++ showFactors ts ++ "\n\n"
      --           writeIORef treesRef $ updList trees curr $ foldl f t ps
      --           extendPT False False False False ApplySubst
      --           setProof False False msg ps subsAppliedToAll
      --           clearTreeposs; drawCurr'
        
      --   -- | Used by 'setSubst''.
      --   applySubstTo :: String -> Action
      --   applySubstTo x = do
      --       trees <- readIORef treesRef
      --       substitution <- readIORef substitutionRef

      --       if null trees then labBlue' start
      --                     else applySubstTo' x $ fst substitution x
        
      --   -- | Used by 'applySubstTo' and 'checkForward'.
      --   applySubstTo' :: String -> TermS -> Action
      --   applySubstTo' x v = do
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       treeposs <- readIORef treepossRef

      --       let t = trees!!curr
      --           p = emptyOrLast treeposs
      --           msg = "SUBSTITUTING " ++ showTerm0 v ++ " for " ++ x
      --       sig <- getSignature
      --       case isAny t x p of
      --           Just q | polarity True t q -> finish (q++[0]) t sig msg True
      --           _ -> case isAll t x p of
      --               Just q
      --                   | polarity False t q -> finish (q++[0]) t sig msg True
      --               _ -> finish p t sig msg False
      --       where finish p t sig msg b = do
      --               curr <- readIORef currRef

      --               modifyIORef treesRef $ \trees -> updList trees curr t'
      --               extendPT False False False False $ ApplySubstTo x v
      --               drawThis t' (map (p++) $ freeXPositions sig x u) "green"
      --               setProof b False msg [p] $ subsAppliedTo x
      --               (f,dom) <- readIORef substitutionRef
      --               setSubst' (upd f x $ V x, dom `minus1` x)
      --               where t' = replace t p $ u>>>for v x
      --                     u = getSubterm t p
        
      --   -- | Used by 'checkForward', 'specialize' and 'applyClause'.
      --   applyTheorem :: Bool -> Maybe Int -> TermS -> Action
      --   applyTheorem saveRedex k th = do
      --       sig <- getSignature
      --       extendPT False False True True $ Theorem saveRedex th
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       treeposs <- readIORef treepossRef
      --       varCounter <- readIORef varCounterRef
      --       let t = trees!!curr
      --           ps = emptyOrAll treeposs
      --           redices = map (getSubterm t) ps
      --           n = length ps
      --           ([th'],vc) =
      --               renameApply [if saveRedex then copyRedex th else th]
      --                                       sig t varCounter
      --           f t (redex:rest) (p:ps) qs vc
      --                       = case applySingle th' redex t p sig vc of
      --                                   Just (t,vc) -> f t rest ps (p:qs) vc
      --                                   _ -> f t rest ps qs vc
      --           f _ _ _ [] _  = labRed' $ notUnifiable k
      --           f t _ _ qs vc = do
      --                       writeIORef varCounterRef vc
      --                       maybeSimplify sig t
      --                       makeTrees sig
      --                       finish qs
      --           str = showTree False $ case th of
      --               F "===>" [F "True" [],th] -> th
      --               F "<===" [F "False" [],th] -> mkNot sig th
      --               _ -> th
      --           finish qs = do
      --               setTreesFrame []
      --               setProof True True (applied True str) qs
      --                                      $ thApplied k
      --       when (nothing k) $ enterText' str
      --       if isTaut th then do
      --           writeIORef varCounterRef vc
      --           f t redices ps [] vc
      --       else
      --           if n > 1 && isDisCon th && n == noOfComps th
      --           then do
      --               writeIORef varCounterRef vc
      --               applyDisCon k th' redices t ps sig $ applied True str
      --           else
      --             if saveRedex || isSimpl th || all (correctPolarity t) ps
      --                then if isAxiom sig th then
      --                        narrowOrRewritePar t sig k [th] saveRedex ps
      --                     else if isTheorem th then do
      --                                               writeIORef varCounterRef vc
      --                                               f t redices ps [] vc 
      --                                          else labRed' $ noTheorem k
      --                else labRed' $ noAppT k
      --       where correctPolarity t p = isHornT th && b || isCoHornT th && not b
      --                                where b = polarity True t p
        
      --   -- | Used by 'checkForward'. Called by menu item
      --   -- /use transitivity/ from menu /transform selection/.
      --   applyTransitivity :: Action
      --   applyTransitivity = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           let t = trees!!curr
      --               ps = emptyOrAll treeposs
      --               redices = map (getSubterm1 t) ps
      --           case redices of
      --               F x [l,r]:_ -> do
      --                   varCounter <- readIORef varCounterRef
      --                   let p:qs = ps
      --                       n = varCounter "z"
      --                       z = 'z':show n
      --                       n' = n+1
      --                   if transitive x && null qs && polarity True t p then do
      --                       let u = anyConj [z] [F x [l,V z],F x [V z,r]]
      --                       curr <- readIORef currRef
      --                       modifyIORef treesRef $ \trees ->
      --                           updList trees curr $ replace1 t p u
      --                       setZcounter n'
      --                   else do
      --                       let z' = 'z':show n'
      --                           u | qs == [p ++ [0]]
      --                               = anyConj [z] [mkEq l $ V z, F x [V z, r]]
      --                             | qs == [p ++ [1]]
      --                               = anyConj [z] [F x [l, V z], mkEq (V z) r]
      --                             | otherwise
      --                               = anyConj [z, z'] [mkEq l $ V z
      --                                                 , F x [V z, V z']
      --                                                 , mkEq (V z') r]
      --                       curr <- readIORef currRef
      --                       modifyIORef treesRef $ \trees ->
      --                           updList trees curr $ replace1 t p u
      --                       setZcounter $ n'+1
      --                   finish ps
      --               _ ->
      --                   if any null ps then labMag "Select proper subtrees!"
      --                   else do
      --                       let qs = map init ps
      --                           q = head qs
      --                           u = getSubterm t q
      --                       if allEqual qs && isConjunct u then
      --                           case transClosure redices of
      --                               Just v ->
      --                                   if polarity False t q then do
      --                                       let us = v:removeTerms (subterms u)
      --                                                   redices
      --                                           t' = replace1 t q
      --                                               $ mkConjunct us
      --                                       curr <- readIORef currRef
      --                                       modifyIORef treesRef $ \trees ->
      --                                           updList trees curr t'
      --                                       finish ps
      --                                   else labRed' $ noApp "Transitivity"
      --                               _ -> labMag "Select composable atoms!"
      --                       else labRed' $ noApp "Transitivity"
      --       where anyConj xs = mkAny xs . F "&"
      --             finish ps = do
      --                    extendPT False False False False ApplyTransitivity
      --                    setProof True False "TRANSITIVITY" ps
      --                        transitivityApplied
      --                    clearTreeposs; drawCurr'

      --   -- | Called by button "<---" ('backBut') or keypress "Up" while left
      --   -- label ('lab') is active.
      --   backProof' :: Action
      --   backProof' = do
      --       restore <- readIORef restoreRef
      --       if restore then do
      --           oldTreeposs <- readIORef oldTreepossRef
      --           writeIORef treepossRef oldTreeposs
      --           writeIORef restoreRef False
      --           drawCurr'
      --       else do
      --           checking <- readIORef checkingRef
      --           if checking then checkBackward
      --           else do
      --               proofPtr <- readIORef proofPtrRef
      --               proofTPtr <- readIORef proofTPtrRef
      --               proofTerm <- readIORef proofTermRef
      --               if proofPtr < 1 then labMag emptyProof
      --               else do
      --                   proof <- readIORef proofRef
      --                   let ps = peTreePoss (proof!!proofPtr)
      --                   modifyIORef proofPtrRef pred
      --                   proofPtr <- readIORef proofPtrRef
      --                   changeState proofPtr ps
      --               let n = searchback deriveStep $ take proofTPtr proofTerm
      --               writeIORef proofTPtrRef $ Haskell.fromMaybe 0 n
        
      --   -- | Minimize solver window. Exported by public 'Epaint.Solver' method
      --   -- 'Epaint.backWin'.
      --   backWin' :: Action
      --   backWin' = windowIconify  win
        
      --   -- | Bring solver window to front, even if minimized. Exported by public
      --   -- 'Epaint.Solver' method 'Epaint.bigWin'.
      --   bigWin' :: Action
      --   bigWin' = windowDeiconify  win >> windowPresent  win
        
      --   -- | Used by slider horBut.
      --   blowHor :: Int -> Action
      --   blowHor i = do
      --       modifyIORef spreadRef $ \spread -> (i,snd spread)
      --       picEval <- readIORef picEvalRef
      --       spread <- readIORef spreadRef
      --       setEval paint picEval spread
        
      --   -- | Used by slider verBut.
      --   blowVer :: Int -> Action
      --   blowVer i = do
      --       modifyIORef spreadRef $ \spread -> (fst spread,i)
      --       picEval <- readIORef picEvalRef
      --       spread <- readIORef spreadRef
      --       setEval paint picEval spread
        
      --   {-
      --       | Builds a Kripke model based on the given @mode@.
      --       0 -> cycle free
      --       1 -> pointer-free
      --       2 -> normal
      --       3 -> rebuild last one
      --       4 -> from current graph
      --       Used by 'checkForward' and multiple entries from "specification"
      --       menu.
      --   -}
      --   buildKripke :: Int -> Action
      --   buildKripke 3 = do                              -- from current graph
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else do
      --       curr <- readIORef currRef
      --       let t = trees!!curr
      --           (states',atoms',rules') = graphToTransRules t
      --       changeSimpl "states" $ mkList states'
      --       changeSimpl "atoms" $ mkList atoms'
      --       changeSimpl "labels" $ mkList []
      --       writeIORef transRulesRef rules'
      --       writeIORef kripkeRef (states',atoms',[],[],[],[],[])
      --       sig <- getSignature
      --       let (rs1,_) = rewriteSig sig (sig&states)
      --           (rs2,_) = rewriteSig sig (sig&atoms)
      --           tr = pairsToInts states' rs1 states'
      --           va = pairsToInts states' rs2 atoms'
      --       writeIORef kripkeRef (states',atoms',[],tr,[],va,[])
      --       delay $ setProof True False kripkeMsg []
      --                $ kripkeBuilt 3 0 (length states') 0 $ length atoms'

      --   buildKripke 4 = do                            -- from regular expression
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else do
      --          sig <- getSignature
      --          trees <- readIORef treesRef
      --          curr <- readIORef currRef
      --          treeposs <- readIORef treepossRef
      --          let t = trees!!curr
      --              p = emptyOrLast treeposs
      --          case parseRE sig $ getSubterm t p of
      --            Just (e,as) -> do
      --               let (_,nda) = regToAuto e
      --                   as' = as `minus1` "eps"
      --                   (sts,delta) = powerAuto nda as' 
      --                   finals = searchAll (elem 1) sts
      --                   mkTerm = mkList . map mkConst
      --                   f (st,a) = (mkPair (mkTerm st) $ leaf a,[],
      --                               mkTerm $ delta st a)
      --                   states' = map mkTerm sts
      --                   labels' = map leaf as'
      --                   atom' = leaf "final"
      --               changeSimpl "states" $ mkList states'
      --               changeSimpl "atoms" $ mkList [atom']
      --               changeSimpl "labels" $ mkList labels'
      --               writeIORef transRulesRef $ map f $ prod2 sts as'
      --               writeIORef kripkeRef (states',[atom'],labels',[],[],[],[])
      --               sig <- getSignature
      --               let (_,rsL) = rewriteSig sig (sig&states)
      --                   trL = tripsToInts states' labels' rsL states'
      --               writeIORef kripkeRef
      --                 (states',[atom'],labels',[],trL,[finals],[])
      --               delay $ setProof True False kripkeMsg []
      --                     $ kripkeBuilt 4 0 (length sts) (length as') 1
      --            _ -> labMag "Select a regular expression!"

      --   buildKripke mode = do
      --     trees <- readIORef treesRef
      --     when (null trees) $ enterTree' False $ V""
      --     str <- ent `gtkGet` entryText
      --     sig <- getSignature
      --     let noProcs = if (sig&isDefunct) "procs" 
      --                      then case parse pnat str of Just n -> n; _ -> 0
      --                      else 0
      --     when (noProcs > 0) $ changeSimpl "procs" $ mkConsts [0..noProcs-1]
      --     simplRules <- readIORef simplRulesRef
      --     let iniStates = [t | (F "states" _,_,t) <- simplRules]
      --     changeSimpl "states" $ if null iniStates then mkList [] 
      --                                              else head iniStates
      --     delay $ buildKripke1 mode noProcs

      --   buildKripke1 mode noProcs = do
      --     sig <- getSignature
      --     let states = simplify2List sig "states"
      --         labels = simplify2List sig "labels" 
      --     writeIORef kripkeRef (states,[],labels,[],[],[],[])
      --     changeSimpl "states" $ mkList states
      --     changeSimpl "labels" $ mkList labels
          
      --     sig <- getSignature
      --     let (states,rs,rsL) = rewriteStates sig mode
      --         tr  = pairsToInts states rs states
      --         trL = tripsToInts states labels rsL states
      --     writeIORef kripkeRef (states,[],labels,tr,trL,[],[])
      --     changeSimpl "states" $ mkList states
      --     delay $ buildKripke2 mode noProcs states labels tr trL
        
      --   buildKripke2 mode noProcs states labels tr trL = do
      --     sig <- getSignature
      --     let atoms' = simplify2List sig "atoms"
      --     writeIORef kripkeRef (states,atoms',labels,tr,trL,[],[])
      --     changeSimpl "atoms" $ mkList atoms'
      --     sig <- getSignature
      --     let (rs,rsL) = rewriteSig sig (sig&atoms)
      --         va  = pairsToInts states rs atoms'
      --         vaL = tripsToInts states labels rsL atoms'
      --     writeIORef kripkeRef (states,atoms',labels,tr,trL,va,vaL)
      --     delay $ setProof True False kripkeMsg []
      --           $ kripkeBuilt mode noProcs (length states) (length labels)
      --           $ length atoms'
        
      --   buildRegExp = do
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else do
      --          str <- ent `gtkGet` entryText
      --          sig <- getSignature
      --          let finish start = do
      --                 trees <- readIORef treesRef
      --                 curr <- readIORef currRef
      --                 writeIORef treesRef
      --                   $ updList trees curr $ showRE $ autoToReg sig start
      --                 extendPT False False False False BuildRE
      --                 setProof False False "BUILDING A REGULAR EXPRESSION" []
      --                                      regBuilt
      --                 clearTreeposs; drawCurr'
      --          case parse (term sig) str of
      --               Just start | start `elem` (sig&states) -> finish start
      --               _ -> do
      --                    trees <- readIORef treesRef
      --                    curr <- readIORef currRef
      --                    treeposs <- readIORef treepossRef
      --                    let start = label (trees!!curr) $ emptyOrLast treeposs
      --                    case parse (term sig) $ takeWhile (/= ':') start of
      --                         Just start | start `elem` (sig&states)
      --                           -> finish start
      --                         _ -> labRed' "Enter or select an initial state!"
        
      --   -- | Called by menu item /build unifier/ from menu
      --   -- /transform selection/.
      --   buildUnifier :: Action
      --   buildUnifier = do
      --       treeposs <- readIORef treepossRef
      --       if length treeposs /= 2 || any null treeposs
      --       then labMag "Select two proper subtrees!"
      --       else do
      --           trees <- readIORef treesRef
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           let t = trees!!curr
      --               [p,q] = treeposs
      --               u = getSubterm t p
      --               v = getSubterm t q
      --           unifyAct u v t t p q
        
      --   -- | Called by all menu items from /call enumerators/ sub menu of the
      --   -- tree menu.
      --   callEnum :: String -> Action
      --   callEnum obj = do
      --       writeIORef formulaRef False
      --       writeIORef joinedRef False
      --       writeIORef matchingRef 0
      --       matchBut `gtkSet` [ buttonLabel := "match" ]
      --       splitBut `gtkSet` [ buttonLabel := "join" ]
      --       clearTreeposs
      --       setInterpreter' obj
      --       sig <- getSignature
      --       let ts = case simplifyIter sig $ F "compl" [] of F "[]" us -> us
      --                                                        _ -> []
      --           compl = curry $ setToFun $ zipWith f (evens ts) $ odds ts
      --                 where f t u = (showTerm0 t,showTerm0 u)
      --       (enum&buildEnum) obj $ if obj `elem` ["alignment","palindrome"]
      --                              then compl else const2 False
        
      --   -- | Initialize the 'moveNode' action. Called if the right mouse
      --   -- button is clicked on a node inside the canvas.
      --   catchNode :: Pos -> Action
      --   catchNode (x, y) = do
      --       treeposs <- readIORef treepossRef

      --       if null treeposs then labMag "Select a target node!"
      --       else do
      --           ctree <- readIORef ctreeRef

      --           -- should be fine without: (x,y) <- adaptPos pt
      --           case getSubtree (get ctree) x y of
      --               Just (p,cu) -> do
      --                   let z = root cu
      --                   if last treeposs <<= p then drawNode z cyan
      --                                          else drawNode z magenta
      --                   writeIORef nodeRef $ Just (z,p)
      --                   canv `gtkSet` [ canvasCursor := SbUpArrow ]
      --               _ -> return ()
        
      --   -- | Initialize the 'moveSubtree' action. Called if the left mouse
      --   -- button is clicked on a node inside the canvas.
      --   catchSubtree :: Pos -> Action
      --   catchSubtree pt@(x, y) = do
      --       trees <- readIORef treesRef

      --       when (notnull trees) $ do
      --           Just ct <- readIORef ctreeRef
      --           treeposs <- readIORef treepossRef

      --           -- should be fine without: (x,y) <- adaptPos pt
      --           case getSubtree ct x y of
      --               Just (p,cu)
      --                   | p `elem` treeposs -> do -- deselect subtree
      --                       setTreeposs $ Remove p
      --                       drawSubtrees
      --                   | True -> do -- select subtree
      --                       writeIORef isSubtreeRef $ Just False
      --                       setTreeposs $ Add [p]
      --                       writeIORef nodeRef $ Just (root cu,p)
      --                       writeIORef penposRef $ Just pt
      --                       writeIORef subtreeRef $ Just cu
      --                       writeIORef suptreeRef $ Just ct
      --                       canv `gtkSet` [ canvasCursor := Hand2 ]
      --                       drawSubtrees
      --               _ -> when (notnull treeposs) $ do -- deselect last
      --                       setTreeposs $ Remove $ last treeposs
      --                       drawSubtrees
        
      --   -- | Initialize the 'moveTree' action. Called if the middle mouse button
      --   -- is clicked on a node inside the canvas.
      --   catchTree :: Pos -> Action
      --   catchTree pt@(x, y) = do
      --       trees <- readIORef treesRef

      --       when (notnull trees) $ do
      --           ctree <- readIORef ctreeRef
      --           treeposs <- readIORef treepossRef

      --           -- should be fine without: (x,y) <- adaptPos pt
      --           let Just ct = ctree
      --           case getSubtree ct x y of
      --               Just (p,cu) | p `elem` treeposs -> do -- cut subtree
      --                   writeIORef isSubtreeRef $ Just True
      --                   let a = root cu
      --                   writeIORef nodeRef $ Just (a,p)
      --                   writeIORef penposRef $ Just pt
      --                   writeIORef subtreeRef $ Just cu
      --                   writeIORef suptreeRef $ Just $ replace0 ct p $ V a
      --                   canv `gtkSet` [ canvasCursor := Hand2 ]
      --               _ -> do            -- move tree
      --                   writeIORef isSubtreeRef $ Just False
      --                   writeIORef penposRef $ Just pt
      --                   canv `gtkSet` [ canvasCursor := Crosshair ]
        
      --   -- | Changes the background of the canvas area.
      --   changeCanvasBackground :: Color -> Action
      --   changeCanvasBackground c@(RGB r g b) = do
      --       let f n = fromIntegral $ n * 256
      --           (r', g' , b') = (f r, f g, f b)
      --       canv `gtkSet` [ canvasBackground := c ]
      --       widgetModifyBg scrollCanv StateNormal $ gtkColor r' g' b'
        
      --   -- | Used by 'releaseSubtree' and 'replaceText''.
      --   changeMode :: TermS -> Action
      --   changeMode t = do
      --       formula <- readIORef formulaRef

      --       sig <- getSignature
      --       let b = isFormula sig t
      --           str = if b then "formula" else "term"
      --       if b /= formula
      --       then do
      --           writeIORef formulaRef b
      --           writeIORef treeModeRef "tree"
      --           writeIORef treesRef [t]
      --           modifyIORef counterRef $ \counter -> upd counter 't' 1
      --           writeIORef currRef 0
      --           treeSlider `gtkSet` [ widgetSensitive := False ]
      --           setCurrInPaint paint 0
      --           termBut `gtkSet` [ labelText := str ]
      --           setNarrow False False
      --       else do
      --           curr <- readIORef currRef
      --           trees <- readIORef treesRef
      --           writeIORef treesRef $ updList trees curr t
        
      --   changeSimpl x t = do
      --     simplRules <- readIORef simplRulesRef
      --     case search ((== x) . root . pr1) simplRules of 
      --          Just i -> modifyIORef simplRulesRef $ \simpleRules ->
      --                          updList simplRules i rule
      --          _ -> modifyIORef simplRulesRef $ \simpleRules -> rule:simplRules
      --     where rule = (leaf x,[],t)

        
      --   -- | Used by 'checkBackward', 'forwProof'' and 'backProof'.
      --   changeState :: Int -> [[Int]] -> Action
      --   changeState ptr ps = do
      --       proof <- readIORef proofRef
      --       trees <- readIORef treesRef
      --       safe <- readIORef safeRef
      --       joined <- readIORef joinedRef
      --       safeBut <- readIORef safeButRef

      --       let proofElem = proof!!ptr
      --       writeIORef treesRef $ peTrees proofElem
      --       modifyIORef counterRef $ \counter -> upd counter 't' $ length trees
      --       writeIORef treeModeRef $ peTreeMode proofElem
      --       writeIORef currRef $ peCurr proofElem
      --       writeIORef permsRef $ pePerms proofElem
      --       writeIORef varCounterRef $ peVarCounter proofElem
      --       writeIORef newPredsRef $ peNewPreds proofElem
      --       writeIORef solPositionsRef $ peSolPositions proofElem
      --       writeIORef constraintsRef $ peConstraints proofElem
      --       writeIORef joinedRef $ peJoined proofElem
      --       writeIORef safeRef $ peSafe proofElem
      --       setTreesFrame ps
      --       setSubst' (peSubstitution proofElem)
      --       labGreen' (peMsgL proofElem)
      --       safeBut `gtkSet` [ menuItemLabel := eqsButMsg $ not safe ]
      --       splitBut `gtkSet` [ buttonLabel := if joined then "split" else "join" ]

      --   changeStrat = do
      --     modifyIORef simplStratRef $ \simplStrat ->
      --       case simplStrat of DF -> BF; BF -> PA; PA -> DF
      --     setStrat

      --   -- | Used by 'backProof'.
      --   checkBackward :: Action
      --   checkBackward = do
      --     proofTPtr <- readIORef proofTPtrRef
      --     if proofTPtr < 1
      --        then do labMag emptyProof; (paint&labSolver) emptyProof; enterRef
      --     else do
      --         modifyIORef proofTPtrRef pred
      --         proofTPtr <- readIORef proofTPtrRef
      --         proofTerm <- readIORef proofTermRef
      --         case proofTerm!!proofTPtr of
      --              Mark _ -> do
      --                  writeIORef treepossRef []
      --                  drawCurr'
      --              Matching _    -> do
      --                matchTerm <- readIORef matchTermRef
      --                when (not $ null matchTerm) $ do
      --                  modifyIORef matchTermRef tail
      --                  matchTerm <- readIORef matchTermRef
      --                  writeIORef matchingRef $ head matchTerm
      --              Refuting _    -> do
      --                refuteTerm <- readIORef refuteTermRef
      --                when (not $ null refuteTerm) $ do
      --                  modifyIORef refuteTermRef tail
      --                  refuteTerm <- readIORef refuteTermRef
      --                  writeIORef refutingRef $ head refuteTerm
      --              SetStrat _    -> do
      --                stratTerm <- readIORef stratTermRef
      --                when (not $ null stratTerm) $ do
      --                  modifyIORef stratTermRef tail
      --                  stratTerm <- readIORef stratTermRef
      --                  writeIORef simplStratRef $ head stratTerm
      --              Simplifying _ -> do
      --                simplTerm <- readIORef simplTermRef
      --                when (not $ null simplTerm) $ do
      --                  modifyIORef simplTermRef tail
      --                  simplTerm <- readIORef simplTermRef
      --                  writeIORef simplifyingRef $ head simplTerm
      --              NegateAxioms ps1 cps1 -> do
      --                  proofPtr <- readIORef proofPtrRef
      --                  (ps,cps,cs,ds,fs,hs) <- readIORef symbolsRef

      --                  writeIORef symbolsRef
      --                      (minus ps ps2,minus cps cps2,cs,ds,fs,hs)
      --                  modifyIORef axiomsRef
      --                      $ \axioms -> axioms `minus` axs axioms
      --                  when (proofPtr > 0) $ do
      --                      proof <- readIORef proofRef
      --                      modifyIORef proofPtrRef pred
      --                      proofPtr <- readIORef proofPtrRef
      --                      labColorToPaint greenback (peMsgL (proof!!proofPtr))
      --                  where ps2 = map mkComplSymbol cps1
      --                        cps2 = map mkComplSymbol ps1
      --                        axs = noSimplsFor (ps2++cps2)
      --              _ -> do
      --                  proofPtr <- readIORef proofPtrRef
      --                  when (proofPtr > 0) $ do
      --                      proof <- readIORef proofRef
      --                      modifyIORef proofPtrRef pred
      --                      proofPtr <- readIORef proofPtrRef
      --                      changeState proofPtr $ peTreePoss (proof!!proofPtr)
      --         enterRef
        
        -- -- | Used by 'forwProof'' and 'runChecker'.
        -- checkForward :: Action
        -- checkForward = do
        --     proofTPtr <- readIORef proofTPtrRef
        --     proofTerm <- readIORef proofTermRef
        --     if proofTPtr >= length proofTerm
        --       then do labMag endOfProof; (paint&labSolver) endOfProof; enterRef
        --     else do
        --         proofPtr <- readIORef proofPtrRef
        --         let step = proofTerm!!proofTPtr
        --             k = proofPtr+1
        --         proof <- readIORef proofRef
        --         when (deriveStep step && k < length proof)
        --             $ writeIORef proofPtrRef k
        --         case step of
        --             AddAxioms axs -> addCongAxioms' axs
        --             ApplySubst -> applySubst
        --             ApplySubstTo x t -> applySubstTo' x t
        --             ApplyTransitivity -> applyTransitivity
        --             BuildKripke m -> buildKripke m
        --             BuildRE -> buildRegExp
        --             CollapseStep b -> collapseStep b
        --             CollapseVars -> collapseVarsCom
        --             ComposePointers -> composePointers
        --             CopySubtrees -> copySubtrees
        --             CreateIndHyp -> createIndHyp
        --             CreateInvariant b -> createInvariant b
        --             DecomposeAtom -> decomposeAtom
        --             EvaluateTrees -> evaluateTrees
        --             ExpandTree b n -> expandTree' b n
        --             FlattenImpl -> flattenImpl
        --             Generalize cls -> generalize' cls
        --             Induction True n -> applyInduction n
        --             Induction _ n -> applyCoinduction n
        --             Mark ps -> do
        --                 writeIORef treepossRef ps
        --                 drawCurr'
        --             Matching n -> do
        --               writeIORef matchingRef n
        --               modifyIORef matchTermRef $ \matchTerm -> n:matchTerm
        --             Minimize -> minimize
        --             ModifyEqs m -> modifyEqs m
        --             Narrow limit sub -> narrow'' limit sub
        --             NegateAxioms ps cps -> negateAxioms' ps cps
        --             PermuteSubtrees -> permuteSubtrees
        --             RandomLabels -> randomLabels
        --             RandomTree -> randomTree
        --             ReduceRE m -> reduceRegExp m
        --             Refuting b -> do
        --               writeIORef refutingRef b
        --               modifyIORef refuteTermRef $ \refuteTerm -> b:refuteTerm
        --             ReleaseNode -> releaseNode
        --             ReleaseSubtree -> releaseSubtree
        --             ReleaseTree -> releaseTree
        --             RemoveCopies -> removeCopies
        --             RemoveEdges b -> removeEdges b
        --             RemoveNode -> removeNode
        --             RemoveOthers -> removeOthers
        --             RemovePath -> removePath
        --             RemoveSubtrees -> removeSubtrees
        --             RenameVar x -> renameVar' x
        --             ReplaceNodes x -> replaceNodes' x
        --             ReplaceOther -> replaceOther
        --             ReplaceSubtrees ps ts -> replaceSubtrees' ps ts
        --             ReplaceText x -> replaceText' x
        --             ReplaceVar x u p -> replaceVar x u p
        --             ReverseSubtrees -> reverseSubtrees
        --             SafeEqs -> switchSafe
        --             SetAdmitted block xs -> setAdmitted' block xs
        --             SetCurr msg n -> setCurr msg n
        --             SetStrat s -> do
        --               writeIORef simplStratRef s
        --               modifyIORef stratTermRef $ \stratTerm -> s:stratTerm
        --             Simplify limit sub -> simplify'' limit sub
        --             Simplifying b -> do
        --               writeIORef simplifyingRef b
        --               modifyIORef simplTermRef $ \simplTerm -> b:simplTerm
        --             ShiftPattern -> shiftPattern
        --             ShiftQuants -> shiftQuants
        --             ShiftSubs ps -> shiftSubs' ps
        --             SplitTree -> splitTree
        --             StretchConclusion -> stretch False
        --             StretchPremise -> stretch True
        --             SubsumeSubtrees -> subsumeSubtrees
        --             Theorem b th -> applyTheorem b Nothing th
        --             Transform m -> transformGraph m
        --             UnifySubtrees -> unifySubtrees
        --         modifyIORef proofTPtrRef succ
        --         enterRef
        
      --   -- | Exported by public 'Epaint.Solver' method 'Epaint.checkInSolver'.
      --   checkInSolver' :: Action
      --   checkInSolver' = writeIORef checkingPRef (False,True)
        
      --   -- | Used by 'checkProofF' and 'checkProofT'.
      --   checkProof :: String -> Bool -> String -> Action
      --   checkProof pterm inPainter file = do
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else case parse (list command) $ removeComment 0 pterm of
      --          Just pt -> do
      --            writeIORef checkingRef True
      --            when inPainter $ do
      --              writeIORef checkingPRef (True,False)
      --              (paint&buildPaint) True
      --              showTreePicts
      --            writeIORef proofTermRef pt
      --            writeIORef proofTPtrRef 0
      --            enterRef
      --            trees <- readIORef treesRef
      --            curr <- readIORef currRef
      --            fast <- readIORef fastRef
      --            initialize [] $ showTree fast $ trees!!curr
      --            quit `gtkSet` [ buttonLabel := "quit check" ]
      --            replaceCommandButton quitSignalRef quit setDeriveMode
      --            labGreen' $ proofLoaded file
      --            checkingP <- readIORef checkingPRef
      --            runChecker False
      --          _ -> labRed' $ "There is no proof term in " ++ file ++ "."
        
      --   -- | Called by check proof options in tree menu.
      --   checkProofF :: Bool -> Action
      --   checkProofF inPainter = do
      --     str <- ent `gtkGet` entryText
      --     case words str of
      --          [file,sp] -> do
      --                       let newSpeed = parse pnat sp
      --                           fileT = file++"T"
      --                       when (just newSpeed) $ writeIORef speedRef
      --                                            $ get newSpeed
      --                       pterm <- lookupLibs fileT
      --                       checkProof pterm inPainter fileT
      --          [file]    -> do
      --                       let fileT = file++"T"
      --                       pterm <- lookupLibs fileT
      --                       checkProof pterm inPainter fileT
      --          _         -> labMag "Enter a file name!"

        
      --   -- | Called by check proof options in tree menu.
      --   checkProofT :: Bool -> Action
      --   checkProofT inPainter = do
      --       sp <- ent `gtkGet` entryText
      --       let newSpeed = parse pnat sp
      --       when (just newSpeed) $ writeIORef speedRef $ get newSpeed
      --       pterm <- getTextHere
      --       checkProof pterm inPainter "the text field"
        
      --   -- | Used by many 'Epaint.Solver' methods.
      --   clearTreeposs :: Action
      --   clearTreeposs = setTreeposs $ Replace []
        
      --   -- | Used by 'enterFormulas'', 'enterTerms', 'enterText'' and
      --   -- 'enterRef'. Called by "remove text" button.
      --   clearText :: Action
      --   clearText = do
      --       buffer <- tedit `gtkGet` textViewBuffer
      --       buffer `gtkSet` [ textBufferText := "" ]
        
      --   -- | Used by 'checkForward'. Called by menu item /collapse level/
      --   -- from /graph/ menu.
      --   collapseStep :: Bool -> Action
      --   collapseStep b = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           counter <- readIORef counterRef
      --           part <- readIORef partRef
      --           let t = trees!!curr
      --               p = emptyOrLast treeposs
      --               u = getSubterm1 t p
      --               n = counter 'c'
      --               (v,part') = collapseLoop b (u,part) n
      --               setPr = setProof True False "COLLAPSING THE SUBTREE" [p]
      --           extendPT False False False False $ CollapseStep b
      --           if u == v then do
      --               setPr collapsed
      --               clearTreeposs
      --               resetLevel
      --               writeIORef partRef (id,[])
      --           else do
      --               curr <- readIORef currRef
      --               modifyIORef treesRef
      --                   $ \trees -> updList trees curr $ replace1 t p v
      --               setPr $ levelMsg n
      --               drawCurr'
      --               modifyIORef counterRef $ \counter -> incr counter 'c'
      --               writeIORef partRef part'

        -- collapseVarsCom :: Action
        -- collapseVarsCom = do
        --   trees <- readIORef treesRef
        --   if null trees then labBlue' start
        --   else do
        --        sig <- getSignature
        --        trees <- readIORef treesRef
        --        curr <- readIORef currRef
        --        treeposs <- readIORef treepossRef
        --        let t = trees!!curr
        --            ps = emptyOrAll treeposs
        --            ts = map (collapseVars sig . getSubterm1 t) ps
        --        modifyIORef treesRef $ \trees -> updList trees curr $ fold2 replace1 t ps ts
        --        extendPT False False False False CollapseVars
        --        setProof True False "COLLAPSING THE VARIABLES" ps collapsedVars
        --        drawCurr'

      --   -- | Used by 'checkForward'. Called by menu item /compose pointers/
      --   -- from /graph/ menu. 
      --   composePointers :: Action
      --   composePointers = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           -- sig <- getSignature
      --           let t = trees!!curr
      --               ps = emptyOrAll treeposs
      --               ts = map (composePtrs . getSubterm1 t) ps
      --           writeIORef treesRef
      --               $ updList trees curr $ fold2 replace1 t ps ts
      --           extendPT False False False False ComposePointers
      --           setProof True False "COMBINING THE POINTERS OF THE TREES" ps
      --              pointersComposed
      --           drawCurr'
        
      --   -- | Called by menu items /combine for symbol/ ('True') and
      --   -- /invert for symbol/ ('False') from /axioms/ menu.
      --   compressAxioms :: Bool -> Action
      --   compressAxioms b = do
      --       sig <- getSignature
      --       str <- ent `gtkGet` entryText
      --       trees <- readIORef treesRef
      --       treeposs <- readIORef treepossRef
      --       axioms <- readIORef axiomsRef
      --       x <- if null trees || null treeposs then return str
      --            else do
      --               curr <- readIORef currRef
      --               return $ label (trees!!curr) $ head treeposs
      --       let axs = noSimplsFor [x] axioms
      --       if isPred sig x || isDefunct sig x || isCopred sig x
      --       then
      --           if null axs then labRed' $ noAxiomsFor [x]
      --           else do
      --               varCounter <- readIORef varCounterRef
      --               let (th,k) = compressAll b sig (varCounter "z") axs
      --               modifyIORef theoremsRef $ \theorems -> th:theorems
      --               setZcounter k
      --               enterFormulas' [th]
      --               labGreen' $ newCls "theorems" "the text field"
      --       else
      --           labMag "Enter a predicate, a defined function or a copredicate!"
        
      --   -- | Called by menu item /[combine for symbol].. in entry field/ from
      --   -- /axioms/ menu.
      --   compressClauses :: Action
      --   compressClauses = do
      --       sig <- getSignature
      --       str <- ent `gtkGet` entryText
      --       numberedExps <- readIORef numberedExpsRef
      --       let (exps,b) = numberedExps
      --       case parse intRanges str of
      --           Just (n:ks) | n < length exps ->
      --               if b then do
      --                   varCounter <- readIORef varCounterRef
      --                   let i = varCounter "z"
      --                       (th,k) = combineOne sig i ks (exps!!n) exps
      --                   modifyIORef theoremsRef $ \theorems -> th:theorems
      --                   setZcounter k
      --                   enterFormulas' [th]
      --                   labGreen' $ newCls "theorems" "the text field"
      --               else labMag "Enter clauses into the text field!"
      --           _ -> labMag $ enterNumber ++ " Enter argument positions!"
        
      --   -- | Used by 'checkForward'. Called by menu item /copy/ from menu
      --   -- /transform selection/ or by pressing key @c@ on left label.
      --   copySubtrees :: Action
      --   copySubtrees = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           treeposs <- readIORef treepossRef
      --           curr <- readIORef currRef
      --           let ps = emptyOrAll treeposs
      --               t = trees!!curr
      --           if any null ps then labMag "Select proper subtrees!"
      --           else do
      --               writeIORef treesRef $ updList trees curr $ copy ps t
      --               extendPT False False False False CopySubtrees
      --               let b = all idempotent $ map (label t . init) ps
      --               setProof b False "COPYING THE SUBTREES" ps
      --                                   "The selected tree have been copied."
      --               drawCurr'
      --       where copy (p:ps) t = copy (map (rshiftPos0 p) ps) t3
      --                        where t1 = rshiftPos p t; q = init p; k = last p+1
      --                              F x ts = getSubterm t1 q
      --                              u = F x $ take k ts++V"":drop k ts
      --                              t2 = mapT dec $ replace0 t1 q u
      --                              n = length p-1; p' = incrPos p n
      --                              t3 = replace0 t2 p' $ getSubterm t1 p
      --                              dec x = if isPos x && p' <<= q
      --                                      then mkPos0 $ decrPos q n else x
      --                                      where q = getPos x
      --             copy _ t      = t
        
      --   -- | Used by 'checkForward'. Called by menu item
      --   -- /create induction hypotheses/ from tree menu.
      --   createIndHyp :: Action
      --   createIndHyp = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           treeposs <- readIORef treepossRef
      --           if null treeposs then labMag "Select induction variables!"
      --           else do
      --               curr <- readIORef currRef
      --               let t = trees!!curr
      --                   xs = map (label t) treeposs
      --               sig <- getSignature
      --               if all (isFovar sig) xs &&
      --                  and (zipWith (isAllOrFree t) xs treeposs)
      --               then do
      --                   let f x = V $ if x `elem` xs then '!':x else x
      --                       g f = mkTup $ map f xs
      --                       hyps = mkIndHyps t $ F ">>" [g f,g V]
      --                   modifyIORef treesRef $ \trees -> updList trees curr $
      --                       mkAll (frees sig t `minus` xs) $ t>>>f
      --                   writeIORef indClausesRef hyps
      --                   modifyIORef theoremsRef $ \theorems -> hyps++theorems
      --                   extendPT False False False False CreateIndHyp
      --                   setProof True False "SELECTING INDUCTION VARIABLES"
      --                       treeposs $ indHypsCreated xs
      --                   clearTreeposs
      --                   drawCurr'
      --               else labMag "Select induction variables!"
        
      --   -- | Used by 'checkForward'. Called by create invariant menu items from
      --   -- /transform selection/ menu.
      --   createInvariant :: Bool -> Action
      --   createInvariant b = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           sig <- getSignature
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           let t = trees!!curr
      --               (p,conj,i) = case treeposs of
      --                          [] -> ([],t,0)
      --                          [q] | isFormula sig u -> (q,u,0)
      --                              | notnull q -> ([],t,last q)
      --                                where u = getSubterm t q
      --                          [q,r] | notnull r -> (q,getSubterm t q,last r)
      --                          _ -> ([],t,-1)
      --           if i > -1 && universal sig t p conj
      --           then case preStretch True (isDefunct sig) conj of
      --               Just (f,varps) -> do
      --                   varCounter <- readIORef varCounterRef
      --                   case stretchPrem (varCounter "z") varps conj of
      --                       (F "===>" [F "=" [F _ xs,d],conc],m) -> do
      --                           let lg = length xs
      --                           if i < lg
      --                           then do
      --                               axioms <- readIORef axiomsRef
      --                               case derivedFun sig f xs i lg axioms of
      --                                   -- ax is f(xs)=loop(take i xs++inits)
      --                                   Just (loop,inits,ax)-> do
      --                                       let n = m+length inits
      --                                           (as,bs) = splitAt (lg-i) xs
      --                                           cs = map newVar [m..n-1]
      --                                           u = mkInvs b loop as bs
      --                                                   cs inits d conc
      --                                       curr <- readIORef currRef
      --                                       modifyIORef treesRef $ \trees ->
      --                                           updList trees curr
      --                                               $ replace t p u
      --                                       setZcounter n
      --                                       extendPT False False False False $
      --                                                CreateInvariant b
      --                                       setProof True False
      --                                           (creatingInvariant str ax)
      --                                           [p] $ invCreated b
      --                                       clearTreeposs; drawCurr'
      --                                   _ -> labRed' $ f
      --                                           ++ " is not a derived function."
      --                           else labRed' $ wrongArity f lg
      --                       _ -> labRed' concCallsPrem
      --               _ -> notStretchable "The premise"
      --           else labRed' $ noApp str
      --       where str = if b then "HOARE INVARIANT CREATION"
      --                   else "SUBGOAL INVARIANT CREATION"
        
      --   -- | Creates sub menus for /specification/ menu. Used by 'buildSolve1'.
      --   createSpecMenu :: Bool -> Menu -> Action
      --   createSpecMenu add m = do
      --       mapM_ (mkButF m cmd) specfiles1
      --       mkBut m (if add then "from file (Return)" else "from file")
      --               $ getFileAnd cmd
      --       when add
      --         $ Haskell.void $ mkBut m "from text field" $ addSpecWithBase ""
      --       subMenu <- mkSub m "more"
      --       mapM_ (mkButF subMenu cmd) specfiles2
      --       subMenu <- mkSub subMenu "more"
      --       mapM_ (mkButF subMenu cmd) specfiles3
      --       return ()
      --       where cmd = if add then addSpecWithBase else loadText True

      --   createSub mode menu = do
      --     mkBut menu "from file" $ getFileAnd $ addClauses mode
      --     mkBut menu "from text field" $ addClauses mode ""
      --     when (mode == 0) $ do
      --       mkBut menu "from entry field" addNamedAxioms; return ()
      --     solve <- readIORef solveRef
      --     other <- getSolver solve
      --     mkBut menu ("from "++ other) $ do tree <- (solve&getTree)
      --                                       case tree of
      --                                           Just t
      --                                             -> addTheorems t other
      --                                           _ -> labBlue' $ startOther other
      --     return ()

        -- -- | Used by 'checkForward'. Called by /decompose atom/ menu item
        -- -- from /transform selection/ menu.
        -- decomposeAtom :: Action
        -- decomposeAtom = do
        --     trees <- readIORef treesRef
        --     if null trees then labBlue' start
        --     else do
        --         curr <- readIORef currRef
        --         treeposs <- readIORef treepossRef
        --         let t = trees!!curr
        --             p = emptyOrLast treeposs
        --             b = polarity True t p
        --             F x [l,r] = getSubterm1 t p
        --             finish u = do
        --                 curr <- readIORef currRef
        --                 modifyIORef treesRef $ \trees ->
        --                     updList trees curr $ replace1 t p u
        --                 extendPT False False False False DecomposeAtom
        --                 setProof True False "DECOMPOSING THE ATOM" [p]
        --                     atomDecomposed
        --                 clearTreeposs; drawCurr'
        --         sig <- getSignature
        --         case x of "=" | b -> finish $ splitEq sig True l r
        --                   "=/=" | not b -> finish $ splitEq sig False l r
        --                   _ -> labRed' atomNotDecomposed
        
delay :: a -> a
delay = id
        
      --   -- | Used by 'drawPointer', 'drawShrinked', 'drawThis', 'moveTree' and
      --   -- 'setInterpreter'.
      --   draw :: TermSP -> Action
      --   draw ct = do
      --       sizeState <- readIORef sizeStateRef
      --       treeposs <- readIORef treepossRef

      --       clear canv
      --       writeIORef ctreeRef $ Just ct
      --       let (_,_,maxx,maxy) = minmax $ foldT (bds sizeState) ct
      --           -- Expander2: Size does not fit. Added size to avoid crop.
      --           sizefix = 100
      --           size@(_,h) = (max 100 (maxx+sizefix),max 100 (maxy+sizefix))
      --       writeIORef canvSizeRef size
      --       -- TODO check
      --       when (h > 100) $ tedit `gtkSet` [ widgetHeightRequest := 0]
      --       canv `gtkSet` [ canvasSize := size]
      --       if null treeposs then drawTree ct ct black blue []
      --       else drawTree2 ct ct black blue red darkGreen [] treeposs
      --       -- when (notnull treeDir)
      --       --     $ delay 100 $ saveGraphD' treeDir =<< readIORef picNoRef
      --     where bds (n,w) (a,(x,y)) pss = (x-x',y-y'):(x+x',y+y'):concat pss
      --                          where (x',y') = (nodeWidth w a,n`div`2)
        
      --   {- |
      --       Draws a line from position @(x, y)@ to the position of the root node
      --       of the tree @ct@ in color @color@. The font size that has been set
      --       is substracted from the line. This is used by 'drawTree' and
      --       'drawTree2' to draw the edges of a function graph.
      --   -}
      --   drawArc :: Pos -> TermSP -> Color -> Action
      --   drawArc (x,y) ct color =
      --       when (not $ isPos a) $ do
      --           font <- readIORef fontRef

      --           (above,below) <- getTextHeight canv font
      --           line canv [(x,y+below),(x',y'-above)]
      --               $ lineOpt{ lineFill = color }
      --           return ()
      --       where (a,(x',y')) = root ct
        
      --   {- |
      --       Draw current tree. Used by all functions that (re-)draw the current
      --       tree. Called by font size button on change. Exported by public
      --       'Epaint.Solver' method 'Epaint.drawCurr'.
      --   -}
      --   drawCurr' :: Action
      --   drawCurr' = do
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef

      --       drawThis (trees!!curr) [] ""
        
      --   -- | Called if 'horBut' or 'treeSlider' is changed.
      --   drawNewCurr :: Action
      --   drawNewCurr = do
      --       trees <- readIORef treesRef
      --       when (notnull trees) drawCurr'
        
      --   -- | Draws a single text node. Used by 'drawTree', 'drawTree2',
      --   -- 'moveNode', 'moveSubtree' and 'catchNode'.
      --   drawNode :: (String, Pos) -> Color -> Action
      --   drawNode (a,p) c =
      --     if isPos a then done
      --     else do
      --       font <- readIORef fontRef
      --       canvasText canv p textOpt{ textFont = Just font
      --                                    , textFill = c'
      --                                    , textJustify = CenterAlign
      --                                    }
      --               (delQuotes a)
      --       done
      --    where c' = case parse colPre a of Just (c,_) -> c; _ -> c
        
      --   -- | Used by 'drawTree'.
      --   drawPointer :: TermSP -> Color -> [Int] -> Pos -> [Int] -> Action
      --   drawPointer ct ac p mid@(x,y) q = do
      --     font <- readIORef fontRef
      --     (above,below) <- getTextHeight canv font
      --     let arc = [(x1,y1+below),(x,y-above)]
      --         target = (x',if y <= y' then y'-above else y'+above)
      --     if q `elem` allPoss ct then do
      --        draw (arc++[mid,target]) $ f $ if q << p then orange else magenta
      --        done
      --     else do draw (arc++[(x-10,y+10)]) $ f red; done    -- dangling pointer
      --     where (_,(x1,y1)) = label ct $ init p              -- pred of source
      --           (_,(x',y')) = label ct q                     -- target
      --           f color = if ac == white then white else color
      --           draw path color = (canv&line) path lineOpt{ lineFill = color
      --                                                     , lineArrow = Just Last
      --                                                     , lineSmooth = True
      --                                                     }

      --   -- | Called on change by 'verBut'.
      --   drawShrinked :: Action
      --   drawShrinked = do
      --       trees <- readIORef treesRef
      --       corner <- readIORef cornerRef
      --       spread <- readIORef spreadRef
      --       ctree <- readIORef ctreeRef
      --       when (notnull trees)
      --           $ draw $ shrinkTree (snd corner) (snd spread) $ get ctree
        
      --   -- | Used by 'releaseSubtree', 'setSubtrees' and 'catchSubtree'.
      --   drawSubtrees :: Action
      --   drawSubtrees = do
      --       Just ct <- readIORef ctreeRef
      --       treeposs <- readIORef treepossRef
      --       oldTreeposs <- readIORef oldTreepossRef

      --       drawTree3 ct ct black blue red darkGreen [] treeposs
      --           $ minis (<<=) $ treeposs `join` oldTreeposs
        
      --   -- | Used by 'applySubstTo'', 'drawCurr'', 'showCoords',
      --   -- 'showCycleTargets', 'showGlb', 'showNumbers', 'showPolarities',
      --   -- 'showPositions', 'showPreds', 'showSucs', 'showSyms' and 'showVals'.
      --   drawThis :: TermS -> [[Int]] -> String -> Action
      --   drawThis t ps col = do
      --       showState <- readIORef showStateRef
      --       treeposs <- readIORef treepossRef
      --       maxHeap <- getMaxHeap
      --       font <- readIORef fontRef
      --       spread <- readIORef spreadRef
      --       corner <- readIORef cornerRef

      --       let qs = if showState then [] else treeposs
      --           u = cutTree maxHeap (colHidden t) ps col qs
      --       sizes@(_,w) <- mkSizes canv font $ nodeLabels u
      --       writeIORef sizeStateRef sizes
      --       draw $ coordTree w spread corner u
      --       return ()

      --   {- |
      --       @drawTree ct ct nc ac []@ draws the nodes of @ct@ in color @nc@ and
      --       the arcs of @ct@ in color @ac@. Used by 'draw', 'drawTree2',
      --       'moveSubtree' and 'releaseSubtree'.
      --   -}
      --   drawTree :: TermSP -- ^ ct
      --            -> TermSP -- ^ ct
      --            -> Color -- ^ nc
      --            -> Color -- ^ ac
      --            -> [Int]
      --            -> Action
      --   drawTree (F cx@(_,q) cts) ct nc ac p = do
      --       drawNode cx nc
      --       drawTrees cts $ succsInd p cts
      --       where drawTrees (ct':cts) (p:ps) = do
      --                       drawArc q ct' ac
      --                       drawTree ct' ct nc ac p
      --                       drawTrees cts ps
      --             drawTrees _ _ = return ()
      --   drawTree (V cx@(a,q)) ct nc ac p
      --       | isPos a = drawPointer ct ac p q $ getPos a
      --       | True    = drawNode cx nc

      --   {- |
      --       @drawTree2 ct ct nc ac nc' ac' [] qs@ draws the nested ones among
      --       the subtrees at positions @qs@ alternately in (text,line)-colors
      --       (@nc@,@ac@) and (@nc'@,@ac'@). Used by 'draw' and 'drawTree3'.
      --   -}
      --   drawTree2 :: TermSP -- ^ ct
      --             -> TermSP -- ^ ct
      --             -> Color -- ^ nc
      --             -> Color -- ^ ac
      --             -> Color -- ^ nc'
      --             -> Color -- ^ ac'
      --             -> [Int]
      --             -> [[Int]] -- ^ qs
      --             -> Action
      --   drawTree2 ct@(V _) ct0 nc ac nc' ac' p qs
      --       | p `elem` qs = drawTree ct ct0 nc' ac' p
      --       | True      = drawTree ct ct0 nc ac p
      --   drawTree2 (F cx@(_,q) cts) ct nc ac nc' ac' p qs
      --       | p `elem` qs = do
      --           drawNode cx nc'
      --           drawTrees2 q cts nc' ac' nc ac ps
      --       | True      = do
      --           drawNode cx nc
      --           drawTrees2 q cts nc ac nc' ac' ps
      --               where ps = succsInd p cts
      --                     drawTrees2 q (ct':cts) nc ac nc' ac' (p:ps) = do
      --                                   drawArc q ct' ac
      --                                   drawTree2 ct' ct nc ac nc' ac' p qs
      --                                   drawTrees2 q cts nc ac nc' ac' ps
      --                     drawTrees2 _ _ _ _ _ _ _ = return ()

      --   {- |
      --       @drawTree3 ct .. rs@ applies @drawTree2 ct ..@ to the subtrees of
      --       @ct@ at positions @rs@. Used by 'drawSubtrees'.
      --   -}
      --   drawTree3 :: TermSP -- ^ ct
      --             -> TermSP -- ^ ct
      --             -> Color -- ^ nc
      --             -> Color -- ^ ac
      --             -> Color -- ^ nc'
      --             -> Color -- ^ ac'
      --             -> [Int]
      --             -> [[Int]] -- ^ qs
      --             -> [[Int]] -- ^ rs
      --             -> Action
      --   drawTree3 ct' ct nc ac nc' ac' p qs rs
      --       | any (<<= p) rs
      --           = drawTree2 ct' ct nc ac nc' ac' p qs
      --   drawTree3 (V _) _ _ _ _ _ _ _ _ = return ()
      --   drawTree3 (F (_,q) cts) ct nc ac nc' ac' p qs rs
      --       = drawTrees3 q cts nc ac nc' ac' ps
      --       where ps = succsInd p cts
      --             drawTrees3 q (ct':cts) nc ac nc' ac' (p:ps) = do
      --                   drawTree3 ct' ct nc ac nc' ac' p qs rs
      --                   drawTrees3 q cts nc ac nc' ac' ps
      --             drawTrees3 _ _ _ _ _ _ _ = return ()
        
enterFormulas' :: [TermS] -> Base.Action
enterFormulas' _ = done

      --   -- Show terms in textfield. Used by 'showTerms'.
      --   enterTerms :: [TermS] -> Action
      --   enterTerms ts = do
      --       checking <- readIORef checkingRef
      --       when (not checking) $ do
      --           clearText
      --           addText $ lines $ showSum ts
      --           writeIORef numberedExpsRef (ts,False)
        
enterText' :: String -> Base.Action
enterText' _ = done
        
        
      --   {- | 
      --       Show pointer in textfield. Used by 'checkBackward', 'checkForward',
      --       'checkProof', 'setDeriveMode' and 'showProofTerm'. Exported by
      --       public 'Epaint.Solver' method 'Epaint.enterRef'.
      --   -}
      --   enterRef :: Action
      --   enterRef = do clearText
      --                 proofTPtr <- readIORef proofTPtrRef
      --                 proofTerm <- readIORef proofTermRef
      --                 addText $ lines $ show
      --                         $ addPtr proofTPtr proofTerm
      --       where addPtr 0 (step:pt) = POINTER step:pt
      --             addPtr n (step:pt) = step:addPtr (n-1) pt
      --             addPtr _ pt        = pt
        
      --   {- |
      --       Show tree in canvas. Used by 'initCanvas', 'parseText',
      --       'randomTree', 'showEqsOrGraph' and 'showRelation'. Exported by
      --       public 'Epaint.Solver' method 'Epaint.enterTree'.
      --   -}
      --   enterTree' :: Bool -> TermS -> Action
      --   enterTree' b t = do
      --       simplifying <- readIORef simplifyingRef
      --       refuting <- readIORef refutingRef
      --       fast <- readIORef fastRef

      --       setTime
      --       writeIORef formulaRef b
      --       writeIORef treeModeRef "tree"
      --       writeIORef treesRef [t]
      --       modifyIORef counterRef $ \counter -> upd counter 't' 1
      --       writeIORef proofTermRef []
      --       writeIORef proofTPtrRef 0
      --       clearTreeposs
      --       sig <- getSignature
      --       makeTrees sig
      --       initialize (sigVars sig t) $ showTree fast t
      --       setTreesFrame []
      --       labGreen' $ objects++str
      --    where objects = if b then "Formulas" else "Terms"
      --          str = " are displayed on the canvas."
        
      --   -- | Used by 'checkForward'. Called by "evaluate" menu item
      --   -- from "transform selection" menu.
      --   evaluateTrees :: Action
      --   evaluateTrees = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           sig <- getSignature
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           let t = trees!!curr
      --               ps = emptyOrAll treeposs
      --               ts = map (evaluate sig . getSubterm1 t) ps
      --           writeIORef treesRef
      --               $ updList trees curr $ fold2 replace1 t ps ts
      --           extendPT False False False False EvaluateTrees
      --           setProof True False "EVALUATING THE TREES" ps evaluated
      --           drawCurr'
        
      --   -- | Called by expand menu items from
      --   -- "graph" menu.
      --   expandTree :: Bool -> Action
      --   expandTree b = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           limit <- ent `gtkGet` entryText
      --           expandTree' b $ case parse pnat limit of Just n -> n; _ -> 0
        
      --   -- | Used by 'expandTree' and 'checkForward'.
      --   expandTree' :: Bool -> Int -> Action
      --   expandTree' b limit = do
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       treeposs <- readIORef treepossRef
      --       let t = trees!!curr
      --           ps = emptyOrAll treeposs
      --           f u p = replace0 u p
      --                   $ (if b then expandOne else expand) limit t p
      --       writeIORef treesRef $ updList trees curr $ moreTree $ foldl f t ps
      --       extendPT False False False False $ ExpandTree b limit
      --       setProof True False "EXPANDING THE SUBTREES" ps $
      --           expanded ++ circlesUnfolded limit
      --       clearTreeposs; drawCurr'

      --   extendPT m r s t step = do
      --     checking <- readIORef checkingRef
      --     when (not checking) $ do
      --        matchTerm <- readIORef matchTermRef
      --        matching <- readIORef matchingRef
      --        refuteTerm <- readIORef refuteTermRef
      --        refuting <- readIORef refutingRef
      --        simplTerm <- readIORef simplTermRef
      --        simplifying <- readIORef simplifyingRef
      --        stratTerm <- readIORef stratTermRef
      --        simplStrat <- readIORef simplStratRef
      --        let cm = m && (null matchTerm  || head matchTerm /= matching)
      --            cr = r && (null refuteTerm || head refuteTerm /= refuting)
      --            cs = s && (null simplTerm  || head simplTerm /= simplifying)
      --            ct = t && (null stratTerm  || head stratTerm /= simplStrat)
      --        let steps = (if cm then [Matching matching]        else []) ++
      --                    (if cr then [Refuting refuting]        else []) ++
      --                    (if cs then [Simplifying simplifying]  else []) ++
      --                     if ct then [SetStrat simplStrat,step] else [step]
      --        when cm $ writeIORef matchTermRef $ matching:matchTerm
      --        when cr $ writeIORef refuteTermRef $ refuting:refuteTerm
      --        when cs $ writeIORef simplTermRef $ simplifying:simplTerm
      --        when ct $ writeIORef stratTermRef $ simplStrat:stratTerm
      --        proofTPtr <- readIORef proofTPtrRef
      --        modifyIORef proofTermRef
      --          $ \proofTerm -> take proofTPtr proofTerm ++ steps
      --        proofTerm <- readIORef proofTermRef
      --        writeIORef proofTPtrRef $ length proofTerm

      --   -- | Used by 'applyDisCon'.
      --   finishDisCon :: Maybe Int
      --                -> Bool
      --                -> Bool
      --                -> [TermS]
      --                -> TermS
      --                -> [TermS]
      --                -> TermS
      --                -> [[Int]]
      --                -> [Int]
      --                -> [[Int]]
      --                -> Sig
      --                -> String
      --                -> Action
      --   finishDisCon k b c ts reduct redices t ps pred qs sig msg = do
      --       varCounter <- readIORef varCounterRef
      --       case applyMany b c ts reduct redices t ps pred qs sig varCounter of
      --           Just (t,vc) -> do
      --               maybeSimplify sig t
      --               writeIORef varCounterRef vc
      --               setProof True True msg ps $ thApplied k
      --               clearTreeposs; drawCurr'
      --           _ -> labRed' $ notUnifiable k
        
      --   -- | Used by 'releaseSubtree' and 'releaseTree'.
      --   finishRelease :: TermS -> [Int] -> Step -> Action
      --   finishRelease t p step = do
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef

      --       writeIORef treesRef $ updList trees curr t
      --       extendPT False False False False step
      --       clearTreeposs; drawCurr'
      --       setProof False False "REPLACING THE SUBTREE" [p]
      --                            "The selected tree has been replaced."
        
      --   -- | Used by 'checkForward'. Called by /flatten (co-)Horn clause/ menu
      --   -- item from /transform selection/ menu.
      --   flattenImpl :: Action
      --   flattenImpl = do
      --       trees <- readIORef treesRef
      --       formula <- readIORef formulaRef
      --       if null trees || not formula
      --       then labMag "Load and parse a Horn or co-Horn clause!"
      --       else do
      --           sig <- getSignature
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           varCounter <- readIORef varCounterRef
      --           let t = trees!!curr
      --               xs = if null treeposs then defuncts sig t
      --                    else filter (isDefunct sig) $ map (label t) treeposs
      --               (u,n) = flatten (varCounter "z") xs t
      --           writeIORef treesRef $ updList trees curr u
      --           setZcounter n
      --           extendPT False False False False FlattenImpl
      --           setProof True False "FLATTENING" [[]] flattened
      --           clearTreeposs; drawCurr'
        
      --   -- | Used by 'setDeriveMode' and 'stopRun''. Called by keypress @Up@ on
      --   -- left label ('lab').  Exported by public 'Epaint.Solver' method
      --   -- 'Epaint.forwProof'.
      --   forwProof' :: Action
      --   forwProof' = do
      --       checking <- readIORef checkingRef
      --       if checking then checkForward
      --       else do
      --           proofPtr <- readIORef proofPtrRef
      --           proofTerm <- readIORef proofTermRef
      --           proof <- readIORef proofRef
      --           let k = proofPtr+1
      --               lg = length proofTerm
      --           if k >= length proof then labMag endOfProof
      --           else do
      --               writeIORef proofPtrRef k
      --               changeState k []
      --           proofTPtr <- readIORef proofTPtrRef
      --           when (proofTPtr < lg) $ do
      --               let n = search deriveStep $ drop proofTPtr proofTerm
      --               modifyIORef proofTPtrRef $ \proofTPtr
      --                   -> if just n then proofTPtr + get n+1 else lg
        
      --   -- | Called by /generalize/ menu item
      --   -- from /transform selection/ menu.
      --   generalize :: Action
      --   generalize = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           let t = trees!!curr
      --               p = emptyOrLast treeposs
      --               cl = getSubterm t p
      --           sig <- getSignature
      --           if isTerm sig cl then labRed' "Select a formula!"
      --           else do
      --               str <- ent `gtkGet` entryText
      --               numberedExps <- readIORef numberedExpsRef
      --               let (exps,b) = numberedExps
      --               case parse intRanges str of
      --                   Just ns | all (< length exps) ns ->
      --                       if b then generalizeEnd t p cl $ map (exps!!) ns
      --                       else labMag "Enter formulas into the text field!"
      --                   _ -> do
      --                       str <- getTextHere
      --                       case parseE (implication sig) str of
      --                           Correct cl' -> generalizeEnd t p cl [cl']
      --                           p -> incorrect p str illformedF
        
      --   -- | Used by 'checkForward'. 
      --   generalize' :: [TermS] -> Action
      --   generalize' cls = do
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       treeposs <- readIORef treepossRef
      --       let t = trees!!curr
      --           p = emptyOrLast treeposs
      --       generalizeEnd t p (getSubterm t p) cls
        
      --   -- | Used by 'generalize' and 'generalize''.
      --   generalizeEnd :: TermS -> [Int] -> TermS -> [TermS] -> Action
      --   generalizeEnd t p cl cls = do
      --       curr <- readIORef currRef
      --       modifyIORef treesRef $ \trees ->
      --           updList trees curr $ replace t p $ f $ cl:cls
      --       enterFormulas' cls
      --       extendPT False False False False $ Generalize cls
      --       setProof True False "GENERALIZING" [p] generalized
      --       clearTreeposs; drawCurr'
      --       where f = if polarity True t p then mkConjunct else mkDisjunct
        
      --   -- Get string from entry field ('ent'). Exported by public
      --   -- 'Epaint.Solver' method 'Epaint.getEntry'.
      --   getEntry' :: Request String
      --   getEntry' = ent `gtkGet` entryText
        
      --   -- | Apply action @act@ on filename entered in entry field 'ent'. Used
      --   -- by all load and store operation on files.
      --   getFileAnd :: (String -> Action) -> Action
      --   getFileAnd act = do -- Note [Filechooser]
      --       file <- ent `gtkGet` entryText
      --       if null file then labMag "Enter a file name!" else act file
        
      --   {- Note [Filechooser]
      --   ~~~~~~~~~~~~~~~~~~~~~
      --   This should be replaced by usage of the GTK+ file chooser. But seperated
      --   operations are needed for open and save dialogs. As a result all
      --   @getFileAnd@ function calls must be identified as load or store
      --   operation.
      --   -}
        
      --   -- | Exported by public 'Epaint.Solver' method 'Epaint.getFont'.
      --   getFont' :: Request FontDescription
      --   getFont' = readIORef fontRef
        
      --   -- | Used by 'showSubtreePicts' and 'showTreePicts'.
      --   getInterpreter = do
      --     sig <- getSignature
      --     picEval <- readIORef picEvalRef
      --     return $ case picEval of 
      --                   "tree"               -> widgetTree sig
      --                   "matrices"           -> searchPic matrix
      --                   "matrix solution"    -> solPic sig matrix
      --                   "linear equations"   -> linearEqs
      --                   "level partition"    -> searchPic (partition 0)
      --                   "preord partition"   -> searchPic (partition 1)
      --                   "heap partition"     -> searchPic (partition 2)
      --                   "hill partition"     -> searchPic (partition 3)
      --                   "alignment"          -> searchPic alignment
      --                   "palindrome"         -> searchPic alignment
      --                   "dissection"         -> searchPic dissection
      --                   _                    -> searchPic (widgets sig black)
        
      --   -- | Get value of 'treeSize' scale. Used by 'drawThis'.
      --   getMaxHeap :: Request Int
      --   getMaxHeap = truncate <$> (treeSize `gtkGet` rangeValue)
        
      --   getPicNo' = readIORef picNoRef

getSignature :: Request Sig
getSignature sST = do
    (ps,cps,cs,ds,fs,hs) <- sST `Gtk.get` symbolsRef
    (sts,labs,ats,tr,trL,va,vaL) <- sST `Gtk.get` kripkeRef
    simplRules <- sST `Gtk.get` simplRulesRef
    transRules <- sST `Gtk.get` transRulesRef
    (block,xs) <- sST `Gtk.get` constraintsRef
    safe <- sST `Gtk.get` safeRef

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
      simpls' = simplRules; transitions' = transRules
      states' = sts; atoms' = ats; labels' = labs;
      trans' = tr; transL' = trL; value' = va; valueL' = vaL
      safeEqs' = safe
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

      --   -- | Returns name of this solver object. Exported by public
      --   -- 'Epaint.Solver' method 'Epaint.getSolver'.
      --   getSolver' :: Request String
      --   getSolver' = return this
        
getTextHere :: Request String
getTextHere sST = sST `Gtk.get` _teditTextRef
        
      --   -- | Exported by public 'Epaint.Solver' method 'Epaint.getTree'.
      --   getTree' :: Request (Maybe TermS)
      --   getTree' = do
      --       trees <- readIORef treesRef
      --       if null trees then do
      --           labBlue' start
      --           return Nothing
      --       else do
      --           curr <- readIORef currRef
      --           return $ Just $ trees!!curr
        
      --   -- | Called by button "hide" ('hideBut').
      --   hideOrShow :: Action
      --   hideOrShow = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           drawCurr'
      --           modifyIORef showStateRef not
      --           showState <- readIORef showStateRef
      --           hideBut `gtkSet`
      --               [ buttonLabel := if showState then "hide" else "show" ]
        
      --   -- | Minimize solver window. Exported by public 'Epaint.Solver' method
      --   -- 'Epaint.iconify'.
      --   iconify' :: Action
      --   iconify' = windowIconify win
        
incorrect :: Parse TermS -> String -> String -> Base.Action
incorrect _ _ error = labRed' error
        
      --   -- | Called on keypress @Left@ or @Right@ while left label ('lab') is
      --   -- active.
      --   incrCurr :: Bool -> Action
      --   incrCurr b = do
      --       curr <- readIORef currRef
      --       let next = if b then curr+1 else curr-1
      --       trees <- readIORef treesRef
      --       setCurr newCurr $ next `mod` length trees
        
      --   -- | Lower or raise a number in the entry field by one. Called by
      --   -- buttons /entry-1/ ('minusBut') and /entry+1/ ('plusBut').
      --   incrEntry :: Bool -> Action
      --   incrEntry b = do
      --       str <- ent `gtkGet` entryText
      --       let k = parse nat str; f = entrySetText ent . show
      --       if b then case k of
      --           Just n -> f $ n+1
      --           _ -> ent `gtkSet` [ entryText := "0" ]
      --       else case k of
      --           Just n | n > 0 -> f $ n-1
      --           _ -> ent `gtkSet` [ entryText := "" ]
        
      --   -- | Used by all menu items /[show graph].. in painter/ and
      --   -- /[show matrix].. of (...)/ from /graph/ menu.
      --   initCanvas :: Action
      --   initCanvas = do
      --       trees <- readIORef treesRef
      --       when (null trees)
      --           $ enterTree' False $ F "see painter" []
      --           -- delay 100 $ return ()
        
      --   -- | Used by 'checkProof', 'enterTree'' and 'setNewTrees''.
      --   initialize :: [String] -> String -> Action
      --   initialize vars str = do
      --     symbols@(ps,cps,cs,ds,fs,hs) <- readIORef symbolsRef
      --     (nps,ncps) <- readIORef newPredsRef
      --     let (ps',cps') = (ps `minus` nps,cps `minus` ncps)
      --     constraints@(block,xs) <- readIORef constraintsRef
      --     treeMode <- readIORef treeModeRef
      --     trees <- readIORef treesRef
      --     varCounter <- readIORef varCounterRef
      --     safe <- readIORef safeRef
      --     joined <- readIORef joinedRef
      --     indClauses <- readIORef indClausesRef

      --     writeIORef symbolsRef (ps',cps',cs,ds,fs,hs)
      --     modifyIORef axiomsRef $ \axioms -> removeTerms axioms indClauses
      --     modifyIORef theoremsRef
      --         $ \theorems -> removeTerms theorems indClauses
      --     writeIORef indClausesRef []
      --     writeIORef newPredsRef nil2
      --     writeIORef solPositionsRef []
      --     writeIORef varCounterRef
      --       $ iniVC $ ps'++cps'++cs++ds++fs++map fst hs++vars
      --     setSubst' (V,[])
      --     writeIORef partRef (id,[])
      --     writeIORef permsRef $ \n -> [0..n-1]
      --     varCounter <- readIORef varCounterRef
      --     perms <- readIORef permsRef
      --     writeIORef proofRef
      --         [ ProofElem
      --             { peMsg = "Derivation of\n\n"++str++
      --                                 '\n':'\n':admitted block xs++
      --                                 '\n':equationRemoval safe
      --             , peMsgL = ""
      --             , peTreeMode = treeMode
      --             , peTrees = trees
      --             , peTreePoss = []
      --             , peCurr = 0
      --             , peVarCounter = varCounter
      --             , pePerms = perms
      --             , peNewPreds = nil2
      --             , peSolPositions = []
      --             , peSubstitution = (V,[])
      --             , peConstraints = constraints
      --             , peJoined = joined
      --             , peSafe = safe
      --             }
      --         ]
      --     writeIORef proofPtrRef 0
      --     writeIORef counterRef $ const 0
      --     writeIORef currRef 0
        
      --   -- | Called by menu item /instantiate/ from /transform selection/ menu
      --   instantiate :: Action
      --   instantiate = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           sig <- getSignature
      --           str <- ent `gtkGet` entryText
      --           let str' = removeComment 0 str
      --           case parseE (term sig) str' of
      --               Correct t -> do
      --                   treeposs <- readIORef treepossRef
      --                   replaceQuant t (emptyOrLast treeposs)
      --                   labRed' notInstantiable
      --               p -> incorrect p str' illformedT
        
      --   -- | Exported by public 'Epaint.Solver' method 'Epaint.isSolPos'.
      --   isSolPos' :: Int -> Request Bool
      --   isSolPos' n = elem n <$> readIORef solPositionsRef
        
      --   -- | Called by menu item /Kleene axioms for symbols/ from menu /axioms/
      --   kleeneAxioms :: Action
      --   kleeneAxioms = do
      --       sig <- getSignature
      --       str <- ent `gtkGet` entryText
      --       trees <- readIORef treesRef
      --       treeposs <- readIORef treepossRef
      --       curr <- readIORef currRef
      --       let x = if null trees || null treeposs then str
      --               else label (trees!!curr) $ head treeposs
      --           copred = isCopred sig x
      --           f = if copred then mkHornLoop else mkCoHornLoop
      --       if copred || isPred sig x  then do
      --           axioms <- readIORef axiomsRef
      --           let axs = noSimplsFor [x] axioms
      --           if null axs then labRed' $ noAxiomsFor [x]
      --           else do
      --               varCounter <- readIORef varCounterRef
      --               symbols <- readIORef symbolsRef
      --               let i = V $ 'i':show (varCounter "i")
      --                   (axs',k) = f sig x axs i $ varCounter "z"
      --                   (ps,cps,cs,ds,fs,hs) = symbols
      --                   ps' = x:(x++"Loop"):ps
      --               writeIORef symbolsRef (ps',cps`minus1`x,cs,ds,fs,hs)
      --               modifyIORef axiomsRef
      --                   $ \axioms -> axioms `minus` axs `join` axs'
      --               modifyIORef varCounterRef
      --                   $ \varCounter -> upd (incr varCounter "i") "z" k
      --               enterFormulas' axs'
      --               labGreen' $ if copred then newPredicate str1 str2 x
      --                           else newPredicate str2 str1 x
      --       else labMag "Enter either a predicate or a copredicate!"
      --       where (str1,str2) = ("copredicate","predicate")
        
      --   -- | Shows @str@ in the left label ('lab') and set the label background
      --   -- to blue. Exported by public 'Epaint.Solver' method 'Epaint.labBlue'.
      --   labBlue' :: String -> Action
      --   labBlue' str = labColor str blueback

      --   -- | Shows @str@ in left label ('lab') and set the label background to
      --   -- @col@. Used by 'labBlue'', 'labColorToPaint', 'labGreen'', 'labMag'
      --   -- and  'labRed''.
      --   labColor :: String -> Background -> Action
      --   labColor str col = do
      --       lab `gtkSet` [ labelText := str ]
      --       setBackground lab col
        
      --   -- | Used by 'checkBackward', 'narrowPar', 'narrowSubtree', 'setCurr',
      --   -- 'setProof', 'simplifyPar' and 'simplifySubtree'.
      --   labColorToPaint :: Background -> String -> Action
      --   labColorToPaint col str = do
      --       labColor str col
      --       labSolver paint str
        
      --   {- unused
      --   labColorToPaintT col str = do
      --       (time0,_) <-  readIORef timesRef
      --       if time0 == 0 then labColor str col
      --       else do
      --           time <- getCPUTime
      --           writeIORef timesRef (0,300)
      --           labColor (str++'\n':show (mkSecs time0 time)++" sec") col
      --       labSolver paint str
      --   -}
        
labGreen' :: String -> Base.Action
labGreen' _ = done
        
      --   -- | Shows @str@ in the left label and set the label background to
      --   -- magenta.
      --   labMag :: String -> Action
      --   labMag = flip labColor magback
        
labRed' :: String -> Base.Action
labRed' = assertFailure . ("Expander error message: "++)
        
      --   -- | Lookup @file@ and load content into text area.
      --   -- Called by all menu items in "load text" submenu from tree menu and
      --   -- "specification" menu.
      --   loadText :: Bool -> FilePath -> Action
      --   loadText b file = do
      --     str <- lookupLibs file
      --     if null str then labRed' $ file ++ " is not a file name."
      --                 else if b then do
      --                             enterText' str
      --                             labGreen' $ loaded file
      --                           else do
      --                             solve <- readIORef solveRef
      --                             solve&bigWin
      --                             (solve&enterText) str
        
      --   -- | Used by 'applyInd', 'applyTheorem', 'enterTree'', 'narrowLoop',
      --   -- 'narrowPar', 'replaceSubtrees'', 'replaceVar', 'simplify''' and
      --   -- 'splitTree'.
      --   makeTrees :: Sig -> Action
      --   makeTrees sig = do
      --     treeMode <- readIORef treeModeRef
      --     trees <- readIORef treesRef
      --     case treeMode of
      --      "tree"    -> do
      --                   joined <- readIORef joinedRef
      --                   if joined then return ()
      --                   else case trees of
      --                        [t@(F "|" _)]   -> do
      --                                           writeIORef solPositionsRef []
      --                                           split (mkSummands t) "summand"
      --                        [t@(F "&" _)]   -> do
      --                                           writeIORef solPositionsRef []
      --                                           split (mkFactors t) "factor"
      --                        [t@(F "<+>" _)] -> split (mkTerms t) "term"
      --                        _               -> return ()
      --      "summand" -> if null ts then actMore [mkFalse] "tree"
      --                              else actMore ts treeMode
      --                   where ts = mkSummands $ F "|" trees
      --      "factor"  -> if null ts then actMore [mkTrue] "tree"
      --                              else actMore ts treeMode
      --                   where ts = mkFactors $ F "&" trees
      --      _         -> if null ts then actMore [unit] "tree"
      --                              else actMore ts treeMode
      --                   where ts = mkTerms $ F "<+>" trees

      --    where split = actMore . map (dropnFromPoss 1)
      --          actMore ts mode = do
      --               newTrees <- readIORef newTreesRef
      --               curr <- readIORef currRef
      --               counter <- readIORef counterRef
      --               formula <- readIORef formulaRef
      --               trees <- readIORef treesRef

      --               writeIORef newTreesRef $ newTrees || lg /= length trees
      --               writeIORef currRef $ curr `mod` lg
      --               writeIORef treesRef ts
      --               writeIORef counterRef $ upd counter 't' lg
      --               writeIORef treeModeRef $ if lg == 1 then "tree" else mode
      --               writeIORef solPositionsRef
      --                   $ if formula then solPoss sig ts
      --                                else []
      --               where lg = length ts
        
      --   -- | Used by 'applyInd', 'applyTheorem', 'finishDisCon', 'narrowPar',
      --   -- 'replaceSubtrees'' and 'replaceVar'.
      --   maybeSimplify :: Sig -> TermS -> Action
      --   maybeSimplify sig t = do
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       simplifying <- readIORef simplifyingRef

      --       writeIORef treesRef $ updList trees curr
      --           $ if simplifying then simplifyIter sig t else t
        
      --   -- | Used by 'checkForward'. Called by menu item "minimize" from
      --   -- "specification" menu.
      --   minimize :: Action
      --   minimize = do
      --     sig <- getSignature
      --     simplRules <- readIORef simplRulesRef
      --     when (notnull (sig&states)) $ do
      --        let (states,tr,trL,va,vaL) = mkQuotient sig
      --        writeIORef kripkeRef
      --           $ (states,(sig&atoms),(sig&labels),tr,trL,va,vaL)
      --        changeSimpl "states" $ mkList states
      --        extendPT False False False False Minimize
      --        setProof True False "MINIMIZING THE KRIPKE MODEL" [] $ minimized 
      --                            $ length states
        
      --   modifyEqs m = do
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else do
      --          sig <- getSignature
      --          trees <- readIORef treesRef
      --          curr <- readIORef currRef
      --          treeposs <- readIORef treepossRef
      --          let t = trees!!curr
      --              p:ps = emptyOrAll treeposs
      --              u = getSubterm1 t p
      --              act p u = do
      --                  writeIORef treesRef $ updList trees curr $ replace1 t p u
      --                  extendPT False False False False $ ModifyEqs m
      --                  setProof False False "MODIFYING THE EQUATIONS" [p] $
      --                                       eqsModified
      --                  clearTreeposs; drawCurr'
      --          case m of 0 -> case parseEqs u of
      --                              Just eqs -- from equations to equations
      --                                -> do
      --                                   let t = connectEqs eqs
      --                                   firstClick <- readIORef firstClickRef
      --                                   if firstClick
      --                                      then do
      --                                        act p t
      --                                        writeIORef substitutionRef
      --                                          (const t,[])
      --                                        writeIORef firstClickRef False
      --                                      else do
      --                                        (f,_) <- readIORef substitutionRef
      --                                        let u = eqsToGraphs $ f ""
      --                                        act p u
      --                                        writeIORef substitutionRef (V,[])
      --                                        writeIORef firstClickRef True
      --                              _ -> labMag "Select iterative equations!"
      --                    1 -> case parseEqs u of
      --                              Just eqs -> act p $ eqsTerm
      --                                                $ autoEqsToRegEqs sig eqs
      --                              _ -> labMag "Select iterative equations!"
      --                    2 -> case parseEqs u of
      --                              Just eqs | just v -> act [] $ get v
      --                                         where v = substituteVars t eqs ps
      --                              _ -> labMag instantiateVars
      --                    _ -> case parseIterEq u of
      --                             Just (Equal x t) | just e
      --                               -> act p $ mkEq (V x) $ showRE $ fst $ get e
      --                                  where e = solveRegEq sig x t
      --                             _ -> labMag "Select a regular equation!"

      --   {- |
      --       Moves a node of a tree on the canvas. Click and hold the right
      --       mouse button over a node. Move the node to its new destination. When
      --       the mouse button is released the node will be inserted into the new
      --       position. It is initialized with 'catchNode' on mouse button press
      --       and finished with 'releaseNode' on mouse button release. Called by
      --       mouse move actions while pressing right button.
            
      --       See 'moveSubtree' and 'moveTree'.
      --   -}
      --   moveNode :: Pos -> Action
      --   moveNode (x, y) = do
      --       treeposs <- readIORef treepossRef

      --       if null treeposs then labMag "Select a target node!"
      --       else do
      --           node <- readIORef nodeRef
      --           ctree <- readIORef ctreeRef

      --           let f p a col1 col2 = drawNode a $ if last treeposs <<= p
      --                                              then col1 else col2
      --           case node of Just (z,p) -> do f p z red black; return ()
      --                        _ -> return ()
      --           -- (x,y) <- adaptPos pt
      --           case getSubtree (get ctree) x y of
      --               Just (p,cu) -> do
      --                   let a = root cu
      --                   f p a cyan magenta
      --                   writeIORef nodeRef $ Just (a,p)
      --               _ -> writeIORef nodeRef Nothing
        
      --   {- |
      --       Moves a subtree of a tree on the canvas. Click and hold the left
      --       mouse button over a subtree. Move the subtree to its new
      --       destination. When the mouse button is released the subtree will be
      --       inserted into the new position. It is initialized with
      --       'catchSubtree' on mouse button press and finished with
      --       'releaseSubtree' on mouse button release. Called by
      --       mouse move actions while pressing left button.
            
      --       See 'moveNode' and 'moveTree'.
      --   -}
      --   moveSubtree :: Pos -> Action
      --   moveSubtree pt@(x1,y1) = do
      --       isSubtree <- readIORef isSubtreeRef
      --       penpos <- readIORef penposRef

      --       when (just isSubtree && just penpos) $ do
      --           Just ct <- readIORef ctreeRef
      --           Just cu <- readIORef subtreeRef
      --           treeposs <- readIORef treepossRef
      --           firstMove <- readIORef firstMoveRef
      --           node <- readIORef nodeRef

      --           let (x0,y0) = get penpos
      --               cu' = transTree2 (x1-x0,y1-y0) cu
      --               p = last treeposs
      --           if firstMove && not (get isSubtree)
      --               then drawTree cu ct black blue p
      --               else drawTree cu ct white white p
      --           writeIORef firstMoveRef False
      --           writeIORef penposRef $ Just pt
      --           writeIORef subtreeRef $ Just cu'
      --           when (just node) $ drawNode (fst $ get node) black
      --           drawTree cu' ct red darkGreen p
      --           -- (x,y) <- adaptPos pt
      --           suptree <- readIORef suptreeRef
      --           case getSubtree (get suptree) x1 y1 of
      --               Just (p,cu) -> do
      --                   let a = root cu
      --                   drawNode a magenta
      --                   writeIORef nodeRef $ Just (a,p)
      --               _ -> writeIORef nodeRef Nothing
        
      --   {- |
      --       Moves the tree on the canvas. Click and hold the middle
      --       mouse button over the tree. Move the tree to its new
      --       destination. When the mouse button is released the tree will be
      --       inserted into the new position. It is initialized with
      --       'catchTree' on mouse button press and finished with
      --       'releaseTree' on mouse button release. Called by
      --       mouse move actions while pressing middle button.
            
      --       See 'moveNode' and 'moveSubtree'.
      --   -}
      --   moveTree :: Pos -> Action
      --   moveTree p@(x,y) = do
      --       isSubtree <- readIORef isSubtreeRef

      --       case isSubtree of
      --           Just True -> moveSubtree p
      --           Just _ -> do
      --               penpos <- readIORef penposRef

      --               when (just penpos) $ do
      --                   ctree <- readIORef ctreeRef

      --                   let (x0,y0) = get penpos
      --                       q@(i,j) = (x-x0,y-y0)
      --                   draw $ transTree2 q $ get ctree
      --                   modifyIORef cornerRef
      --                       $ \corner -> (fst corner+i,snd corner+j)
      --                   writeIORef penposRef $ Just p
      --           _ -> return ()
        
      --   -- | Called by 'narrowBut'. Exported by public 'Epaint.Solver' method
      --   -- 'Epaint.narrow'.
      --   narrow' :: Action
      --   narrow' = do
      --       trees <- readIORef treesRef

      --       if null trees then labBlue' start
      --       else do
      --           str <- ent `gtkGet` entryText
      --           case parse pnat str of
      --               Just limit -> narrow'' limit True
      --               _ -> case parse pnatSecs str of
      --                       Just n -> do
      --                           modifyIORef timesRef $ \times -> (fst times,n)
      --                           narrow'' (-1) True
      --                       _ -> narrow'' 1 False
        
      --   -- | Used by 'checkForward' and 'narrow''.
      --   narrow'' :: Int -> Bool -> Action
      --   narrow'' limit sub = do
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       formula <- readIORef formulaRef
      --       constraints <- readIORef constraintsRef
      --       axioms <- readIORef axiomsRef
      --       treeposs <- readIORef treepossRef

      --       sig <- getSignature
      --       writeIORef ruleStringRef
      --           $ if formula then "NARROWING" else "REWRITING"
      --       modifyIORef counterRef $ \counter -> upd counter 'd' 0
      --       let t = trees!!curr
      --           cls = filter (not . isSimpl) axioms
      --       if null treeposs then do
      --           extendPT True True True True $ Narrow limit True
      --           setTime
      --           narrowLoop sig cls 0 limit
      --       else if sub then do setTime; narrowSubtree t sig cls limit
      --            else do
      --               extendPT True True True True $ Narrow 0 False
      --               narrowOrRewritePar t sig (Just $ -1) cls False treeposs
        
      --   -- | Used by 'narrow'''.
      --   narrowLoop :: Sig -> [TermS] -> Int -> Int -> Action
      --   narrowLoop sig cls k limit
      --           | limit == 0 = finish k
      --           | True       = do
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       treeMode <- readIORef treeModeRef
      --       formula <- readIORef formulaRef
      --       simplifying <- readIORef simplifyingRef

      --       let t = trees!!curr
      --       case treeMode of
      --           "tree"
      --               | formula ->
      --                   if isSol sig t then do
      --                       writeIORef solPositionsRef [0]
      --                       finishNar k
      --                   else do
      --                       joined <- readIORef joinedRef
      --                       writeIORef solPositionsRef []
      --                       if joined then mkStep t $ finish k
      --                       else case trees of [F "|" ts] -> split ts "summand"
      --                                          [F "&" ts] -> split ts "factor"
      --                                          _ -> mkStep t $ finish k
      --               | True -> do
      --                   joined <- readIORef joinedRef
      --                   if joined then mkStep t $ finish k
      --                   else case trees of [F "<+>" ts] -> split ts "term"
      --                                      _ -> mkStep t $ finish k
      --           "summand"
      --               | simplifying -> case t of F "|" ts -> actMore ts treeMode
      --                                          F "&" ts -> actMore ts "factor"
      --                                          _ -> actMore [t] "tree"
      --               | null ts -> actMore [mkFalse] "tree"
      --               | True    -> actMore ts treeMode
      --                           where t = simplifyIter sig $ mkDisjunct trees
      --                                 ts = mkSummands $ F "|" trees
      --           "factor"
      --               | simplifying -> case t of F "|" ts -> actMore ts "summand"
      --                                          F "&" ts -> actMore ts treeMode
      --                                          _ -> actMore [t] "tree"
      --               | null ts -> actMore [mkTrue] "tree"
      --               | True    -> actMore ts treeMode
      --                           where t = simplifyIter sig $ mkConjunct trees
      --                                 ts = mkFactors $ F "&" trees
      --           _
      --               | simplifying -> case t of F "<+>" ts -> actMore ts "term"
      --                                          _ -> actMore [t] "tree"
      --               | null ts -> actMore [unit] "tree"
      --               | True    -> actMore ts treeMode
      --                   where t = simplifyIter sig $ mkSum trees
      --                         ts = mkTerms $ F "<+>" trees
      --    where finish k = makeTrees sig >> finishNar k
      --          finishNar k = do
      --               ruleString <- readIORef ruleStringRef
      --               formula <- readIORef formulaRef
      --               solPositions <- readIORef solPositionsRef
      --               setProof True True ruleString [] $
      --                   finishedNar formula k ++ solved solPositions
      --               setTreesFrame []
      --          mkStep t stop = do
      --               formula <- readIORef formulaRef
      --               narrowStep sig cls limit t proceed stop formula
      --          proceed t n vc = do
      --               curr <- readIORef currRef
      --               writeIORef varCounterRef vc
      --               modifyIORef counterRef $ \counter -> upd counter 'd' k'
      --               modifyIORef treesRef $ \trees -> updList trees curr t
      --               narrowLoop sig cls k' (limit-n)
      --               where k' = k+n
      --          split = actMore . map (dropnFromPoss 1)
      --          actMore ts mode = do
      --               trees <- readIORef treesRef
      --               curr <- readIORef currRef
      --               formula <- readIORef formulaRef

      --               let b n newTrees = newTrees || lg /= length trees
      --                                           || curr /= n
      --                   searchRedex (n:ns) = do
      --                       modifyIORef newTreesRef $ b n
      --                       writeIORef currRef n
      --                       mkStep (trees!!n) $ searchRedex ns
      --                   searchRedex _ = do
      --                       modifyIORef newTreesRef $ b 0
      --                       writeIORef currRef 0
      --                       finish k
      --                   ks = drop curr is++take curr is
      --               writeIORef treesRef ts
      --               modifyIORef counterRef $ \counter -> upd counter 't' lg
      --               writeIORef treeModeRef $ if lg == 1 then "tree" else mode
      --               writeIORef solPositionsRef
      --                   $ if formula then solPoss sig ts else []
      --               solPositions <- readIORef solPositionsRef
      --               searchRedex $ ks `minus` solPositions
      --               where lg = length ts; is = indices_ ts

      --   -- used by applyTheorem and narrow' 
      --   narrowOrRewritePar :: TermS -> Sig -> Maybe Int -> [TermS] -> Bool
      --                      -> [[Int]] -> Action
      --   narrowOrRewritePar t sig k cls saveRedex ps = do
      --       varCounter <- readIORef varCounterRef
      --       formula <- readIORef formulaRef

      --       let f g = g t sig k cls saveRedex [] ps [] varCounter
      --       if formula || ps `subset` boolPositions sig t then f narrowPar
      --                                                     else f rewritePar
        
      --   -- | Used by 'rewritePar'.
      --   narrowPar :: TermS
      --             -> Sig
      --             -> Maybe Int
      --             -> [TermS]
      --             -> Bool
      --             -> [TermS]
      --             -> [[Int]]
      --             -> [[Int]]
      --             -> (String -> Int)
      --             -> Action
      --   narrowPar t sig k cls saveRedex used (p:ps) qs vc =
      --       if p `notElem` positions t --- || isVarRoot sig redex
      --       then narrowPar t sig k cls saveRedex used ps qs vc
      --       else do
      --           matching <- readIORef matchingRef
      --           axioms <- readIORef axiomsRef
      --           rand <- readIORef randRef
      --           let b = matching > 1
      --               apply at r = applyAxs cls1 cls3 axioms redex at r sig vc' b
      --               applyR at r = applyAxsR cls1 cls3 axioms rand redex at r sig
      --                                        vc' b
      --           if isDefunct sig sym then case atomPosition sig t p of
      --               Just (q,at,r) ->
      --                   if even matching then case apply at r of
      --                       (Backward reds vc,used') ->
      --                           proceed q mkDisjunct reds used' vc
      --                       (MatchFailure str,_) -> labMsg str
      --                       _ -> next
      --                   else case applyR at r of
      --                       (Backward reds vc,used',rand')-> do
      --                           writeIORef randRef rand'
      --                           proceed q mkDisjunct reds used' vc
      --                       (MatchFailure str,_,_) -> labMsg str
      --                       _ -> next
      --               _ -> next
      --           else
      --               if notnull p && isTerm sig redex then do
      --                   let q = init p
      --                   case (getSubterm t q,last p) of
      --                       (at@(F "->" [_,_]),0) ->
      --                           if even matching then case apply at [0] of
      --                               (Backward reds vc,used')
      --                                -> proceed q mkDisjunct reds used' vc
      --                               (MatchFailure str,_) -> labMsg str
      --                               _ -> next
      --                           else case applyR at [0] of
      --                               (Backward reds vc,used',rand') -> do
      --                                   writeIORef randRef rand'
      --                                   proceed q mkDisjunct reds used' vc
      --                               (MatchFailure str,_,_) -> labMsg str
      --                               _ -> next
      --                       _ -> next
      --               else
      --                   if isPred sig sym || isCopred sig sym then
      --                       if even matching then case apply redex [] of
      --                           (Backward reds vc,used') ->
      --                               proceed p mkDisjunct reds used' vc
      --                           (Forward reds vc,used') ->
      --                               proceed p mkConjunct reds used' vc
      --                           (MatchFailure str,_) ->
      --                               labMsg str
      --                           _ -> next
      --                       else case applyR redex [] of
      --                           (Backward reds vc,used',rand') -> do
      --                               writeIORef randRef rand'
      --                               proceed p mkDisjunct reds used' vc
      --                           (Forward reds vc,used',rand') -> do
      --                               writeIORef randRef rand'
      --                               proceed p mkConjunct reds used' vc
      --                           (MatchFailure str,_,_) -> labMsg str
      --                           _ -> next
      --                   else next
      --    where redex = getSubterm t p; sym = getOp redex
      --          cls1 = filterClauses sig redex cls
      --          cls2 = if saveRedex then map copyRedex cls1 else cls1
      --          (cls3,vc') = renameApply cls2 sig t vc
      --          proceed q f reds used' vc =
      --                    narrowPar (replace t q $ f reds) sig k cls saveRedex
      --                              (used `join` used') ps (p:qs) vc
      --          next = narrowPar t sig k cls saveRedex used ps qs vc
      --          labMsg = labColorToPaint magback
      --   narrowPar _ _ k _ _ [] _ _ _ =
      --       labColorToPaint magback $ subtreesNarrowed k
      --   narrowPar t sig k _ _ used _ qs vc = do
      --       writeIORef varCounterRef vc
      --       maybeSimplify sig t
      --       makeTrees sig
      --       finish $ thApplied k
      --       where finish msg = do
      --               modifyIORef counterRef $ \counter -> upd counter 'd' 1
      --               setProof True True (applied b str) qs msg
      --               setTreesFrame []
      --             b = length used == 1
      --             str = showFactors used
        
      --   -- | Used by 'narrowSubtree' and 'narrowLoop'.
      --   narrowStep :: Sig
      --              -> [TermS]
      --              -> Int
      --              -> TermS
      --              -> (TermS -> Int -> (String -> Int) -> Action)
      --              -> Action
      --              -> Bool
      --              -> Action
      --   narrowStep sig cls limit t proceed stop nar = do
      --       times <- readIORef timesRef

      --       time <- getCPUTime
      --       let (time0,timeout) = times
      --           m = if limit < 0 then 1 else limit
      --       if mkSecs time0 time > timeout then stop
      --       else do
      --           matching <- readIORef matchingRef
      --           varCounter <- readIORef varCounterRef
      --           simplifying <- readIORef simplifyingRef
      --           axioms <- readIORef axiomsRef

      --           if even matching then do
      --               refuting <- readIORef refutingRef

      --               let (u,n,vc) = applyLoop t m varCounter cls axioms sig nar
      --                                         matching refuting simplifying
      --               if n == 0 then stop else proceed u n vc
      --           else do
      --               rand <- readIORef randRef
      --               let (u,n,vc,rand') = applyLoopRandom rand t m varCounter cls
      --                                        axioms sig nar matching simplifying
      --               writeIORef randRef rand'
      --               if n == 0 then stop else proceed u n vc
        
      --   -- | Used by 'narrow'''.
      --   narrowSubtree :: TermS -> Sig -> [TermS] -> Int -> Action
      --   narrowSubtree t sig cls limit = do
      --       treeposs <- readIORef treepossRef

      --       let p = emptyOrLast treeposs
      --           u = getSubterm t p
      --           nar = isFormula sig u
      --           sn = subtreesNarrowed (Nothing :: Maybe Int)
      --           (str,str') = if nar then ("NARROWING",sn)
      --                               else ("REWRITING",sn++onlyRew)
      --           proceed u n vc = do
      --               simplifying <- readIORef simplifyingRef
      --               curr <- readIORef currRef

      --               let v = if simplifying then simplifyIter sig u else u
      --               modifyIORef treesRef
      --                   $ \trees -> updList trees curr $ replace t p v
      --               writeIORef varCounterRef vc
      --               extendPT True True True True $ Narrow limit True
      --               modifyIORef counterRef $ \counter -> upd counter 'd' n
      --               setProof True True str [p]
      --                   $ appliedToSub (map toLower str) n
      --               setTreesFrame []
      --           stop = labColorToPaint magback str'
      --       narrowStep sig cls limit u proceed stop nar
        
      --   -- | Called by menu item /negate for symbols/ from /axioms/ menu or
      --   -- by pressing @n@ on left label ('lab').
      --   negateAxioms :: Action
      --   negateAxioms = do
      --       str <- ent `gtkGet` entryText
      --       sig <- getSignature
      --       trees <- readIORef treesRef
      --       treeposs <- readIORef treepossRef
      --       curr <- readIORef currRef
      --       symbols <- readIORef symbolsRef
      --       let xs = if null trees || null treeposs then words str
      --                else map (label $ trees!!curr) treeposs
      --           (ps,cps,_,_,_,_) = symbols
      --           ps1 = filter (isPred sig) $ meet xs ps
      --           cps1 = filter (isCopred sig) $ meet xs cps
      --       negateAxioms' ps1 cps1
        
      --   -- | Used by 'checkForward' and 'negateAxioms'.
      --   negateAxioms' :: [String] -> [String] -> Action
      --   negateAxioms' ps1 cps1 = do
      --       symbols <- readIORef symbolsRef
      --       axioms <- readIORef axiomsRef
      --       let (ps,cps,cs,ds,fs,hs) = symbols
      --           xs = ps1++cps1
      --           axs1 = noSimplsFor xs axioms
      --           ps2 = map mkComplSymbol cps1
      --           cps2 = map mkComplSymbol ps1
      --           str = complsAdded xs
      --           msg = init str ++ " (see the text field)."
      --       if null axs1 then
      --           labRed' $ "There are no axioms for "++ showStrList xs
      --       else do
      --           writeIORef symbolsRef
      --               (ps `join` ps2,cps `join` cps2,cs,ds,fs,hs)
      --           sig <- getSignature
      --           let axs2 = map (mkComplAxiom sig) axs1
      --           modifyIORef axiomsRef (`join` axs2)
      --           enterFormulas' axs2
      --           trees <- readIORef treesRef
      --           if null trees then labGreen' msg
      --           else do
      --               extendPT False False False False $ 
      --                        NegateAxioms ps1 cps1
      --               setProof True False str [] msg
        
      --   -- | Shows error message "@str@ cannot be stretched." on left label.
      --   -- Used by 'applyClause', 'applyCoinduction', 'applyInduction',
      --   -- 'createInvariant' and 'stretch'.
      --   notStretchable :: String -> Action
      --   notStretchable str = labRed' $ str ++ " cannot be stretched."
        
parseConjects :: Sig -> FilePath -> String -> Action
parseConjects sig file conjs sST =
    case parseE (implication sig) conjs of
        Correct t -> do
            let ts = if isConjunct t then subterms t else [t]
            sST `Gtk.set` [conjectsRef :~ \conjects -> conjects `join` ts]
            labGreen' $ newCls "conjectures" file
        p -> incorrect p conjs illformed
        
      --   -- | Used by 'addSigMap' and 'addSigMapT'.
      --   parseSigMap :: FilePath -> String -> Action
      --   parseSigMap file str = do
      --       signatureMap <- readIORef signatureMapRef
      --       sig <- getSignature
      --       sig' <- getSignatureR =<< readIORef solveRef
      --       case parseE (sigMap signatureMap sig sig') str of
      --           Correct f -> do
      --               writeIORef signatureMapRef f
      --               labGreen' $ newSigMap file
      --           Partial f rest -> do
      --               enterText' $ showSignatureMap f $ check rest
      --               labRed' illformedSM
      --           _ -> do
      --               enterText' str
      --               labRed' illformedSM
        
        
        -- -- | Parses the text from text area and show it as a graph on the
        -- -- canvas. Called by button /parse up/ ('upBut') or by pressing the
        -- -- @Up@ on active text area ('tedit').
        -- parseText :: Action
        -- parseText = do
        --     numberedExps <- readIORef numberedExpsRef

        --     str <- ent `gtkGet` entryText
        --     let (exps, b) = numberedExps
        --     case parse intRanges str of
        --         Just ns | all (< length exps) ns -> do
        --             ent `gtkSet` [ entryText := "" ]
        --             let exps' = map (exps !!) ns
        --             if b then enterTree' True $ mkConjunct exps'
        --                  else enterTree' False $ mkSum exps'
        --         _ -> do
        --             str <- getTextHere
        --             sig <- getSignature
        --             case parseE (implication sig) str of
        --                 Correct t -> enterTree' True t
        --                 _ -> case parseE (term sig) str of
        --                     Correct cl -> enterTree' False cl
        --                     p -> incorrect p str illformed
        
parseTerms :: Sig -> FilePath -> String -> Action
parseTerms sig file ts sST =  case parseE (term sig) ts of
    Correct t -> do
        let ts = if isSum t then subterms t else [t]
        sST `Gtk.set` [termsRef :~ \terms -> ts `join` terms]
        labGreen' $ newCls "terms" file
    p -> incorrect p ts illformed
        
      --   -- | Display the graph from canvas ('canv') as a text representation in
      --   -- the text area ('tedit'). Called by button /parse down/ ('downBut') or
      --   -- by pressing the @Down@ key on the active text area ('tedit').
      --   parseTree :: Action
      --   parseTree = do
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       fast <- readIORef fastRef
      --       treeposs <- readIORef treepossRef
      --       formula <- readIORef formulaRef

      --       if null trees then labBlue' start
      --       else do
      --           let t = trees!!curr
      --               enter _ _ [t] = enterText' $ showTree fast t
      --               enter b "" ts = if b then enter True "&" ts
      --                                    else enter False "<+>" ts
      --               enter _ x ts  = enterText' $ showTree fast $ F x ts
      --           if null treeposs
      --           then do enter formula "" [t]; labGreen' treeParsed
      --           else do
      --               sig <- getSignature
      --               let ts@(u:us) = map (getSubterm1 t) treeposs
      --                   b = isFormula sig u
      --               if null $ tail treeposs
      --                   then do enter b "" [u]; labGreen' treeParsed
      --                   else if all (== b) $ map (isFormula sig) us
      --                           then do
      --                               x <- ent `gtkGet` entryText
      --                               enter b x $ addNatsToPoss ts
      --                               labGreen' $ init treeParsed ++ "s."
      --                           else labMag "Select either formulas or terms!"
        
      --   permuteSubtrees = do
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else do
      --          curr <- readIORef currRef
      --          treeposs <- readIORef treepossRef
      --          let t = trees!!curr
      --              p = emptyOrLast treeposs
      --          case getSubterm1 t p of
      --               F x ts@(_:_:_) -> do
      --                    let n = length ts
      --                    modifyIORef permsRef
      --                      $ \perms -> upd perms n $ nextPerm $ perms n
      --                    perms <- readIORef permsRef
      --                    modifyIORef treesRef
      --                      $ \trees -> updList trees curr $ replace1 t p $ F x
      --                                                $ map (ts!!) $ perms n
      --                    extendPT False False False False PermuteSubtrees
      --                    setProof (permutative x) False
      --                             "PERMUTING THE SUBTREES" [p] permuted
      --                    drawCurr'
      --               _ -> done

      --   -- | Used by 'checkForward'. Called by menu item /random labels/ from
      --   -- /transform selection/ menu or by pressing shift + L on active left
      --   -- lable ('lab').
      --   randomLabels :: Action
      --   randomLabels = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           str <- ent `gtkGet` entryText
      --           if null str then labRed' "Enter labels!"
      --           else do
      --               curr <- readIORef currRef
      --               rand <- readIORef randRef
      --               let (t,rand') = labelRandomly rand str $ trees!!curr
      --               writeIORef treesRef $ updList trees curr t
      --               writeIORef randRef rand'
      --               extendPT False False False False RandomLabels
      --               setProof False False "LABELING NODES" []
      --                   "The nodes have been labeled randomly."
      --               drawCurr'
        
      --   -- | Used by 'checkForward'. Called by menu item /random tree/ from
      --   -- /transform selection/ menu or by pressing shift + @T@ on active left
      --   -- lable ('lab').
      --   randomTree :: Action
      --   randomTree = do
      --       str <- ent `gtkGet` entryText
      --       if null str then labRed' "Enter labels!"
      --       else do
      --           rand <- readIORef randRef
      --           let (t,rand') = buildTreeRandomly rand str
      --           enterTree' False t
      --           writeIORef randRef rand'
      --           extendPT False False False False RandomTree
      --           delay $ setProof False False "GENERATING A TREE" []
      --                           "A tree has been generated randomly."
        
      --   -- | Called by menu item /re-add/ from /specification/ menu.
      --   reAddSpec :: Action
      --   reAddSpec = do
      --       specfiles <- readIORef specfilesRef
      --       if null specfiles then labRed' iniSpec
      --       else removeSpec >> addSpecWithBase (head specfiles)
        
      --   -- | Called by button /redraw/ ('clearS').
      --   redrawTree :: Action
      --   redrawTree = do
      --       treeposs <- readIORef treepossRef
      --       when (notnull treeposs) $ do
      --           writeIORef restoreRef True
      --           clearTreeposs
      --       drawCurr'

      --   reduceRegExp mode = do
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else do
      --          sig <- getSignature
      --          trees <- readIORef treesRef
      --          curr <- readIORef currRef
      --          treeposs <- readIORef treepossRef
      --          let ps = emptyOrAll treeposs
      --              t = trees!!curr
      --              ts = map (getSubterm t) ps
      --              es = map (parseRE sig) ts
      --              f (Just (e,_)) = showRE $ g e
      --              g = case mode of 0 -> distribute
      --                               1 -> reduceLeft
      --                               _ -> reduceRight
      --          if any nothing es then labMag "Select regular expressions!"
      --          else do
      --               modifyIORef treesRef
      --                 $ \trees -> updList trees curr
      --                             $ fold2 replace0 t ps $ map f es
      --               extendPT False False False False $ ReduceRE mode
      --               setProof False False "REDUCING THE REGULAR EXPRESSIONS"
      --                                    ps regReduced
      --               clearTreeposs; drawCurr'

      --   -- | Finishes the 'moveNode' action. Called on right mouse button
      --   -- release on active canvas.
      --   releaseNode :: Action
      --   releaseNode = do
      --     treeposs <- readIORef treepossRef

      --     if null treeposs then labMag "Select a target node!"
      --     else do
      --         node <- readIORef nodeRef
      --         let p = last treeposs
      --         case node of
      --              Just (_,q) | notnull q && p /= q -> do
      --                  trees <- readIORef treesRef
      --                  curr <- readIORef currRef

      --                  let t = replace (trees!!curr) q $ mkPos p
      --                  if p `elem` allPoss t
      --                      then do
      --                          modifyIORef treesRef
      --                              $ \trees -> updList trees curr t
      --                          let r = init q
      --                          extendPT False False False False ReleaseNode
      --                          setProof False False "INSERTING AN ARC" [r,p] $
      --                                   arcInserted r p
      --                      else labRed' dangling
      --                  drawCurr'
      --                  writeIORef nodeRef Nothing
      --                  canv `gtkSet` [ canvasCursor := LeftPtr ]
      --              _ -> labMag "Select a non-root position!"
        
      --   -- | Finishes the 'moveSubtree' action. Called on left mouse button
      --   -- release on active canvas.
      --   releaseSubtree :: Action
      --   releaseSubtree = do
      --       isSubtree <- readIORef isSubtreeRef

      --       when (just isSubtree) $ do
      --           node <- readIORef nodeRef
      --           treeposs <- readIORef treepossRef
      --           subtree <- readIORef subtreeRef
      --           ctree <- readIORef ctreeRef

      --           let source = last treeposs
      --               finish = do
      --                   drawTree (get subtree) (get ctree)
      --                       white white source
      --                   drawSubtrees
      --           case node of
      --               Just (_,target) -> do
      --                   curr <- readIORef currRef
      --                   trees <- readIORef treesRef

      --                   let t = trees!!curr
      --                       u = getSubterm1 t source
      --                   if source == target then finish
      --                   else do
      --                       beep 
      --                       when (null target) $ changeMode u
      --                       replaceQuant u target
      --                       finishRelease
      --                           (replace2 t source t target)
      --                           source ReleaseSubtree
      --               _ -> do
      --                   setTreeposs $ Remove source
      --                   finish
      --           resetCatch
        
      --   -- | Finishes the 'moveTree' action. Called on middle mouse button
      --   -- release on active canvas.
      --   releaseTree :: Action
      --   releaseTree = do
      --       isSubtree <- readIORef isSubtreeRef

      --       case isSubtree of
      --           Just True -> do
      --               trees <- readIORef treesRef
      --               curr <- readIORef currRef
      --               treeposs <- readIORef treepossRef
      --               varCounter <- readIORef varCounterRef
      --               substitution <- readIORef substitutionRef
      --               node <- readIORef nodeRef

      --               let t = trees!!curr
      --                   p = last treeposs
      --                   u = getSubterm1 t p
      --                   z = 'z':show (varCounter "z")
      --                   (g,dom) = substitution
      --                   f t = finishRelease t p ReleaseTree
      --               case node of
      --                   Just (_,q) -> when (p /= q) $ do
      --                       beep
      --                       f $ replace1 t q u
      --                   _ -> f $ replace t p $ V z
      --               setSubst' (g `andThen` for u z, dom `join1` z)
      --               modifyIORef varCounterRef
      --                   $ \varCounter -> incr varCounter "z"
      --               resetCatch
      --           Just False -> do
      --               writeIORef penposRef Nothing
      --               canv `gtkSet` [canvasCursor := LeftPtr ]
      --               resetCatch
      --           _ -> return ()
        
      --   -- | Called by menu item /[remove in entry field].. for symbols/ from
      --   -- /axioms/ menu.
      --   removeAxiomsFor :: Action
      --   removeAxiomsFor = do
      --       str <- ent `gtkGet` entryText
      --       trees <- readIORef treesRef
      --       treeposs <- readIORef treepossRef
      --       axioms <- readIORef axiomsRef
      --       curr <- readIORef currRef
      --       let xs = if null trees || null treeposs then words str
      --                else mkSet $ map (label $ trees!!curr) treeposs
      --           axs = clausesFor xs axioms
      --       if null axs then labRed' $ noAxiomsFor xs
      --       else do
      --           writeIORef axiomsRef $  removeTerms axioms axs
      --           axioms <- readIORef axiomsRef
      --           writeIORef simplRulesRef $ trips ["==","<==>"] axioms
      --           writeIORef transRulesRef $ trips ["->"] axioms
      --           labGreen' $ axsRemovedFor xs
        
      --   -- | Called by menu item /remove in entry field/ from /axioms/ menu
      --   -- and menu items /[remove theorems].. in entry field/,
      --   -- /[remove conjects].. in entry field/
      --   -- and /[show conjects].. in entry field/ from menu /theorems/.
      --   removeClauses :: Int -> Action
      --   removeClauses n = do
      --       str <- ent `gtkGet` entryText
      --       numberedExps <- readIORef numberedExpsRef
      --       let (exps,_) = numberedExps
      --       case parse intRanges str of
      --           Just ns | all (< length exps) ns -> do
      --               let ts = map (exps!!) ns
      --               case n of
      --                 0 -> do
      --                     modifyIORef axiomsRef
      --                         $ \axioms -> removeTerms axioms ts
      --                     axioms <- readIORef axiomsRef
      --                     writeIORef simplRulesRef $ trips ["==","<==>"] axioms
      --                     writeIORef transRulesRef $ trips ["->"] axioms
      --                     showAxioms True
      --                 1 -> do
      --                     modifyIORef theoremsRef
      --                         $ \theorems -> removeTerms theorems ts
      --                     showTheorems True
      --                 2 -> do
      --                     modifyIORef conjectsRef
      --                         $ \conjects -> removeTerms conjects ts
      --                     showConjects
      --                 _ -> do
      --                     modifyIORef termsRef
      --                         $ \terms -> removeTerms terms ts
      --                     showTerms
      --           _ -> labMag enterNumbers
        
      --   -- | Called by menu item /remove conjects/ from menu /theorems/.
      --   removeConjects :: Action
      --   removeConjects = do
      --       writeIORef conjectsRef []
      --       writeIORef indClausesRef []
      --       labGreen' $ "There are neither conjectures nor "
      --           ++ "induction hypotheses."
        
      --   -- | Used by 'checkForward'. Called by menu item /remove copies/
      --   -- from menu /graph/.
      --   removeCopies :: Action
      --   removeCopies = do
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else do
      --         curr <- readIORef currRef
      --         treeposs <- readIORef treepossRef
      --         let t = trees!!curr
      --             p = emptyOrLast treeposs
      --         if isHidden t || null p
      --         then labMag selectSub
      --         else do
      --             writeIORef treesRef
      --                 $ updList trees curr $ removeAllCopies t p
      --             extendPT False False False False RemoveCopies
      --             setProof True False "REMOVING COPIES OF THE SUBTREE" [p]
      --                      copiesRemoved
      --             clearTreeposs; drawCurr'
        
      --   -- | Used by 'checkForward'. Called by menu items /split cycles/ and
      --   -- /more tree arcs/ from menu /graph/.
      --   removeEdges :: Bool -> Action
      --   removeEdges b = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           curr <- readIORef currRef
      --           writeIORef treesRef $ updList trees curr $ f $ trees!!curr
      --           extendPT False False False False $ RemoveEdges b
      --           setProof False False "REMOVING EDGES" [] $ edgesRemoved b
      --           clearTreeposs; drawCurr'
      --       where f = if b then removeCyclePtrs else moreTree

        -- removeKripke = do writeIORef kripkeRef ([],[],[],[],[],[],[])
        --                   labGreen' "The Kripke model has been removed."

      --   -- | Used by 'checkForward'. Called by menu item /remove node/ from menu
      --   -- /transform selection/.
      --   removeNode :: Action
      --   removeNode = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           let t = trees!!curr
      --               p = emptyOrLast treeposs
      --           if isHidden t || null p
      --               then labMag selectSub
      --               else do
      --                   writeIORef treesRef
      --                       $ updList trees curr $ removeNonRoot t p
      --                   extendPT False False False False RemoveNode
      --                   setProof False False "REMOVING THE NODE" [p]
      --                                      "The selected node has been removed."
      --                   clearTreeposs; drawCurr'
        
      --   -- | Used by 'checkForward'. Called by menu item /remove other trees/
      --   -- from tree menu.
      --   removeOthers :: Action
      --   removeOthers = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           treeMode <- readIORef treeModeRef
      --           if treeMode == "tree" then labGreen' "There is only one tree."
      --           else do
      --               curr <- readIORef currRef
      --               modifyIORef solPositionsRef
      --                   $ \solPositions -> [0 | curr `elem` solPositions]
      --               writeIORef treeModeRef "tree"
      --               treeMode <- readIORef treeModeRef
      --               writeIORef treesRef [trees!!curr]
      --               modifyIORef counterRef $ \counter -> upd counter 't' 1
      --               writeIORef currRef 0
      --               extendPT False False False False RemoveOthers
      --               setTreesFrame []
      --               setProof (treeMode == "summand") False
      --                            "REMOVING THE OTHER TREES" [] removedOthers
        
      --   -- | Used by 'checkForward'. Called by menu item /remove path/ from menu
      --   -- /transform selection/ or by keypress @p@ on active left label
      --   -- ('lab').
      --   removePath :: Action
      --   removePath = do
      --       trees <- readIORef treesRef
      --       treeposs <- readIORef treepossRef
      --       if null trees || null treeposs then labMag selectSub
      --       else do
      --           curr <- readIORef currRef
      --           let p = last treeposs
      --           writeIORef treesRef
      --               $ updList trees curr $ removeTreePath p $ trees!!curr
      --           extendPT False False False False RemovePath
      --           setProof False False "REMOVING THE PATH" [p]
      --               ("The selected subtree and its ancestor"
      --               ++ " nodes have been removed.")
      --           clearTreeposs; drawCurr'
        
      --   -- | Called by menu item /remove map/ from menu /signature/.
      --   removeSigMap :: Action
      --   removeSigMap = do
      --       writeIORef signatureMapRef (id,[])
      --       labGreen' iniSigMap
        
      --   -- | Used by 'reAddSpec'. Called by menu item /remove/ from menu
      --   -- /specification/.
      --   removeSpec :: Action
      --   removeSpec = do
      --       empty specfilesRef
      --       empty axiomsRef
      --       empty simplRulesRef
      --       empty transRulesRef
      --       empty theoremsRef
      --       empty conjectsRef
      --       empty termsRef
      --       writeIORef kripkeRef ([],[],[],[],[],[],[])
      --       writeIORef symbolsRef iniSymbols
      --       writeIORef signatureMapRef (id,[])
      --       where empty = flip writeIORef []
        
      --   -- | Called by menu item /remove/ from menu /substitution/.
      --   removeSubst :: Action
      --   removeSubst = do setSubst' (V,[]); labGreen' emptySubst
        
      --   -- | Used by 'checkForward'. Called by menu item /remove/ from menu
      --   -- /transform selection/ or by pressing key @r@ with left label ('lab')
      --   -- active.
      --   removeSubtrees :: Action
      --   removeSubtrees = do
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       if null trees then labBlue' start
      --       else do
      --           treeposs <- readIORef treepossRef
      --           let t = trees!!curr
      --               lg = length trees
      --               ps = if null treeposs then [[]] else minis (<<=) treeposs
      --           if ps == [[]] then
      --               if lg < 2 then labRed' "There is at most one tree."
      --               else do
      --                   modifyIORef solPositionsRef
      --                       $ \solPositions -> shift curr solPositions
      --                   writeIORef treesRef $ context curr trees
      --                   modifyIORef counterRef $ \counter -> decr counter 't'
      --                   treeMode <- readIORef treeModeRef
      --                   let b = treeMode == "summand"
      --                   writeIORef treeModeRef
      --                       $ if lg == 2 then "tree" else treeMode
      --                   trees <- readIORef treesRef
      --                   writeIORef currRef
      --                       $ if curr < length trees then curr else 0
      --                   extendPT False False False False RemoveSubtrees 
      --                   setTreesFrame []
      --                   setProof b False "REMOVING THE CURRENT TREE" []
      --                       "The current tree has been removed."
      --           else if any null ps then labRed' $ noApp "Subtree removal"
      --               else do
      --                   sig <- getSignature
      --                   let qs = map init ps
      --                       q = head qs
      --                       u = getSubterm t q
      --                       r:rs = ps
      --                       b = last r == 0 && null rs && isImpl u && c ||
      --                           allEqual qs && (isDisjunct u && c ||
      --                                           isConjunct u && not c)
      --                       c = polarity True t q
      --                       t' = lshiftPos (foldl expandInto t ps) ps
      --                   simplifying <- readIORef simplifyingRef
      --                   writeIORef treesRef
      --                       $ updList trees curr $ if b && simplifying
      --                                              then simplifyIter sig t'
      --                                              else t'
      --                   extendPT False False True True RemoveSubtrees
      --                   setProof b True "REMOVING SUBTREES" ps removed
      --                   clearTreeposs; drawCurr'
        
      --   -- | Called by menu item /remove theorems/ from menu /theorems/.
      --   removeTheorems :: Action
      --   removeTheorems = do
      --       writeIORef theoremsRef []
      --       labGreen' "There are no theorems."
        
      --   -- | Called by menu item /rename/ from menu /substitution/.
      --   renameVar :: Action
      --   renameVar = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           str <- ent `gtkGet` entryText
      --           renameVar' str
        
      --   -- | Used by 'checkForward' and 'renameVar'.
      --   renameVar' :: String -> Action
      --   renameVar' str = do
      --       sig <- getSignature
      --       case parse (conjunct sig) str of
      --           Just (F "&" ts) -> proceed ts
      --           Just t -> proceed [t]
      --           _ -> labMag
      --               "Enter a conjunction of equations between variables."
      --       where proceed ts =
      --               case parseRenaming ts of
      --                   Just f -> do
      --                       trees <- readIORef treesRef
      --                       curr <- readIORef currRef
      --                       treeposs <- readIORef treepossRef
      --                       let t = trees!!curr
      --                           ps = emptyOrAll treeposs
      --                           ts = map (getSubterm t) ps
      --                           us = map (renameAll f) ts
      --                       writeIORef treesRef
      --                           $ updList trees curr $ fold2 replace t ps us
      --                       extendPT False False False False $ RenameVar str
      --                       setProof False False "RENAMING VARIABLES" ps
      --                                           "Variables have been renamed."
      --                       clearTreeposs; drawCurr'
      --                   _ -> labMag "Enter equations between variables."
        
      --   -- | Called by menu item /label roots with entry/ from menu /graph/ or
      --   -- by pressing @l@ with left label ('lab') active.
      --   replaceNodes :: Action
      --   replaceNodes = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           x <- ent `gtkGet` entryText
      --           if null x then labRed' "The entry field is empty."
      --           else replaceNodes' x
        
      --   -- | Used by 'checkForward' and 'replaceNodes'.
      --   replaceNodes' :: String -> Action
      --   replaceNodes' x = do
      --       sig <- getSignature
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       treeposs <- readIORef treepossRef
      --       let t = trees!!curr
      --           ps = emptyOrAll treeposs
      --           ts = map (changeRoot . getSubterm t) ps
      --           new = if isFovar sig x then V x else F x []
      --           changeRoot (V _)    = new
      --           changeRoot (F _ []) = new
      --           changeRoot (F _ ts) = F x ts
      --           changeRoot t        = t
      --       writeIORef treesRef $ updList trees curr $ fold2 replace0 t ps ts
      --       extendPT False False False False $ ReplaceNodes x; drawCurr'
      --       setProof False False "REPLACING NODES" ps $ nodesReplaced x
        
      --   -- | Used by 'checkForward'. Called from menu item
      --   -- /replace by tree of Solver@N@/ from menu /transform selection/.
      --   replaceOther :: Action
      --   replaceOther = do
      --       solve <- readIORef solveRef
      --       other <- getSolver solve
      --       tree <- getTree solve
      --       case tree of
      --           Just t -> do
      --               treeposs <- readIORef treepossRef
      --               curr <- readIORef currRef
      --               let p = emptyOrLast treeposs
      --               modifyIORef treesRef $ \trees
      --                   -> updList trees curr $ replace1 (trees!!curr) p t
      --               extendPT False False False False ReplaceOther
      --               setProof False False "REPLACING A SUBTREE" [p]
      --                   $ replaceIn other
      --               clearTreeposs; drawCurr'
      --           _ -> labBlue' $ startOther other
        
      --   -- | Used by 'instantiate' and 'releaseSubtree'.
      --   replaceQuant :: TermS -> [Int] -> Action
      --   replaceQuant u target = do
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef

      --       let t = trees!!curr
      --           x = label t target
      --       when (x /= root u)
      --           $ case isAny t x target of
      --               Just q | polarity True t q -> replaceVar x u q
      --               _ -> case isAll t x target of
      --                           Just q | polarity False t q -> replaceVar x u q
      --                           _ -> return ()

      --   -- | Called by menu item /replace by other sides of in/equations/
      --   -- from menu /transform selection/.
      --   replaceSubtrees :: Action
      --   replaceSubtrees = do
      --       treeposs <- readIORef treepossRef
      --       if null treeposs then labMag selectCorrectSubformula
      --       else do
      --           trees <- readIORef treesRef
      --           curr <- readIORef currRef
      --           let t = trees!!curr
      --               p:ps = case treeposs of [p] -> [[],p]; _ -> treeposs
      --               u:us = map (getSubterm1 t) (p:ps)
      --               ts = getOtherSides u p us ps
      --           maybe (labMag selectCorrectSubformula) (replaceSubtrees' ps) ts
        
      --   -- | Used by 'checkForward' and 'replaceSubtrees'.
      --   replaceSubtrees' :: [[Int]] -> [TermS] -> Action
      --   replaceSubtrees' ps ts = do
      --       sig <- getSignature
      --       extendPT False False True True $ ReplaceSubtrees ps ts
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       let t = fold2 replace1 (trees!!curr) ps ts
      --       maybeSimplify sig t
      --       makeTrees sig
      --       setTreesFrame []
      --       setProof True True "REPLACING THE SUBTREES" ps replacedTerm
        
      --   -- | Called by menu item /insert\/replace by text/ from menu
      --   -- /transform selection/ or by pressing @i@ while left lable ('lab') is
      --   -- active.
      --   replaceText :: Action
      --   replaceText = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           str <- getTextHere
      --           replaceText' str
        
        -- -- | Used by 'checkForward' and 'replaceText'.
        -- replaceText' :: String -> Action
        -- replaceText' str = do
        --     sig <- getSignature
        --     treeposs <- readIORef treepossRef
        --     let ps = emptyOrAll treeposs
        --     case parseE (implication sig ++ term sig) str of
        --          Correct u -> finish u ps
        --          p -> incorrect p str illformed
        --     where finish u ps@(p:_) = do
        --             trees <- readIORef treesRef
        --             curr <- readIORef currRef
        --             case changeTerm (trees!!curr) u ps of
        --                 Wellformed t -> do
        --                     if null p then changeMode t
        --                     else writeIORef treesRef $ updList trees curr t
        --                     extendPT False False False False $ ReplaceText str
        --                     setProof False False "REPLACING THE SUBTREES" ps
        --                              textInserted
        --                     clearTreeposs; drawCurr'
        --                 Bad str -> labMag str
        
      --   -- | Used by 'checkForward'.
      --   replaceVar :: String -> TermS -> [Int] -> Action
      --   replaceVar x u p = do
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef

      --       sig <- getSignature
      --       extendPT False False True True $ ReplaceVar x u p
      --       let t = trees!!curr
      --           F z [v] = getSubterm t p
      --           quant:xs = words z
      --           zs = xs `join` [ x | x <- frees sig u `minus` frees sig t
      --                          , nothing $ isAny t x p
      --                          , nothing $ isAll t x p
      --                          ]
      --           t1 = replace t p $ F (unwords $ quant:zs) [v>>>for u x]
      --       maybeSimplify sig t1
      --       makeTrees sig
      --       finish
      --       where str = showTerm0 u
      --             msg = "SUBSTITUTING " ++ str ++ " FOR " ++ x
      --             finish = do
      --                   setTreesFrame []
      --                   setProof True True msg [p]
      --                                    $ subMsg str x
        
      --   -- | Used by 'releaseSubtree' and 'releaseTree'.
      --   resetCatch :: Action
      --   resetCatch = do
      --       writeIORef nodeRef Nothing
      --       writeIORef penposRef Nothing
      --       writeIORef subtreeRef Nothing
      --       writeIORef suptreeRef Nothing
      --       writeIORef isSubtreeRef Nothing
      --       writeIORef firstMoveRef True
      --       canv `gtkSet` [ canvasCursor := LeftPtr ]
        
      --   resetLevel :: Action
      --   resetLevel = modifyIORef counterRef $ \counter -> upd counter 'c' 0

      --   -- | Used by 'checkForward'. Called by menu item /reverse/ from menu
      --   -- /transform selection/.
      --   reverseSubtrees :: Action
      --   reverseSubtrees = do
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else do
      --         treeposs <- readIORef treepossRef
      --         if forsomeThereis (<<) treeposs treeposs
      --         then labMag "Select non-enclosing subtrees!"
      --         else do
      --             curr <- readIORef currRef
      --             let t = trees!!curr
      --                 ps = emptyOrAll treeposs
      --                 x = label t $ init $ head ps
      --                 b = allEqual (map init ps) && permutative x
      --             case ps of
      --                 [p] -> do
      --                     let u = getSubterm t p
      --                         ps = succsInd p $ subterms u
      --                     finish t ps $ permutative $ root u
      --                 _ -> if any null ps
      --                      then labRed' $ noApp "Subtree reversal"
      --                      else finish t ps b
      --     where finish t ps b = do
      --            curr <- readIORef currRef
      --            modifyIORef treesRef $ \trees ->
      --                updList trees curr $ fold2 exchange t (f ps)
      --                                     $ f $ reverse ps
      --            extendPT False False False False ReverseSubtrees
      --            setProof b False "REVERSING THE LIST OF (SUB)TREES" ps reversed
      --            clearTreeposs; drawCurr'
      --            where f = take $ length ps`div`2
        
      --   -- | Used by 'narrowOrRewritePar'.
      --   rewritePar :: TermS
      --              -> Sig
      --              -> Maybe Int
      --              -> [TermS]
      --              -> Bool
      --              -> [TermS]
      --              -> [[Int]]
      --              -> [[Int]]
      --              -> (String -> Int)
      --              -> Action
      --   rewritePar t sig k cls saveRedex used (p:ps) qs vc =
      --       if p `notElem` positions t --- || isVarRoot sig redex
      --       then rewritePar t sig k cls saveRedex used ps qs vc
      --       else do
      --           matching <- readIORef matchingRef
      --           axioms <- readIORef axiomsRef
      --           let cls1 = filterClauses sig redex $ filter unconditional cls
      --               cls2 = if saveRedex then map copyRedex cls1 else cls1
      --               (cls3,vc') = renameApply cls2 sig t vc
      --           if even matching then
      --               case applyAxsToTerm cls1 cls3 axioms redex sig vc of
      --                   (Sum reds vc,used') ->
      --                       rewritePar (replace t p $ mkSum reds) sig k cls
      --                           saveRedex (used `join` used') ps (p:qs) vc
      --                   _ -> rewritePar t sig k cls saveRedex used ps qs vc'
      --           else do
      --               rand <- readIORef randRef
      --               case applyAxsToTermR cls1 cls3 axioms rand redex sig vc of
      --                   (Sum reds vc,used',rand') -> do
      --                       writeIORef randRef rand'
      --                       rewritePar (replace t p $ mkSum reds) sig k cls
      --                           saveRedex (used `join` used') ps (p:qs) vc
      --                   _ -> rewritePar t sig k cls saveRedex used ps qs vc'
      --       where redex = getSubterm t p
      --   rewritePar t sig k cls saveRedex used _ qs vc =
      --       narrowPar t sig k cls saveRedex used [] qs vc
        
      --   -- | Used by 'checkProof' and 'stopRun''.
      --   runChecker :: Bool -> Action
      --   runChecker b = do
      --     when b $ do
      --       sp <- ent `gtkGet` entryText
      --       let newSpeed = parse pnat sp
      --       when (just newSpeed) $ writeIORef speedRef $ get newSpeed
      --       checkingP <- readIORef checkingPRef
      --       when (fst checkingP) $ (paint&setButton) 3 runOpts
      --     runOpts (deriveBut, deriveButSignalRef)
      --     runProof <- runner $ do checkForward
      --                             checkingP <- readIORef checkingPRef
      --                             when (fst checkingP) showPicts'
      --     writeIORef checkerRef runProof
      --     speed <- readIORef speedRef
      --     (runProof&startRun) speed
      --     where runOpts (btn, cmd) = do
      --             btn `gtkSet` [ buttonLabel := "stop run" ]
      --             replaceCommandButton cmd btn stopRun'
        
      --   {- |
      --       Stores @str@ in a file. The file is stored in the programs user
      --       folder with the filename @file@. The filename is also prepend to
      --       the file as a comment.

      --       Used by 'saveSigMap', 'saveSpec', 'saveTree' and 'saveTrees'.
      --   -}
      --   saveFile :: FilePath -> String -> Action
      --   saveFile file str = do
      --       mkDir <$> home
      --       path <- userLib file
      --       writeFile path $ "-- " ++ file ++'\n':str
        
      --   -- | Called by button "save pic" ('saveBut').
      --   saveGraph dir = do
      --     dirPath <- pixpath dir
      --     let lg = length dir
      --         (prefix,suffix) = splitAt (lg-4) dir
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else if lg < 5 || suffix `notElem` words ".eps .png .gif" then do
      --             trees <- readIORef treesRef
      --             treeMode <- readIORef treeModeRef
      --             fast <- readIORef fastRef
      --             saveFile dir $ showTree fast $ joinTrees treeMode trees
      --             labGreen' $ saved "trees" dir
      --          else do
      --               let f n = do
      --                       writeIORef currRef n
      --                       treeSlider `gtkSet` [rangeValue := fromIntegral n]
      --                       clearTreeposs
      --                       drawCurr'
      --                       delay $ saveGraphDH True canv dir dirPath n
      --               trees <- readIORef treesRef
      --               case trees of
      --                 []  -> labBlue' start
      --                 [_] -> do
      --                   file <- savePic suffix canv dirPath
      --                   lab2 `gtkSet` [labelText := saved "tree" file]
      --                 _   -> do
      --                   renewDir dirPath
      --                   saver <- runner2 f $ length trees-1
      --                   (saver&startRun) 500
      --                   labGreen' $ saved "trees" dirPath

            
      --   -- | Called by button "save pic to dir" ('saveDBut').
      --   saveGraphD :: Action
      --   saveGraphD = do
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start else do
      --       picNo <- readIORef picNoRef
      --       saveGraphDP' True canv picNo
        
      --   saveGraphDP' b screen n = do
      --     picDir <- readIORef picDirRef
      --     when (notnull picDir) $ do
      --       pp <- pixpath picDir
      --       saveGraphDH b screen picDir pp n
      --       modifyIORef picNoRef succ
        
      --   -- | Used by 'draw' and 'saveGraphN'.
      --   saveGraphDH :: Bool -> Canvas -> FilePath -> FilePath -> Int -> Action
      --   saveGraphDH b screen dir dirPath n = do
      --     mkHtml screen dir dirPath n
      --     let pic = if b then "tree" else "graph in the painter"
      --     lab2 `gtkSet` [ labelText := saved pic $ mkFile dirPath n]
        
      --   -- | Called by menu item /save proof to file/ from tree menu or by
      --   -- pressing key @s@ while left label ('lab') is active.
      --   saveProof :: Action
      --   saveProof = do
      --       proof <- readIORef proofRef
      --       if null proof then labMag "The proof is empty"
      --       else do
      --           trees <- readIORef treesRef
      --           solPositions <- readIORef solPositionsRef
      --           proofTerm <- readIORef proofTermRef
      --           -- TODO use filechooser widget instead.
      --           file <- ent `gtkGet` entryText
      --           filePath <- userLib file
      --           let pfile = filePath ++ "P"
      --               tfile = filePath ++ "T"
      --           write pfile $ '\n':showDeriv proof trees solPositions
      --           write tfile $ show proofTerm
      --           labGreen' $ saved "proof" pfile ++ '\n':saved "proof term" tfile
      --       where write file str = writeFile file $ "-- " ++ file ++ '\n':str
        
      --   -- | Called by menu item /save map to file/ from menu /signature/.
      --   saveSigMap :: FilePath -> Action
      --   saveSigMap file = do
      --       signatureMap <- readIORef signatureMapRef
      --       saveFile file $ showSignatureMap signatureMap ""
      --       labGreen' $ saved "signature map" file
        
      --   -- | Called by menu item /save to file/ from menu /specification/.
      --   saveSpec :: FilePath -> Action
      --   saveSpec file = do
      --       symbols <- readIORef symbolsRef
      --       axioms <- readIORef axiomsRef
      --       theorems <- readIORef theoremsRef
      --       conjects <- readIORef conjectsRef
      --       terms <- readIORef termsRef
      --       saveFile file $ showSignature (minus6 symbols iniSymbols)
      --                               $ f "\naxioms:\n" showFactors axioms ++
      --                                 f "\ntheorems:\n" showFactors theorems ++
      --                                 f "\nconjects:\n" showFactors conjects ++
      --                                 f "\nterms:\n" showSum terms
      --       labGreen' $ saved "specification" file
      --       where f str g cls = if null cls then "" else str ++ g cls
                
      --   -- | Called by all /[admit all simplifications and axioms] ../ menu
      --   -- items from menu /signature/.
      --   setAdmitted :: Bool -> Action
      --   setAdmitted block = do
      --       trees <- readIORef treesRef
      --       treeposs <- readIORef treepossRef
      --       str <- ent `gtkGet` entryText
      --       curr <- readIORef currRef
      --       setAdmitted' block $ if null trees || null treeposs then words str
      --                            else map (label $ trees!!curr) treeposs
        
      --   -- | Called by /admit all simplifications and axioms/ from menu
      --   -- /signature/.
      --   setAdmitted' :: Bool -> [String] -> Action
      --   setAdmitted' block xs = do
      --       trees <- readIORef treesRef
      --       let msg = admitted block xs
      --       writeIORef constraintsRef (block,xs)
      --       if null trees then labGreen' msg
      --       else do
      --           extendPT False False False False $ SetAdmitted block xs
      --           setProof True False "ADMITTED" [] msg
        
      --   -- | Called by /collapse after simplify/ from menu
      --   -- /graph/.
      --   setCollapse :: Action
      --   setCollapse = do
      --       modifyIORef collSimplsRef not
      --       collSimpls <- readIORef collSimplsRef
      --       setStrat
        
      --   -- | Used by 'buildSolve'', 'checkForward', 'incrCurr',
      --   -- 'setCurrInSolve'' and 'simplify'''.
      --   setCurr :: String -> Int -> Action
      --   setCurr msg n = do
      --       curr <- readIORef currRef

      --       if n /= curr then do
      --           writeIORef currRef n
      --           treeSlider `gtkSet` [ rangeValue := fromIntegral n ]
      --           setCurrInPaint paint n
      --           extendPT False False False False $ SetCurr msg n
      --           setProof True False "MOVED" [] msg
      --           clearTreeposs
      --           drawCurr'
      --       else labColorToPaint magback msg

      --   -- | Exported by public 'Epaint.Solver' method 'Epaint.setCurrInSolve'.
      --   setCurrInSolve' :: Int -> Action
      --   setCurrInSolve' n = do
      --       trees <- readIORef treesRef
      --       when (n < length trees) $ setCurr newCurr n
        
      --   -- | Used by 'buildSolve''.
      --   setDeriveMode :: Action
      --   setDeriveMode = do
      --     checking <- readIORef checkingRef
      --     if checking then do
      --        checker <- readIORef checkerRef
      --        checker&stopRun0
      --        writeIORef checkingRef False
      --        isNew <- paint&getNewCheck
      --        checkingP <- readIORef checkingPRef
      --        when (snd checkingP) $ do
      --                              paint&setNewCheck
      --                              (paint&setButton) 1 $ f "narrow/rewrite" narrow'
      --                              (paint&setButton) 2 $ f "simplify" simplify'
      --                              (paint&setButton) 3 $ \(btn,cmd) -> do
      --                                btn `gtkSet` [ buttonLabel := "" ]
      --                                replaceCommandButton cmd btn $ done
      --        writeIORef checkingPRef (False,False)
      --        writeIORef speedRef 500
      --        writeIORef matchTermRef []
      --        writeIORef refuteTermRef []
      --        writeIORef simplTermRef []
      --        writeIORef stratTermRef []
      --        set "derive"
      --        quit `gtkSet` [ buttonLabel := "quit" ]
      --        replaceCommandButton quitSignalRef quit mainQuit
      --     else do
      --          simplifying <- readIORef simplifyingRef
      --          refuting <- readIORef refutingRef
      --          case (simplifying,refuting) of
      --               (False,False) -> do
      --                                writeIORef simplifyingRef True
      --                                set "derive & simplify"
      --               (True,False)  -> do
      --                                writeIORef refutingRef True
      --                                set "derive & simplify & refute"
      --               (True,_)      -> do
      --                                writeIORef simplifyingRef False
      --                                set "derive & refute"
      --               _             -> do
      --                                writeIORef refutingRef False
      --                                set "derive"
      --     where set str = do
      --                deriveBut `gtkSet` [ buttonLabel := str ]
      --                replaceCommandButton deriveButSignalRef
      --                    deriveBut setDeriveMode
      --           f str act (btn,cmd) = do
      --             btn `gtkSet` [ buttonLabel := str ]
      --             replaceCommandButton cmd btn $ do
      --                 paint&remote
      --                 act
      --                 showTreePicts

        
      --   {- |
      --       Set font of text area ('tedit'), entry field ('ent'), left label
      --       ('lab') and right label ('lab2').
      --       Called by button 'fontBut' on font change.
      --   -}
      --   setFont :: FontDescription -> Action
      --   setFont fo = do
      --       writeIORef fontRef fo
      --       size <- fontDescriptionGetSize fo
      --       -- By changing the font size slider, setFontSize is called, which
      --       -- handles the font changing of the GUI elements.
      --       when (just size) $ fontSize `gtkSet` [ rangeValue := get size]
      --       trees <- readIORef treesRef
      --       when (notnull trees) drawCurr'
        
      --   {- |
      --       Set font size of text area ('tedit'), entry field ('ent'), left
      --       label ('lab') and right label ('lab2').
      --       Called by scale 'fontSize'.
      --   -}
      --   setFontSize :: Action
      --   setFontSize = do
      --       fo <- readIORef fontRef
      --       size <- fontSize `gtkGet` rangeValue
      --       fontDescriptionSetSize fo size
      --       fo' <- fontDescriptionCopy fo
      --       fontDescriptionSetFamily fo' monospace
      --       widgetOverrideFont tedit $ Just fo'
      --       widgetOverrideFont ent $ Just fo'
      --       fontDescriptionSetFamily fo' sansSerif
      --       fontDescriptionSetStyle fo' StyleItalic
      --       widgetOverrideFont lab $ Just fo'
      --       widgetOverrideFont lab2 $ Just fo'
        
      --   -- | The @opts@ function sets the behavior of the forward button
      --   -- ('forwBut').
      --   -- Exported by public 'Epaint.Solver' method 'Epaint.setForw'.
      --   setForw' :: ButtonOpts -> Action
      --   setForw' opts = opts (forwBut, forwButSignalRef) -- Note [setForw]
        
      --   {- Note [setForw]
      --   ~~~~~~~~~~~~~~~~~
      --   The behavior of the setForw' function changed with the port from
      --   O'Haskell/Tcl to GTK+. Originally @opts@ was a list of button options.
      --   Since GTK+ works different and the option system also was strongly mixed
      --   with the object oriented inheritance system, this function now takes a
      --   function as parameter, which handles the change in the button behavior.
      --   -}
        
      --   -- | Changes the picture interpreter. This determines how the painter is
      --   -- handling the graph on a call.
      --   -- Used by 'callEnum' and 'checkProof'. Called by interpreter button.
      --   setInterpreter' :: String -> Action
      --   setInterpreter' eval = do
      --       sig <- getSignature
      --       writeIORef picEvalRef eval
      --       interpreterLabel `gtkSet` [ labelLabel := eval ]
      --       spread <- readIORef spreadRef
      --       setEval paint eval spread
      --       draw <- ent `gtkGet` entryText
      --       writeIORef drawFunRef draw
      --       drawFun <- readIORef drawFunRef
      --       labGreen' $ newInterpreter eval drawFun
        
      --   -- | Used by 'changeMode', 'setDeriveMode' and 'setTreeposs'. Called by
      --   -- button 'matchBut'.
      --   setNarrow :: Bool -> Bool -> Action
      --   setNarrow chgMatch chgRandom = do
      --     treeposs <- readIORef treepossRef
      --     trees <- readIORef treesRef
      --     curr <- readIORef currRef
      --     formula <- readIORef formulaRef

      --     sig <- getSignature
      --     let nar = formula || notnull treeposs &&
      --                     treeposs `subset` boolPositions sig (trees!!curr)
      --         set' str1 str2 = do
      --           matchBut `gtkSet` [ buttonLabel := str1 ]
      --           randomBut `gtkSet` [ buttonLabel := str2 ]
      --           narrowBut `gtkSet`
      --             [ buttonLabel := if nar then "narrow" else "rewrite"]
      --     when (chgMatch && nar) $ do
      --         modifyIORef matchingRef
      --             $ \matching -> (matching+2) `mod` 4
      --     when chgRandom $ do
      --       modifyIORef matchingRef $ \matching ->
      --         if even matching then matching+1 
      --                          else matching-1
      --     matching <- readIORef matchingRef
      --     case matching of
      --       0 -> set' "match" "all"
      --       1 -> set' "match" "random"
      --       2 -> set' "unify" "all"
      --       _ -> set' "unify" "random"
        
      --   -- | Exported by public 'Epaint.Solver' method 'Epaint.setNewTrees'.
      --   setNewTrees' :: [TermS] -> String -> Action
      --   setNewTrees' ts typ = do
      --       writeIORef treesRef ts
      --       modifyIORef counterRef $ \counter -> upd counter 't' $ length ts
      --       writeIORef treeModeRef typ
      --       initialize [] "trees"
      --       setTreesFrame []

      --   setPicDir :: Bool -> Action
      --   setPicDir b = do
      --     dir <- ent `gtkGet` entryText
      --     writeIORef picDirRef $ if b || null dir then "picDir" else dir
      --     picDir <- readIORef picDirRef
      --     lab2 `gtkSet` [ labelText := picDir ++ " is the current directory"]
      --     pp <- pixpath picDir
      --     mkDir pp
      --     writeIORef picNoRef 0


      --   setProof :: Bool -> Bool -> String -> [[Int]] -> String -> Action
      --   setProof correct simplPossible msg ps labMsg = do
      --     proof <- readIORef proofRef
      --     proofPtr <- readIORef proofPtrRef
      --     trees <- readIORef treesRef
      --     curr <- readIORef currRef
      --     counter <- readIORef counterRef
      --     ruleString <- readIORef ruleStringRef
      --     newTrees <- readIORef newTreesRef
      --     formula <- readIORef formulaRef
      --     matching <- readIORef matchingRef
      --     simplifying <- readIORef simplifyingRef
      --     refuting <- readIORef refutingRef
      --     treeMode <- readIORef treeModeRef
      --     varCounter <- readIORef varCounterRef
      --     solPositions <- readIORef solPositionsRef
      --     substitution <- readIORef substitutionRef
      --     newPreds <- readIORef newPredsRef
      --     joined <- readIORef joinedRef
      --     safe <- readIORef safeRef
      --     constraints <- readIORef constraintsRef
      --     fast <- readIORef fastRef
      --     simplStrat <- readIORef simplStratRef
      --     let oldProofElem = proof!!proofPtr
      --         t = trees!!curr
      --         n = counter 'd'
      --         msgAE = msg == "ADMITTED" || msg == "EQS"
      --         msgSP = msg == "SPLIT"
      --         msgMV = msg == "MOVED" || msg == "JOIN"
      --         str | msgAE     = labMsg
      --             | msgSP     = labMsg ++ show (length trees)
      --                              ++ ' ':treeMode ++ "s."
      --                              ++ showCurr fast t treeMode
      --             | msgMV     = labMsg ++ showCurr fast t treeMode
      --             | newTrees  = showNew fast (length trees) t msg n ps treeMode
      --             | otherwise = showPre fast t msg n ps treeMode
      --         str0 = "\nThe axioms have been MATCHED against their redices."
      --             `onlyif` matching < 2
      --         str1 = ("\nThe reducts have been simplified " ++
      --                 stratWord simplStrat ++ ".") `onlyif` simplifying
      --         str2 str = "\nFailure "++ str ++" have been removed."
      --                 `onlyif` refuting
      --         str3 =
      --             if correct then case ruleString of
      --                                 "NARROWING" -> str0++str1++str2 "atoms"
      --                                 "REWRITING" -> str1++str2 "terms"
      --                                 _ -> str1 `onlyif` simplPossible
      --             else "\nCAUTION: This step may be semantically incorrect!"
      --         (msgP,msgL) = if null str3 then (str,labMsg)
      --                                    else (str++'\n':str3,labMsg++str3)
      --         msg1 = msgL ++ if newTrees || msgAE || msgSP || msgMV ||
      --                           notnull msgL && head msgL == ' ' ||
      --                           trees /= (oldProofElem&peTrees)
      --                        then "" else "\nThe "++ formString formula ++
      --                                     " has not been modified."
      --         u = joinTrees treeMode trees
      --         us = map (joinTrees treeMode . peTrees) proof
      --         pred =  search (== u) us
      --         cmsg = "\nThe " ++ formString formula ++ " coincides with no. " ++
      --                show (get pred)
      --         (msg2,msg3) = if just pred then (msgP++cmsg,msg1++cmsg)
      --                                    else (msgP,msg1)
      --     when (null ruleString || n > 0) $ do
      --        modifyIORef proofPtrRef succ
      --        proofPtr <- readIORef proofPtrRef
      --        perms <- readIORef permsRef
      --        let next = ProofElem
      --                 { peMsg = msg2
      --                 , peMsgL = msg3
      --                 , peTreeMode = treeMode
      --                 , peTrees = trees
      --                 , peTreePoss = ps
      --                 , peCurr = curr
      --                 , pePerms = perms
      --                 , peVarCounter = varCounter
      --                 , peNewPreds = newPreds
      --                 , peSolPositions = solPositions
      --                 , peSubstitution = substitution
      --                 , peSafe = safe
      --                 , peConstraints = constraints
      --                 , peJoined = joined
      --                 }
      --        modifyIORef proofRef
      --          $ \proof -> take proofPtr proof++[next]
      --  -- else picNo := picNo-1
      --     writeIORef newTreesRef False
      --     writeIORef ruleStringRef ""
      --     labColorToPaint greenback $ show proofPtr ++ ". " ++ msg3
        
      --   setQuit' :: ButtonOpts -> Action
      --   setQuit' opts = opts (quit, quitSignalRef)

        
      --   -- | Used by 'addSubst', 'changeState', 'initialize', 'releaseTree',
      --   -- 'removeSubst' and 'unifyAct'. Exported by public 'Epaint.Solver'
      --   -- method 'Epaint.setSubst'.
      --   setSubst' :: (String -> TermS,[String]) -> Action
      --   setSubst' subst@(_,dom) = do
      --       setBackground applyBut $ if null dom then blueback else redback
      --       domMenu <- getMenu "domMenu" -- Note [DomMenu]
      --       containerForeach domMenu (containerRemove domMenu) -- Note [DomMenu]
      --       mapM_ (mkButF domMenu applySubstTo) dom
      --       writeIORef substitutionRef subst
        
      --   {- Note [DomMenu]
      --   ~~~~~~~~~~~~~~~~~
        
      --   Since Gtk+3 MenuButton is not implemented by Haskells gtk3 package,
      --   it is not possible to access the subToBut button. Instead the domMenu
      --   has become part of the glade file and will never be replaced. Instead
      --   of creating a new domMenu every time setSubst' is called, all items
      --   are removed.
      --   -}
        
      --   {- unused
      --   -- | Called by button "set" ('subBut').
      --   setSubtrees :: Action
      --   setSubtrees = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           str <- ent `gtkGet` entryText
      --           curr <- readIORef currRef
      --           let f = natToLabel $ posTree [] $ trees!!curr
      --           case parse intRanges str of
      --               Just ns | all (just . f) ns -> do
      --                   let qs = map get $ map f ns
      --                   treeposs <- readIORef treepossRef
      --                   setTreeposs $ Add $ qs `minus` treeposs
      --                   drawSubtrees
      --                   labGreen' $ case qs of
      --                              [q] -> "The tree at position " ++ show q ++
      --                                     " has been selected."
      --                              _ -> "The trees at position " ++
      --                                   init (tail $ show qs `minus1` ' ') ++
      --                                   " have been selected."
      --               _ -> labMag "Enter tree positions in heap order!"
      --   -}

      --   setStrat = do
      --     simplStrat <- readIORef simplStratRef
      --     let str = stratWord simplStrat
      --     collSimpls <- readIORef collSimplsRef
      --     stratBut `gtkSet`
      --       [buttonLabel := if collSimpls then str++"C" else str]

      --   -- | Used by 'showSubtreePicts', 'showTreePicts', 'simplify''',
      --   -- 'enterTree'' and 'narrow'''.
      --   setTime :: Action
      --   setTime = do
      --       (_, t) <- readIORef timesRef
      --       time <- getCPUTime
      --       writeIORef timesRef (time, t)
        
      --   -- | Used by 'catchSubtree', 'clearTreeposs', 'releaseSubtree',
      --   -- 'setSubtrees', 'setTreesFrame', 'showChanged' and 'unifyAct'.
      --   setTreeposs :: PossAct -> Action
      --   setTreeposs step = do
      --     treeposs <- readIORef treepossRef

      --     writeIORef oldTreepossRef treeposs
      --     writeIORef treepossRef $ case step of
      --                             Add ps -> treeposs++ps
      --                             Remove p -> treeposs`minus1`p
      --                             Replace ps -> ps
      --     treeposs <- readIORef treepossRef
      --     when (not $ null treeposs)
      --        $ extendPT False False False False $ Mark treeposs
      --     setNarrow False False
        
      --   -- | Used by 'simplify''', 'splitTree', 'applyInd', 'applyTheorem',
      --   -- 'changeState', 'enterTree'', 'narrowLoop', 'narrowPar',
      --   -- 'narrowSubtree', 'removeOthers', 'removeSubtrees',
      --   -- 'replaceSubtrees'', 'replaceVar' and 'setNewTrees''.
      --   setTreesFrame :: [[Int]] -> Action
      --   setTreesFrame ps = do
      --       trees <- readIORef treesRef
      --       treeMode <- readIORef treeModeRef
      --       curr <- readIORef currRef
      --       formula <- readIORef formulaRef

      --       let lg = length trees
      --           str = case treeMode of "tree" -> formString formula
      --                                  _ -> show lg ++ ' ':treeMode ++ "s"
      --       rangeSetRange treeSlider 0 $ fromIntegral (lg-1)
      --       treeSlider `gtkSet` [ widgetSensitive := True
      --                        , rangeValue := fromIntegral curr
      --                        ]
      --       setCurrInPaint paint curr
      --       termBut `gtkSet` [ labelText := str ]
      --       setTreeposs $ Replace ps
      --       drawCurr'
        
      --   -- | Change varCounter state. Used by 'applyClause', 'applyCoinduction',
      --   -- 'applyTransitivity', 'compressAxioms', 'compressClauses',
      --   -- 'createInvariant', 'flattenImpl', 'showEqsOrGraph' and 'stretch'.
      --   setZcounter :: Int -> Action
      --   setZcounter n = modifyIORef varCounterRef
      --       $ \varCounter -> upd varCounter "z" n
        
      --   -- | Used by 'checkForward'. Called by menu item /shift pattern to rhs/
      --   -- from menu /transform selection/.
      --   shiftPattern :: Action
      --   shiftPattern = do
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else do
      --         treeposs <- readIORef treepossRef
      --         curr <- readIORef currRef
      --         let [p,q] = case treeposs of [r] -> [[],r]; _ -> treeposs
      --             r = drop (length p) q
      --             t = trees!!curr
      --         if null treeposs || length treeposs > 2 || not (p << q)
      --         then labMag "Select a (conditional) equation and a pattern!"
      --         else do
      --             sig <- getSignature
      --             case makeLambda sig (getSubterm1 t p) r of
      --                 Just cl -> do
      --                     curr <- readIORef currRef
      --                     modifyIORef treesRef $ \trees ->
      --                         updList trees curr $ replace1 t p cl
      --                     extendPT False False False False ShiftPattern
      --                     setProof True False "SHIFTING A PATTERN" [[]]
      --                         "A pattern has been shifted."
      --                     clearTreeposs; drawCurr'
      --                 _ -> labMag "The selected pattern cannot be shifted."
        
      --   -- | Used by 'checkForward'. Called by menu item /move up quantifiers/
      --   -- from menu /transform selection/. 
      --   shiftQuants :: Action
      --   shiftQuants = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           let t = trees!!curr
      --               ps = treeposs
      --           if null ps || any null ps then errorMsg
      --           else do
      --               let qs = map init ps
      --                   ts = map (getSubterm1 t) ps
      --                   qvars = map (\t -> alls t++anys t) ts
      --               if allEqual qs && any notnull qvars then do
      --                   sig <- getSignature
      --                   let q = head qs
      --                       u = getSubterm1 t q
      --                       x = root u
      --                   if isF u && x `elem` words "==> Not & |" then do
      --                       varCounter <- readIORef varCounterRef
      --                       let (as,es,v,vc) = moveUp sig varCounter x
      --                                               (subterms u) $ map last ps
      --                           v' = simplifyIter sig v
      --                       finish (replace1 t q $ mkAll as $ mkAny es v') ps vc
      --                   else errorMsg
      --               else errorMsg
      --       where finish t ps vc = do
      --                   curr <- readIORef currRef
      --                   modifyIORef treesRef $ \trees -> updList trees curr t
      --                   writeIORef varCounterRef vc
      --                   extendPT False False False False ShiftQuants
      --                   setProof True False "MOVING UP QUANTIFIERS" ps moved
      --                   clearTreeposs; drawCurr'
      --             errorMsg = labRed' $ noApp "Move up quantifiers"
        
      --   -- Called by menu item /shift subformulas/ from menu
      --   -- /transform selection/. 
      --   shiftSubs :: Action
      --   shiftSubs = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           treeposs <- readIORef treepossRef
      --           if null treeposs || any null treeposs
      --           then labRed' $ noApp "Shift subformulas"
      --           else shiftSubs' treeposs
        
      --   -- | Used by 'checkForward' and 'shiftSubs'.
      --   shiftSubs' :: [[Int]] -> Action
      --   shiftSubs' ps = do
      --       sig <- getSignature
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       case shiftSubformulas sig (trees!!curr) ps of
      --           Just t -> do
      --               writeIORef treesRef $ updList trees curr t
      --               extendPT False False False False $ ShiftSubs ps
      --               setProof True False "SHIFTING SUBFORMULAS" ps shifted
      --               clearTreeposs; drawCurr'
      --           _ -> labRed' $ noApp "Shift subformulas"
        
      --   -- | Used by 'removeClauses'. Called by menu items /show/ and
      --   -- /[show].. in text field of SolverN/ from menu /axioms/.
      --   showAxioms :: Bool -> Action
      --   showAxioms b = do
      --       axioms <- readIORef axiomsRef
      --       if null axioms then labGreen' "There are no axioms."
      --       else
      --           if b then do
      --               enterFormulas' axioms
      --               labGreen' $ see "axioms"
      --           else do
      --               solve <- readIORef solveRef
      --               bigWin solve
      --               enterFormulas solve axioms
        
      --   -- | Called by menu item /[show].. for symbols/ from menu /axioms/ or by
      --   -- pressing button @x@ while left label ('lab') is active.
      --   showAxiomsFor :: Action
      --   showAxiomsFor = do
      --       str <- ent `gtkGet` entryText
      --       treeposs <- readIORef treepossRef
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       axioms <- readIORef axiomsRef
      --       let ps = emptyOrAll treeposs
      --           xs = if null trees || null treeposs && notnull str
      --                then words str
      --                else mkSet $ map (label $ trees!!curr) ps
      --           axs = clausesFor xs axioms
      --       if null axs then labRed' $ noAxiomsFor xs
      --       else do
      --           enterFormulas' axs
      --           labGreen' $ see $ "axioms for " ++ showStrList xs
        
      --   -- | Called by menu item /show changed/ from tree menu.
      --   showChanged :: Action
      --   showChanged = do
      --       proofPtr <- readIORef proofPtrRef
      --       if proofPtr <= 0 then labMag "The proof is empty."
      --       else do
      --           proof <- readIORef proofRef
      --           curr <- readIORef currRef
      --           writeIORef restoreRef True
      --           let proofElem = proof!!(proofPtr-1)
      --               k = peCurr proofElem
      --               ts = peTrees proofElem
      --           if k == curr then do
      --               trees <- readIORef treesRef
      --               let ps = changedPoss (ts!!k) (trees!!k)
      --               setTreeposs $ Replace ps
      --               drawCurr'
      --           else labMag newCurr
        
      --   -- | Used by 'removeClauses'. Called by menu item /show conjects/ from
      --   -- menu /theorems/.
      --   showConjects :: Action
      --   showConjects = do
      --       conjects <- readIORef conjectsRef
      --       if null conjects then labGreen' "There are no conjectures."
      --       else do
      --           enterFormulas' conjects
      --           labGreen' $ see "conjectures"
        
      --   -- | Called by menu item /coordinates/ from menu /nodes/.
      --   showCoords :: Action
      --   showCoords = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           writeIORef restoreRef True
      --           curr <- readIORef currRef
      --           ctree <- readIORef ctreeRef
      --           drawThis (cTree (trees!!curr) $ get ctree) [] ""
        
      --   -- | Called by menu item /cycle targets/ from menu /nodes/.
      --   showCycleTargets :: Action
      --   showCycleTargets = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           writeIORef restoreRef True
      --           curr <- readIORef currRef
      --           let t = trees!!curr
      --           drawThis t (cycleTargets t) "green"
        
      --   -- | Called by menu item /greatest lower bound/ from menu /nodes/.
      --   showGlb :: Action
      --   showGlb = do
      --       treeposs <- readIORef treepossRef
      --       if null treeposs then labMag "Select subtrees!"
      --       else do
      --           writeIORef restoreRef True
      --           trees <- readIORef treesRef
      --           curr <- readIORef currRef
      --           drawThis (trees!!curr) [glbPos treeposs] "green"
        
      --   -- | Called by menu item /show induction hypotheses/ from menu
      --   -- /theorems/.
      --   showIndClauses :: Action
      --   showIndClauses = do
      --       indClauses <- readIORef indClausesRef
      --       if null indClauses
      --       then labGreen' "There are no induction hypotheses."
      --       else do
      --           enterFormulas' indClauses
      --           labGreen' $ see "induction hypotheses"
        
      --   -- | Called by all /show matrix/ menu items from menu /graph/.
      --   showMatrix :: Int -> Action
      --   showMatrix m = do
      --     kripke <- readIORef kripkeRef
      --     treeposs <- readIORef treepossRef
      --     trees <- readIORef treesRef
      --     curr <- readIORef currRef
      --     spread <- readIORef spreadRef
      --     sig <- getSignature
      --     let [sts,ats,labs] 
      --             = map (map showTerm0) [sig&states,sig&atoms,sig&labels]
      --         p:ps = emptyOrAll treeposs
      --         t = getSubterm1 (trees!!curr) p
      --         f = if null ps then id else drop $ length p
      --         is = [i | [i,1] <- map f ps]
      --     pict <- runT $ matrix sizes0 spread t
      --     let u = case m of 0 -> Hidden $ BoolMat sts sts
      --                                   $ deAssoc0 $ mkPairs sts sts (sig&trans)
      --                       1 -> Hidden $ BoolMat ats sts
      --                                   $ deAssoc0 $ mkPairs ats sts (sig&value)
      --                       2 -> Hidden $ BoolMat sts ats
      --                                   $ deAssoc0 $ mkPairs sts ats $ out sig
      --                       3 -> Hidden $ ListMat sts (labs' trips) $ trips
      --                            where
      --                              trips = mkTriples sts labs sts (sig&transL)
      --                       4 -> Hidden $ ListMat ats (labs' trips) $ trips
      --                            where
      --                              trips = mkTriples ats labs sts (sig&valueL)
      --                       5 -> Hidden $ ListMat sts (labs' trips) $ trips
      --                            where trips = mkTriples sts labs ats $ outL sig
      --                       _ -> case parseEqs t of
      --                               Just eqs -> mat m $ eqsToGraph is eqs
      --                               _ -> if just pict then t else mat m t
      --     pict <- runT $ matrix sizes0 spread u
      --     if m > 5 && null trees then labBlue' start
      --     else
      --         if nothing pict then labMag "The matrix is empty."
      --         else do
      --             font <- readIORef fontRef
      --             sizes <- mkSizes canv font $ stringsInPict $ get pict
      --             fast <- readIORef fastRef
      --             spread <- readIORef spreadRef
      --             (paint&setEval) "" spread
      --             pict <- (matrix sizes spread u)&runT
      --             curr <- readIORef currRef
      --             (paint&callPaint) [get pict] [curr] False curr "white"
      --     where labs' trips = mkSet [x | (_,x,_:_) <- trips]
      --           mat 6 t = Hidden $ BoolMat dom1 dom2 ps
      --                     where ps = deAssoc0 $ graphToRel t
      --                           (dom1,dom2) = sortDoms ps
      --           mat _ t = Hidden $ ListMat dom1 dom2 ts
      --                    where ts = graphToRel2 (evenNodes t) t
      --                          (dom1,dom2) = sortDoms $ map (pr1 *** pr2) ts
        
      --   -- | Called by all /(...) numbers/ menu items from /nodes/ menu.
      --   showNumbers :: Int -> Action
      --   showNumbers m = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           writeIORef restoreRef True
      --           col <- ent `gtkGet` entryText
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           let t = trees!!curr
      --               p = emptyOrLast treeposs
      --               u = getSubterm1 t p
      --               c = case parse color col of Just d -> d; _ -> black
      --               (v,_) = order c label u
      --           drawThis (replace1 t p v) [] ""
      --    where label (RGB 0 0 0) n = show n
      --          label c n           = show c++'$':show n
      --          order = case m of 1 -> levelTerm -- "level numbers"
      --                            2 -> preordTerm -- "preorder positions"
      --                            3 -> heapTerm -- "heap positions"
      --                            _ -> hillTerm -- "hill positions"
        
      --   -- | Called by button /paint/ ('paintBut'). Exported by public
      --   -- 'Epaint.Solver' method 'Epaint.showPicts'.
      --   showPicts' :: Action
      --   showPicts' = do
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else do
      --          checking <- readIORef checkingRef
      --          if checking then do
      --             modifyIORef checkingPRef $ \checkingP -> (True,snd checkingP)
      --             isNew <- paint&getNewCheck
      --             if isNew then do
      --                           (paint&buildPaint) True
      --                           (paint&setButton) 3 runOpts
      --                           showTreePicts
      --                      else showTreePicts
      --          else do
      --               treeposs <- readIORef treepossRef
      --               if null treeposs then showTreePicts else showSubtreePicts
      --     where runOpts (btn, cmd) = do
      --               btn `gtkSet` [ buttonLabel := "run proof" ]
      --               replaceCommandButton cmd btn $ runChecker True

        
      --   -- | Called by menu item /polarities/ from menu /nodes/.
      --   showPolarities :: Action
      --   showPolarities = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           writeIORef restoreRef True
      --           curr <- readIORef currRef
      --           let t = trees!!curr
      --               ps = polTree True [] t
      --           drawThis (colorWith2 "green" "red" ps t) [] ""
        
      --   -- | Called by menu item /positions/ from menu /nodes/.
      --   showPositions :: Action
      --   showPositions = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           writeIORef restoreRef True
      --           curr <- readIORef currRef
      --           let t = trees!!curr
      --           drawThis (mapT f $ posTree [] t) (cPositions isPos t) "red"
      --       where f = unwords . map show
        
      --   -- | Called by menu item /predecessors/ from menu /nodes/.
      --   showPreds :: Action
      --   showPreds = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           writeIORef restoreRef True
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           let t = trees!!curr
      --               ps = concatMap (nodePreds t) $ emptyOrAll treeposs
      --           drawThis t ps "green"
        
      --   -- | Called by both /show proof/ menu items from tree menu.
      --   showProof :: Bool -> Action
      --   showProof b = do
      --       proof <- readIORef proofRef
      --       if null proof then labMag "The proof is empty."
      --       else do
      --           trees <- readIORef treesRef
      --           solPositions <- readIORef solPositionsRef
      --           let str = '\n':showDeriv proof trees solPositions
      --           if b then do enterText' str; labGreen' $ see "proof"
      --                else do
      --                   solve <- readIORef solveRef
      --                   solve&bigWin
      --                   (solve&enterText) str
        
      --   -- | Called by both /show proof term/ menu items from tree menu.
      --   showProofTerm :: Action
      --   showProofTerm = do
      --     proofTerm <- readIORef proofTermRef
      --     if null proofTerm then labMag "The proof term is empty."
      --     else do labGreen' $ see "proof term"; enterRef

        
      --   -- | Used by 'checkForward'. Called by all /show relation/ menu items
      --   -- from menu /graph/.
      --   showRelation :: Int -> Action
      --   showRelation m = do
      --       kripke <- readIORef kripkeRef
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       treeposs <- readIORef treepossRef
      --       sig <- getSignature
      --       let [sts,ats,labs] 
      --               = map (map showTerm0) [sig&states,sig&atoms,sig&labels]
      --           t = trees!!curr
      --           p:ps = emptyOrAll treeposs
      --           u = getSubterm1 t p
      --           f = if null ps then id else drop $ length p
      --           is = [i | [i,1] <- map f ps]
      --       case m of
      --          0 -> act1 $ mkRelConstsI sts sts (sig&trans) 
      --          1 -> act1 $ mkRelConstsI ats sts (sig&value)
      --          2 -> act1 $ mkRelConstsI sts ats $ out sig
      --          3 -> act1 $ mkRel2ConstsI sts labs sts (sig&transL)
      --          4 -> act1 $ mkRel2ConstsI ats labs sts (sig&valueL)
      --          5 -> act1 $ mkRel2ConstsI sts labs ats $ outL sig
      --          _ -> if null trees then labBlue' start
      --               else act2 t p $ case parseEqs u of
      --                                    Just eqs -> eqsToGraph is eqs
      --                                    _ -> u
      --    where act1 ts = enterTree' False $ h ts
      --          act2 t p u = do
      --               curr <- readIORef currRef
      --               modifyIORef treesRef $ \trees ->
      --                   updList trees curr $ replace1 t p $ h $ f m u
      --               clearTreeposs; drawCurr'
      --               where f 6 = mkRelConsts . graphToRel
      --                     f _ = mkRel2Consts . graphToRel2 (evenNodes u)
      --          g t@(F "()" ts) us = case last ts of F "[]" [] -> us
      --                                               _ -> t:us
      --          h = mkList . foldr g []
        
      --   -- | Called by menu item /show sig/ from menu /signature/.
      --   showSig :: Action
      --   showSig = do
      --     symbols <- readIORef symbolsRef
      --     constraints <- readIORef constraintsRef
      --     safe <- readIORef safeRef

      --     enterText' $ showSignature (minus6 symbols iniSymbols) ""
      --     let (block,xs) = constraints
      --     labGreen' $ see "signature" ++ '\n':admitted block xs
      --                                 ++ '\n':equationRemoval safe

        
      --   -- | Called by menu item /show map/ from menu /signature/.
      --   showSigMap :: Action
      --   showSigMap = do
      --       signatureMap <- readIORef signatureMapRef
      --       if null $ snd signatureMap then labGreen' iniSigMap
      --       else do
      --           enterText' $ showSignatureMap signatureMap ""
      --           labGreen' $ see "signature map"
        
      --   -- | Called by menu item /[show].. solutions/ from menu /substitution/.
      --   showSolutions :: Action
      --   showSolutions = do
      --       sig <- getSignature
      --       formula <- readIORef formulaRef
      --       trees <- readIORef treesRef
      --       labGreen' $ solved $ if formula then solPoss sig trees else []
        
      --   -- | Called by menu items /show/ and /[show].. in text field of SolverN/
      --   -- from menu /substitution/.
      --   showSubst :: Int -> Action
      --   showSubst mode = do
      --     (f,dom) <- readIORef substitutionRef
      --     let ts = substToEqs f dom
      --         typ = if length ts == 1 then "tree" else "factor"
      --     if null dom then labGreen' emptySubst
      --     else do
      --          case mode of 0 -> do
      --                            enterFormulas' ts
      --                            labGreen' $ see "substitution"
      --                       1 -> do
      --                            solve <- readIORef solveRef
      --                            solve&bigWin
      --                            (solve&enterFormulas) ts
      --                       _ -> do
      --                            solve <- readIORef solveRef
      --                            solve&bigWin
      --                            (solve&setNewTrees) ts typ

      --   -- | Used by 'showPicts''.
      --   showSubtreePicts :: Action
      --   showSubtreePicts = do
      --       sig <- getSignature
      --       eval <- getInterpreter
      --       str <- ent `gtkGet` entryText
      --       trees <- readIORef treesRef
      --       curr <- readIORef currRef
      --       treeposs <- readIORef treepossRef
      --       drawFun <- readIORef drawFunRef
      --       spread <- readIORef spreadRef
      --       let t = trees!!curr
      --           ts = applyDrawFun sig drawFun str $ map (closedSub t) treeposs
      --           picts = map (eval sizes0 spread) ts
      --       picts <- mapM runT picts
      --       font <- readIORef fontRef
      --       sizes <- mkSizes canv font
      --                 $ concatMap (stringsInPict . getJust) picts
      --       fast <- readIORef fastRef
      --       setTime
      --       back <- ent `gtkGet` entryText
      --       spread <- readIORef spreadRef
      --       let picts = map (eval sizes spread) ts
      --       picts <- mapM runT picts
      --       (paint&callPaint) [concatMap getJust picts] [] True curr back
        
      --   -- | Called by menu item /successors/ from menu /nodes/.
      --   showSucs :: Action
      --   showSucs = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           writeIORef restoreRef True
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           let t = trees!!curr
      --           drawThis t
      --               (concatMap (nodeSucs t) $ emptyOrAll treeposs) "green"
        
      --   -- | Called by menu items /constructors/, /variables/ and
      --   -- /free variables/ from menu /nodes/.
      --   showSyms :: (Sig -> TermS -> [[Int]]) -> Action
      --   showSyms f = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           writeIORef restoreRef True
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           sig <- getSignature
      --           let t = trees!!curr
      --               p = emptyOrLast treeposs
      --           drawThis t (map (p++) $ f sig $ getSubterm t p) "green"
        
      --   -- | Used by 'removeClauses'. Called by menu item /show terms/
      --   -- from menu /theorems/.
      --   showTerms :: Action
      --   showTerms = do
      --       terms <- readIORef termsRef
      --       if null terms then labGreen' "There are no terms to be reduced."
      --       else do
      --           enterTerms terms
      --           labGreen' $ see "terms"
        
      --   -- | Used by 'removeClauses'. Called by menu items /show theorems/
      --   -- and /[show theorems].. in text field of SolverN/ from menu
      --   -- /theorems/.
      --   showTheorems :: Bool -> Action
      --   showTheorems b = do
      --       theorems <- readIORef theoremsRef
      --       if null theorems then labGreen' "There are no theorems."
      --       else
      --           if b then do
      --               enterFormulas' theorems
      --               labGreen' $ see "theorems"
      --           else do
      --               solve <- readIORef solveRef
      --               bigWin solve
      --               enterFormulas solve theorems
        
      --   -- | Called by menu item /[show theorems].. for symbols/ from menu
      --   -- /theorems/.
      --   showTheoremsFor :: Action
      --   showTheoremsFor = do
      --       str <- ent `gtkGet` entryText
      --       trees <- readIORef treesRef
      --       treeposs <- readIORef treepossRef
      --       curr <- readIORef currRef
      --       theorems <- readIORef theoremsRef
      --       let xs = if null trees || null treeposs then words str
      --                else map (label $ trees!!curr) treeposs
      --           cls = clausesFor xs theorems
      --       if null cls
      --       then labRed' $ "There are no theorems for " ++ showStrList xs ++ "."
      --       else do
      --           enterFormulas' cls
      --           labGreen' $ see $ "theorems for " ++ showStrList xs
        
      --   showTransOrKripke m = do
      --     sig <- getSignature
      --     str <- ent `gtkGet` entryText
      --     varCounter <- readIORef varCounterRef
      --     let [sts,ats,labs] = map (map showTerm0)
      --                              [sig&states,sig&atoms,sig&labels]
      --         vcz = varCounter "z"
      --         (eqs,zn)    = relToEqs vcz $ mkPairs sts sts (sig&trans)
      --         (eqsL,zn')  = relLToEqs zn $ mkTriples sts labs sts (sig&transL)
      --         trGraph     = eqsToGraph [] eqs
      --         trGraphL    = eqsToGraph [] eqsL
      --         atGraph     = if all null (sig&trans) then emptyGraph
      --                       else outGraph sts ats (out sig) trGraph
      --         atGraphL    = if null (sig&labels) then emptyGraph
      --                       else outGraphL sts labs ats (out sig) (outL sig)
      --                                                             trGraphL
      --         inPainter t = do
      --                      drawFun <- readIORef drawFunRef
      --                      let u = head $ applyDrawFun sig drawFun str [t]
      --                      spread <- readIORef spreadRef
      --                      pict <-  (widgetTree sig sizes0 spread u)&runT
      --                      if nothing pict then labMag "The tree is empty."
      --                      else do
      --                           font <- readIORef fontRef
      --                           sizes <- mkSizes canv font $ stringsInPict $ get pict
      --                           (paint&setEval) "tree" spread
      --                           pict <- (widgetTree sig sizes spread u)&runT
      --                           curr <- readIORef currRef
      --                           (paint&callPaint) [get pict] [curr] False curr 
      --                                                                    "white"

      --     setZcounter zn'
      --     solve <- readIORef solveRef
      --     case m of 0  -> enterTree' False trGraph
      --               1  -> enterTree' False $ colorClasses sig trGraph
      --               2  -> inPainter trGraph
      --               3  -> do (solve&bigWin); (solve&enterTree) False trGraph
      --               4  -> enterTree' False trGraphL
      --               5  -> enterTree' False $ colorClasses sig trGraphL
      --               6  -> inPainter trGraphL
      --               7  -> do (solve&bigWin); (solve&enterTree) False trGraphL
      --               8  -> enterTree' False atGraph
      --               9  -> inPainter atGraph
      --               10 -> do (solve&bigWin); (solve&enterTree) False atGraph
      --               11 -> enterTree' False atGraphL
      --               12 -> inPainter atGraphL
      --               _  -> do (solve&bigWin); (solve&enterTree) False atGraphL

      --   -- | Used by 'stopRun'', 'runChecker', 'setDeriveMode' and 'showPicts''.
      --   showTreePicts :: Action
      --   showTreePicts = do                          -- without transformer:
      --       sig <- getSignature
      --       eval <- getInterpreter                 -- getInterpreter
      --       str <- ent `gtkGet` entryText
      --       drawFun <- readIORef drawFunRef
      --       trees <- readIORef treesRef
      --       spread <- readIORef spreadRef
      --       let ts = applyDrawFun sig drawFun str trees
      --           picts = map (eval sizes0 spread) ts
      --       picts <- mapM runT picts           -- return ()
      --       font <- readIORef fontRef
      --       sizes <- mkSizes canv font
      --                 $ concatMap (stringsInPict . getJust) picts
      --       fast <- readIORef fastRef
      --       setTime
      --       back <- ent `gtkGet` entryText
      --       checkingP <- readIORef checkingPRef
      --       checking <- readIORef checkingRef
      --       curr <- readIORef currRef
      --       let picts = map (eval sizes spread) ts
      --       picts <- mapM runT picts           -- return ()
      --       (paint&callPaint) (map getJust picts) (indices_ ts) False curr back
        
      --   -- | Called by menu item /values/ from menu /nodes/.
      --   showVals :: Action
      --   showVals = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           writeIORef restoreRef True
      --           curr <- readIORef currRef
      --           let t = trees!!curr
      --           drawThis t (valPositions t) "green"
        
      --   -- | Called by 'Epaint.Solver' and 'Epaint.Painter' buttons /simplifyDF/
      --   -- ('simplButD') and /simplifyBF/ ('simplButB'). Exported by public
      --   -- 'Epaint.Solver' method 'Epaint.simplify'.
      --   simplify' :: Action
      --   simplify' = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           str <- ent `gtkGet` entryText
      --           let act = simplify''
      --           case parse pnat str of Just limit -> act limit True
      --                                  _ -> act 100 False
        
      --   -- | Used by 'checkForward' and 'simplify''.
      --   simplify'' :: Int -> Bool -> Action
      --   simplify'' limit sub = do
      --     simplStrat <- readIORef simplStratRef
      --     writeIORef ruleStringRef $ "SIMPLIFYING " ++ stratWord simplStrat
      --     extendPT False False False True $ Simplify limit sub
      --     sig <- getSignature
      --     trees <- readIORef treesRef
      --     curr <- readIORef currRef
      --     treeposs <- readIORef treepossRef
      --     let t = trees!!curr
      --     if null treeposs then do
      --         treeMode <- readIORef treeModeRef
      --         formula <- readIORef formulaRef
      --         collSimpls <- readIORef collSimplsRef
      --         simplStrat <- readIORef simplStratRef
      --         solPositions <- readIORef solPositionsRef
      --         setTime
      --         let (u,n,cyclic) = simplifyLoop sig limit simplStrat t
      --             v = if collSimpls then collapse False u else u
      --             msg0 = "The " ++ (if treeMode == "tree" then formString formula
      --                               else "previous " ++ treeMode)
      --                           ++ " is simplified."
      --             msg = finishedSimpl n ++ solved solPositions ++
      --                   ("\nThe simplification became cyclical." `onlyif` cyclic)
      --         if n == 0 then do
      --             modifyIORef counterRef $ \counter -> decr counter 't'
      --             counter <- readIORef counterRef
      --             if counter 't' > 0
      --             then setCurr msg0 $ (curr+1) `mod` length trees
      --             else do
      --                 labMag treesSimplified
      --                 labSolver paint treesSimplified
      --         else do
      --             modifyIORef treesRef $ \trees -> updList trees curr v
      --             makeTrees sig
      --             modifyIORef counterRef $ \counter -> upd counter 'd' n
      --             ruleString <- readIORef ruleStringRef
      --             setProof True False ruleString [] msg
      --             setTreesFrame []
      --     else if sub then do
      --                      simplStrat <- readIORef simplStratRef
      --                      simplifySubtree t sig limit simplStrat
      --                 else simplifyPar t sig treeposs []
        
      --   -- | Used by 'simplify'''.
      --   simplifyPar :: TermS -> Sig -> [[Int]] -> [[Int]] -> Action
      --   simplifyPar t sig (p:ps) qs =
      --       case simplifyOne sig t p of
      --           Just t -> simplifyPar t sig ps (p:qs)
      --           _ -> simplifyPar t sig ps qs
      --   simplifyPar _ _ [] [] = labColorToPaint magback
      --              "The selected trees are simplified at their root positions."
      --   simplifyPar t _ _ qs = do
      --       curr <- readIORef currRef
      --       modifyIORef treesRef $ \trees -> updList trees curr t
      --       modifyIORef counterRef $ \counter -> upd counter 'd' 1
      --       setProof True False "SIMPLIFYING THE SUBTREES" qs simplifiedPar
      --       clearTreeposs; drawCurr'
        
      --   -- | Used by 'simplify'''.
      --   simplifySubtree :: TermS -> Sig -> Int -> Strategy -> Action
      --   simplifySubtree t sig limit strat = do
      --     treeposs <- readIORef treepossRef
      --     collSimpls <- readIORef collSimplsRef
      --     simplStrat <- readIORef simplStratRef
      --     let p = emptyOrLast treeposs
      --         (u,n,cyclic) = simplifyLoop sig limit strat $ getSubterm t p
      --         v = if collSimpls then collapse False u else u
      --         msg = appliedToSub "simplification" n ++
      --               ("\nThe simplification became cyclical." `onlyif` cyclic)
      --     if n == 0 then labColorToPaint magback
      --         "The tree selected at last is simplified."
      --     else do
      --         curr <- readIORef currRef
      --         modifyIORef treesRef
      --             $ \trees -> updList trees curr $ replace1 t p v
      --         modifyIORef counterRef $ \counter -> upd counter 'd' n
      --         ruleString <- readIORef ruleStringRef
      --         setProof True False ruleString [p] msg
      --         clearTreeposs; drawCurr'
        
      --   -- | Called by menu item /specialize/ from menu /transform selection/.
      --   specialize :: Action
      --   specialize = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           str <- ent `gtkGet` entryText
      --           (exps,b) <- readIORef numberedExpsRef
      --           case parse nat str of
      --               k@(Just n) | n < length exps ->
      --                   if b then finish k $ exps!!n
      --                   else labMag "Enter formulas into the text field!"
      --               _ -> do
      --                   str <- getTextHere
      --                   sig <- getSignature
      --                   case parseE (implication sig) str of
      --                       Correct th -> finish Nothing th
      --                       p -> incorrect p str illformedF
      --       where finish k th = applyTheorem False k $
      --                               case th of F "Not" [th] -> mkHorn mkFalse th
      --                                          _ -> mkCoHorn mkTrue th
        
      --   -- | Used by 'checkForward'. Called by button /split\/join/
      --   -- ('splitBut').
      --   splitTree :: Action
      --   splitTree = do
      --     trees <- readIORef treesRef
      --     when (notnull trees) $ do
      --         sig <- getSignature
      --         extendPT False False False False SplitTree
      --         joined <- readIORef joinedRef
      --         if joined then do
      --             writeIORef joinedRef False
      --             splitBut `gtkSet` [ buttonLabel := "join" ]
      --             makeTrees sig
      --             setTreesFrame []
      --             setProof True False "SPLIT" [] "The tree has been split."
      --         else do
      --             writeIORef joinedRef True
      --             splitBut `gtkSet` [ buttonLabel := "split" ]
      --             treeMode <- readIORef treeModeRef
      --             trees <- readIORef treesRef
      --             let t = joinTrees treeMode trees
      --             writeIORef treeModeRef "tree"
      --             writeIORef treesRef [t]
      --             writeIORef currRef 0
      --             modifyIORef counterRef $ \counter -> upd counter 't' 1
      --             formula <- readIORef formulaRef
      --             writeIORef solPositionsRef [0 | formula && isSol sig t]
      --             setTreesFrame []
      --             setProof True False "JOIN" [] "The trees have been joined."
        
      --   -- | Called by menu items /coinduction/ and /induction/ from menu
      --   -- /transform selection/.
      --   startInd :: Bool -> Action
      --   startInd ind = do
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else do
      --          str <- ent `gtkGet` entryText
      --          let pars = words str
      --          case pars of
      --             ["ext",limit] | just k -> f $ get k where k = parse pnat limit
      --             _ -> f 0
      --     where f = if ind then applyInduction else applyCoinduction

        
      --   stateEquiv :: Action
      --   stateEquiv = do
      --     sig <- getSignature
      --     let f (i,j) = mkTup [(sig&states)!!i,(sig&states)!!j]
      --     enterTree' False $ mkList $ map f $ bisim sig 
        
      --   -- | Called by 'deriveBut' if it shows /stop run/. The 'deriveBut' is
      --   -- set to /stop run/ when 'runChecker' is called. Exported by public
      --   -- 'Epaint.Solver' method 'Epaint.stopRun'.
      --   stopRun' :: Action
      --   stopRun' = do
      --     checking <- readIORef checkingRef
      --     when checking $ do
      --       checker <- readIORef checkerRef
      --       checker&stopRun0
      --       runOpts (deriveBut, deriveButSignalRef)
      --     checkingP <- readIORef checkingPRef
      --     when (fst checkingP) $ (paint&setButton) 3 runOpts
      --     where runOpts (btn,cmd) = do
      --              btn `gtkSet` [ buttonLabel := "run proof" ]
      --              replaceCommandButton cmd btn $ runChecker True

        
      --   -- | Used by 'checkForward'. Called by all /stretch/ menu items from
      --   -- /transform selection/ menu.
      --   stretch :: Bool -> Action
      --   stretch prem = do
      --       trees <- readIORef treesRef
      --       if null trees then labBlue' start
      --       else do
      --           curr <- readIORef currRef
      --           treeposs <- readIORef treepossRef
      --           let t = trees!!curr
      --               p = emptyOrLast treeposs
      --               u = getSubterm t p
      --               (f,step,str) =
      --                       if prem then (stretchPrem,StretchPremise,"PREMISE")
      --                       else (stretchConc,StretchConclusion,"CONCLUSION")
      --           case preStretch prem (const True) u of
      --               Just (_,varps) -> do
      --                   varCounter <- readIORef varCounterRef
      --                   let (v,n) = f (varCounter "z") varps u
      --                   curr <- readIORef currRef
      --                   modifyIORef treesRef
      --                       $ \trees -> updList trees curr $ replace t p v
      --                   setZcounter n
      --                   extendPT False False False False step
      --                   setProof True False ("STRETCHING THE "++str)
      --                       [p] stretched
      --                   clearTreeposs; drawCurr'
      --               _ -> notStretchable $ "The "++str
        
      --   -- | Used by 'checkForward'. Called by menu item /subsume/ from menu
      --   -- /transform selection/.
      --   subsumeSubtrees :: Action
      --   subsumeSubtrees = do
      --       treeposs <- readIORef treepossRef
      --       if length treeposs /= 2 || any null treeposs
      --       then labMag "Select two proper subtrees!"
      --       else do
      --           trees <- readIORef treesRef
      --           curr <- readIORef currRef
      --           let t = trees!!curr
      --               ps@[p,q] = treeposs
      --               prem = getSubterm t p
      --               conc = getSubterm t q
      --               r = init p
      --               s = init q
      --               u = getSubterm t r
      --           sig <- getSignature
      --           if subsumes sig prem conc then
      --               if r == s then
      --                   if isImpl u then do
      --                       curr <- readIORef currRef
      --                       modifyIORef treesRef $ \trees ->
      --                           updList trees curr $ replace t r mkTrue
      --                       finish ps "premise"
      --                   else if isConjunct u then do
      --                       let u' = F "&" $ context (last q) $ subterms u
      --                       curr <- readIORef currRef
      --                       modifyIORef treesRef $ \trees ->
      --                           updList trees curr $ replace1 t r u'
      --                       finish ps "factor"
      --                   else if isDisjunct u then do
      --                       let u' = F "|" $ context (last p) $ subterms u
      --                       curr <- readIORef currRef
      --                       modifyIORef treesRef $ \trees ->
      --                           updList trees curr $ replace t r u'
      --                       finish ps "summand"
      --                   else labGreen' msg
      --               else labGreen' msg
      --           else labRed' "The selected trees are not subsumable."
      --       where msg = "The selected trees are subsumable."
      --             finish ps str = do
      --                       extendPT False False False False SubsumeSubtrees
      --                       setProof True False "SUBSUMPTION" ps $ subsumed str
      --                       clearTreeposs; drawCurr'
        
      --   -- | Sitch state varibale 'fastRef' and alternate 'fastBut' label
      --   -- between "fast" and "slow". Called by 'fastBut'.
      --   switchFast :: Action
      --   switchFast = do
      --       modifyIORef fastRef not
      --       fast <- readIORef fastRef
      --       fastBut `gtkSet` [ buttonLabel := if fast then "indented text"
      --                                              else "continuous text" ]
        
      --   -- | Alternate between safe and unsafe equation removal. Called by menu
      --   -- item /safe\/unsafe equation removal/ from menu /signature/.
      --   switchSafe :: Action
      --   switchSafe = do
      --       modifyIORef safeRef not
      --       extendPT False False False False SafeEqs
      --       safe <- readIORef safeRef
      --       setProof True False "EQS" [] $ equationRemoval $ not safe
      --       safe <- readIORef safeRef
      --       safeBut <- readIORef safeButRef
      --       safeBut `gtkSet` [ menuItemLabel := eqsButMsg safe]

      --   transformGraph mode = do
      --     trees <- readIORef treesRef
      --     if null trees then labBlue' start
      --     else do
      --          sig <- getSignature
      --          trees <- readIORef treesRef
      --          curr <- readIORef currRef
      --          varCounter <- readIORef varCounterRef
      --          treeposs <- readIORef treepossRef
      --          let t = trees!!curr
      --              vcz = varCounter "z"
      --              relToEqs1 = relToEqs vcz . deAssoc1
      --              relToEqs3 = relLToEqs vcz . deAssoc3
      --              p:ps = emptyOrAll treeposs
      --              u = getSubterm1 t p
      --              (q,f,r) = if null ps then ([],id,p)
      --                                   else (p,drop $ length p,head ps)
      --              (eqs,zn) = graphToEqs vcz (getSubterm1 t q) $ f r
      --              is = [i | [i,1] <- map f ps]
      --              x = label t r
      --              act zn p u = do
      --                       writeIORef treesRef
      --                         $ updList trees curr $ replace1 t p u
      --                       when (mode == 3) $ setZcounter zn
      --                       extendPT False False False False $ Transform mode
      --                       setProof False False "TRANSFORMING THE GRAPH" [p] $
      --                                transformed
      --                       clearTreeposs; drawCurr'
      --          case mode of 0 -> act 0 p $ collapse True u
      --                       1 -> act 0 p $ collapse False u
      --                       2 -> case parseColl parseConsts2 u of
      --                            Just rel -- from pairs to a graph
      --                              -> do
      --                                 let (eqs,zn) = relToEqs1 rel
      --                                 act zn p $ eqsToGraphx x eqs
      --                            _ -> case parseColl parseConsts3 u of
      --                                 Just rel -- from triples to a graph
      --                                   -> do
      --                                      let (eqs,zn) = relToEqs3 rel
      --                                      act zn p $ eqsToGraphx x eqs
      --                                 _ -> case parseEqs u of
      --                                      Just eqs -- from equations to a graph
      --                                        -> act vcz p $ eqsToGraph is eqs
      --                                      _ -> -- from a graph to a graph
      --                                        act vcz q $ eqsToGraphx x eqs
      --                       _ -> case parseColl parseConsts2 u of
      --                            Just rel -- from pairs to equations
      --                              -> do
      --                                 let (eqs,zn) = relToEqs1 rel
      --                                 act zn p $ eqsTerm eqs
      --                            _ -> case parseColl parseConsts3 u of
      --                                 Just rel -- from triples to equations
      --                                   -> do
      --                                      let (eqs,zn) = relToEqs3 rel
      --                                      act zn p $ eqsTerm eqs
      --                                 _ -> -- from a graph to equations
      --                                      act vcz p $ eqsTerm eqs

      --   -- | Used by 'buildUnifier' and 'unifyOther'.
      --   unifyAct :: TermS -> TermS -> TermS -> TermS -> [Int] -> [Int] -> Action
      --   unifyAct u u' t t' p q = do
      --       writeIORef restoreRef True
      --       sig <- getSignature
      --       case unify u u' t t' p q V sig [] of
      --           Def (f,True) -> do
      --               let xs = frees sig u ++ frees sig u'
      --                   dom = domSub xs f
      --               if null dom then labGreen' $ unifiedT ++ emptySubst
      --               else
      --                   if any hasPos $ map f dom then labRed' posInSubst
      --                   else do
      --                       setSubst' (f,dom)
      --                       labGreen' $ unifiedT ++ "See substitution > show."
      --           Def (_,False) -> labRed' partialUnifier
      --           BadOrder -> labRed' noUnifier
      --           Circle p q -> labRed' $ circle p q
      --           NoPos p -> do
      --               setTreeposs $ Replace [p]
      --               drawCurr'
      --               labRed' dangling
      --           NoUni -> labRed' noUnifier
      --           OcFailed x -> labRed' $ ocFailed x
        
      --   -- | Called by menu item /unify with tree of SolverN/ from menu
      --   -- /transform selection/.
      --   unifyOther :: Action
      --   unifyOther = do
      --       solve <- readIORef solveRef
      --       tree <- getTree solve
      --       case tree of
      --           Just t -> do
      --               treeposs <- readIORef treepossRef
      --               trees <- readIORef treesRef
      --               curr <- readIORef currRef
      --               let p = emptyOrLast treeposs
      --                   t' = trees!!curr
      --                   u = getSubterm t' p
      --               unifyAct t u t t' [] p
      --           _ -> do
      --               other <- getSolver solve
      --               labBlue' $ startOther other
        
      --   -- | Used by 'checkForward'. Called by menu item /unify/ from menu
      --   -- /transform selection/.
      --   unifySubtrees :: Action
      --   unifySubtrees = do
      --     treeposs <- readIORef treepossRef
      --     if length treeposs /= 2 || any null treeposs
      --        then labMag "Select two proper subtrees!"
      --     else do
      --          trees <- readIORef treesRef
      --          curr <- readIORef currRef
      --          let t = trees!!curr
      --              ps@[p,q] = treeposs
      --              u = getSubterm1 t p
      --              u' = getSubterm1 t q
      --              r = init p
      --              v = getSubterm1 t r
      --              b = polarity True t r
      --          if r == init q then do
      --             sig <- getSignature
      --             if isConjunct v && b then do
      --                let xs = if null r then []
      --                         else anys $ getSubterm1 t $ init r
      --                case unifyS sig xs u u' of
      --                    Just f -> do
      --                        let us = map (>>>f) $ init $ subterms v
      --                            t' = replace1 t r $ mkConjunct us
      --                        curr <- readIORef currRef
      --                        modifyIORef treesRef $ \trees ->
      --                            updList trees curr t'
      --                        extendPT False False False False UnifySubtrees
      --                        setProof True False "FACTOR UNIFICATION" ps $
      --                                 unified "factor"
      --                        clearTreeposs; drawCurr'
      --                    _ -> labRed' noUnifier
      --             else if isDisjunct v && not b then do
      --                     let xs = if null r then []
      --                                        else alls $ getSubterm1 t $ init r
      --                     case unifyS sig xs u u' of
      --                      Just f -> do
      --                           let us = map (>>>f) $ init $ subterms v
      --                               t' = replace1 t r $ mkDisjunct us
      --                           curr <- readIORef currRef
      --                           modifyIORef treesRef $ \trees ->
      --                               updList trees curr t'
      --                           extendPT False False False False UnifySubtrees
      --                           setProof True False "SUMMAND UNIFICATION" ps $
      --                                    unified "summand"
      --                           clearTreeposs; drawCurr'
      --                      _ -> labRed' noUnifier
      --                  else labRed' $ noApp "Subtree unification"
      --          else labMag "Select subtrees with the same predecessor!"


-- test functions
loadSpec spec = do
  sState <- initSolverState
  addSpecWithBase spec sState

test_all_specifications = buildTest $ do
    dir <- builtinLibDir
    list <- listDirectory dir
    listOfFiles <- filterM (doesFileExist . (dir </>)) list
    let listOfSpecs
            = Data.List.sort
            $ filter isKnownFailure
            $ filter isSpecification listOfFiles
        listOfTests = map mkSpecTest listOfSpecs
        tests = testGroup "specifications" listOfTests
    return tests

