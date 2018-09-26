module SpecificationTest (tests) where

import Test.Framework
import Test.Framework.Providers.HUnit
import Test.HUnit

import Base.OHaskell
import Base.System
import Eterm
import Esolve

import Control.Monad (void, msum, when, unless, filterM)
import Data.IORef
import Data.Maybe (isJust, fromJust, isNothing, fromMaybe)
import Data.List (isSuffixOf, isInfixOf, isPrefixOf)
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
    , isPrefixOf "["
    ]

-- generated with "script/fails.hs"
isKnownFailure :: FilePath -> Bool
isKnownFailure file = all (/= file) ["rhpytree","raintabB","rot","rainpie","rainpoly","quad","yinyang","rainrect2","polysG4","graph10","rainpyt","crossing1","nemos","listsols","parity","polysG6","recttabAS","rainpoly3","transIn","polysG1","rainpoly2","rainpytl","EXwait","partn","rotnew","flashpoly","rainsnow3","factor3-4-6-2","lr2run","joins","evensmorse","kripke4","mapiter2","fib01","topempty","STACK2IMPL","btree","tgraph","flashplait","pulse","hanoiAlt","mapziptup","lr1run","fruit","gettup","poppush","iterloop","rects","light","oddszip","tree","graph7","rects0","graph6","infbintree","auto1","flowers","partflattenN","solver","recttabA","PAFLall","part1","flash","recttabB","rainpie3","natstream","rainplait2","toppush","testnew5","polar","safe","AFcrit","robotGraph","reqs","knight","recttabBS","rotplait","shuttle","graph5","rotweetysh","lift","flashsnow","trans2sols","morsef","mergePalt","shuttle3","rotweety","flashshine","waveG","gear","wave","natloop","dissW","rainpyt3","rects4","STACKconjs","KNIGHTsols","kinotest","zipmorse","rainrect","puzzle","tweetynet","LRaltRun","queens5solM","snake","rotgrow","showtest1","mapiter1","notfairblink2","robot80-120","distestG","polysG10","rectangle","polysG3","rainpoly2-1","SOL1tree","paths","roturt","rotweety3","invinv","cbau2-0","quad2","states","pytree2","maploop0","graph8","rainpie2","rainplait","matrix","polysG7","set","SOLSPICT2","rotwave","polysG9","rainrectld","rainsnow2","transDesc","iterate","product","lr2Act","flash2","copyrem","shuttle2","SolverCG","relalgdb","testgrow","hanoiLab","cobintree","robot","five2","part2","five","echo3","notfairblink","polytab","maploop","mats","lightsnow","graph3","rects2","decagon","palindrome","pushcomp","solspict","rainpoly5","logConj1","rainpie5","liftAlt","rframe","factor6-6-6-2","iter1iter2","logConj0","sum","rainsnow","rotpoly","updeq","rects3","plaits","pulse2","natloopN","primes6","shuttles","cpic1","graph4","morseinv2","pairs","rainpytd","needcoind","queens5sol","coregs","rainsnow1","distest2-2","rainplait3","showtest2","shuttles2","monad","polysG8","morphs","drei","band","rotweety2","graph9","pytree3","rainpoly3-1","part3","flash0","tattooG","mutexquad","snakes","popempty","shine","rotmat","mapfact","cpic2","kinotest2","fern2-12-1-1","hanoi","coin","mutexco","rainpyt2","rainpyt2l","LRalt","polysG2","quad3","PUSHCOMP2","tattoo4","quad1","pytree1","pascal4","fahrplan","Notsorted","rainplait4","sortperm","logConj2","eqtest","SOLSPICT1","natstreamSol","hanoiActs","rainpyt2d","sendmore","morseinv","primes5","colorhull"]


test_all_specifications = buildTest $ do
    dir <- builtinLibDir
    list <- listDirectory dir
    listOfFiles <- filterM (doesFileExist . (dir </>)) list
    let listOfSpecs
            = reverse
            $ filter isKnownFailure
            $ filter isSpecification listOfFiles
        listOfTests = map mkSpecTest listOfSpecs
        tests = testGroup "specifications" listOfTests
    return tests


loadSpec spec = do
    let -- messages

        illformed :: String
        illformed = "The term or formula in the text field is not well-formed."

        illformedF :: String
        illformedF = "The formula in the text field is not well-formed."

        illformedSig :: String
        illformedSig = "The signature in the text field is not well-formed."
    
    
    -- REFS
    
    safeRef <- newIORef True

    checkingRef <- newIORef False

    axiomsRef <- newIORef []
    conjectsRef <- newIORef []
    iniStatesRef <- newIORef []
    simplRulesRef <- newIORef []
    solPositionsRef <- newIORef []
    specfilesRef <- newIORef []
    termsRef <- newIORef []
    theoremsRef <- newIORef []
    transRulesRef <- newIORef []

    constraintsRef <- newIORef (True,[])

    symbolsRef <- newIORef iniSymbols
    varCounterRef <- newIORef $ const 0
    kripkeRef <- newIORef ([],[],[],[],[],[],[])



    let 

        addAxioms :: TermS -> String -> Action
        addAxioms t file = do
            sig <- getSignature
            let axs = if isConjunct t then subterms t else [t]
                cls = filter (not . isAxiom sig) axs
            if null cls then do
                writeIORef solPositionsRef []
                modifyIORef axiomsRef $ \axioms -> axioms `join` axs
                modifyIORef simplRulesRef $ \simplRules ->
                    simplRules ++ trips ["==","<==>"] axs
                simplRules <- readIORef simplRulesRef
                modifyIORef transRulesRef
                    $ \transRules -> transRules ++ trips ["->"] axs
                -- let iniStates = [t | (F "states" _,_,F "[]" ts) <- simplRules]
                -- changeSimpl "states" $ mkList iniStates
                labGreen' $ newCls "axioms" file
            else do
                enterFormulas' cls
                labRed' "The clauses in the text field are not axioms."

        addSpec' :: Bool -> FilePath -> Action
        addSpec' b file = do
            checking <- readIORef checkingRef
            unless checking $ do
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
        
        addSpecWithBase :: FilePath -> Action
        addSpecWithBase spec = do
          addSpec' True "base"
          when (spec /= "base") $ addSpec' True spec

        addTheorems :: TermS -> FilePath -> Action
        addTheorems t file = do
            -- sig <- getSignature
            modifyIORef theoremsRef $ \theorems ->
                theorems `join` if isConjunct t then subterms t else [t]
            labGreen' $ newCls "theorems" file
        
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
              isConstruct'  = (`elem` cs)  ||| isJust . parse int
                              ||| isJust . parse real
                              ||| isJust . parse quoted
                              ||| isJust . parse (strNat "inj")
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
        
        parseConjects :: Sig -> FilePath -> String -> Action
        parseConjects sig file conjs =
            case parseE (implication sig) conjs of
                Correct t -> do
                    let ts = if isConjunct t then subterms t else [t]
                    modifyIORef conjectsRef $ \conjects -> conjects `join` ts
                p -> incorrect p conjs illformed
        
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
                    labRed' illformedSig
                _ -> do
                    labRed' illformedSig
        
        parseTerms :: Sig -> FilePath -> String -> Action
        parseTerms sig file ts =  case parseE (term sig) ts of
            Correct t -> do
                let ts = if isSum t then subterms t else [t]
                modifyIORef termsRef $ \terms -> ts `join` terms
            p -> incorrect p ts illformed
          
        -- modified test versions
        incorrect :: Parse TermS -> String -> String -> Action
        incorrect _ _ error = labRed' error
        
        labRed' :: String -> Action
        labRed' = assertFailure . ("Expander error message: "++)
        
        labGreen' :: String -> Action
        labGreen' _ = return ()

        delay :: Action -> Action
        delay = id

        newCls :: String -> FilePath -> String
        newCls _ _ = ""

        enterFormulas' :: [TermS] -> Action
        enterFormulas' _ = return ()

        newSig :: FilePath -> String
        newSig = id

        getTextHere :: IO String
        getTextHere = error "file not found"

    addSpecWithBase spec
    return ()
    