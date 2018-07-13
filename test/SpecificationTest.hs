module SpecificationTest (tests) where

import Test.Framework
import Test.Framework.Providers.HUnit
import Test.HUnit

import System.Expander
import Eterm
import Esolve

import Control.Monad (void, msum, when, unless, filterM)
import Data.IORef
import Data.Maybe (isJust, fromJust, isNothing, fromMaybe)
import Prelude hiding ((++),concat)
import System.Directory
import System.FilePath


tests =  test_all_specifications

mkSpecTest name = testCase name $ loadSpec name

test_all_specifications = buildTest $ do
    dir <- builtinLibDir
    list <- listDirectory dir
    listOfFiles <- filterM (doesFileExist . (dir </>)) list
    let listOfSpecs = filter (not . hasExtension) listOfFiles
        listOfTests = map mkSpecTest listOfSpecs
        tests = testGroup "specifications" listOfTests
    return tests

type Cmd = IO
type Action = Cmd ()
type Request = Cmd

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
    