{-
Module      : Epaint (update from November 15, 2021)
Copyright   : (c) Peter Padawitz and Jos Kusiek, 2021
License     : BSD3
Stability   : experimental
Portability : portable

Epaint contains:

* compilers of trees into pictures,
* the painter,
* functions generating, modifying or combining pictures.
-}

module Epaint where

import Eterm
import Prelude ()
import qualified Base.Haskell as Haskell
import Base.System
import Data.Array
import Graphics.Rendering.Cairo.Types (LineCap (LineCapRound))

infixr 5 <:>, <++>

font16 :: Maybe String
font16 = Just "font16"

labFont :: IO FontDescription
labFont = fontDescriptionFromString "Sans italic 16"

monospace, defaultButton :: String
monospace     = "Monospace 18"    -- original Courier is not supported by all OS
defaultButton = "default_button"

-- Solver record

data Solver = Solver
    { addSpec         :: Bool -> FilePath -> Action
                                       -- adds a specification from a file
    , backWin         :: Action        -- minimizes a solver window
    , bigWinR         :: Action 
    , checkInSolver   :: Action
    , drawCurr        :: Action        -- draws the current tree
    , buildSolve      :: Action        -- creates and initializes the solver GUI
    , enterTextR      :: String -> Action        -- shows text in text field
    , enterFormulasR  :: [TermS] -> Action       -- shows formulas in text field
    , enterTreeR      :: Bool -> TermS -> Action -- shows tree on canvas
    , getEntry        :: Request String    -- gets string from entry field
    , getSolver       :: Request String    -- returns name of this solver object
    , getText         :: Request String    -- returns content of text area
    , getFont         :: Request FontDescription
    , getPicNo        :: Request Int
    , getSignatureR   :: Request Sig
    , getTreeR        :: Request (Maybe TermS)
    , isSolPos        :: Int -> Request Bool
    , labBlueR         :: String -> Action
                         -- shows string in left label field
                         -- and sets the field background to blue
    , labRedR          :: String -> Action
                         -- shows string in left label field
                         -- and sets the field background to a pulsating red
    , labGreenR        :: String -> Action
                         -- shows string in left label field
                         -- and sets the field background to green
    , narrow          :: Action
    , proofBackward   :: Action
    , proofForward    :: Action
    , saveGraphDP     :: Bool -> Canvas -> Int -> Action
    , setCurrInSolve  :: Int -> Action
    , setForw         :: ButtonOpts -> Action 
    , setQuit         :: ButtonOpts -> Action
    , setInterpreterR :: String -> Action
    , setNewTreesR    :: [TermS] -> String -> Action
    , setSubst        :: (String -> TermS,[String]) -> Action
    , showPicts       :: Action
    , simplify        :: Action
    , stopRun         :: Action
    }
  
data Step = AddAxioms [TermS] | ApplySubst | ApplySubstTo String TermS |
            ApplyTransitivity | BuildKripke Int | BuildRE | Coinduction |
            CollapseStep Bool | CollapseVars | ComposePointers | CopySubtrees |
            CreateIndHyp | CreateInvariant Bool | DecomposeAtom | DerefNodes |
            DetKripke | Distribute | EvaluateTrees | ExpandTree Bool Int | 
            FlattenImpl | Generalize [TermS] | Induction | 
            Mark [[Int]] [[Int]] |Matching Int Int | Minimize | ModifyEqs Int | 
            MoveQuant | Narrow Int Bool | NegateAxioms [String] [String] |
            PermuteSubtrees | RandomLabels | RandomTree | ReduceRE Int |
            RefNodes | Refuting Bool | ReleaseNode | ReleaseSubtree |
            ReleaseTree | RemoveCopies | RemoveEdges Bool | RemoveNode |
            RemoveOthers | RemovePath | RemoveSubtrees | RenameVar String |
            ReplaceNodes String | ReplaceOther |
            ReplaceSubtrees [[Int]] [TermS] | ReplaceText String |
            ReplaceVar String TermS [Int] | ReverseSubtrees | SafeSimpl Bool |
            SetAdmitted Bool [String] | SetCurr String Int | SetDeriveMode |
            ShiftPattern | ShiftQuants | ShiftSubs [[Int]] | ShowKripke |
            Simplify Int Bool | Simplifying Bool |
            SimplStrat Strategy Strategy | SplitTree | StretchConclusion |
            StretchPremise | SubsumeSubtrees | Theorem Bool TermS |
            Transform Int | UnifySubtrees | POINTER Step deriving (Eq,Show)

-- small templates

data Runner = Runner {startRun :: Int -> Action, stopRun0 :: Action}

runner :: Action -> Template Runner
runner act = do runRef <- newIORef undefined
                return Runner {startRun = \millisecs 
                                           -> do run0 <- periodic millisecs act
                                                 writeIORef runRef run0
                                                 runnableStart run0,
                               stopRun0 = readIORef runRef >>= runnableStop}

-- used by Ecom > runChecker

runner2 :: (Int -> Action) -> Int -> Template Runner
runner2 act bound = do
    runRef <- newIORef undefined
    nRef <- newIORef 0
    let startRun millisecs = do run0 <- periodic millisecs loop
                                writeIORef runRef run0
                                runnableStart run0
        loop = do n <- readIORef nRef; act n
                  if n < bound then modifyIORef nRef succ else stopRun0
        stopRun0 = readIORef runRef >>= runnableStop
    return Runner {startRun = startRun, stopRun0 = stopRun0}

-- used by Ecom > saveGraph

switcher :: Action -> Action -> Template Runner                      -- not used
switcher actUp actDown = do
    runRef <- newIORef undefined
    upRef  <- newIORef True
    let startRun millisecs = do run0 <- periodic millisecs loop
                                writeIORef runRef run0
                                runnableStart run0
        loop = do up <- readIORef upRef
                  if up then actUp else actDown
                  modifyIORef upRef not
    return Runner {startRun = startRun, 
                   stopRun0 = readIORef runRef >>= runnableStop}

oscillator :: (Int -> Action) -> (Int -> Action) -> Int -> Int -> Int
              -> Template Runner
oscillator actUp actDown lwb width upb = do 
    runRef <- newIORef undefined            
    valRef <- newIORef (lwb - 1)
    upRef  <- newIORef True
    let startRun millisecs = do run0 <- periodic millisecs loop
                                writeIORef runRef run0
                                runnableStart run0
        loop = do up <- readIORef upRef
                  val <- readIORef valRef
                  if up then do actUp val; writeIORef valRef (val + width)
                        else do actDown val; writeIORef valRef (val-width)
                  when (val < lwb || val > upb) (writeIORef upRef (not up))
    return Runner {startRun = startRun, 
                   stopRun0 = readIORef runRef >>= runnableStop}
        
-- used by Epaint and Ecom > labRed

data Scanner = Scanner {startScan0 :: Int -> Picture -> Action,
                        startScan  :: Int -> Action,
                        addScan    :: Picture -> Action,
                        stopScan0  :: Action,
                        stopScan   :: Action,
                        isRunning  :: Request Bool}

scanner :: (Widget_ -> Action) -> Template Scanner
scanner act = do                                
    runRef     <- newIORef undefined
    runningRef <- newIORef False
    asRef      <- newIORef []
    return $ let startScan0 delay bs = do writeIORef asRef bs
                                          startScan delay
                 startScan delay = do running <- readIORef runningRef
                                      run <- readIORef runRef
                                      as <- readIORef asRef
                                      when running $ runnableStop run
                                      run0 <- periodic delay loop
                                      runnableStart run0
                                      writeIORef runRef run0
                                      writeIORef runningRef True
                 loop = do as <- readIORef asRef
                           case as of 
                                w:s -> do when (noRepeat w) $ writeIORef asRef s
                                          act w
                                          when (isFast w) loop
                                _ -> stopScan
                 stopScan = do 
                             running <- readIORef runningRef
                             when running $ do readIORef runRef >>= runnableStop 
                                               writeIORef runningRef False
             in Scanner {startScan0 = startScan0,
                         startScan  = startScan,
                         addScan    = \bs -> do as <- readIORef asRef
                                                writeIORef asRef $ bs++as,
                         stopScan0  = stopScan >> writeIORef asRef [],
                         stopScan   = stopScan,
                         isRunning  = readIORef runningRef}
            
-- used by drawPict,scaleAndDraw

-- PAINTER types

type Point   = (Double,Double)
type Point3  = (Double,Double,Double)
type Line_   = (Point,Point)
type Lines   = [Line_]
type Path    = [Point]
type State   = (Point,Double,Color,Int) -- (center,orientation,hue,lightness)
type Graph   = (Picture,Arcs)
type Picture = [Widget_]
type Arcs    = [[Int]]
type TermW   = Term Widget_

-- ([w1,...,wn],[as1,...,asn]) :: Graph represents a graph with node set 
-- {w1,...,wn} and edge set {(wi,wj) | j in asi, 1 <= i,j <= n}.

data Widget_ = Arc State Double Double Double | Bunch Widget_ [Int] |
               Dot Color Point | Fast Widget_ | Gif Int Bool String Widget_ |
               New | Tria State Double | Text_ State Int [String] [Int] | 
               Oval State Double Double | Path Double State Int Path | 
               Path0 Double Color Int Int Path | 
               Poly State Int [Double] Double | Rect State Double Double | 
               Repeat Widget_ | Skip | Slice State ArcStyleType Double Double |
               Tree State Graph | Turtle State Double [TurtleAct] | WTree TermW 
               deriving (Read,Show,Eq)

-- Bunch combines a widget with the list of the target indices of w.
-- The Int parameter of Text_ is the text height.
-- The center of Tree .. ct agrees with the root of ct.
-- Wtree ocurs only as a singeton picture: WTree in pict ==> pict = [Wtree t]

data TurtleAct = Close | Draw | Jump Double | JumpA Double | Move Double | 
                 MoveA Double | Open Int | OpenC Color | OpenS Double | 
                 OpenW Double | Turn Double | Widg Bool Widget_ 
                 deriving (Read,Show,Eq)
                  
-- JumpA and MoveA ignore the scale of the enclosing turtle.
-- The Int parameter of Open determines the mode of the path ending when the 
-- next Close/Draw command is reached; see drawWidget (Path0 c i m ps).
-- Widg False w ignores the orientation of w.
-- Widg True w adds it to the orientation of the enclosing turtle.
-- Close and Draw finish a polygon resp. path starting at the preceding Open 
-- command.

type WidgTrans = Widget_ -> Widget_
type PictTrans = Picture -> Picture
type ActsTrans = [TurtleAct] -> [TurtleAct]

instance Root Widget_ where undef = Skip

isWidg,isPict,isTree,isTurt,isFast,isSkip,isRedDot,propNode :: Widget_ -> Bool
isWidg (Dot _ _)      = True    
isWidg (Oval _ _ _)   = True
isWidg (Path _ _ _ _) = True
isWidg (Poly _ m _ _) = m < 4           -- poly/S/F/SF
isWidg (Rect _ _ _)   = True    
isWidg (Tria _ _)     = True    
isWidg _              = False
isPict (Poly _ m _ _) = m > 3           -- polyR/L/T/LT 
isPict (Turtle _ _ _) = True
isPict _              = False    
isTree (Tree _ _)     = True
isTree _              = False
isTurt (Turtle _ _ _) = True
isTurt _              = False
isFast (Fast _)       = True
isFast _              = False
isSkip (Bunch w _)    = isSkip w
isSkip Skip           = True
isSkip _              = False
isRedDot (Bunch w _)           = isRedDot w
isRedDot (Dot (RGB 255 0 0) _) = True
isRedDot _                     = False
propNode = not . (isRedDot ||| isSkip)

isWAct :: TurtleAct -> Bool
isWAct (Widg _ _) = True
isWAct _          = False
 
propNodes :: Picture -> [Int]
propNodes pict = [i | i <- indices_ pict, propNode $ pict!!i]
                              
shiftPict rect pict sc = (map (transXY (-x1,-y1)) pict',size) where
   (pict',bds) = foldr f ([],(0,0,0,0)) $ indices_ pict
   f i (ws,bds) = (w:ws,minmax4 (widgFrame w) bds)
                  where w = scaleWidg 0 (sc i) $ pict!!i
   (x1,y1,x2,y2) = if just rect then minmax4 (widgFrame $ get rect) bds else bds
   size = apply2 (max 100 . round . (+110)) (x2-x1,y2-y1)

-- PAINTER messages

combi :: Show a => a -> String
combi n = "The current combination is " ++ show n ++ "."
 
decoupled str = str ++ " of the current graph have been decoupled."

noPictIn :: String -> String
noPictIn file = file ++ " does not contain a picture term."

subtreesMsg :: String -> String
subtreesMsg solver = "The selected subtrees of " ++ solver ++ 
                     " have the following pictorial representations:"

treesMsg :: (Eq b, Num b, Show b, Show a) => a -> b -> String -> Bool -> String
treesMsg k 1 solver b =
                       "A single tree has a pictorial representation. It is " ++
                       ("solved and " `onlyif` b) ++ "located at position " ++
                       show k ++ " of " ++ solver ++ "."
treesMsg k n solver b = show n ++
                   " trees have pictorial representations. The one below is " ++
                   ("solved and " `onlyif` b) ++ "located at position " ++
                   show k ++ " of " ++ solver ++ "."

saved :: String -> String -> String
saved "graphs" file = "The trees have been saved to " ++ file ++ "."
saved "trees" file = "The trees have been saved to " ++ file ++ "."
saved object file  = "The " ++ object ++ " has been saved to " ++ file ++ "."

savedCode :: String -> String -> String
savedCode object file = "The Haskell code of the " ++ object ++ 
                        " has been saved to " ++ file ++ "."
 
unturtled str = str ++ " of the current graph have been unturtled."

-- PAINTER record and template

type ButtonOpts = (Button, IORef (ConnectId Button)) -> Action
type MenuOpts   = MenuItem -> IORef (ConnectId MenuItem) -> Action

data Painter = Painter {buildPaint     :: Bool -> Action,
                        callPaint      :: [Picture] -> [Int] -> Bool -> Int 
                                           -> String -> Pos -> String -> Action,
                        getNewCheck    :: Request Bool,
                        labSolver      :: String -> Action,
                        remote         :: Action,
                        setButton      :: Int -> ButtonOpts -> Action,
                        setCurrInPaint :: Int -> Action,
                        setNewCheck    :: Action}

painter :: Int -> IORef Solver -> IORef Solver -> Template Painter
painter pheight solveRef solve2Ref = do
    builder <- loadGlade "Painter"
    let getObject :: GObjectClass cls => (GObject -> cls) -> String -> IO cls
        getObject = builderGetObject builder
        getButton = getObject castToButton
        getLabel  = getObject castToLabel
        getScale  = getObject castToScale
    but1 <- getButton "button1"
    but2 <- getButton "button2"
    but3 <- getButton "button3"
    ref1 <- newIORef $ error "narrowButSignal not set"
    ref2 <- newIORef $ error "simplifyDSignal not set"
    ref3 <- newIORef $ error "simplifyBSignal not set"
    canv <- canvas
    scrollCanv <- getObject castToScrolledWindow "scrollCanv"
    combiBut <- getButton "combiBut"
    fastBut <- getButton "fastBut"
    edgeBut <- getButton "edgeBut"
    lab <- getLabel "lab"
    modeEnt <- getObject castToEntry "modeEnt"
    pictSlider <- getScale "pictSlider"
    saveEnt <- getObject castToEntry "saveEnt"
    saveDBut <- getButton "saveDBut"
    spaceEnt <- getObject castToEntry "spaceEnt"
    stopBut <- getButton "stopBut"
    win <- getObject castToWindow "win"
    colorSlider <- getScale "colorSlider"
    scaleSlider <- getScale "scaleSlider"
    delaySlider <- getScale "delaySlider"
    
    fontRef <- newIORef undefined
    stopButSignalRef <- newIORef $ error "undefined stopButSignalRef"
    
    -- canvSizeRef <- newIORef (0,0)
    colorScaleRef <- newIORef (0,[])
    colsRef <- newIORef 0
    currRef <- newIORef 0
    -- delayRef <- newIORef 1
    drawModeRef <- newIORef 0
    gradeRef <- newIORef 0
    noOfGraphsRef <- newIORef 0
    spreadRef <- newIORef (0,0)
    
    oldRscaleRef <- newIORef 1
    rscaleRef <- newIORef 1
    scaleRef <- newIORef 1
    
    arrangeModeRef <- newIORef "t1"
    bgcolorRef <- newIORef white
    
    fastRef <- newIORef False
    connectRef <- newIORef False
    subtreesRef <- newIORef False
    isNewRef <- newIORef True
    isNewCheckRef <- newIORef True
     
    changedWidgetsRef <- newIORef nil2
    oldGraphRef <- newIORef nil2
   
    picturesRef <- newIORef []
    edgesRef <- newIORef []
    permutationRef <- newIORef []
    rectIndicesRef <- newIORef []
    scansRef <- newIORef []
    solverMsgRef <- newIORef []
    treeNumbersRef <- newIORef []
    
    oldRectRef <- newIORef Nothing
    -- osciRef <- newIORef Nothing
    penposRef <- newIORef Nothing
    rectRef <- newIORef Nothing
    sourceRef <- newIORef Nothing
    targetRef <- newIORef Nothing
    bunchpictRef <- newIORef Nothing
    
    let addPict = do
            file <- gtkGet saveEnt entryText
            rect <- readIORef rectRef
            rscale <- readIORef rscaleRef
            scale <- readIORef scaleRef
            (pict,arcs) <- loadGraph file
            (pictures,edges,curr) <- currGraph
            if null pict then labRed $ file ++ " is not a graph."
            else do let graph@(pict',arcs') = (pictures!!curr,edges!!curr)
                        f sc pict = concatGraphs [graph,(spict,arcs)]
                                    where spict = scalePict 0 (1/sc) pict
                    case rect of 
                         Just r -> do let (x,y,_,_) = widgFrame r
                                          pict1 = map (transXY (x,y)) pict
                                      graph@(pict',_) <- f rscale pict1
                                      setCurrGraph graph
                                      let inds = getRectIndices pict' rscale r
                                      writeIORef rectIndicesRef inds
                         _ -> do graph <- f scale pict
                                 setCurrGraph graph
                    scaleAndDraw $ file ++ " has been added."
        
        arrangeButton "perm" graph@(pict,arcs) = do 
            old <- readIORef permutationRef
            arrangeMode <- readIORef arrangeModeRef
            let new = nextPerm old
            writeIORef permutationRef new
            setCurrGraph $ if isCTreeMode arrangeMode 
                           then (permuteTree old new,arcs)
                           else permutePositions graph old new
            scaleAndDraw "The widgets have been permuted."
            where permuteTree is ks = fold2 exchgWidgets pict ss ts
                                      where (ss,ts) = unzip $ permDiff is ks
                  permutePositions gr is ks = fold2 exchgPositions gr ss ts
                                      where (ss,ts) = unzip $ permDiff is ks
        arrangeButton mode graph@(pict,_) = do 
            writeIORef arrangeModeRef mode
            let x = head mode 
                (colsNo,angle) = (parse pnat *** parse real) $ drop 2 mode
            if x `elem` "at" 
               then writeIORef gradeRef $ if just angle then get angle else 0
               else writeIORef colsRef $ if just colsNo then get colsNo 
                                                        else square pict
            d <- spaceEnt `gtkGet` entryText
            let dist = parse real d
            if just dist
               then writeIORef spreadRef $ apply2 (*(get dist)) (10,10)
               else when (x == 'm') $ writeIORef spreadRef (0,0)
            arrangeGraph True act graph
            where act gr = do setCurrGraph gr
                              scaleAndDraw "The widgets have been arranged."

-- used by arrangeOrCopy
        
        arrangeGraph changed act graph = do
            scale <- readIORef scaleRef
            spread <- readIORef spreadRef
            grade <- readIORef gradeRef
            arrangeMode <- readIORef arrangeModeRef
            cols <- readIORef colsRef
            let graph2@(pict,_) = scaleGraph scale graph1
                f x = case parse nat x of 
                           Just i -> pict!!i
                           _ -> if x == "<+>" then Skip else posWidg x
                ws = termWToPict arrangeMode spread grade 
                        $ mapT (scaleWidg 0 scale . f) $ graphToTerm True graph1
                actS = act . scaleGraph (1/scale)
            if isTreeMode arrangeMode 
               then if changed then do writeIORef bunchpictRef $ Just ws
                                       actS $ pictToGraph ws
                               else act graph
               else do writeIORef bunchpictRef Nothing
                       actS $ shelf graph2 cols spread 'M' True True arrangeMode
            where graph1 = bunchesToArcs graph 
                       
-- used by arrangeButton,newPaint
      
        arrangeOrCopy = do
            (pictures,edges,curr) <- currGraph
            rect <- readIORef rectRef
            case rect of
             Just r@(Rect _ b _) -> do
                  rectIndices <- readIORef rectIndicesRef
                  scale <- readIORef scaleRef
                  rscale <- readIORef rscaleRef
                  let (pict,arcs) = (pictures!!curr,edges!!curr)
                      ms = rectIndices
                      ns = indices_ pict `minus` ms
                      lg = length pict
                      translate = transXY (2*b,0)
                      vs = [pict!!n | n <- ms]
                      ws = scalePict 0 (rscale/scale) vs
                      pict' = fold2 updList pict ms ws
                      arcs' = foldl f arcs ns ++    -- add arcs into rect
                              map (map g . (arcs!!)) ms  
                                                    -- add arcs in and from rect
                      f arcs n = updList arcs n $ is++map g (ms`meet`is)
                                 where is = arcs!!n
                      g m = case search (== m) ms of Just i -> lg+i; _ -> m
                  writeIORef oldRectRef rect
                  writeIORef oldRscaleRef rscale
                  setCurrGraph (pict'++map translate vs,arcs')
                  writeIORef rectRef $ Just $ translate r
                  writeIORef rectIndicesRef [lg..lg+length ms-1]
                  scaleAndDraw "The selection has been copied."
             _ -> do mode <- modeEnt `gtkGet` entryText
                     when (notnull mode) $ do 
                       arrangeMode <- readIORef arrangeModeRef
                       spread <- readIORef spreadRef
                       grade <- readIORef gradeRef
                       graph@(pict,arcs) <- concatGraphs $ zip pictures edges
                       writeIORef picturesRef [pict]
                       writeIORef edgesRef [arcs]
                       writeIORef noOfGraphsRef 1
                       writeIORef currRef 0
                       pictSlider `gtkSet` [widgetSensitive := False]
                       arrangeButton mode graph
        
        buildPaint checking = do
          solve <- readIORef solveRef
          solver <- getSolver solve
          icon <- iconPixbuf
          gtkSet win [windowTitle := "Painter" ++ [last solver],
                      windowDefaultHeight := pheight,
                      windowIcon := Just icon]
          on win deleteEvent $ do lift close; return True
          
          fast <- readIORef fastRef
          gtkSet fastBut [buttonLabel := if fast then "slow" else "fast"]
          on fastBut buttonActivated switchFast
          
          font <- fontDescriptionFromString "Sans italic 16"
          widgetOverrideFont lab $ Just font
          
          font <- fontDescriptionFromString monospace
          widgetOverrideFont modeEnt $ Just font
          widgetOverrideFont saveEnt $ Just font
          widgetOverrideFont spaceEnt $ Just font
          
          gtkSet stopBut [buttonLabel := "stop"]
          stopButSignal <- on stopBut buttonActivated $ interrupt True
          writeIORef stopButSignalRef stopButSignal
                    
          let f (but,ref) str act = do               -- Gtk needs signals
                                   gtkSet but [buttonLabel := str]
                                   addContextClass but defaultButton
                                   on but buttonActivated act >>= writeIORef ref
          if checking then do f (but1,ref1) "<---" $ do proofBackward solve
                                                        showPicts solve
                              f (but2,ref2) "--->" $ do proofForward solve
                                                        showPicts solve
                              f (but3,ref3) "stop run" $ stopRun solve
          else do f (but1,ref1) "narrow/rewrite" $ do remote; narrow solve
                                                      showPicts solve
                  f (but2,ref2) "simplify" $ do remote; simplify solve
                                                showPicts solve
                  f (but3,ref3) "" done
          when checking $ writeIORef isNewCheckRef False
          
          on combiBut buttonActivated combis
          on edgeBut buttonActivated switchConnect
          on saveDBut buttonActivated saveGraphD
            
          closeBut <- getButton "closeBut"
          gtkSet closeBut [buttonLabel := "back to " ++ solver]
          on closeBut buttonActivated close
          
          modeBut <- getButton "modeBut"
          on modeBut buttonActivated arrangeOrCopy
                               
          renewBut <- getButton "renewBut"
          on renewBut buttonActivated $ showPicts solve
            
          resetScaleBut <- getButton "resetScaleBut"
          on resetScaleBut buttonActivated resetScale
             
          solve2 <- readIORef solve2Ref
          solver2 <- getSolver solve2
          solBut <- getButton "solBut"
          gtkSet solBut [buttonLabel := "show in " ++ solver2]
          on solBut buttonActivated showInSolver
             
          undoBut <- getButton "undoBut"
          on undoBut buttonActivated undo

          let setLeft act = do but <- eventButton
                               lift $ when (but == LeftButton) act
                               return False
          on colorSlider valueChanged moveColor
          on colorSlider buttonPressEvent $ setLeft pressColorScale
          on colorSlider buttonReleaseEvent $ setLeft releaseColor
          on delaySlider buttonReleaseEvent $ setLeft setDelay
          -- on delaySlider valueChanged
          --           $ gtkGet delaySlider rangeValue >>= writeIORef delayRef
          on pictSlider valueChanged $ do n <- gtkGet pictSlider rangeValue
                                          writeIORef currRef $ truncate n
          on pictSlider buttonReleaseEvent $ setLeft remoteDraw
          on scaleSlider valueChanged moveScale
          on scaleSlider buttonPressEvent $ setLeft pressColorScale
          on scaleSlider buttonReleaseEvent $ setLeft releaseScale
            
          -- scroll support for canvas
          containerAdd scrollCanv $ getDrawingArea canv
          changeCanvasBackground white

          let drawingArea = getDrawingArea canv
          widgetAddEvents drawingArea
                         [Button1MotionMask,Button2MotionMask,Button3MotionMask]
          on drawingArea buttonPressEvent $ do 
                                    n <- eventButton; p <- eventCoordinates
                                    lift $ pressButton (fromEnum n) $ round2 p
                                    return False
          on drawingArea motionNotifyEvent $ do
                                    modifier <- eventModifierMouse
                                    p <- eventCoordinates
                                    let b m = m `elem` [Button1,Button2,Button3]
                                        rp = round2 p
                                    lift $ case Haskell.find b modifier of 
                                                Just Button1 -> moveButton 1 rp
                                                Just Button2 -> moveButton 2 rp
                                                Just Button3 -> moveButton 3 rp
                                                _ -> done
                                    return False
          on drawingArea buttonReleaseEvent $ do 
                                    n <- eventButton
                                    lift $ releaseButton $ fromEnum n
                                    return False
          on lab keyPressEvent $ do key <- eventKeyName
                                    lift $ case unpack key of "d" -> decouple
                                                              "p" -> mkPlanar
                                                              "t" -> mkTurtle
                                                              "u" -> unTurtle
                                                              _ -> done
                                    return False
          on saveEnt keyPressEvent $ do 
                                 key <- eventKeyName
                                 lift $ case unpack key of "Up" -> addPict
                                                           "Down" -> saveGraph
                                                           "Right" -> removePict
                                                           _ -> done
                                 return False
          widgetShowAll win
          writeIORef isNewRef False
          windowIconify win
        
        callPaint picts poss b n picEval hv back = do
            when (notnull graphs) $ do
                 writeIORef noOfGraphsRef $ length graphs
                 let (pictures,edges) = unzip graphs
                 writeIORef picturesRef pictures
                 writeIORef edgesRef edges
                 solve <- readIORef solveRef
                 getFont solve >>= writeIORef fontRef
                 writeIORef treeNumbersRef poss
                 writeIORef subtreesRef b
                 writeIORef bgcolorRef $ case parse color back of 
                                              Just col -> col; _ -> white
                 noOfGraphs <- readIORef noOfGraphsRef
                 modifyIORef currRef $ \curr -> 
                                 if b then if curr < noOfGraphs then curr else 0
                                      else get $ search (== n) poss ++ Just 0
                 writeIORef scaleRef 1
                 writeIORef arrangeModeRef ar
                 writeIORef spreadRef sp
                 isNew <- readIORef isNewRef
                 if isNew then buildPaint False >> newPaint else newPaint
            where graphs = map pictToGraph $ filter notnull picts
                  (ar,sp) = if picEval == "tree" then ("t1",fromInt2 hv) 
                                                 else ("m1",(0,0))
        
        changeCanvasBackground c@(RGB r g b) = do    -- Gtk only
            gtkSet canv [canvasBackground := c]
            widgetModifyBg scrollCanv StateNormal $ gtkColor (f r) (f g) (f b)
            where f n = fromIntegral $ n * 256
             
        close = do
            scans <- readIORef scansRef
            mapM_ stopScan0 scans
            clear canv
            windowIconify win
            solve <- readIORef solveRef; bigWinR solve
            stopRun solve
            checkInSolver solve
        
        combis = do
            str <- gtkGet spaceEnt entryText
            modifyIORef drawModeRef $ \drawMode -> case parse nat str of
                                                   Just n | n < 16 -> n
                                                   _ -> (drawMode+1) `mod` 16
            gtkSet spaceEnt [entryText := ""]
            drawMode <- readIORef drawModeRef
            setBackground combiBut $ if drawMode == 0 then blueback else redback
            scaleAndDraw $ combi drawMode

        concatGraphs []      = return nil2
        concatGraphs [graph] = return graph
        concatGraphs graphs  = do
            spread <- readIORef spreadRef
            grade <- readIORef gradeRef
            arrangeMode <- readIORef arrangeModeRef
            let pict = termWToPict arrangeMode spread grade
                f graph@([WTree t],_) = pictToGraph $ pict t
                f graph               = graph
                (picts,arcss) = unzip $ map (bunchesToArcs . f) graphs
            return (concat picts,foldl g [] arcss)
            where g arcs = (arcs++) . map (map (+(length arcs)))

-- used by addPict,arrangeOrCopy

        currGraph = do 
            pictures <- readIORef picturesRef
            edges <- readIORef edgesRef
            curr <- readIORef currRef
            return (pictures,edges,curr)
                         
        decouple = do
            (pictures,edges,curr) <- currGraph
            rect <- readIORef rectRef
            rectIndices <- readIORef rectIndicesRef
            let (graph,inds) = unTree (pictures!!curr,edges!!curr) $ 
                                      if just rect then (`elem` rectIndices)
                                                   else const True
            setCurrGraph graph                   
            if just rect 
               then do writeIORef oldRectRef rect
                       writeIORef rectIndicesRef inds
                       scaleAndDraw $ decoupled "All trees in the selection"
               else scaleAndDraw $ decoupled "All trees"
        
        draw55 = drawPict . map (transXY (5,5))
        
        drawArcs col graph = do
            arrangeMode <- readIORef arrangeModeRef
            let f ps = line canv (map round2 ps) $ 
                                 lineOpt {lineFill = col, lineSmooth = True, 
                                          lineArrow = case arrangeMode of 
                                                           "no" -> Nothing
                                                           "fi" -> Just First
                                                           "bo" -> Just Both
                                                           _ -> Just Last}
            when (arrangeMode /= "dis") $ do mapM_ f $ buildAndTrimPaths graph
        
        drawPict pict = do
            fast <- readIORef fastRef
            if fast || all isFast pict then mapM_ drawWidget pict
            else do scans <- readIORef scansRef
                    delay <- getDelay
                    let lgs = length scans
                        (picts1,picts2) = splitAt lgs picts
                        g sc pict = do run <- isRunning sc
                                       (if run then addScan else h) sc pict
                        h sc = startScan0 sc delay
                    zipWithM_ g scans picts1
                    when (lgp > lgs) $ do
                        scs <- Haskell.replicateM (lgp-lgs) $ scanner drawWidget
                        zipWithM_ h scs picts2
                        modifyIORef scansRef (++scs)
           where picts = if New `elem` pict then f pict [] [] else [pict]
                 f (New:pict) picts pict' = f pict (picts++[pict']) []
                 f (w:pict) picts pict'   = f pict picts $ pict'++[w]
                 f _ picts pict'          = picts++[pict']
                 lgp = length picts
        
        drawText :: Point -> Color -> Int -> String -> IO () 
        drawText p c i x = do
            bgcolor <- readIORef bgcolorRef
            let col = if c == white then bgcolor
                      else mkLight i $ case parse colPre x of 
                                            Just (c',_) | c == black -> c'
                                            _ -> c
            font <- readIORef fontRef
            canvasText canv (round2 p) textOpt {textFill = col,
                                                textJustify = CenterAlign,
                                                textFont = Just font}
                                       $ delQuotes x
        
        drawWidget (Arc ((x,y),a,c,i) w r b) = do
            bgcolor <- readIORef bgcolorRef
            let out = outColor c i bgcolor
            canvasArc canv (x,y) r (-a,b) $
                   arcOpt {arcStyle = Perimeter, arcOutline = out, arcWidth = w}
            done
        drawWidget (Fast w) = 
            if isPict w then mapM_ drawWidget $ mkPict w else drawWidget w
        drawWidget (Gif pos alpha file hull) = do
            let (p,_,c,_) = getState hull
            if c == white then drawWidget hull
            else do pic <- loadPhoto pos alpha file
                    mapM_ (canvasImage canv (round2 p) imageOpt) pic
        drawWidget (Oval ((x,y),0,c,i) rx ry) = do
            bgcolor <- readIORef bgcolorRef
            canvasOval canv (x,y) (rx,ry) $
                       ovalOpt {ovalOutline = outColor c i bgcolor,
                                ovalFill = Just $ fillColor c i bgcolor}
            done
        drawWidget (Path0 w c i m ps) = do
            bgcolor <- readIORef bgcolorRef
            let out = outColor c i bgcolor
                fill = Just $ fillColor c i bgcolor
                optsL :: Int -> LineOpt
                optsL 0 = lineOpt {lineFill = out, lineWidth = w,
                                   lineCapStyle = LineCapRound}
                optsL _ = (optsL 0) {lineSmooth = True}
                optsP :: Int -> PolygonOpt
                optsP 2 = polygonOpt {polygonOutline = out,
                                      polygonFill = fill}
                optsP _ = (optsP 2) {polygonSmooth = True}
            if m < 2 then act (line canv) $ optsL m
                     else act (canvasPolygon canv) $ optsP m
            where act f opts = mapM_ (flip f opts . map round2) $ splitPath ps
                            -- do flip f opts $ map round2 ps; done
        drawWidget (Repeat w) = drawWidget w
        drawWidget Skip       = done
        drawWidget (Slice ((x,y),a,c,i) t r b) = do
            bgcolor <- readIORef bgcolorRef
            let out = outColor c i bgcolor
                fill = Just $ fillColor c i bgcolor
            canvasArc canv (x,y) r (-a,b) $
                      arcOpt {arcStyle = t, arcOutline = out, arcFill = fill}
            done
        drawWidget (Text_ (p,_,c,i) height strs lgs) = zipWithM_ f [0..] strs
            where ps = textsCtrs p height lgs
                  f k = drawText (ps!!k) c i
        drawWidget (Tree (p,a,c,i) (pict,arcs)) = do
            drawPict pict'
            bgcolor <- readIORef bgcolorRef
            drawArcs (outColor c i bgcolor) (pict',arcs)
            where pict' = moveTurnPict p a pict
        drawWidget w | isWidg w = drawWidget $ reduceWidg w
                     | isPict w = drawPict $ mkPict w
        drawWidget _            = done
        
        getDelay = do rv <- gtkGet delaySlider rangeValue
                      return $ truncate rv

        getNewCheck = readIORef isNewCheckRef

        interrupt b = if b then do scans <- readIORef scansRef
                                   mapM_ stopScan scans
                                   stopBut `gtkSet` [buttonLabel := "go"]
                                   replaceCommandButton stopButSignalRef stopBut
                                                      $ interrupt False
                           else do delay <- getDelay
                                   scans <- readIORef scansRef
                                   mapM_ (`startScan` delay) scans 
                                   gtkSet stopBut [buttonLabel := "stop"]
                                   replaceCommandButton stopButSignalRef stopBut
                                                      $ interrupt True
        
        labColor :: String -> Background -> Action
        labColor str color = do gtkSet lab [labelText := str]
                                setBackground lab color
        
        labGreen,labRed :: String -> Action
        labGreen = flip labColor greenback
        labRed   = flip labColor redpulseback
        
        labSolver = writeIORef solverMsgRef
        
        loadGraph file = do
            str <- lookupLibs file         
            if null str then do solve <- readIORef solveRef
                                labRedR solve $ file ++ " is not a file name."
                                return nil2
            else case parse graphString str of Just graph -> return graph
                                               _ -> return nil2
      -- used by addPict
        
        mkPlanar = do
            n <- saveEnt `gtkGet` entryText  
            (pictures,edges,curr) <- currGraph
            let maxmeet = case parse pnat n of Just n -> n; _ -> 200
                reduce = planarAll maxmeet (pictures!!curr,edges!!curr)
            rect <- readIORef rectRef
            if just rect then do rectIndices <- readIORef rectIndicesRef
                                 rscale <- readIORef rscaleRef
                                 let (graph,is) = reduce rect rectIndices rscale
                                 writeIORef rectIndicesRef is
                                 finish graph maxmeet True
            else do scale <- readIORef scaleRef
                    finish (fst $ reduce Nothing [] scale) maxmeet False
            where finish graph maxmeet b = do
                    setCurrGraph graph
                    scaleAndDraw $  
                      "The " ++ (if b then "selection" else "current graph") ++
                      " has been reduced to widgets that overlap in at most " ++
                      show maxmeet ++ " pixels."
        
        mkTurtle = do
            (pictures,edges,curr) <- currGraph
            rect <- readIORef rectRef
            rectIndices <- readIORef rectIndicesRef
            rscale <- readIORef rscaleRef
            let (pict,arcs) = (pictures!!curr,edges!!curr)
                Rect (p@(x,y),_,_,_) b h = get rect
                ks@(k:rest) = rectIndices
                w = transXY p
                    $ mkTurt (x-b,y-h) rscale $ map (pict!!) rectIndices
            if just rect then
               case map (pict!!) ks of
                   [Turtle {}] -> labGreen "The selection is already a turtle."
                   _ -> do setCurrGraph $ removeSub (updList pict k w,arcs) rest
                           writeIORef rectIndicesRef [k]
                           scaleAndDraw "The selection has been turtled."
            else case pict of
                      [Turtle {}] -> labGreen "The picture is already a turtle."
                      _ -> do scale <- readIORef scaleRef
                              setCurrGraph ([mkTurt p0 scale pict],[[]])
                              scaleAndDraw "The current graph has been turtled."
                                                   
        moveButton n p@(x,y) = do
            penpos <- readIORef penposRef
            when (just penpos) $ do 
                (pictures,_,curr) <- currGraph
                let (x0,y0) = get penpos
                    q@(x1,y1) = fromInt2 (x-x0,y-y0)
                    pict = pictures!!curr
                connect <- readIORef connectRef
                if connect    -- draw (smooth) arc, exchange nodes or move color
                   then do scale <- readIORef scaleRef
                           case getWidget (fromInt2 p) scale pict of
                                widget@(Just (_,w)) 
                                  -> do source <- readIORef sourceRef
                                        if nothing source 
                                           then writeIORef sourceRef widget 
                                           else writeIORef targetRef widget
                                        drawPict [lightWidg w]
                                _ -> done
                else case n of                         
                      1 -> do (ns,vs) <- readIORef changedWidgetsRef
                              let translate = transXY q
                                  ws = map translate vs
                              writeIORef changedWidgetsRef (ns,ws)
                              rectIndices <- readIORef rectIndicesRef
                              when (ns `shares` rectIndices) $ -- move selection
                                   modifyIORef rectRef $ Just . translate . get
                      2 -> do rect <- readIORef rectRef
                              when (just rect) $ do         -- enlarge selection
                                   let r@(Rect (p,_,_,_) b h) = get rect
                                       r' = Rect (add2 p q,0,black,0) (b+x1) 
                                                 $ h+y1
                                   writeIORef rectRef $ Just r'
                                   setFast True
                                   draw55 [delWidg r,r']
                      _ -> do changedWidgets <- readIORef changedWidgetsRef
                              let (ns,vs) = changedWidgets     -- rotate widgets
                                  ws = map (turnWidg x1) vs    
                              writeIORef changedWidgetsRef (ns,ws)
                              setFast True
                              rect <- readIORef rectRef
                              draw55 $ map delWidg vs ++ 
                                       case rect of Just r -> r:ws; _ -> ws
                writeIORef penposRef $ Just p
        
        moveColor = do
            n0 <- gtkGet colorSlider rangeValue
            let n = truncate n0
            when (n /= 0) $ do
                 modifyIORef colorScaleRef $ \(_, csSnd) -> (n,csSnd)
                 (_,ws) <- readIORef changedWidgetsRef
                 when (pictSize ws < 20) $ do setFast True
                                              draw55 $ map (shiftCol n) ws
        
        moveScale = do 
            n0 <- gtkGet scaleSlider rangeValue
            let n = truncate n0
            when (n /= 0) $ do 
                 rect <- readIORef rectRef
                 rscale <- readIORef rscaleRef
                 scale <- readIORef scaleRef
                 changedWidgets <- readIORef changedWidgetsRef
                 colorScale <- readIORef colorScaleRef
                 let sc = if just rect then rscale else scale
                     (_,us) = colorScale
                     (is,vs) = changedWidgets
                     ws = scalePict 0 (sc+fromInt n/10*sc) us 
                 writeIORef colorScaleRef (n,us)
                 when (pictSize ws < 20) $ do
                      writeIORef changedWidgetsRef (is,ws)
                      setFast True
                      draw55 $ map delWidg vs ++ 
                               case rect of Just r -> r:ws; _ -> ws

        newPaint = do
            solve <- readIORef solveRef; backWin solve
            windowDeiconify win; windowPresent win
            bgcolor <- readIORef bgcolorRef; changeCanvasBackground bgcolor
            gtkSet stopBut [buttonLabel := "stop"]
            replaceCommandButton stopButSignalRef stopBut $ interrupt True
            subtrees <- readIORef subtreesRef
            noOfGraphs <- readIORef noOfGraphsRef
            rangeSetRange pictSlider 0 $ fromIntegral $ noOfGraphs-1
            (pictures,edges,curr) <- currGraph
            gtkSet pictSlider [rangeValue := fromIntegral curr
                              , widgetSensitive := True]
            writeIORef rectRef Nothing
            writeIORef rectIndicesRef []
            writeIORef changedWidgetsRef nil2
            writeIORef gradeRef 0
            writeIORef colsRef 6
            arrangeMode <- readIORef arrangeModeRef
            gtkSet modeEnt [entryText := arrangeMode]
            spread <- readIORef spreadRef
            grade <- readIORef gradeRef
            let graph@(pict,_) = (pictures!!curr,edges!!curr)
                ws = termWToPict arrangeMode spread grade $ pictToTermW pict
                (bunch,new) = if isTreeMode arrangeMode 
                              then (Just ws,pictToGraph ws) else (Nothing,graph)
                act (pict,arcs) = do
                     modifyIORef picturesRef $ \picts -> updList picts curr pict
                     modifyIORef edgesRef $ \edges -> updList edges curr arcs
                     writeIORef permutationRef $ propNodes pict
                     scaleAndDraw ""              
            writeIORef bunchpictRef bunch 
            arrangeGraph False act new where
               -- pictToTermW [w1,..,wn] returns F(Skip)[t1,..,tn] where ti is
               -- the widget term that is equivalent to wi.
                  pictToTermW :: Picture -> TermW
                  pictToTermW [WTree t] = t
                  pictToTermW [w]       = leaf w
                  pictToTermW pict      = F Skip $ zipWith f [0..] pict where
                   f i (Text_ _ _ [x] _) | take 4 x == "pos " 
                         = V $ posWidg $ "pos "++unwords (map show $ i:getPos x)
                   f _ w = leaf w

        pressButton n p = do
            scans <- readIORef scansRef
            mapM_ stopScan0 scans
            (pictures,edges,curr) <- currGraph
            when (notnull pictures) $ do
              writeIORef penposRef $ Just p
              rectIndices <- readIORef rectIndicesRef
              let p' = fromInt2 p
                  (pict,arcs) = (pictures!!curr,edges!!curr)
                  f sc = scalePict 0 sc $ map (pict!!) rectIndices
              connect <- readIORef connectRef
              scale <- readIORef scaleRef
              rect <- readIORef rectRef
              rscale <- readIORef rscaleRef
              rectIndices <- readIORef rectIndicesRef
              when (not connect) $ case n of                         
                1 -> case rect of
                          Just r | p' `inRect` r -> do         -- move selection
                             writeIORef changedWidgetsRef (rectIndices,f rscale)
                             canv `gtkSet` [canvasCursor := Dotbox]
                          _ -> do scale <- readIORef scaleRef
                                  case getWidget p' scale pict of
                                     Just (n,w) -> do          -- move widget
                                          writeIORef changedWidgetsRef ([n],[w])
                                          canv `gtkSet` [canvasCursor := Hand2]
                                     _ -> done                  
                2 -> do writeIORef oldRectRef rect
                        writeIORef oldRscaleRef rscale
                        let pict' = 
                               fold2 updList pict rectIndices $ f $ rscale/scale
                        if just rect then do                 -- remove selection
                           setCurrGraph (pict',arcs) 
                           writeIORef rectRef Nothing
                           writeIORef rectIndicesRef []   
                        else do                              -- create selection
                             writeIORef rectRef $ Just (Rect (p',0,black,0) 0 0)
                             canv `gtkSet` [canvasCursor := Icon]
                        writeIORef rscaleRef scale
                _ -> do writeIORef changedWidgetsRef $ 
                                     if just rect then (rectIndices,f rscale)
                                     else (indices_ pict,scalePict 0 scale pict)
                        canv `gtkSet` [canvasCursor := Exchange]       -- rotate
        
        pressColorScale = do 
            scans <- readIORef scansRef
            mapM_ stopScan0 scans
            (pictures,_,curr) <- currGraph
            rect <- readIORef rectRef
            rectIndices <- readIORef rectIndicesRef
            let pict = pictures!!curr; ws = map (pict!!) rectIndices
            if just rect then do
               rscale <- readIORef rscaleRef
               writeIORef changedWidgetsRef (rectIndices,scalePict 0 rscale ws)
               writeIORef colorScaleRef (0,ws)
            else do 
              scale <- readIORef scaleRef
              writeIORef changedWidgetsRef(indices_ pict,scalePict 0 scale pict)
              writeIORef colorScaleRef (0,pict)

        releaseButton n = do
            (pictures,edges,curr) <- currGraph
            connect <- readIORef connectRef
            let graph@(pict,arcs) = (pictures!!curr,edges!!curr)
            if connect then do
               source <- readIORef sourceRef
               target <- readIORef targetRef
               if nothing source || nothing target then nada
               else do let (s,v) = get source
                           (t,w) = get target
                           ts = arcs!!s
                           is = getSupport graph s t
                           redDots = just is
                           connected = redDots || t `elem` ts
                           (_,_,c,i) = getState v
                           f (p,a,_,_) = (p,a,c,i)
                           w' = updState f $ pict!!t
                           graph1 = if redDots then removeSub graph $ get is
                                    else (pict,updList arcs s $ ts `minus1` t)
                           graph2 = (pict,updList arcs s $ t:ts)
                       arrangeMode <- readIORef arrangeModeRef
                       case n of
                        1 -> if arrangeMode == "paste"
                                then setDrawSwitch (updList pict t w',arcs)
                                                  "The target has been colored."
                             else if connected then setDrawSwitch graph1 
                                                      "An arc has been removed."
                                  else if s == t then nada
                                       else setDrawSwitch graph2
                                                      "An arc has been drawn."
                        2 -> do let gr = if isCTreeMode arrangeMode
                                         then (exchgWidgets pict s t,arcs)
                                         else exchgPositions graph s t
                                setDrawSwitch gr
                                        "Source and target have been exchanged."
                        _ -> if s == t && just is || s /= t && connected && 
                                not (isRedDot v || isRedDot w) then nada
                             else setDrawSwitch (addSmoothArc graph 
                                    (s,t,v,w,ts)) "A smooth arc has been drawn."
            else do rect <- readIORef rectRef
                    rscale <- readIORef rscaleRef
                    scale <- readIORef scaleRef
                    changedWidgets <- readIORef changedWidgetsRef
                    arrangeMode <- readIORef arrangeModeRef
                    case n of
                     2 -> case rect of
                          Just r -> do let inds = getRectIndices pict rscale r
                                       writeIORef rectIndicesRef inds
                                       if null inds then 
                                          do writeIORef rectRef Nothing; nada
                                       else scaleAndDraw
                                                 "A subgraph has been selected."
                          _ -> scaleAndDraw "The selector has been removed."
                     _ -> do let f = if just rect then scaleWidg 0 $ 1/rscale
                                     else transXY (-5,-5). scaleWidg 0 (1/scale)
                                 g = fold2 updList
                                 pair w i j = (g pict ij [f w,pict!!i],
                                       g arcs ij $ map (map h . (arcs!!)) [j,i])
                                              where ij = [i,j]
                                                    h k | k == i = j
                                                        | k == j = i
                                                        | True   = k
                                 graph = case changedWidgets of 
                                       ([k],[w]) | nothing rect ->
                                        case arrangeMode of 
                                             "back" -> pair w 0 k
                                             "front" -> pair w (length pict-1) k
                                             _ -> (updList pict k $ f w,arcs)
                                       (ks,ws) -> (g pict ks $ map f ws,arcs)
                             setCurrGraph graph
                             scaleAndDraw 
                                      "The selection has been moved or rotated."
                    writeIORef penposRef Nothing
                    writeIORef sourceRef Nothing
                    writeIORef targetRef Nothing
                    writeIORef changedWidgetsRef nil2
                    canv `gtkSet` [canvasCursor := LeftPtr]
            where nada = scaleAndDraw "Nothing can be done."
                  setDrawSwitch graph str = do setCurrGraph graph
                                               scaleAndDraw str; switchConnect
        
        releaseColor = do
            (pictures,edges,curr) <- currGraph
            (n,_) <- readIORef colorScaleRef
            (is,_) <- readIORef changedWidgetsRef
            let f i w = if i `elem` is then shiftCol n w else w
                (pict,arcs) = (pictures!!curr,edges!!curr)
            when (n /= 0) $ do setCurrGraph (zipWith f [0..] pict,arcs)
                               scaleAndDraw ""
                               writeIORef changedWidgetsRef nil2
                               colorSlider `gtkSet` [rangeValue := 0]
        
        releaseScale = do
            (pictures,edges,curr) <- currGraph
            mode <- modeEnt `gtkGet` entryText
            (n,_) <- readIORef colorScaleRef
            rect <- readIORef rectRef
            rectIndices <- readIORef rectIndicesRef
            rscale <- readIORef rscaleRef
            scale <- readIORef scaleRef
            let sc = if just rect then rscale+fromInt n/10*rscale 
                                     else scale+fromInt n/10*scale
                f = updState $ \(p,a,c,i) -> (apply2 (*sc) p,a,c,i)
                (pict,arcs) = (pictures!!curr,edges!!curr)
                g p i w = if i `elem` rectIndices
                          then transXY p $ f $ transXY (neg2 p) w else w
            when (n /= 0) $ do
                 rect <- readIORef rectRef
                 rscale <- readIORef rscaleRef
                 case rect of
                      Just r@(Rect (p,_,_,_) _ _) 
                        -> do writeIORef oldRectRef rect
                              writeIORef oldRscaleRef rscale
                              if isTreeMode mode then 
                                 do writeIORef rectRef $ Just $ scaleWidg 0 sc r
                                    setCurrGraph (zipWith (g p) [0..] pict,arcs)
                              else writeIORef rscaleRef sc
                      _ | isTreeMode mode -> setCurrGraph (map f pict,arcs)
                        | True -> writeIORef scaleRef sc
                 scaleAndDraw ""
                 writeIORef changedWidgetsRef nil2
                 scaleSlider `gtkSet` [rangeValue := 0]
        
        remote = do
            subtrees <- readIORef subtreesRef
            when (not subtrees) $ do treeNumbers <- readIORef treeNumbersRef
                                     curr <- readIORef currRef
                                     solve <- readIORef solveRef
                                     setCurrInSolve solve (treeNumbers!!curr)
        
        remoteDraw = do
            solve <- readIORef solveRef
            remote; drawCurr solve; showPicts solve

        removePict = do
            (pictures,edges,curr) <- currGraph
            rect <- readIORef rectRef
            rscale <- readIORef rscaleRef
            scale <- readIORef scaleRef
            let graph@(pict,arcs) = (pictures!!curr,edges!!curr)
            if just rect then do writeIORef oldRectRef rect
                                 readIORef rscaleRef >>= writeIORef oldRscaleRef
                                 rectIndices <- readIORef rectIndicesRef
                                 setCurrGraph $ removeSub graph rectIndices
                                 writeIORef rectRef Nothing
                                 writeIORef rectIndicesRef []
                                 readIORef scaleRef >>= writeIORef rscaleRef
                                 scaleAndDraw "The selection has been removed."
            else do setCurrGraph nil2
                    readIORef scansRef >>= mapM_ stopScan0
                    clear canv; labGreen "The graph has been removed."
        
        resetScale = mapM_ (flip writeIORef 1) [oldRscaleRef,rscaleRef,scaleRef]
         
        saveGraph = do
            (pictures,edges,curr) <- currGraph
            if null pictures then labRed "Enter pictures!"
            else do file <- saveEnt `gtkGet` entryText
                    rect <- readIORef rectRef
                    rectIndices <- readIORef rectIndicesRef
                    rscale <- readIORef rscaleRef
                    scale <- readIORef scaleRef
                    filePath <- pixpath file
                    usr <- userLib file
                    let graph@(pict,arcs) = (pictures!!curr,edges!!curr)
                        (pict1,arcs1) = subgraph graph rectIndices
                        pict2 = scalePict 0 rscale pict1
                        (x,y,_,_) = pictFrame pict2
                        pict3 = map (transXY (-x,-y)) pict2
                        lg = length file
                        (prefix,suffix) = splitAt (lg-4) file
                        write = writeFile usr
                        msg str = labGreen $ savedCode str usr
                        act1 = mkHtml canv prefix filePath
                        act2 n = do writeIORef currRef n
                                    pictSlider `gtkSet`
                                               [rangeValue := fromIntegral n]
                                    remoteDraw; gtkDelay 100 $ act1 n; done
                        act3 =  case pict3 of
                           [w] -> do write $ show $ updState st w; msg "widget"
                           _   -> do write $ show (pict3,arcs1); msg "selection"
                        act4 = do write $ show (scalePict 0 scale pict,arcs)
                                  msg "entire graph"
                    if null file then labRed "Enter a file name!"
                    else if lg < 5 || suffix `notElem` words ".eps .png .gif" 
                            then if just rect then act3 else act4
                         else case pictures of
                              [_] -> do file <- savePic suffix canv filePath
                                        labGreen $ saved "graph" file
                              _ -> do renewDir filePath
                                      saver <- runner2 act2 $ length pictures-1
                                      startRun saver 500
                                      labGreen $ saved "graphs" 
                                               $ filePath ++ ".html"
            where st (_,_,c,_) = st0 c

        saveGraphD = do
            solve <- readIORef solveRef
            str <- saveEnt `gtkGet` entryText
            picNo <- getPicNo solve
            saveGraphDP solve False canv $ case parse nat str of Just n -> n
                                                                 _ -> picNo

        scaleAndDraw msg = do
            (pictures,edges,curr) <- currGraph
            scans <- readIORef scansRef
            mapM_ stopScan0 scans
            clear canv
            sc <- scanner drawWidget
            writeIORef scansRef [sc]
            gtkSet stopBut [buttonLabel := "stop"]
            replaceCommandButton stopButSignalRef stopBut $ interrupt True
            n <- gtkGet saveEnt entryText
            drawMode <- readIORef drawModeRef
            rect <- readIORef rectRef
            rectIndices <- readIORef rectIndicesRef
            rscale <- readIORef rscaleRef
            scale <- readIORef scaleRef
            let maxmeet = case parse pnat n of Just n -> n; _ -> 200
                graph = (pictures!!curr,edges!!curr)
                reduce = planarAll maxmeet graph
                (graph',is) = if drawMode == 15 && 
                                   msg /= "A subgraph has been selected."
                              then if just rect 
                                   then reduce rect rectIndices rscale
                                   else reduce Nothing [] scale
                              else (graph,rectIndices)
                (pict,arcs) = bunchesToArcs graph'
                sc i = if i `elem` is then rscale else scale
                (pict1,size) = shiftPict rect pict sc
                f = scaleWidg 0 . recip . sc
                mp pictures = updList pictures curr $ zipWith f [0..] pict1
                me edges = updList edges curr arcs
            modifyIORef picturesRef mp
            modifyIORef edgesRef me
            canv `gtkSet` [canvasSize := size]
            arrangeMode <- readIORef arrangeModeRef
            treeNumbers <- readIORef treeNumbersRef
            let pict2 = map (transXY (5,5)) pict1
                f = filter propNode
                pict3 = f pict2
                ws = if just rect then f $ map (pict3!!) is else pict3
                (hull,qs) = convexPath (map coords ws) pict3
            drawMode <- readIORef drawModeRef
            if drawMode `elem` [0,15] then drawPict pict2
            else case drawMode of 
                 1 -> drawPict pict3
                 2 -> drawPict $ f $ colorLevels True pict2 arcs
                 3 -> drawPict $ f $ colorLevels False pict2 arcs
                 4 -> drawPict $ pict3++hull
                 5 -> do font <- readIORef fontRef
                         (hei,wid) <- mkSizes canv font $ map show qs
                         let addNo x p = Text_ (p,0,dark red,0) hei [x] [wid x]
                         drawPict $ pict3++hull++zipWith (addNo . show) [0..] qs
                 _ -> drawPict $ joinPict drawMode pict3
            drawArcs black (pict2,arcs)
            when (just rect) $ 
                             do let (x1,y1,x2,y2) = pictFrame $ map (pict2!!) is
                                    (b,h) = (abs (x2-x1)/2,abs (y2-y1)/2)
                                    r = Rect ((x1+b,y1+h),0,black,0) b h
                                writeIORef rectRef $ Just r; draw55 [r]
            solve <- readIORef solveRef
            solver <- getSolver solve
            let k = treeNumbers!!curr
            b <- isSolPos solve k
            subtrees <- readIORef subtreesRef
            noOfGraphs <- readIORef noOfGraphsRef
            let str1 = if subtrees then subtreesMsg solver
                                   else treesMsg k noOfGraphs solver b
                add str = if null str then "" else '\n':str
            solverMsg <- readIORef solverMsgRef
            labGreen $ str1 ++ add solverMsg ++ add msg

        setButton 1 opts = opts (but1,ref1)
        setButton 2 opts = opts (but2,ref2)
        setButton 3 opts = opts (but3,ref3)

        setCurrGraph (pict,arcs) = do
            (pictures,edges,curr) <- currGraph
            let graph@(pict',_) = (pictures!!curr,edges!!curr)
            writeIORef oldGraphRef graph
            writeIORef picturesRef $ updList pictures curr pict
            writeIORef edgesRef $ updList edges curr arcs
            when (length pict /= length pict') $
                 writeIORef permutationRef $ propNodes pict
        
        setCurrInPaint n = do
            pictures <- readIORef picturesRef
            when (n < length pictures) $ do
                 writeIORef currRef n
                 pictSlider `gtkSet` [rangeValue := fromIntegral n]
                 scaleAndDraw ""
        
        setDelay = do 
            fast <- readIORef fastRef
            when (not fast) $ do
                 scans <- readIORef scansRef
                 runs <- mapM isRunning scans
                 let scs = [scans!!i | i <- indices_ scans, runs!!i]
                 if null scs then scaleAndDraw ""
                 else do delay <- getDelay
                         mapM_ (`startScan` delay) scs
        
        setFast b = do 
            writeIORef fastRef b
            isNew <- readIORef isNewRef
            when (not isNew) $
                 fastBut `gtkSet` [buttonLabel := if b then "slow" else "fast"]
        
        setNewCheck = writeIORef isNewCheckRef True

        showInSolver = do
            (pictures,edges,curr) <- currGraph
            rect <- readIORef rectRef
            rscale <- readIORef rscaleRef
            rectIndices <- readIORef rectIndicesRef
            let graph = bunchesToArcs (pictures!!curr,edges!!curr)
            solve2 <- readIORef solve2Ref
            enterTreeR solve2 False $ graphToTerm False $
                  if just rect 
                  then scaleGraph rscale $ subgraph graph rectIndices else graph
        
        switchConnect = do 
            modifyIORef connectRef not
            connect <- readIORef connectRef
            setBackground edgeBut $ if connect then redback else blueback

        switchFast = do
            fast <- readIORef fastRef
            setFast $ not fast
            scaleAndDraw ""
        
        undo = do
            drawMode <- readIORef drawModeRef
            if drawMode == 0 then do
              do oldGraph <- readIORef oldGraphRef
                 if null $ fst oldGraph
                    then labRed "The current graph has no predecessor."
                 else do oldGraph@(pict,_) <- readIORef oldGraphRef
                         setCurrGraph oldGraph
                         readIORef oldRectRef >>= writeIORef rectRef
                         readIORef oldRscaleRef >>= writeIORef rscaleRef
                         rscale <- readIORef rscaleRef
                         rect <- readIORef rectRef
                         writeIORef rectIndicesRef $
                                    maybe [] (getRectIndices pict rscale) rect
                         scaleAndDraw ""
            else do modifyIORef drawModeRef pred
                    drawMode <- readIORef drawModeRef
                    when (drawMode == 0) $ setBackground combiBut blueback
                    scaleAndDraw $ combi drawMode
        
        unTurtle = do
            (pictures,_,curr) <- currGraph
            rect <- readIORef rectRef
            rectIndices <- readIORef rectIndicesRef
            let (pict,is) = unTurt (pictures!!curr) $ 
                          if just rect then (`elem` rectIndices) else const True
            setCurrGraph $ pictToGraph pict                                           
            if just rect 
               then do writeIORef oldRectRef rect
                       modifyIORef rectIndicesRef (++is)
                       scaleAndDraw $ unturtled "All turtles in the selection"
               else scaleAndDraw $ unturtled "All turtles"
           
    return Painter {buildPaint     = buildPaint,
                    callPaint      = callPaint,
                    getNewCheck    = getNewCheck,
                    labSolver      = labSolver,
                    remote         = remote,
                    setButton      = setButton,
                    setCurrInPaint = setCurrInPaint,
                    setNewCheck    = setNewCheck}
                                       
replaceCommandButton :: ButtonClass button => IORef (ConnectId button) 
                                           -> button -> IO () -> IO ()
replaceCommandButton connectIdRef button act = do
                     id <- readIORef connectIdRef
                     signalDisconnect id
                     id <- on button buttonActivated act
                     writeIORef connectIdRef id

replaceCommandMenu :: MenuItemClass menuItem => IORef (ConnectId menuItem) 
                                             -> menuItem -> IO () -> IO ()
replaceCommandMenu connectIdRef menuItem act = do
                     id <- readIORef connectIdRef
                     signalDisconnect id
                     id <- on menuItem menuItemActivated act
                     writeIORef connectIdRef id
 
data WidgStore = WidgStore {saveWidg :: String -> Widget_ -> Action, 
                            loadWidg :: String -> Request Widget_}   -- not used
        
widgStore :: Template WidgStore                                      
widgStore = do
    storeRef <- newIORef $ const Skip
    return WidgStore
               {saveWidg = \file w -> do store <- readIORef storeRef
                                         writeIORef storeRef $ upd store file w,
                loadWidg = \file -> do store <- readIORef storeRef
                                       return $ store file}
                                       
-- basic PAINTER functions 
                   
isTreeMode (x:_) = x `elem` "aot"
isTreeMode _     = False
 
isCTreeMode (x:_) = x `elem` "acot"
isCTreeMode _     = False
 
-- used by arrangeButton,releaseButton

p0 :: Point
p0 = (0,0)

st0 :: Color -> State
st0 c = (p0,0,c,0)

st0B :: State
st0B = st0 black

path0 :: Double -> Color -> Int -> Path -> Widget_
path0 w = Path w . st0

getPict :: Maybe Picture -> Picture
getPict (Just pict) = pict
getPict _           = [Skip]

noRepeat :: Widget_ -> Bool
noRepeat (Repeat _) = False
noRepeat _          = True

fast :: WidgTrans
fast (Turtle st sc acts) = Fast $ Turtle st sc $ map f acts
                           where f (Widg b w) = Widg b $ fast w
                                 f act        = act
fast (Bunch w is)        = Bunch (fast w) is
fast (Fast w)            = fast w
fast w                   = Fast w

(<:>) :: TurtleAct -> [TurtleAct] -> [TurtleAct]
Move 0<:>acts            = acts
Move a<:>(Move b:acts)   = Move (a+b):acts
MoveA 0<:>acts           = acts
MoveA a<:>(MoveA b:acts) = MoveA (a+b):acts
Jump 0<:>acts            = acts
Jump a<:>(Jump b:acts)   = Jump (a+b):acts
JumpA 0<:>acts           = acts
JumpA a<:>(JumpA b:acts) = JumpA (a+b):acts
Turn 0<:>acts            = acts
Turn a<:>(Turn b:acts)   = Turn (a+b):acts
act<:>(act':acts)        = act:act'<:>acts
act<:>_                  = [act]

(<++>) :: [TurtleAct] -> [TurtleAct] -> [TurtleAct]
(act:acts)<++>acts' = act<:>acts<++>acts'
_<++>acts           = acts

reduceActs :: [TurtleAct] -> [TurtleAct]
reduceActs (act:acts) = act<:>reduceActs acts
reduceActs _          = []

up,down,back,open,wait :: TurtleAct
up   = Turn $ -90
down = Turn 90
back = Turn 180
open = OpenC black
wait = widg Skip

close2 :: [TurtleAct]
close2 = [Close,Close]

widg,wfast :: Widget_ -> TurtleAct
widg  = Widg False
wfast = widg . fast
  
posWidg :: String -> Widget_
posWidg x = Text_ st0B 0 [x] [0]

textWidget :: Color -> Sizes -> String -> Widget_
textWidget c (height,width) x = Text_ (st0 c) height strs $ map width strs
                                where strs = map (map h) $ words $ map (g . f) x
                                      f ' ' = '\"'; f c = c
                                      g '\'' = ' '; g c = c
                                      h '\"' = ' '; h c = c

inRect :: (Double,Double) -> Widget_ -> Bool
(x',y') `inRect` Rect ((x,y),_,_,_) b h = x-b <= x' && x' <= x+b &&
                                           y-h <= y' && y' <= y+h
 
pictToGraph :: Picture -> Graph
pictToGraph pict = (pict,replicate (length pict) [])

pictSize :: Picture -> Int
pictSize = sum . map f where f (Path0 _ _ _ _ ps) = length ps
                             f w | isWidg w     = f $ reduceWidg w
                             f w | isPict w     = pictSize $ mkPict w
                             f (Bunch w _)      = f w
                             f (Fast w)         = f w
                             f (Repeat w)       = f w
                             f _                = 1

getPoints,getAllPoints :: Widget_ -> Path

getPoints (Path0 _ _ _ _ ps) = ps
getPoints _                  = error "getPoints"
  
getAllPoints (Bunch w _)        = getAllPoints w
getAllPoints (Fast w)           = getAllPoints w
getAllPoints (Repeat w)         = getAllPoints w
getAllPoints (Path0 _ _ _ _ ps) = ps
getAllPoints w | isWidg w       = getAllPoints $ reduceWidg w
getAllPoints w | isPict w       = concatMap getAllPoints $ mkPict w
getAllPoints w                  = concatMap getAllPoints $ hulls False w

removeSub,subgraph :: Graph -> [Int] -> Graph
removeSub (pict,arcs) (i:is) = removeSub graph $ f is where
                               graph = (context i pict,map f $ context i arcs)
                               f = foldl g []
                               g is k | k < i  = k : is
                                      | k == i = is
                                      | True   = (k-1) : is
removeSub graph _            = graph
subgraph graph@(pict,_)      = removeSub graph . minus (indices_ pict)
                         
center,gravity :: Widget_ -> Point
center w  = ((x1+x2)/2,(y1+y2)/2) where (x1,y1,x2,y2) = widgFrame w
gravity w = apply2 (/(fromInt $ length qs)) $ foldl1 add2 qs 
            where qs = mkSet $ getHullPts True w        
            
actsCenter :: [TurtleAct] -> Point
actsCenter acts = ((x1+x2)/2,(y1+y2)/2) 
                   where (x1,y1,x2,y2) = turtleFrame st0B 1 acts

jumpTo,moveTo :: Point -> [TurtleAct]
jumpTo (0,0) = []
jumpTo p     = [Turn a,Jump $ distance p0 p,Turn $ -a] where a = angle p0 p
moveTo (0,0) = []
moveTo p     = [Turn a,Move $ distance p0 p,Turn $ -a] where a = angle p0 p

getActs :: Widget_ -> [TurtleAct]
getActs Skip              = []
getActs (Turtle _ _ acts) = acts
getActs w                 = [widg w]

actsToCenter :: [TurtleAct] -> [TurtleAct]
actsToCenter acts = jumpTo (neg2 $ actsCenter acts) ++ acts

shiftWidg :: Point -> WidgTrans
shiftWidg (0,0) w = w
shiftWidg p w     = turtle0 (getCol w) $ jumpTo (neg2 p) ++ getActs w

inCenter :: WidgTrans -> WidgTrans
inCenter tr w = turtle0 (getCol w') $ jumpTo p ++ [widg w']
                where p = gravity w
                      w' = tr $ shiftWidg p w

addFrame :: Double -> Double -> Color -> Int -> Widget_ -> Widget_
addFrame width d c m w = turtle0 (getCol w) $ jumpTo (neg2 center)++
                                [widg $ path0 width c m $ last ps:ps]++getActs w
                          where (x1,y1,x2,y2) = widgFrame w
                                center = ((x1+x2)/2,(y1+y2)/2)
                                ps = [(x2d,y1d),(x2d,y2d),(x1d,y2d),(x1d,y1d)]
                                x1d = x1-d; y1d = y1-d; x2d = x2+d; y2d = y2+d
           
-- nodeLevels b graph!!n returns the length of a shortest path from a root of 
-- graph to n. nodeLevels True counts in control points. nodeLevels False 
-- disregards control points.

nodeLevels :: Bool -> Graph -> [Int]
nodeLevels b (pict,arcs) = iter (replicate (length nodes) 0) nodes
 where nodes = indices_ pict
       iter levels free = if null free then levels else iter levels' free'
                       where (levels',free') = f (levels,free`minus1`root) root
                             root = case searchGet g free of Just (_,m) -> m
                                                             _ -> head free
       g m = null [n | n <- nodes, m `elem` arcs!!n]
       f p i = foldl h p (arcs!!i)
             where h p@(levels,free) j = 
                     if j `notElem` free then p
                     else let k = if b && isRedDot (pict!!j) then 0 else 1
                          in f (updList levels j (levels!!i+k),free`minus1`j) j


-- used by shelf,colorLevels

-- colorLevels b pict arcs colors all nodes of pict on the same level with the
-- same color.

colorLevels :: Bool -> Picture -> Arcs -> Picture
colorLevels alternate pict arcs = map f nodes
      where nodes = indices_ pict
            levels = nodeLevels False (pict,arcs)
            f n = if propNode w then updCol (g alternate $ levels!!n) w else w
                  where w = pict!!n
            g True k = if odd k then complColor c else c
            g _ k    = hue 0 c (maximum levels+1) k
            c = case searchGet (/= black) $ map getCol $ filter propNode pict of
                     Just (_,d) -> d
                     _ -> red

-- used by scaleAndDraw

angle :: RealFloat a => (a,a) -> (a,a) -> a
angle (x1,y1) (x2,y2) = atan2' (y2-y1) (x2-x1)*180/pi    

atan2' :: RealFloat a => a -> a -> a
atan2' 0 0 = atan2 0 1
atan2' x y = atan2 x y

slope :: (Double, Double) -> (Double, Double) -> Double
slope (x1,y1) (x2,y2) = if x1 == x2 then fromInt maxBound else (y2-y1)/(x2-x1) 

-- successor moves on a circle.
-- successor p (distance p q) (angle p q) = q. 

successor :: Floating a => (a,a) -> a -> a -> (a,a)
successor (x,y) r a = (x+r*c,y+r*s) where (s,c) = sincos a               
                                 -- successor p 0 _ = p
                                 -- successor (x,y) r 0 = (x+r,y) 
                                 -- successor (x,y) r a = rotate (x,y) a (x+r,y)

sincos :: Floating t => t -> (t, t)
sincos a = (sin rad,cos rad) where rad = a*pi/180       -- sincos 0 = (0,1)

-- successor2 moves on an ellipse.

successor2 :: Floating a => (a,a) -> a -> a -> a -> (a,a)
successor2 (x,y) rx ry a = (x+rx*c,y+ry*s) where (s,c) = sincos a            

distance :: Floating a => (a,a) -> (a,a) -> a
distance (x1,y1) (x2,y2) = sqrt $ (x2-x1)^2+(y2-y1)^2
                                                         
perimeter :: Path -> Double
perimeter ps = if peri <= 0 then 0.01 else peri
               where peri = sum $ zipWith distance ps $ tail ps
               
addPoints :: Path -> [Double] -> Path
addPoints ps []               = ps
addPoints (p:ps@(q:_)) (d:ds) = if d > d' then p:addPoints ps (d-d':ds)
                                 else p:addPoints (successor p d a:ps) ds
                                where d' = distance p q; a = angle p q
addPoints _ _ = error "addPoints"
                     
adaptLength :: Int -> Path -> Path
adaptLength n ps = if n > 0 then addPoints ps $ dps/2:replicate (n-1) dps
                            else ps
                   where dps = perimeter ps/k; k = fromInt n

area :: Path -> Double
area ps = abs (sum $ zipWith f ps $ tail ps++[head ps])/2
          where f (x1,y1) (x2,y2) = (x1-x2)*(y1+y2)

mindist :: (Floating a, Ord a) => (a, a) -> [(a, a)] -> (a, a)
mindist p (q:qs) = f (distance p q,q) qs
              where f dr@(d',_) (q:qs) = if d < d' then f (d,q) qs else f dr qs
                                         where d = distance p q 
                    f (_,r) _                  = r 

-- straight ps checks whether ps represents a straight line.

straight :: Path -> Bool
straight ps = and $ zipWith3 straight3 ps tps $ tail tps where tps = tail ps

straight3 :: Point -> Point -> Point -> Bool
straight3 (x1,y1) (x2,y2) (x3,y3) = x1 == x2 && x2 == x3 || 
                                     x1 /= x2 && x2 /= x3 &&
                                    (y2-y1)/(x2-x1) == (y3-y2)/(x3-x2)
             
reducePath :: Path -> Path
reducePath (p:ps@(q:r:s)) | straight3 p q r = reducePath $ p:r:s
                          | True            = p:reducePath ps
reducePath ps                               = ps     

mkLines :: Path -> Lines
mkLines ps = zip qs $ tail qs where qs = reducePath ps

getLines,getAllLines :: Widget_ -> Lines
getLines    = mkLines . getPoints
getAllLines = mkLines . getAllPoints

-- rotate q a p rotates p clockwise by a around q on the axis (0,0,1).

rotate :: Point -> Double -> Point -> Point
rotate _ 0 p             = p         
rotate q@(i,j) a p@(x,y) = if p == q then p else (i+x1*c-y1*s,j+x1*s+y1*c)
                           where (s,c) = sincos a; x1 = x-i; y1 = y-j

-- rotateA q (a,nx,ny,nz) p rotates p clockwise by a around q on the axis
-- (nx,ny,nz).

rotateA :: Point -> Double -> Point3 -> Point -> Point    -- not used
rotateA _ 0 _ p                       = p
rotateA q@(i,j) a (nx,ny,nz) p@(x,y) = if p == q then p      
                                       else (f i (c'*nx*nx+c) (c'*nx*ny-s*nz),
                                             f j (c'*nx*ny+s*nz) (c'*ny*ny+c))
                                       where (s,c) = sincos a; c' = 1-c
                                             f i a b = i+(x-i)*a+(y-j)*b

mkActs :: Picture -> [(Point,Double)] -> [TurtleAct]
mkActs pict = (++[Close]) . fst . fold2 f ([open],p0) pict
              where f (acts,p) w (q,a) = (acts++acts',q) 
                      where acts' = [Turn b,Jump d,Turn $ a-b,widg w,Turn $ -a]
                            b = angle p q; d = distance p q

-- used by mkTurt and dots 
                                             
mkTurt :: Point -> Double -> Picture -> Widget_
mkTurt p sc pict = Turtle st0B (1/sc) $ actsToCenter acts
                   where pict' = scalePict 0 sc $ filter propNode pict
                         f = map $ coords***orient
                         acts = jumpTo (neg2 p) ++ mkActs pict' (f pict')
                
-- used by mkSnow,mkTurtle,planarAll,pictTrans
 
unTurt :: Picture -> (Int -> Bool) -> (Picture,[Int])
unTurt pict b = (pict',[k..k+n-1])
     where (_,pict',n) = foldr f (length pict-1,[],0) pict; k = length pict
           f w (i,pict,k) = if isTurt w && b i then (i-1,ws++pict,k+length ws-1) 
                                               else (i-1,w:pict,k)
                            where ws = mkPict w
                
-- used by planarAll,pictTrans,unTurtle
       
unTree :: Graph -> (Int -> Bool) -> (Graph,[Int])
unTree (pict,arcs) b = ((pict',arcs'),inds) where
    k = length pict-1
    inds = snd $ foldl f (0,[]) $ indices_ pict where
           f (n,ks) i = case pict!!i of 
                        Tree _ (_,arcs) 
                          | b i  -> (n+length arcs,ks++map (n+) (indices_ arcs))
                        _ | b i  -> (n+1,ks++[n])
                          | True -> (n+1,ks)
    pict' = snd $ foldr f (k,[]) pict 
            where f (Tree (p,a,_,_) (pict,_)) (i,pict') | b i 
                                = (i-1,moveTurnPict p a pict++pict')
                  f w (i,pict') = (i-1,w:pict')
    arcs' = snd $ foldr f (k,[]) pict 
            where f (Tree (p,a,_,_) (pict,as:arcs')) (i,arcss) | b i 
                                = (i-1,(map g (arcs!!i)++map h as)
                                       :map (map h) arcs'++arcss) 
                                  where h arc = get $ search (== w) pict' where
                                                w = moveTurnWidg p a $ pict!!arc
                  f _ (i,arcss) = (i-1,map g (arcs!!i):arcss) 
                  g arc = case pict!!arc of Tree (p,a,_,_) (w:_,_) | b arc
                                              -> h $ moveTurnWidg p a w
                                            w -> h w
                          where h w = get $ search (== w) pict'
                                
-- used by decouple

-- getRectIndices pict sc rect returns the indices of all widgets of pict within
-- rect.

getRectIndices :: Picture -> Double -> Widget_ -> [Int]
getRectIndices pict sc rect = [i | i <- indices_ scpict, 
                                   let w = scpict!!i, -- propNode w,
                                   f (coords w) || any f (getHullPts True w)]
                              where scpict = scalePict 0 sc pict
                                    f = (`inRect` rect)

-- used by addPict,releaseButton,undo

splitPath :: [a] -> [[a]]
splitPath ps = if null rs then [qs] else qs:splitPath (last qs:rs)
               where (qs,rs) = splitAt 99 ps
                
-- used by drawWidget Path0             

textsCtrs :: Point -> Int -> [Int] -> Path
textsCtrs (x,y) height lgs = map f $ indices_ lgs 
                             where h = m*fromInt (length lgs)
                                   f i = (x,y-h+m+fromInt i*k) 
                                   k = fromInt height+4
                                   m = k/2
                                  
-- used by drawWidget Text_ and hulls

getState :: Widget_ -> State
getState (Arc st _ _ _)   = st
getState (Dot c p)        = (p,0,c,0)
getState (Gif _ _ _ hull) = getState hull
getState (Oval st _ _)    = st
getState (Path _ st _ _)  = st
getState (Poly st _ _ _)  = st
getState (Rect st _ _)    = st
getState (Slice st _ _ _) = st
getState (Text_ st _ _ _) = st
getState (Tree st _ )     = st
getState (Tria st _)      = st
getState (Turtle st _ _)  = st
getState (Bunch w _)      = getState w
getState (Fast w)         = getState w
getState (Repeat w)       = getState w
getState _                = st0B

coords :: Widget_ -> Point
coords w = p where (p,_,_,_) = getState w

xcoord, ycoord :: Widget_ -> Double
xcoord = fst . coords
ycoord = snd . coords

orient :: Widget_ -> Double
orient w = a where (_,a,_,_) = getState w

getCol :: Widget_ -> Color
getCol w = c where (_,_,c,_) = getState w

filled,filledS :: Num a => Color -> a
filled c  = if c == black then 0 else 2
filledS c = if c == black then 0 else 3

updState,updStateDeep :: (State -> State) -> WidgTrans 
updState f (Arc st w r a)             = Arc (f st) w r a
updState f (Dot c p)                  = Dot c' p'
                                        where (p',_,c',_) = f (p,0,c,0)
updState f (Gif pos alpha file hull)  = Gif pos alpha file $ updState f hull
updState f (Oval st rx ry)            = Oval (f st) rx ry 
updState f (Path w st m ps)           = Path w (f st) m ps
updState f (Poly st m rs a)           = Poly (f st) m rs a
updState f (Rect st b h)              = Rect (f st) b h
updState f (Slice st t r a)           = Slice (f st) t r a
updState f (Text_ st height strs lgs) = Text_ (f st) height strs lgs
updState f (Tree st graph)            = Tree (f st) graph
updState f (Tria st r)                = Tria (f st) r
updState f (Turtle st sc acts)        = Turtle (f st) sc $
                                               map (updAux f updState) acts 
updState f (Bunch w is)               = Bunch (updState f w) is
updState f (Fast w)                   = Fast $ updState f w
updState f (Repeat w)                 = Repeat $ updState f w
updState _ w                          = w
updStateDeep f (Tree st (pict,arcs))  = Tree (f st) (map (updStateDeep f) pict,
                                                     arcs)
updStateDeep f (Turtle st sc acts)    = Turtle (f st) sc $ 
                                               map (updAux f updStateDeep) acts
updStateDeep f w                      = updState f w    
 
updAux f g (OpenC c)  = OpenC d where (_,_,d,_) = f $ st0 c
updAux f g (Widg b w) = Widg b $ g f w
updAux f g act        = act

-- reduceWidg (w (p,a,c,i) ..) rotates widget w around p by a and reduces the
-- widget to Oval or Path0.

reduceWidg :: WidgTrans
reduceWidg (Dot c p)               = Oval (p,0,c,0) 5 5
reduceWidg (Oval (p,a,c,i) rx ry)  = Path0 1 c i (filled c) $ map f [0,5..360]
                                     where f = rotate p a . successor2 p rx ry
reduceWidg (Path w (p,a,c,i) m ps) = Path0 w c i m qs
                                     where qs = map (rotate p a . add2 p) ps
reduceWidg (Poly (p,a,c,i) m rs b) = Path0 1 c i m $ last ps:ps
                                     where ps = polyPts p a b rs
reduceWidg (Rect (p@(x,y),a,c,i) b h) = Path0 1 c i (filled c) $ last qs:qs
                                        where ps = [(x+b,y-h),(x+b,y+h),
                                                    (x-b,y+h),(x-b,y-h)]
                                              qs = map (rotate p a) ps
reduceWidg (Tria (p@(x,y),a,c,i) r) = Path0 1 c i (filled c) $ last qs:qs where
                                      ps = [(x+lg,z),(x-lg,z),(x,y-r)]
                                      lg = r*0.86602         -- r*3/(2*sqrt 3)
                                                             -- = sidelength/2
                                      z = y+lg*0.57735       -- y+lg*sqrt 3/3
                                      qs = map (rotate p a) ps

-- used by drawWidget,hulls

polyPts :: Point -> Double -> Double -> [Double] -> Path
polyPts p a inc = fst . foldl f ([],a)
                    where f (ps,a) 0 = (ps,a+inc)
                          f (ps,a) r = (successor p r a:ps,a+inc)
                          
-- used by reduceWidg,hulls

type TurtleState = (Picture,[(Double,Double,Color,Int,Double,Path)])

mkPict :: Widget_ -> Picture

-- mkPict (Poly (p,a,c,i) mode rs b) with mode > 5 computes triangles or chords
-- of a rainbow polygon with center p, orientation a, inner color c, lightness
-- value i, radia rs and increment angle b.

mkPict (Poly (p,a,c,i) m (r:rs) b) = pict
  where (pict,_,_,_,_,_) = foldl f ([],successor p r a,a+b,c,1,False) $ rs++[r]
        lg = length rs+1
        f (pict,q@(x,y),a,c,k,d) r = if r == 0 then (pict,q,a+b,c,k+1,False)
                                               else (pict++new,p',a+b,c',1,d')
          where p'@(x',y') = successor p r a
                (new,c',d') = if m < 8                 -- polyR/R1/R2/R3
                              then if d then (pict',c,False)
                                   else (pict',hue (m-6) c (lg `div` 2) k,True)
                              else if m < 12           -- polyL/L1/L2/L3
                                   then (mkPict $ w c,hue (m-10) c lg k,d)
                              else if m < 16           -- polyT/T1/T2/T3
                                   then (pict',hue (m-14) c lg k,d)
                              else (mkPict $ w $ h 1,h $ k+k,d)
                                                       -- polyLT/LT1/LT2/LT3
                pict' = fst $ iterate g ([],q)!!k
                g (pict,q) = (pict++[Path0 1 c i 4 [p,q,q']],q')
                             where q' = add2 q $ apply2 (/n) (x'-x,y'-y)
                h = hue (m-16) c $ 2*lg
                n = fromInt k
                w c' = Turtle (p,0,c,i) 1 $ Turn (a-b*(n-1)/2):leafC h d c c'
                       where h = r/2; d = n*distance (h,0) (successor p0 h b)/2

-- mkPict (Turtle (p,a,c,i) sc acts) translates acts into the picture drawn by a
-- turtle that executes acts, starting out from point p with scale factor sc,
-- orientation a, color c and lightness value i.

mkPict (Turtle (p,a,c,i) sc acts) = case foldl f iniState acts of 
                                    (pict,(_,w,c,m,_,ps):_) -> g pict w c m ps
                                    (pict,_) -> pict
        where iniState = ([],[(a,1,c,0,sc,[p])])
              f :: TurtleState -> TurtleAct -> TurtleState
              f (pict,states@((a,w,c,m,sc,ps):s)) act = 
                   case act of Close     -> (g pict w c m ps,s)
                               Draw      -> (g pict w c m ps,(a,w,c,m,sc,[p]):s)
                               Jump d    -> (g pict w c m ps,(a,w,c,m,sc,[q]):s) 
                                              where q = successor p (d*sc) a
                               JumpA d   -> (g pict w c m ps,(a,w,c,m,sc,[q]):s)
                                                where q = successor p d a
                               Move d    -> (pict,(a,w,c,m,sc,ps++[q]):s) 
                                              where q = successor p (d*sc) a
                               MoveA d   -> (pict,(a,w,c,m,sc,ps++[q]):s) 
                                              where q = successor p d a
                               Open m    -> (pict,(a,w,c,m,sc,[p]):states)
                               OpenC c   -> (pict,(a,w,c,m,sc,[p]):states)
                               OpenS sc' -> (pict,(a,w,c,m,sc*sc',[p]):states) 
                               OpenW w   -> (pict,(a,w,c,m,sc,[p]):states)          
                               Turn b    -> (pict,(a+b,w,c,m,sc,ps):s)
                               Widg b x  -> (pict++[moveTurnScale b p a sc x],
                                             states)
                   where p = last ps
              f pair _ = pair
              g pict w c m ps = if length ps < 2 then pict
                                else pict++[Path w (p0,0,c,i) m $ reducePath ps]
mkPict w = [w]

-- used by convexPath,hulls,drawWidget

inFrame :: Point -> Point -> Point -> Bool
inFrame (x1,y1) (x,y) (x2,y2) = min x1 x2 `le` x && x `le` max x1 x2 &&
                                min y1 y2 `le` y && y `le` max y1 y2
                                where le a b = a < b || abs (a-b) < 0.5

-- used by crossing,inWidget,strands

-- interior p lines returns True iff p is located within lines.

interior :: Point -> Lines -> Bool
interior p@(_,y) = odd . length . filter (just . crossing ((p,q),q)) . addSuc
                   where q = (2000,y)

-- used by strands,joinPict 13/14

-- inWidget p@(x,y) = (== p) . coords ||| any (interior p) . getFrameLns 

inWidget :: Point -> Widget_ -> Bool
inWidget p w = inFrame (x1,y1) p (x2,y2) where (x1,y1,x2,y2) = widgFrame w

-- used by getWidget,joinPict 6

-- getWidget p scale pict returns a widget of pict close to p and scales it.

getWidget :: Point -> Double -> Picture -> Maybe (Int,Widget_)
getWidget p sc = searchGetR (not . isSkip &&& inWidget p) .
                 map (transXY (5,5) . scaleWidg 0 sc)

-- used by moveButton,pressButton

getHullPts :: Bool -> Widget_ -> Path
getHullPts edgy = concatMap getPoints . hulls edgy

-- used by getRectIndices,gravity,mkSnow,morphPict,turtleFrame,widgFrame

getFrameLns :: Widget_ -> [Lines]
getFrameLns = map getLines . hulls False

-- used by hullCross

-- hulls edgy w computes frame paths of w.

hulls :: Bool -> Widget_ -> Picture
hulls edgy = f where
 f (Arc (p,a,c,i) _ r b) = if r <= 0 then [] else [Path0 1 c i (filledS c) ps]
                           where ps = q:g (21*r')++reverse qs 
                                      where qs@(q:_) = g $ 19*r'; r' = r/20
                                 g = polyPts p a (-b/36) . replicate 37
 f (Gif _ _ _ hull) = f hull
 f (Oval (p,a,c,i) rx ry) | a == 0 || rx == ry
               = [Path0 1 c i (filledS c) $ map (successor2 p rx ry) [0,5..360]]
 f x@(Path0 _ c i m ps)    = [if edgy || even m then x 
                                                else Path0 1 c i m $ spline ps]
 f (Slice (p,a,c,i) t r b) = if r <= 0 then [] 
                             else [Path0 1 c i (filledS c) $ 
                                   if t == Pie then p:g r++[p] else last qs:qs] 
                             where qs = g r
                                   g = polyPts p a (-b/36) . replicate 37
 f (Text_ (p,a,c,i) height _ lgs) = concatMap f $ zipWith g ps lgs where
                              ps = textsCtrs p height lgs
                              g p lg = Rect (p,a,c,i) b h where b = fromInt lg/2
                              h = (fromInt height+4)/2
 f (Tree (p,a,_,_) (pict,_)) = concatMap f $ moveTurnPict p a pict
 f w | isWidg w              = f $ reduceWidg w
     | isPict w              = concatMap f $ mkPict w
 f (Bunch w _)               = f w
 f (Fast w)                  = f w
 f (Repeat w)                = f w
 f _                         = [] 

-- used by dots,getFrameLns,getHullPts,joinPict,outline,splinePict,strands

stringsInPict :: Picture -> [String]
stringsInPict = concatMap stringsInWidg

-- used by Ecom > showMatrix,showSubtreePicts,showTransOrKripke,showTreePicts

stringsInWidg :: Widget_ -> [String]
stringsInWidg (Bunch w _)        = stringsInWidg w
stringsInWidg (Fast w)           = stringsInWidg w
stringsInWidg (Repeat w)         = stringsInWidg w
stringsInWidg (Text_ _ _ strs _) = strs
stringsInWidg (Tree _ (pict,_))  = stringsInPict pict
stringsInWidg (Turtle _ _ acts)  = concatMap f acts where
                                   f (Widg _ w) = stringsInWidg w
                                   f _          = []
stringsInWidg (WTree t)          = foldT f t where
                                   f w strs = stringsInWidg w++concat strs
stringsInWidg  _                 = []

-- GRAPHICAL INTERPRETERS
 
turtle0 ::  Color -> [TurtleAct] -> Widget_
turtle0 c = Turtle (st0 c) 1 . reduceActs
 
turtle0B :: [TurtleAct] -> Widget_
turtle0B = turtle0 black
 
jturtle :: [TurtleAct] -> Maybe Widget_
jturtle = Just . turtle0B
 
jturtleP :: [TurtleAct] -> Maybe Picture
jturtleP = Just . single . turtle0B

rturtle :: [TurtleAct] -> MaybeT Cmd Picture
rturtle = lift' . jturtleP

loadWidget :: Color -> Sizes -> TermS -> Cmd Widget_
loadWidget c sizes t = do str <- lookupLibs file
                          if null str then return w
                          else return $ case parse widgString $ removeComment 0 
                                                                str of 
                                             Just w -> w
                                             _ -> w
                       where file = showTerm0 t
                             w = textWidget c sizes file

loadTerm :: Sig -> Color -> Sizes -> TermS -> Cmd TermS
loadTerm sig c sizes t = do str <- lookupLibs file
                            if null str then return u
                            else return $ case parse (term sig) $ removeComment 
                                                                  0 str of
                                               Just t -> t
                                               _ -> u
                         where file = showTerm0 t
                               u = leaf $ show c++'$':file

saveWidget :: Widget_ -> TermS -> Cmd ()
saveWidget w t = do path <- userLib $ showTerm0 t; writeFile path $ show w

saveTerm :: TermS -> TermS -> Cmd ()
saveTerm t u = do path <- userLib $ showTerm0 u; writeFile path $ showTerm0 t

concatJust :: Monad m => [MaybeT m [a]] -> MaybeT m [a]
concatJust s = maybeT $ do s <- mapM runT s
                           return $ do guard $ any just s
                                       Just $ concat [as | Just as <- s]

type Interpreter = Sizes -> Pos -> TermS -> MaybeT Cmd Picture

-- The following functions to MaybeT(Cmd)(Picture) are used by 
-- Ecom > getInterpreter.

-- searchPic eval ... t recognizes the maximal subtrees of t that are
-- interpretable by eval and combines the resulting pictures into a single one.

searchPic :: Interpreter -> Interpreter
searchPic eval sizes spread t = g [] t where
       g p t = maybeT $ do pict <- runT (eval sizes spread t)
                           if just pict then return pict
                           else case t of F _ ts -> runT $ h ts
                                          _ -> return Nothing
                        where h = concatJust . zipWithSucs g p . changeLPoss q r
                              q i = [i]; r i = []

-- solPic sig eval ... t recognizes the terms of a solution t that are
-- interpretable by eval and combines the resulting pictures into a single one.

solPic :: Sig -> (Sig -> Interpreter) -> Interpreter
solPic sig eval sizes spread t = case parseSol (solAtom sig) t of
                                      Just sol -> concatJust $ map f sol
                                      _ -> zero
                                 where f = eval sig sizes spread . getTerm
 
-- used by Ecom > getInterpreter

linearEqs :: Sizes -> TermS -> MaybeT Cmd Picture 
linearEqs sizes = f 
          where f (F x [t]) | x `elem` words "bool gauss gaussI" = f t
                f t = lift' $ do eqs <- parseLinEqs t
                                 jturtleP $ termMatrix sizes $ g eqs 1
                g ((poly,b):eqs) n = map h poly++(str,"=",mkConst b):g eqs (n+1)
                                     where h (a,x) = (str,x,mkConst a)
                                           str = show n
                g _ _ = []

planes :: Int -> Sizes -> TermS -> MaybeT Cmd Picture
planes mode sizes t = do guard $ not $ isSum t
                         rturtle $ drawPlanes sizes mode t

alignment :: Sizes -> TermS -> MaybeT Cmd Picture
alignment sizes t = lift' $ do ali <- parseAlignment t
                               jturtleP $ drawAlignment sizes ali

dissection :: TermS -> MaybeT Cmd Picture
dissection (Hidden (Dissect quads)) = rturtle $ drawDissection quads
dissection t = lift' $ do quads <- parseList parseIntQuad t
                          jturtleP $ drawDissection quads
                                   
matrix :: Sig -> Interpreter
matrix sig sizes spread t = hiddenMatrix sizes spread t ++ f t where
      f :: TermS -> MaybeT Cmd Picture
      f t | just u = do bins@(bin:_) <- lift' u
                        let (arr,k,m) = karnaugh (length bin)
                            g = binsToBinMat bins arr
                            trips = [(show i,show j,F (g i j) []) | i <- [1..k],
                                                                    j <- [1..m]]
                        rturtle $ termMatrix sizes trips
                     where u = parseBins t
      f (F _ [])   = zero
      f (F _ ts) | just us = rturtle $ boolMatrix sizes dom1 dom2 pairs
                             where us = mapM parsePair ts
                                   pairs = deAssoc $ get us
                                   (dom1,dom2) = sortDoms pairs
      f (F "wmat" [F "[]" ts]) 
                   = do trips <- mapM (lift' . parseTripT) ts
                        let (dom1,dom2) = sortDoms $ map (pr1 *** pr2) trips
                        rturtle $ widgMatrix sig sizes spread dom1 dom2 trips 
      f (F "[]" ts) | just us 
                   = rturtle $ listMatrix sizes spread dom1 dom2 trips 
                     where us = mapM parseTrip ts; trips = get us
                           (dom1,dom2) = sortDoms $ map (pr1 *** pr2) trips
      f _          = zero

hiddenMatrix :: Sizes -> Pos -> TermS -> MaybeT Cmd Picture
hiddenMatrix sizes _ (Hidden (BoolMat dom1 dom2 pairs@(_:_))) 
                   = rturtle $ boolMatrix sizes dom1 dom2 pairs
hiddenMatrix sizes _ (Hidden (TermMat trips@(_:_))) 
                   = rturtle $ termMatrix sizes trips
hiddenMatrix sizes spread (Hidden (ListMat dom1 dom2 trips@(_:_)))
                   = rturtle $ listMatrix sizes spread dom1 dom2 trips
hiddenMatrix sizes spread (Hidden (EquivMat sig trips@(_:_)))
                   = rturtle $ listMatrix sizes spread dom dom tripsS where
                     dom = map showTerm0 $ states sig
                     tripsS = [(f i,f j,map g ps) | (i,j,ps) <- trips]
                              where f = showTerm0 . (states sig!!)
                                    g (is,js) = showTerm0 $ mkPair (h is) $ h js
                                    h = mkList . map (states sig!!)
hiddenMatrix _ _ _ = zero                                   
         
-- widgetTerm .. t returns the widget term that is equivalent to t.

widgetTerm :: Sig -> Sizes -> Pos -> TermS -> MaybeT Cmd TermW       
widgetTerm sig sizes spread = f [] where
        f :: [Int] -> TermS -> MaybeT Cmd TermW
        f p (F "<+>" ts)        = do ts <- zipWithSucsM f p ts
                                     return $ F Skip ts
        f p (F "widg" ts@(_:_)) = do let u = dropnFromPoss 1 $ last ts
                                          -- expand 0 t $ p++[length ts-1]
                                     [w] <- widgets sig black sizes spread u
                                     ts <- zipWithSucsM f p $ init ts
                                     return $ F w ts
        f p (F x ts)            = do ts <- zipWithSucsM f p ts
                                     return $ F (textWidget black sizes x) ts
        f _ (V x)               = return $ V $ if isPos x then posWidg x
                                               else textWidget black sizes x
        f _ _                   = return $ leaf $ textWidget blue sizes "hidden"

-- used by widgets "tree"

widgetTree :: Sig -> Interpreter
widgetTree sig sizes spread t = do t <- widgetTerm sig sizes spread t
                                   return [WTree t]
                                     
widgets :: Sig -> Color -> Interpreter
widgets sig c sizes spread t = f c t' where
    t' = expand 0 t [] 
    next = nextColor 0 $ depth t'
    hv = fromInt2 spread 
    fs = parseListT . f
    f c (F x [t])     | just tr = do [w] <- f c t; return [get tr w]
                                  where tr = widgTrans $ leaf x
    f c (F x [t])     | just tr = do pict <- fs c t; return $ get tr pict
                                  where tr = pictTrans c $ leaf x
    f c (F x [t])     | just tr = do acts <- turtActs c t
                                     return [turtle0 c $ get tr acts]
                                  where tr = actsTrans $ leaf x
    f c (F "$" [t,u]) | just tr = do [w] <- f c u; return [get tr w]
                                  where tr = widgTrans t
    f c (F "$" [t,u]) | just tr = do pict <- fs c u; return $ get tr pict
                                  where tr = pictTrans c t
    f c (F "$" [t,u]) | just tr = do acts <- turtActs c u
                                     return [turtle0 c $ get tr acts]
                                  where tr = actsTrans t
    f c (F "base" [t])          = do [w] <- f c t; w <- lift' $ mkBased c w
                                     return [w]
                         -- Based widgets are polygons with a horizontal line
                         -- of 90 pixels starting in (90,0) and ending in (0,0). 
                         -- mkBased and mkTrunk generate based widgets.
    f c (F "load" [t])            = do w <- lift $ loadWidget c sizes t
                                       return [updCol c w]
    f c (F "loadT" [t])           = do t <- lift $ loadTerm sig c sizes t
                                       fs c t
    f _ (F "mat" [t])             = matrix sig sizes spread t
    f _ (F "save" [t,u])          = do pict@[w] <- f black t
                                       lift $ saveWidget w u; return pict
    f _ (F "saveT" [t,u])         = do pict@[_] <- f black t
                                       lift $ saveTerm t u; return pict
    f _ (F "tree" [t])            = treeGraph "t1" 0 t
    f _ (F "tree" [mode,t])       = treeGraph (root mode) 0 t
    f _ (F "tree" [mode,grade,t]) = do grade <- lift' $ parse real $ root grade
                                       treeGraph (root mode) grade t   
    f c (F "turt" [t])            = do acts <- turtActs c t
                                       return [turtle0 c acts]
    f _ (F x [t]) | just c        = f (get c) t where c = parse color x
    f c t = concat [do w    <- lift' $ widgConst c sizes spread t; return [w],
                    do pict <- lift' $ widgConsts sizes spread t; return pict]
    treeGraph mode grade t
                   = do t <- widgetTerm sig sizes spread t
                        let pict = termWToPict mode (fromInt2 spread) grade t    
                        return [Tree (st0 c) $ bunchesToArcs $ pictToGraph pict]
                        
    actsTrans :: TermS -> Maybe ActsTrans
    actsTrans (F x []) | z == "hue" = do hmode <- getHue hmode
                                         tmode <- parse nat [last y]
                                         guard $ tmode `elem` [0,1,2]
                                         Just $ hueActs tmode hmode 0
                                      where (y,hmode) = splitAt 4 x; z = init y
    actsTrans _ = Nothing
                        
    turtActs :: Color -> TermS -> MaybeT Cmd [TurtleAct]
    turtActs c t =
     case t of 
          F "anim" [t] -> do [w] <- f c t; return $ onoff w
          F "bar" ts   -> do [i,h] <- mapM (lift' . parseReal) ts
                             guard $ i <= h; return $ bar sizes i h c
          F x (lmode:n:ts) | z == "blos" 
            -> do hmode <- lift' $ getHue hmode
                  lmode <- lift' $ search (== (root lmode)) leafmodes
                  n <- lpnat n; [r,a] <- lift' $ mapM parseReal ts
                  let [f,g] = map (nextColor hmode) [n,2*n]
                  return $ if lmode < 4 
                     then blossom f n c $ case lmode of 0 -> \c -> leafD r a c c
                                                        1 -> \c -> leafA r a c c
                                                        2 -> \c -> leafC r a c c
                                                        _ -> leafS r a
                     else blossomD g n c $ case lmode of 4 -> leafD r a
                                                         5 -> leafA r a
                                                         _ -> leafC r a
               where (z,hmode) = splitAt 4 x
          F "chordL" ts    -> do [h,b] <- lift' $ mapM parseReal ts
                                 return $ chord True h b c
          F "chordR" ts    -> do [h,b] <- lift' $ mapM parseReal ts
                                 return $ chord False h b c
          F "colbars" []   -> return $ colbars sizes c
          F "fadeB" [t]    -> do [w] <- f c t; return $ fade False w
          F "fadeW" [t]    -> do [w] <- f c t; return $ fade True w
          F "fern2" (n:ts) -> do n <- lift' $ parsePnat n
                                 [d,r] <- lift' $ mapM parseReal ts
                                 return $ fern2 n d r
          F "flash" [t]    -> do [w] <- f c t; return $ flash w
          F "$" [F x [t],u] | z == "flower" 
                           -> do fmode <- lift' $ parse nat fmode
                                 [w] <- f c t; pict <- fs (next c) u
                                 return $ widg w:flower fmode pict
                              where (z,fmode) = splitAt 6 x
          F x [n] | x `elem` fractals 
                           -> do n <- lpnat n; return $ fractal c x n
          F "$" [F x [t],u] | x == "grow"
                           -> turtActs c $ apply (F x [leaf "id",t]) u
          F "$" [F "grow" [tr,t],u] 
                           -> do [w] <- f c t; pict <- fs (next c) u
                                 tr <- lift' $ widgTrans tr
                                 return $ grow tr c w $ map getActs pict
          F "hilbP" [n]    -> do n <- lpnat n; return $ hilbert n East
          F x ts | z == "leaf"
                           -> do lmode <- lift' $ search (== lmode) leafmodes
                                 [r,a] <- lift' $ mapM parseReal ts
                                 return $ case lmode of 0 -> leafD r a c c
                                                        1 -> leafA r a c c
                                                        2 -> leafC r a c c
                                                        3 -> leafS r a c
                                                        4 -> leafD r a c c'
                                                        5 -> leafA r a c c'
                                                        _ -> leafC r a c c'
                              where (z,lmode) = splitAt 4 x; c' = complColor c
          F "oleaf" [n]    -> do n <- lift' $ parsePnat n; return $ oleaf c n
          F x [n,d,m] | z == "owave"  
                           -> do pmode <- lift' $ search (== pmode) pathmodes
                                 n <- lift' $ parsePnat n
                                 d <- lift' $ parseReal d
                                 m <- lift' $ parseInt m
                                 return $ owave pmode c d n m
                              where (z,pmode) = splitAt 5 x
          F x rs@(_:_) | z == "peaks" 
                           -> do imode:pmode <- lift' $ Just ipmode
                                 pmode <- lift' $ search (== pmode) polymodes
                                 rs <- lift' $ mapM parseReal rs
                                 guard $ head rs /= 0
                                 return $ peaks imode pmode c rs
                              where (z,ipmode) = splitAt 5 x
          F x [F "[]" ts] | z == "pie" 
                           -> do pmode:hmode <- lift' $ Just phmode
                                 pie pmode hmode c 0 0 ts
                              where (z,phmode) = splitAt 3 x
          F x [m,n,F "[]" ts] | z == "pie" 
                           -> do pmode:hmode <- lift' $ Just phmode
                                 [m,n] <- lift' $ mapM parseNat [m,n]
                                 pie pmode hmode c m n ts
                              where (z,phmode) = splitAt 3 x
          F "pile" [h,i]   -> do h <- lift' $ parsePnat h
                                 i <- lift' $ parseNat i
                                 guard $ i <= h; return $ pile h i
          F "pileR" [t]    -> do h:is <- lift' $ parseList parseNat t
                                 guard $ all (< h) is; return $ pileR h is
          F "place" (t:p)  -> do [w] <- f c t; [x,y] <- lift' $ mapM parseReal p
                                 return $ jumpTo (x,y) ++ [widg w]
          F x (d:ts) | z == "plait"
                           -> do pmode <- lift' $ search (== pmode) pathmodes
                                 d <- lift' $ parseReal d
                                 [n,m] <- lift' $ mapM parsePnat ts
                                 return $ plait pmode c d n m
                              where (z,pmode) = splitAt 5 x
          F x [n] | x `elem` polygons 
                           -> turtActs c $ F x [leaf "id",n]
          F x [tr,n] | x `elem` polygons 
                           -> do tr <- lift' $ widgTrans tr; n <- lpnat n
                                 return $ polygon c x tr n
          F "pulse" [t]    -> do [w] <- f c t; return $ pulse w
          F x [n,w] | z == "spiral"
                           -> do n <- lift' $ parsePnat n
                                 w <- lift' $ parseReal w
                                 return $ spiral (null smode) c n w
                              where (z,smode) = splitAt 6 x
          F "spiralP" [n,w,ps] 
                           -> do n <- lift' $ parsePnat n
                                 w <- lift' $ parseReal w
                                 ps <- lift' $ parseList parseRealReal ps
                                 return $ spiralP c n w ps
          F x [n,w,acts] | z == "spiralT"
                           -> do hmode <- lift' $ getHue hmode
                                 n <- lift' $ parsePnat n
                                 w <- lift' $ parseReal w
                                 actss <- lift' $ parseList turtAct acts
                                 return $ spiralT hmode c n w $ concat actss
                              where (z,hmode) = splitAt 7 x
          F "star" (n:ts)  -> do n <- lift' $ parsePnat n
                                 [r,r'] <- lift' $ mapM parseReal ts
                                 return $ star n c r r'
          F "taichi" ts    -> return $ taichi sizes ts c
          F x (n:ts) | z == "wave" 
                           -> do pmode <- lift' $ search (== pmode) pathmodes
                                 n <- lift' $ parsePnat n
                                 [d,a] <- lift' $ mapM parseReal ts
                                 return $ wave pmode d n a c
                              where (z,pmode) = splitAt 4 x
          F ":" [t,u]      -> do as <- lift' $ turtAct t
                                 bs <- turtActs c u; return $ as++bs
          F "++" ts        -> do [as,bs] <- mapM (turtActs c) ts
                                 return $ as++bs
          _                -> parseListT g t where
                               g :: TermS -> MaybeT Cmd [TurtleAct]
                               g (F "A" [t]) = do [w] <- f c t++return [textw t]
                                                  return [Widg True w]
                               g t   = concat [do acts <- lift' $ turtAct t
                                                  return acts,
                                               do [w] <- f c t++return [textw t]
                                                  return [Widg False w]]
    textw = textWidget black sizes . showTerm0
    lpnat = lift' . parsePnat
         
turtAct :: TermS -> Maybe [TurtleAct]
turtAct (F "B" [])    = Just [back]
turtAct (F "C" [])    = Just [Close]
turtAct (F "D" [])    = return [Draw]
turtAct (F "J" [d])   = do d <- parseReal d; Just [Jump d]
turtAct (F "J" p)     = do [x,y] <- mapM parseReal p; Just $ jumpTo (x,y) 
turtAct (F "L" [])    = Just [up]
turtAct (F "O" [])    = Just [Open 0]
turtAct (F "OS" [])   = Just [Open 1]
turtAct (F "OF" [])   = Just [Open 2]
turtAct (F "OFS" [])  = Just [Open 3]
turtAct (F "OC" [c])  = do c <- parseColor c; Just [OpenC c]
turtAct (F "OW" [w])  = do w <- parseReal w; Just [OpenW w]
turtAct (F "M" [d])   = do d <- parseReal d; Just [Move d]
turtAct (F "M" p)     = do [x,y] <- mapM parseReal p; Just $ moveTo (x,y) 
turtAct (F "R" [])    = Just [down]
turtAct (F "SC" [sc]) = do sc <- parseReal sc; Just [OpenS sc]
turtAct (F "T" [a])   = do a <- parseReal a; Just [Turn a]
turtAct _             = Nothing
    
widgConst :: Color -> Sizes -> Pos -> TermS -> Maybe Widget_
widgConst c sizes@(height,width) spread = f where
    f (F x [])     | x `elem` trunks = Just $ mkTrunk c x
    f (F "arc" ts)                = do [w,r,a] <- mapM parseReal ts
                                       Just $ Arc (st0 c) w r a
    f (F "chord" ts)              = do [r,a] <- mapM parseReal ts
                                       Just $ Slice (st0 c) Chord r a
    f (F "circ" [r])              = do r <- parseReal r; Just $ Oval (st0 c) r r
    f (F "gif" [F file [],b,h])   = do [b,h] <- mapM parseReal [b,h]
                                       Just $ Gif 1 True file $ Rect st0B b h
    f (F "gif" [F file [],p,b,h]) = do p <- parsePnat p
                                       [b,h] <- mapM parseReal [b,h]
                                       Just $ Gif p True file $ Rect st0B b h
    f (F "new" [])                = Just New
    f (F "oval" ts)               = do [rx,ry] <- mapM parseReal ts
                                       Just $ Oval (st0 c) rx ry
    f (F x [ps]) | z == "path"    = do mode <- search (== mode) pathmodes
                                       ps@(_:_) <- parseList parseRealReal ps
                                       Just $ path0 1 c mode ps
                                    where (z,mode) = splitAt 4 x
    f (F x [w,ps]) | z == "path"  = do mode <- search (== mode) pathmodes
                                       w <- parseReal w
                                       ps@(_:_) <- parseList parseRealReal ps
                                       Just $ path0 w c mode ps
                                    where (z,mode) = splitAt 4 x
    f (F x ts) | z == "poly"      = do mode <- search (== mode) polymodes
                                       factor:rs@(_:_) <- Just ts
                                       factor <- parsePnat factor
                                       rs <- mapM parseReal rs
                                       let n = factor*length rs
                                       Just $ Poly (st0 c) mode
                                             (take n $ cycle rs) $ 360/fromInt n
                                    where (z,mode) = splitAt 4 x
    f (F "rect" ts)    = do [b,h] <- mapM parseReal ts; Just $ Rect (st0 c) b h
    f (F "rhomb" [])   = Just $ rhombV c
    f (F "skip" [])    = Just Skip
    f (F "slice" ts)   = do [r,a] <- mapM parseReal ts
                            Just $ Slice (st0 c) Pie r a
    f (F "stick" [])   = Just $ Path 1 (p0,0,c,-16) 2
                                                 [p0,(-4,-8),(0,-150),(4,-8),p0]                            
    f (F "text" ts)    = Just $ textWidget c sizes $ showTree False  $ mkTup ts
    f (F "tpath" [ts]) = do actss <- (parseList turtAct) ts
                            [Path w (_,_,c,_) _ ps]
                                   <- Just $ mkPict $ turtle0 c $ concat actss
                            Just $ path0 w c 0 ps
    f (F "tria" [r])   = do r <- parseReal r; Just $ Tria (st0 c) r
    f _ = Nothing

widgConsts :: Sizes -> Pos -> TermS -> Maybe Picture
widgConsts sizes spread = f where
   f (F "gifs" [d,n,b,h]) = do d <- parseConst d; n <- parsePnat n
                               b <- parseReal b; h <- parseReal h
                               let gif i = Gif i False d $ Rect st0B b h
                               Just $ map gif [1..n]
                            -- Just $ map (turtle0B . onoff . gif) [1..n]
   f _ = Nothing
    
getHue mode = search (== mode) $ "":map show [1..5]

pathmodes  = "":words "S W SW F SF"
polymodes  = pathmodes++words "R R1 R2 R3 L L1 L2 L3 T T1 T2 T3 LT LT1 LT2 LT3"
trackmodes = words "asc sym ang slo"
leafmodes  = words "D A C S D2 A2 C2"

fractals = words "bush bush2 cant dragon fern hilb koch pytreeA wide" ++
           map ("gras"++) ("":words "D A C R")
polygons = words "cactus hexa penta pentaS pytree"
trunks   = words "TR SQ PE PY CA HE LB RB LS RS PS"

depth :: TermS -> Int
depth (F "$" [F x _,t]) | take 6 x == "flower" = depth t+1
depth (F "$" [F "grow" _,t])                   = depth t+1
depth (F x ts) = maximum $ 1:map depth ts
depth _        = 1

widgTrans :: TermS -> Maybe WidgTrans
widgTrans = f where
    f (F "center" [])     = Just $ \w -> shiftWidg (center w) w
    f (F "grav" [])       = Just $ \w -> shiftWidg (gravity w) w
    f (F "id" [])         = Just id
    f (F "inCenter" [tr]) = do tr <- f tr; Just $ inCenter tr
    f (F "planar" [n])    = do maxmeet <- parsePnat n; Just $ planarWidg maxmeet
    f (F x (n:s)) | z == "rainbow" = do hmode <- getHue hmode; n <- parsePnat n
                                        smode <- parse nat [last y] 
                                        frainbow n s hmode smode
                                     where (y,hmode) = splitAt 8 x; z = init y
    f (F "repeat" [])              = Just $ Repeat
    f (F x (i:s)) | z == "shine"   = do i <- parseInt i
                                        guard $ abs i `elem` [1..42]
                                        fshine i s $ if null m then 0 else 1
                                     where (z,m) = splitAt 5 x
    f (F x (d:ts)) | z == "snow"   = do hmode <- getHue hmode; d <- parseReal d
                                        [tm,n,k] <- mapM parsePnat ts
                                        Just $ mkSnow True hmode d tm n k
                                     where (z,hmode) = splitAt 4 x
    f (F x [modes]) | z == "track" = do hmode <- getHue hmode
                                        ftrack z hmode (root modes) 0 0
                                     where (z,hmode) = splitAt 5 x
    f (F x (ms:ts)) | z == "track" = do hmode <- getHue hmode
                                        [m,n] <- mapM parseNat ts
                                        ftrack z hmode (root ms) m n
                                     where (z,hmode) = splitAt 5 x
    f _ = Nothing
    frainbow n s hmode smode = do
              let f i = fromInt i/fromInt n
                  g sc i = sc^^n/sc^^i
              case s of 
               a:s -> do a <- parseReal a                    -- rotation      
                         case s of
                          d:s -> do d <- parseReal d          -- deflection
                                    case s of                 -- scaling factor
                                     sc:s -> do sc <- parseReal sc
                                                rainbow n (g sc) a d hmode smode
                                     _    -> rainbow n f a d hmode smode
                          _ -> rainbow n f a 0 hmode smode
               _ -> rainbow n f 0 0 hmode smode
    fshine i s smode = do 
       let f k = fromInt k/fromInt i
       case s of a:s -> do a <- parseReal a                        -- rotation  
                           case s of d:s -> do d <- parseReal d    -- deflection
                                               shine i f a d smode
                                     _   -> shine i f a 0 smode
                 _ -> shine i f 0 0 smode
    ftrack z hmode modes m n = do guard $ tmode `elem` trackmodes
                                  pmode <- search (== pmode) pathmodes
                                  Just $ track hmode pmode tmode m n
                               where (tmode,pmode) = splitAt 3 modes
                               
pictTrans :: Color -> TermS -> Maybe PictTrans
pictTrans c = f where
      f (F "dark" [])                 = Just $ map $ shiftLight $ -16
      f (F "dots" [n])                = do n <- parsePnat n; Just $ dots n
      f (F "fast" [])                 = Just $ map fast
      f (F "flipH" [])                = Just $ flipPict True
      f (F "flipV" [])                = Just $ flipPict False
      f (F x [w,d]) | z == "frame"    = do w <- parseReal w; d <- parseReal d
                                           mode <- search (== mode) pathmodes
                                           Just $ map $ addFrame w d c mode
                                        where (z,mode) = splitAt 5 x
      f (F x []) | z == "join"        = do mode <- parse pnat mode
                                           guard $ mode `elem` [6..14]
                                           g $ joinPict mode
                                        where (z,mode) = splitAt 4 x
      f (F "light" [])                = Just $ map $ shiftLight 21
      f (F x [w,pm,n]) | z == "morph" = do hmode <- getHue hmode
                                           w <- parseReal w
                                           pm <- search (== (root pm)) pathmodes
                                           n <- parsePnat n
                                           g $ morphPict w pm hmode n 
                                        where (z,hmode) = splitAt 5 x
      f (F "outline" []) = Just outline
      f (F "revpic" [])  = Just reverse
      f (F "rotate" [a]) = do a <- parseReal a; guard $ a /= 0
                              Just $ single . turtle0B . rotatePict a
      f (F x [sc]) | z == "scale" 
                         = do sc <- parseReal sc
                              Just $ scalePict (if null rest then 0 else 1) sc
                           where (z,rest) = splitAt 5 x
      f (F x (n:s)) | x `elem` ["shelf","tower","shelfS","towerS"]
          = do n <- parsePnat n
               let cols pict = if last x == 'S' then square pict else n
                   tr d a b pict = fst $ shelf (pict,[]) (cols pict) (d,d) a b 
                                         False $ if take 5 x == "shelf" 
                                                 then "m1" else "m2"
               case s of 
                 d:s -> do d <- parseReal d                  -- space
                           case s of 
                                a:s -> do a <- parseChar a           -- align: 
                                          case s of                  -- L/R/M
                                            b:s -> do b <- parseChar b -- center
                                                      Just $ tr d a $ b == 'C'
                                            _ -> Just $ tr d a False
                                _   -> Just $ tr d 'M' False
                 _   -> Just $ tr 0 'M' False
      f (F "smooth" [])   = Just smooth
      f (F "spline" [])   = Just splinePict
      f (F "table" [n,d]) = do n <- parsePnat n; d <- parseReal d
                               Just $ single . table n d
      f (F "turn" [a])    = do a <- parseReal a; Just $ map $ turnWidg a
      f (F "unturt" [])   = Just $ fst . flip unTurt (const True)
      f _                 = Nothing
      g tr = Just $ single . mkTurt p0 1 . tr

shiftW :: Num a => ((t, t) -> (a, a)) -> a -> [(t, a)] -> [a]
shiftW maxmin d (x:xs) = fst $ foldl f ([0],x) xs
       where f (s,(fv,cv)) w@(fw,cw) = (s++[last s+abs (rv-cv)+d+abs (cw-lw)],w) 
                                       where (rv,lw) = maxmin (fv,fw)

maxminx ((_,_,xv,_),(xw,_,_,_)) = (xv,xw)
maxminy ((_,_,_,yv),(_,yw,_,_)) = (yv,yw)

midx,midy :: Widget_ -> Double
midx w = (x'-x)/2 where (x,_,x',_) = widgFrame w
midy w = (y'-y)/2 where (_,y,_,y') = widgFrame w

type TermWP = Term (Widget_,Point)

-- coordTreeW (hor,ver) p t adds coordinates to the nodes of t such that p is 
-- the leftmost-uppermost corner of the smallest rectangle enclosing t.
-- hor is the horizontal space between adjacent subtrees. ver is the vertical 
-- space between adjacent tree levels.

coordTreeW :: Point -> Point -> TermW -> TermWP
coordTreeW (hor,ver) p = alignWLeaves hor . f p where
        f (x,y) (V w)    = V (w,(x+midx w,y))
        f (x,y) (F w []) = F (w,(x+midx w,y)) []
        f (x,y) (F w ts) = if bdiff <= 0 then ct' else transTree1 (bdiff/2) ct'
                     where bdiff = midx w-foldT h ct+x
                           hdiff = height w+maximum (map (height . root) ts)
                           height w = y'-y where (_,y,_,y') = widgFrame w
                           ct:cts = map (f (x,y+hdiff/2+ver)) ts
                           cts' = transTreesW hor ct cts
                           ct' = F (w,((g (head cts')+g (last cts'))/2,y)) cts'
                           g = fst . snd . root
                           h (w,(x,_)) = maximum . ((x+midx w):)
                           
-- used by termWToPict      

-- transTreesW hor ct cts orders the trees of ct:cts with a horizontal space of 
-- hor units between adjacent trees. transTreesW takes into account different
-- heights of adjacent trees by shifting them to the left or to the right such 
-- that nodes on low levels of a tree may occur below a neighbour with fewer 
-- levels.

transTreesW :: Double -> TermWP -> [TermWP] -> [TermWP]
transTreesW hor ct = f [ct]
      where f us (t:ts) = if d < 0 then f (map (transTree1 $ -d) us++[t]) ts
                          else f (us++[transTree1 d t]) $ map (transTree1 d) ts
                       -- f (us++[if d < 0 then t else transTree1 d t]) ts
                          where d = maximum (map h us)+hor
                                h u = f (+) maximum u-f (-) minimum t
                                      where f = g $ min (height t) $ height u
            f us _      = us
            g _ op _ (V (w,(x,_)))    = h op w x
            g 1 op _ (F (w,(x,_)) _)  = h op w x
            g n op m (F (w,(x,_)) ts) = m $ h op w x:map (g (n-1) op m) ts
            h op w x = op x $ midx w

-- @alignWLeaves t@ replaces the leaves of @t@ such that all gaps between
-- neighbours become equal.

alignWLeaves :: Double -> TermWP -> TermWP
alignWLeaves hor (F a ts) = F a $ equalWGaps hor $ map (alignWLeaves hor) ts 
alignWLeaves _ t            = t        

equalWGaps :: Double -> [TermWP] -> [TermWP]
equalWGaps hor ts = if length ts > 2 then us++vs else ts
                   where (us,vs) = foldl f ([],[head ts]) $ tail ts
                         f (us,vs) v = if isWLeaf v then (us,vs++[v])
                                        else (us++transWLeaves hor vs v,[v])

isWLeaf :: TermWP -> Bool
isWLeaf (V _)    = True
isWLeaf (F _ []) = True
isWLeaf _        = False

transWLeaves :: Double -> [TermWP] -> TermWP -> [TermWP]
transWLeaves hor ts t = loop hor
              where loop hor = if x1+w1+hor >= x2-w2 then us else loop $ hor+1 
                         where us = transTreesW hor (head ts) $ tail ts
                               [x1,x2] = map (fst . snd . root) [last us,t]
                               [w1,w2] = map (midx . fst . root) [last us,t]
     
addControls :: TermW -> TermW
addControls (F Skip ts) = F Skip $ map addControls ts
addControls (F w ts)    = F w $ map (F (Dot red p0) . single . addControls) ts
addControls t           = t
 
-- used by termWToPict

chgPoss :: Bool -> Widget_ -> Widget_ 
chgPoss b (Text_ _ _ [x] _) | isPos x = posWidg $ "pos " ++ unwords (map show q)
                                      where p = concatMap (\n->[n,0]) $ getPos x
                                            q = if b then context 1 p else p
chgPoss _ w = w
 
-- used by termWToPict

termWToPict :: String -> Point -> Double -> TermW -> Picture
termWToPict mode spread@(hor,ver) grade t = w:ws' where
    (t',ver') = if take 2 mode `elem` words "t2 t4 a2 a4 o5 o6 o7 o8" 
                then (mapT (chgPoss $ isSkip $ root t) $ addControls t,ver/2)
                else (t,ver)
    ct = coordTreeW (hor,ver') (20,20) t'
    ct' = F (v,p0) $ subterms $ transTree2 (-x,-y) ct where (v,(x,y)) = root ct
    -- bunches splits a widget term with widget positions into bunches
    bunches :: TermI -> TermWP -> Picture
    bunches (F _ its) (F (w,p) cts) = Bunch (moveWidg p w) (map root its):
                                      concat (zipWith bunches its cts)
    bunches _ (V (Text_ _ _ [x] _,p)) 
                          | isPos x = [Bunch (Dot red p) 
                                             [root $ getSubterm it $ getPos x]]
    bunches _ (V (w,p))             = [Bunch (moveWidg p w) []]
    row n = zipWith moveWidg ps ws where
            (ws,ps) = unzip [label ct' p | p <- allPoss ct', length p == n]
    vshift = shiftW maxminy ver' $ map f [0..height ct'-1] 
             where f = (widgFrame *** ycoord) . turtle0B . map (Widg True) . row
    chgY i (F (w,(x,y)) cts) = F (w,(x,vshift!!i)) $ map (chgY $ i+1) cts
    chgY i (V (w,(x,y)))     = V (w,(x,vshift!!i))
    mode1:mode2 = mode; n = parse pnat mode2; mode3 = get n
    (it,_) = preordTerm black (const id) t'
    w:ws = bunches it $ if mode1 == 'a' then chgY 0 ct' else ct'
    p@(xp,_) = coords w
    rot a = moveWidg . rotate p a
    ws' | mode1 `elem` "at" && grade /= 0 = map turn ws     -- turn picture
        | mode1 == 'o' && just n = map (orb mode3) ws       -- make orbital tree
        | True                   = ws
    turn w = rot grade (coords w) $ if just n && mode3 `elem` [1,2] then w
                                    else turnWidg grade w
    orb 1 w = rot (polyn x) (xp,y) w      where (x,y) = coords w
    orb 2 w = rot a (xp,y) $ turnWidg a w where a = polyn x; (x,y) = coords w
    orb 3 w = rot (eqDist w y) (xp,y) w   where y = ycoord w
    orb 4 w = rot a (xp,y) $ turnWidg a w where a = eqDist w y; y = ycoord w
    orb m w = if m `elem` [5..8] then orb (m-4) w else w
    polyn x = a*x^2+b*x+c where [a,b,c] = map snd $ sort (<) $ get $ gauss eqs
                                eqs = zipWith lineq [minx,xp,maxx] [-180,0,180]
           -- polyn solves eqs. Given the center (x,y) of a widget w in ws, 
           -- polyn(x) returns the angle by which (xp,y) is rotated around p to 
           -- obtain a suitable projection q of (x,y) on the circle c with 
           -- center p and radius y. Then w is moved to q.
    lineq x z = ([(x^2,"a"),(x,"b"),(1,"c")],z)
    minx = left minw-hor/2; maxx = right maxw+hor/2
    (minw,maxw) = foldl f (w,w) ws where f (u,v) w | left w < left u   = (w,v)
                                                   | right w > right v = (u,w) 
                                                   | True              = (u,v)
    left w  = xcoord w - midx w
    right w = xcoord w + midx w
    eqDist w y = 360*fromInt (getInd vs w)/fromInt (length vs)
                 where vs = sort rel [w | w <- ws, ycoord w == y]
                       rel v w = xcoord v > xcoord w                      
                           
-- used by arrangeGraph,concatGraphs,newPaint,widgets "tree"

-- graphToTerm b graph transforms graph into a term t. t is constructed from the
-- set of equations (b = True) or the binary relation that represents graph.

graphToTerm :: Bool -> Graph -> TermS
graphToTerm b graph = if b then collapse True $ eqsToGraph (indices_ eqs) eqs
                           else relToGraph pairs [] $ domainPT pairs [] 
    where (eqs,_) = relToEqs 0 pairs []
          pairs = map f $ propNodes $ fst graph
          f i = (show i,[show $ last path | k:path <- buildPaths graph, k == i])

-- used by arrangeGraph,showInSolver

-- MORPHING, SCALING and FRAMING

morphPict :: Double -> Int -> Int -> Int -> PictTrans
morphPict width mode m n ws = concat $ zipWith f (init ws) $ tail ws where
       f v w = map g [0..n] -- or n-1
               where [ps,qs] = map (getHullPts False) [v,w]
                     diff = length ps-length qs
                     ps' = adaptLength (-diff) ps
                     qs' = adaptLength diff qs
                     g i = path0 width (hue m (getCol v) n i) mode $ 
                                       zipWith morph ps' qs'
                           where morph (xv,yv) (xw,yw) = (next xv xw,next yv yw)
                                 next x z = (1-inc)*x+inc*z
                                 inc = fromInt i/fromInt n

scaleGraph :: Double -> Graph -> Graph
scaleGraph sc (pict,arcs) = (scalePict 0 sc pict,arcs)

scalePict :: Int -> Double -> PictTrans
scalePict m 1  = id
scalePict m sc = map $ scaleWidg m sc

-- scaleWidg sc w scales w by multiplying its vertices/radia with sc.
-- Dots, gifs and texts are not scaled. 

scaleWidg :: Int -> Double -> WidgTrans
scaleWidg _ 1  w                     = w
scaleWidg _ sc (Arc st w r a)        = Arc st w (r*sc) a
scaleWidg _ sc (Oval st rx ry)       = Oval st (rx*sc) $ ry*sc
scaleWidg _ sc (Path w st m ps)      = Path w st m $ map (apply2 (*sc)) ps
scaleWidg _ sc (Poly st n rs a)      = Poly st n (map (*sc) rs) a 
scaleWidg _ sc (Rect st b h)         = Rect st (b*sc) $ h*sc
scaleWidg _ sc (Slice st t r a)      = Slice st t (r*sc) a
scaleWidg _ sc (Tree st (pict,arcs)) = Tree st (scalePict 0 sc pict,arcs)
scaleWidg _ sc (Tria st r)           = Tria st $ r*sc
scaleWidg 0 sc (Turtle st sc' acts)  = Turtle st (sc*sc') acts
scaleWidg _ sc (Turtle st sc' acts)  = Turtle st sc' $ map scale acts where
                                    scale (Widg b w) = Widg b $ scaleWidg 1 sc w
                                    scale act        = act
scaleWidg m sc (Bunch w is) = Bunch (scaleWidg m sc w) is
scaleWidg m sc (Fast w)     = Fast $ scaleWidg m sc w
scaleWidg m sc (Repeat w)   = Repeat $ scaleWidg m sc w
scaleWidg _ _ w      = w

pictFrame :: Picture -> (Double,Double,Double,Double)
pictFrame pict = foldl f (0,0,0,0) $ indices_ pict
                 where f bds = minmax4 bds . widgFrame . (pict!!)

-- widgFrame w returns the leftmost-uppermost and rightmost-lowermost
-- coordinates of the smallest rectangle that encloses w.

widgFrame :: Widget_ -> (Double,Double,Double,Double)
widgFrame (Turtle st sc acts) = turtleFrame st sc acts
widgFrame w                   = minmax $ coords w:getHullPts True w

-- used by scaleAndDraw,addFrame,shelf

turtleFrame ::State -> Double -> [TurtleAct] -> (Double,Double,Double,Double)
turtleFrame (p,a,_,_) sc acts = minmax $ fst $ foldl f ([p],[(p,a,sc)]) acts
 where f (ps,_:s) Close                  = (ps,s)
       f state Draw                      = state
       f (ps,(p,a,sc):s) (Jump d)        = (p:q:ps,(q,a,sc):s)
                                           where q = successor p (d*sc) a
       f (ps,(p,a,sc):s) (JumpA d)       = (p:q:ps,(q,a,sc):s)
                                           where q = successor p d a
       f (ps,(p,a,sc):s) (Move d)        = (p:q:ps,(q,a,sc):s)
                                           where q = successor p (d*sc) a
       f (ps,(p,a,sc):s) (MoveA d)       = (p:q:ps,(q,a,sc):s)
                                           where q = successor p d a
       f (ps,s@((p,a,sc):_)) (OpenS sc') = (ps,(p,a,sc*sc'):s)
       f (ps,(p,a,sc):s) (Turn b)        = (ps,(p,a+b,sc):s)
       f (ps,s@(st:_)) (Widg b w)        = (g b ps st w,s)
       f (ps,s@(st:_)) _                 = (ps,st:s)
       g b ps (p,a,sc) w = if l == r then ps else l:r:ps
                         where (l,r) = ((x1,y1),(x2,y2))
                               (x1,y1,x2,y2) = minmax $ getHullPts True 
                                                      $ moveTurnScale b p a sc w

-- used by actsCenter,widgFrame

-- PICTURE operators

moveWidg :: Point -> WidgTrans
moveWidg p = updState f where f (_,a,c,i) = (p,a,c,i)

turnWidg :: Double -> WidgTrans
turnWidg a = updState f where f (p,b,c,i) = (p,a+b,c,i)

moveTurnWidg :: Point -> Double -> WidgTrans
moveTurnWidg (x,y) a w = turnWidg a $ moveWidg (i+x,j+y) w 
                         where (i,j) = coords w

moveTurnPict :: Point -> Double -> PictTrans
moveTurnPict p = map . moveTurnWidg p

-- transXY (x,y) w moves w x units to the right and y units to the bottom.

transXY :: Point -> WidgTrans
transXY (0,0) w = w
transXY (a,b) w = moveWidg (x+a,y+b) w where (x,y) = coords w

moveTurnScale :: Bool -> Point -> Double -> Double -> WidgTrans
moveTurnScale True p a sc = scaleWidg 0 sc . turnWidg a . moveWidg p
moveTurnScale _ p a sc    = scaleWidg 0 sc . updState f 
                            where f (_,_,c,i) = (p,a,c,i)

-- used by mkPict Turtle, turtleFrame

updCol :: Color -> WidgTrans
updCol (RGB 0 0 0) = id
updCol c           = updState $ \(p,a,_,i) -> (p,a,c,i)

hueCol :: Int -> PictTrans
hueCol m pict = map f $ indices_ pict
                where n = length pict
                      f k = updState g $ pict!!k
                            where g (p,a,c,i) = (p,a,hue m c n k,i)

shiftCol :: Int -> WidgTrans
shiftCol n w | isRedDot w = w
             | n == 0     = w
             | n > 0      = updState (f n) w
             | True       = updState (f $ 1530+n) w
                            where f n (p,a,c,i) = (p,a,iterate nextCol c!!n,i)

nextHue :: Int -> Int -> WidgTrans
nextHue hue n = updState g where g (p,a,c,i) = (p,a,nextColor hue n c,i)

shiftLight :: Int -> WidgTrans
shiftLight j = updState f where f (p,a,c,i) = (p,a,c,i+j)

lightWidg,delWidg :: WidgTrans
lightWidg = updState f where f (p,a,c,i) = (p,a,light c,i)
delWidg   = updState f where f (p,a,_,_) = (p,a,white,0)

flipPict :: Bool -> PictTrans
flipPict hor = map f where
               f (Arc (p,a,c,i) w r b)   = Arc (p,new a,c,i) w r $ -b
               f (Path w st m ps)        = Path w st m $ map g ps 
               f (Poly (p,a,c,i) n rs b) = Poly (p,new a,c,i) n rs $ -b
               f (Slice (p,a,c,i) t r b) = Slice (p,new a,c,i) t r $ -b
               f (Tree st (pict,arcs))   = Tree st (map h pict,arcs)
                                           where h w = moveWidg (g $ coords w) w
               f (Tria st r) | hor       = Tria st $ -r
               f (Turtle st sc acts)     = Turtle st sc $ if hor then map h acts
                                                          else back:map h acts
                                           where h (Turn a)   = Turn $ -a
                                                 h (Widg b w) = Widg b $ f w
                                                 h act        = act
               f (Bunch w is) = Bunch (f w) is       
               f (Fast w)     = Fast $ f w      
               f (Repeat w)   = Repeat $ f w
               f w            = w
               new a   = if hor then -a else a+180
               g (x,y) = if hor then (x,-y) else (-x,y)

outline :: PictTrans
outline = map $ turtle0B . acts
          where acts w = map widg $ w:if isPict w then map (f c i) outer 
                                                  else map g $ hulls False w
                         where (_,_,_,outer,_) = strands [w]
                               (_,_,c,i) = getState w
                f c i = Path 2 (p0,0,c,i-16) 0
                g (Path0 _ c i _ ps) = f c i ps

widgArea :: Widget_ -> Double                                     -- not used
widgArea w = area $ if isPict w then head outer else g $ head $ hulls False w
             where (_,_,_,outer,_) = strands [w]
                   g (Path0 _ _ _ _ ps) = ps

dots :: Int -> PictTrans
dots n = map $ turtle0B . acts where
         acts w = widg w:if isPict w then concatMap (f c i) outer 
                                     else concatMap g $ hulls False w
                  where (_,_,_,outer,_) = strands [w]
                        (_,_,c,i) = getState w
         f c i = h $ Oval (p0,0,c,i-16) 5 5
         g (Path0 _ c i _ ps) = f c i ps
         h w ps = mkActs (replicate lg w) $ map (\p -> (p,0)) qs
                  where (qs,lg) = reduce ps
         reduce ps = if lg < n+1 then (ps,lg) else (map (ps!!) $ f [lg-1],n)
                   where lg = length ps; step = perimeter ps/(fromInt n-1)
                         f is@(i:_) = if null ks then is else f $ maximum ks:is
                                    where ks = filter b [0..i-1]
                                          b k = step <= distance (ps!!k) (ps!!i)
             
planarWidg :: Int -> WidgTrans
planarWidg maxmeet w = turtle0B $ head $ getMax acts $ pairs ws
       where acts = getActs w
             (ws,as) = split f acts where f (Widg _ _) = True; f _ = False
             f v w = sum $ map area inner
                     where (_,inner,_,_,_) =
                              strands [turtle0B $ filter (`elem` (v:w:as)) acts]
             pairs (v:ws) = [(v,w) | w <- ws, f v w > fromInt maxmeet]++pairs ws
             pairs _      = []

-- ... = if sum $ map area inner > fromInt maxmeet then u else w
--       where u:v:_ = mkPict w; (_,inner,_,_,_) = strands [u,v]
                                                          
planarAll :: Int -> Graph -> Maybe Widget_ -> [Int] -> Double -> (Graph,[Int])
planarAll maxmeet (pict,arcs) (Just rect) rectIndices rscale
                          = (pictToGraph pict2,is) where
                            Rect (p@(x,y),_,_,_) b h = rect
                            k:ks = rectIndices
                            w = transXY p $ reduce $ mkTurt (x-b,y-h) rscale 
                                                   $ map (pict!!) rectIndices
                            reduce = scaleWidg 0 (1/rscale) . planarWidg maxmeet
                            (pict1,_) = removeSub (updList pict k w,arcs) ks
                            (pict2,is) = unTurt pict1 (== k)
                            (x1,y1,x2,y2) = pictFrame $ map (pict2!!) $ k:is
                            (b',h') = (abs (x2-x1)/2,abs (y2-y1)/2)
                            r = Rect ((x1+b',y1+h'),0,black,0) b' h'
planarAll maxmeet (pict,arcs) _ _ scale = (pictToGraph pict2,[]) where
                            pict1 = [reduce $ mkTurt p0 scale pict]
                            (pict2,_) = unTurt pict1 $ const True
                            reduce = scaleWidg 0 (1/scale) . planarWidg maxmeet

smooth :: PictTrans                             -- uses Tcl's splining
smooth = map f where
         f (Path w st m ps)   | m `elem` [0,2] = Path w st (m+1) ps
         f (Poly st m rs b) | m `elem` [0,2] = Poly st (m+1) rs b
         f (Rect st@((x,y),_,c,_) b h) = Path 1 st (filled c+1) $ last ps:ps
                                    where ps = [(x2,y1),(x2,y2),(x1,y2),(x1,y1)]
                                          x1 = x-b; y1 = y-h; x2 = x+b; y2 = y+h
         f (Tria st@((x,y),_,c,_) r)   = Path 1 st (filled c+1) $ last ps:ps
                                    where ps = [(x+lg,z),(x-lg,z),(x,y-r)]
                                          lg = r*0.86602       -- r*3/(2*sqrt 3) 
                                                               -- sidelength/2
                                          z = y+lg*0.57735     -- y+lg*sqrt 3/3
         f (Turtle st sc acts) = Turtle st sc $ map g acts
         f (Bunch w is)        = Bunch (f w) is
         f (Fast w)            = Fast $ f w
         f (Repeat w)          = Repeat $ f w
         f w                   = w
         g (Open m) | m `elem` [0,2] = Open $ m+1
         g (Widg b w)                = Widg b $ f w
         g act                       = act

splinePict :: PictTrans                         -- uses Expander's splining
splinePict = map $ turtle0B . map f . hulls False
             where f (Path0 w c i m ps) = widg $ Path w (p0,0,c,i) m 
                                               $ if odd m then ps else spline ps

hueActs :: Int -> Int -> Int -> ActsTrans
hueActs tmode hmode i acts = fst $ foldl f ([],i) acts where
             n = length $ filter isWAct acts
             f (acts,i) act =
               if tmode == 0 then g True acts act n i
               else case act of Widg b (Turtle st sc as) 
                                  -> (acts++[Widg b w],i+1) where
                                     w = Turtle st sc $ hueActs tmode hmode i as
                                _ -> g (tmode == 2) acts act n i
             g b acts (Widg b' w) n i = (acts++[Widg b' $ updCol c w],
                                         if b then i+1 else i) 
                                        where c = hue hmode (getCol w) n i
             g _ acts act _ i         = (acts++[act],i)

-- mkSnow withCenter huemode d m n k w computes a Koch snowflake from widget w 
-- with turn mode tm in {1,..,6}, depth n and the k copies of scale(i/3)(w) at 
-- level 1<=i<=n revolving around each copy of scale((i-1)/3)(w) at level i-1. 
-- The real number d should be taken from the closed interval [-1,1]. 
-- d affects the radia of the circles consisting of k copies of w.

mkSnow :: Bool -> Int -> Double -> Int -> Int -> Int -> Widget_ -> Widget_
mkSnow withCenter huemode d tm n k w = 
      if n <= 0 then Skip 
      else mkTurt p0 1 $ if withCenter then w:f (n-1) r [p0] else f (n-1) r [p0]
      where ps = getHullPts False w
            r = maximum $ map (distance $ gravity w) ps
            pict = if isTurt w then mkPict w else [w]
            a = 360/fromInt k
            f :: Int -> Double -> Path -> Picture
            f 0 _ _  = []
            f i r ps = zipWith3 g qs angs flips ++ f (i-1) r' qs 
                  where qs = concatMap circle ps 
                        r' = r/3
                        circle p@(x,y) = if odd tm then s else p:s
                            where s = take k $ iterate (rotate p a) (x,y-r+d*r')
                        pict' = zipWith updCol (map (color . getCol) pict) pict
                        color col = hue huemode col n $ n-i
                        g p a b = moveWidg p $ turnWidg a 
                                             $ scaleWidg 0 (b/3^(n-i)) $ h pict'
            h [w]  = w
            h pict = shiftWidg (gravity w') w' where w' = mkTurt p0 1 pict
            angs | tm < 5  = zeros 
                 | tm == 5 = iter++angs
                 | True    = 0:iter++concatMap f [1..n-2]
                             where f i = concatMap (g i) iter 
                                   g 1 a = a:iter
                                   g i a = g k a++f k where k = i-1
            iter = take k $ iterate (+a) 0
            zeros = 0:zeros; ones  = 1:ones; blink = 1: -1:blink
            flips = case tm of 1 -> blink
                               2 -> 1:take k blink++flips
                               _ -> ones
                             
rainbow :: Int -> (Int -> Double) -> Double -> Double -> Int -> Int 
                                                             -> Maybe WidgTrans
rainbow n f a d hue = iterScale n f a d (nextHue hue n) . scaleWidg
                                           
shine :: Int -> (Int -> Double) -> Double -> Double -> Int -> Maybe WidgTrans                           
shine i f a d = iterScale (abs i) f a d (shiftLight $ 42 `div` i) . scaleWidg

iterScale :: Int -> (Int -> Double) -> Double -> Double -> WidgTrans
                                   -> (Double -> WidgTrans) -> Maybe WidgTrans
iterScale n f a d next scf = Just $ turtle0B . h n
                             where h 0 _ = []
                                   h i w = widg (scf (f i) w):Turn a:Jump d
                                                             :h (i-1) (next w)

track :: Int -> Int -> String -> Int -> Int -> WidgTrans
track hue pmode tmode m n w = 
           if null ps then Skip 
           else turtle0B $ map widg $ pr1 $ foldl f ([],p,getCol w) qs
     where all = getAllPoints w 
           ps@(p:qs) = drop m $ take (length all-n) all
           ks = case tmode of "asc" -> indices_ ps
                              "sym" -> half++if lg1`mod`2 == 0 then reverse half 
                                             else lg2:reverse half
                              "ang" -> g angle
                              _     -> g slope
           max = maximum ks
           r = gravity w
           f (ws,p,c) q = (ws',q,nextColor hue max c) 
                          where ps = [p,r,q]
                                ws' = if area ps < 0.1 then ws 
                                      else ws++[path0 1 c pmode ps]
           g rel = map f rels where f rel = case search (== rel) set of 
                                                 Just i -> i; _ -> 0
                                    rels = fst $ foldl h ([],p) qs
                                    set = qsort (<=) $ mkSet rels
                                    h (is,p) q = (is++[rel p q],q)
           lg1 = length ps-1; lg2 = lg1`div`2; half = [0..lg2-1]

wave :: Int -> Double -> Int -> Double -> Color -> [TurtleAct]
wave pmode d n a c = Open pmode:OpenC c:Jump (-fromInt n*x):down:Jump (-5):up:
                     border a++border (-a)++close2
                     where (x,y) = successor p0 d a
                           border a = foldl1 (<++>) (replicate n acts)++
                                      [down,Move 10,down]
                                      where acts = [Turn a,Move d,Turn $ -a-a,
                                                    Move d,Turn a]

-- animations

flash,onoff,pulse :: Widget_ -> [TurtleAct]
flash   = take 100 . f where f w = wfast w:wait:f (nextHue 0 50 w)
onoff w = [wfast w,wait,wfast $ delWidg w]
pulse w = take 58 $ f 10 where widg i = fast $ scaleWidg 0 (fromInt i/10) w
                               f 0 = g 1
                               f i = onoff (widg i)++f (i-1) 
                               g i = onoff (widg i)++g (i+1) 
                                
fade :: Bool -> Widget_ -> [TurtleAct]
fade b = take 168 . if b then f 42 else g 0
         where f i w = if b && i == 0 then g 42 w
                       else wfast w:wait:f (i-1) (shiftLight 1 w)
               g i w = if not b && i == -42 then f 0 w
                       else wfast w:wait:g (i-1) (shiftLight (-1) w)

rotatePict :: Double -> Picture -> [TurtleAct]
rotatePict a pict = take ((2*length pict+2)*round (360/abs a)) acts
                    where acts = wait:map wfast (map delWidg pict)++Turn a:
                                      map wfast pict++acts

peaks :: Char -> Int -> Color -> [Double] -> [TurtleAct]
peaks imode pmode c rs = if imode == 'I' then take 103 $ f 2 
                                         else take 102 $ g (w 36) 35
         where f i = onoff (w i)++f (i+1) 
               g v i = wait:wfast (delWidg v):wfast wi:g wi (i-1) where wi = w i
               w i = Poly (st0 c) pmode (take k $ cycle rs) $ 360/fromInt k
                     where k = i*length rs
                                      
oscillate :: (Int -> [TurtleAct]) -> Int -> [TurtleAct]
oscillate acts n = take (6*n-2) $ f n
                   where f 0 = g 1
                         f i = onoff (turtle0B $ acts i)++f (i-1) 
                         g i = onoff (turtle0B $ acts i)++g (i+1) 

oleaf :: Color -> Int -> [TurtleAct]
oleaf c n = oscillate acts $ min 33 n
            where acts i = leafC (fromInt n) (fromInt i*b) c c
                  b = if n < 33 then 1 else fromInt n/33

owave,plait :: Int -> Color -> Double -> Int -> Int -> [TurtleAct]
owave pmode c d n m = oscillate acts $ abs m
                      where acts i = wave pmode d n (fromInt $ signum m*i) c
plait pmode c d n m = oscillate acts $ m
                      where acts i = wave pmode d n (fromInt i) c ++
                                     wave pmode d n (-fromInt i) (complColor c)

-- table pict d n displays pict as a matrix with n columns and a horizontal and
-- vertical distance of d units between the ANCHORS of adjacent widgets. 
-- table returns an action sequence.

table :: Int -> Double -> Picture -> Widget_
table n d = turtle0B . concatMap g . f
            where f [] = []; f s  = take n s:f (drop n s)
                  g pict = open:concatMap h pict++[Close,down,Jump d,up]
                           where h w = [widg w,Jump d]

-- shelf graph cols (dh,dv) align scaled .. mode displays graph as a matrix with
-- cols columns and a horizontal/vertical spacing of dh/dv units between the
-- borders of adjacent widgets. shelf returns a picture (scaled = True) or an
-- action sequence (scaled = False).
-- If take 2 mode = "m2", the widget anchors are aligned vertically and the 
-- columns according to the value of align (L/M/R). Otherwise the widget anchors
-- are aligned horizontally and the rows according to align.

shelf :: Graph -> Int -> Point -> Char -> Bool -> Bool -> String -> Graph
shelf graph@([],_) _ _ _ _ _ _ = graph
shelf graph@(pict,_) cols (dh,dv) align centered scaled mode = 
 case mode of 'm':'1':_ -> sh graph True False
              'm':'2':_ -> sh graph False False
              "c"       -> sh graph True True 
              _         -> graph
 where lg = length pict
       is = [0..lg-1]
       rows = lg `div` cols
       upb | mode == "c"        = maximum levels
           | lg `mod` cols == 0 = rows - 1
           | True               = rows
       rowIndices = [0..upb]
       levels = nodeLevels True graph
       levelRow i = [j | j <- is, levels!!j == i]
       sh (pict,arcs) b center =
        if center 
        then case searchGet isSkip ws of
                  Just (i,w) -> (w:map (transXY (0,y)) (context i ws),arcs)
                                where y = ycoord w-ycoord (ws!!head (arcs!!i))
                  _ -> (ws,arcs)
        else (if scaled then pict1 b 
              else [turtle0B $ if centered then actsToCenter acts else acts],
              arcs)
        where ws = sortR (pict1 True) $ concatMap levelRow rowIndices
              rowList pict = if mode == "c" then f 0 [] else g pict []
                         where f i picts = if null r then picts
                                           else f (i+1) $ picts++[r]
                                           where r = [pict!!k | k <- levelRow i]
                               g pict picts = if null pict then picts
                                              else g (drop cols pict) $
                                                     picts++[take cols pict]
              row = mkArray (0,upb) $ (if scaled then map $ moveWidg p0 
                                                 else id) . (rowList pict!!) 
              pict1 b = concatMap (g b f) rowIndices where
                        f x z y = moveWidg $ if b then (x+z,y) else (y,x+z)
              acts = concat $ concatMap (g b f) rowIndices where
                     f x z y w = [open,Jump x',down,Jump y',up,widg w,Close]
                                 where (x',y') = if b then (x+z,y) else (y,x+z)
              g b f i = zipWith h (hshift b!i) $ row!i
                 where h x = f x z $ vshift b!!i
                       z = case align of 'L' -> xm-xi; 'R' -> xm'-xi'
                                         _ -> (xm'+xm-xi'-xi)/2
                       (xi,xi') = widgFrames b!i
                       (xm,xm') = widgFrames b!last (maxis rel rowIndices)
                       rel i j = xi'-xi < xj'-xj where (xi,xi') = widgFrames b!i
                                                       (xj,xj') = widgFrames b!j
              xframe = widgFrame *** xcoord
              yframe = widgFrame *** ycoord
              hshift = mkArray (0,upb) . f
                       where f True = shiftW maxminx dh . map xframe . (row!)
                             f _    = shiftW maxminy dv . map yframe . (row!)
              vshift True = shiftW maxminy dv $ map (yframe . h) rowIndices
              vshift _    = shiftW maxminx dh $ map (xframe . h) rowIndices
              h = turtle0B . map widg . (row!)
              widgFrames b = mkArray (0,upb) $ g b . f 
                 where f i = widgFrame $ turtle0B $ 
                             widg (head pict):acts b++[widg $ last pict]
                        where pict = row!i
                              acts True = [Jump $ last $ hshift True!i]
                              acts _    = [down,Jump $ last $ hshift False!i,up]
                       g True (x,_,x',_) = (x,x')
                       g _ (_,y,_,y')    = (y,y')
              widg = Widg True

-- getSupport graph s t returns the red dots on a path from s to t. 

getSupport :: Graph -> Int -> Int -> Maybe [Int]
getSupport graph s t = do (_,_:path@(_:_:_)) <- searchGet f $ buildPaths graph
                          Just $ init path
                       where f path = s `elem` path && t `elem` path &&
                                      getInd path s <= getInd path t

-- used by releaseButton

-- bunchesToArcs (pict,arcs) removes the bunches of pict and adds their edges to
-- arcs.

bunchesToArcs :: Graph -> Graph
bunchesToArcs graph@(pict,_) = (pict2,foldl removeCycles arcs1 cycles)
   where addArcs (pict,arcs) (m,Bunch w is) = (updList pict m w,
                                               updList arcs m $ arcs!!m`join`is)
         addArcs graph (m,Fast w)   = addArcs graph (m,w)
         addArcs graph (m,Repeat w) = addArcs graph (m,w)
         addArcs graph _            = graph
         bunches = zip [0..] $ map getBunch pict
         getBunch (Fast w)   = w
         getBunch (Repeat w) = w
         getBunch w          = w
         cycles = [(s,t,v,w,ts) | b@(s,Bunch v ts) <- bunches,
                                  (t,Bunch w [n]) <- bunches`minus1`b,
                                  t `elem` ts, n == s, isRedDot w]
         cycles' = map f cycles where f (s,t,v,w,_) = (t,s,w,v,[s])
         graph1@(pict1,_) = foldl addSmoothArc graph $ cycles++cycles'
         (pict2,arcs1) = foldl addArcs graph1 $ zip [0..] pict1
         removeCycles arcs (s,t,_,_,_) = map f $ indices_ arcs
                                         where f n | n == s = arcs!!n`minus1`t
                                                   | n == t = arcs!!n`minus1`s
                                                   | True   = arcs!!n

-- used by arrangeGraph,concatGraphs,scaleAndDraw,showInSolver

-- addSmoothArc graph (s,t,..) adds a smooth line from s to t together with the
-- control points of the line.

addSmoothArc :: Graph -> (Int,Int,Widget_,Widget_,[Int]) -> Graph
addSmoothArc (pict,arcs) (s,t,v,w,ts)
                         | s == t = (f [(xp,y),mid,(x,yp)],
                                    setArcs 3 [s,lg,i,j] [targets,[i],[j],[t]])
                         | True   = (f [r], setArcs 1 [s,lg] [targets,[t]])
                         where f = (pict++) . map (Dot red)
                               p@(xp,yp) = coords v 
                               mid@(x,y) = apply2 (+30) p
                               q@(xq,yq) = coords w
                               seORnw = signum (xq-xp) == signum (yq-yp) 
                               r = rotate (div2 $ add2 p q)
                                          (if seORnw then 90 else 270) p
                               lg = length arcs
                               (i,j) = (lg+1,lg+2)
                               targets = lg:ts `minus1` t
                               setArcs n = fold2 updList $ arcs++replicate n []

-- used by releaseButton,bunchesToArcs

arcsToBunches :: Graph -> Picture                                -- not used
arcsToBunches (Bunch w is:pict,ks:arcs) 
                               = Bunch w (is`join`ks):arcsToBunches (pict,arcs)
arcsToBunches (w:pict,is:arcs) = Bunch w is:arcsToBunches (pict,arcs)
arcsToBunches _                = []

-- buildAndTrimPaths transforms the arcs of a graph into paths that do not cross
-- the borders of its picture. 

buildAndTrimPaths :: Graph -> [Path]
buildAndTrimPaths graph@(pict,_) = map f $ buildPaths graph
                   where f (n:ns) = p':ps++[q']
                                    where v = pict!!n
                                          w = pict!!last ns
                                          ps = map (coords . (pict!!)) $ init ns
                                          p = coords v
                                          q = coords w
                                          p' = hullCross (head $ ps++[q],p) v
                                          q' = hullCross (last $ p:ps,q) w

-- used by drawArcs

-- exchgWidgets pict s t exchanges the positions of nodes s and t in the graph
-- and in the plane.

exchgWidgets :: Picture -> Int -> Int -> Picture
exchgWidgets pict s t = updList (updList pict s $ moveWidg (coords v) w) t
                                                $ moveWidg (coords w) v
                        where (v,w) = (pict!!s,pict!!t)

-- used by arrangeButton,releaseButton

-- exchgPositions graph s t exchanges the positions of nodes s and t of graph in
-- the plane. 

exchgPositions :: Graph -> Int -> Int -> Graph
exchgPositions graph@(pict,arcs) s t = (exchgWidgets pict s t,
                                         foldl paths2arcs arcs0 paths7)
      where arcs0 = replicate (length arcs) []
            paths = buildPaths graph
            paths1 = [path | path@(m:_) <- paths, 
                     let n = last path in m == s && n == t || m == t && n == s]
            paths' = paths `minus` paths1
            paths2 = [t:path | m:path <- paths', m == s]
            paths3 = [s:path | m:path <- paths', m == t]
            paths4 = [init path++[t] | path@(_:_) <- paths', last path == s]
            paths5 = [init path++[s] | path@(_:_) <- paths', last path == t]
            paths6 = [path | path@(m:_) <- paths',
                     m /= s && m /= t && let n = last path in n /= s && n /= t]
            paths7 = map reverse paths1++paths2++paths3++paths4++paths5++paths6 
            paths2arcs arcs (m:path@(n:_)) = paths2arcs arcs' path
                                 where arcs' = updList arcs m (arcs!!m`join1`n)
            paths2arcs arcs _ = arcs

-- used by permutePositions,releaseButton

-- buildPaths graph regards the nodes of each maximal path p of graph consisting
-- of red dots as control points of smooth lines that connect a direct
-- predecessor of p with a direct successor of p. 

buildPaths :: Graph -> Arcs
buildPaths (pict,arcs) = connect $ concatMap f $ indices_ pict where
   f i = if isSkip (pict!!i) then [] else [[i,j] | j <- arcs!!i]
   connect (path:paths) = connect2 path paths
   connect _            = []
   connect2 path paths | hpath == lpath     = path:connect paths
                       | lastdot || headdot = case search2 f1 f2 paths of 
                                              Just (i,b) -> connectC (new i b) i
                                              _ -> connect paths
                       | True              = path:connect paths
                         where new i True = ipath++paths!!i
                               new i _    = paths!!i++tpath
                               hpath:tpath = path
                               (ipath,lpath) = (init path,last path)
                               lastdot = isRedDot (pict!!lpath)
                               headdot = isRedDot (pict!!hpath)
                               f1 path = lastdot && lpath == head path
                               f2 path = last path == hpath && headdot
                               connectC path i = connect2 path $ context i paths

-- used by buildAndTrimPaths,exchgPositions,graphToTerm,releaseButton

-- SPLINING

spline :: Path -> Path
spline ps@(p:_:_:_)  = if p == last ps then spline0 True $ init ps
                                       else spline0 False ps
spline ps = ps

-- used by hulls,splinePict

-- spline0 isClosed ps uses ps as control points for constructing a closed resp.
-- open B-spline with degree 3; see Paul Burke, Spline Curves 
-- (http://astronomy.swin.edu.au/~pbourke/curves/spline)
-- or Heinrich Müller, B-Spline-Technik, Vorlesung Geometrisches Modellieren 
-- (http://ls7-www.cs.tu-dortmund.de).

spline0 :: Bool -> Path -> Path
spline0 isClosed ps = first:map f [1..resolution] ++ map g [1..9] ++
                      [if isClosed then first else ps!!(n-1)]
         where first = f 0; n = length ps; resolution = n*6
               f i = point $ upb*fromInt i/fromInt resolution 
               g i = point $ upb+fromInt i/10
               upb = fromInt n-if isClosed then 1 else 3
               point v = foldl1 add2 $ map h [0..n-1] where
                         h i = apply2 (*z) $ ps!!i where
                               z | isClosed && v < u i = blend2 u i $ v-u 0+u n 
                                 | isClosed            = blend2 u i v
                                 | True                = blend2 t i v 
               t i = if i < 3 then 0 else fromInt (min i n)-2
               u i = if i <= n then fromInt i else u (i-1)+u (i-n)-u (i-n-1)
               h d s = if d == 0 then 0 else s
               blend2 t i v = h denom1 sum1+h denom2 sum2
                              where ti = t i; ti3 = t $ i+3
                                    denom1 = t (i+2)-ti;  num1 = v-ti
                                    denom2 = ti3-t (i+1); num2 = ti3-v
                                    sum1 = num1/denom1*blend1 t i v
                                    sum2 = num2/denom2*blend1 t (i+1) v
               blend1 t i v = h denom1 sum1+h denom2 sum2
                              where ti = t i; ti1 = t $ i+1; ti2 = t $ i+2
                                    denom1 = ti1-ti;  num1 = v-ti 
                                    denom2 = ti2-ti1; num2 = ti2-v
                                    sum1 = if b i then num1/denom1 else 0
                                    sum2 = if b $ i+1 then num2/denom2 else 0
                                    b i = t i <= v && v < t (i+1)

-- CROSSINGS and PICTURE EXTENSIONS

-- hullCross (p1,p2) w computes the crossing of (p1,p2) with w such that p2
-- agrees with the coordinates of w.

hullCross :: Line_ -> Widget_ -> Point
hullCross line@(p1@(x1,y1),p2@(x2,y2)) w = 
      case w of Arc _ _ _ _    -> head hull
                Gif _ _ _ hull -> hullCross line hull  
                Oval (_,0,_,_) rx ry  -> if p1 == p2 then p2 
                                         else (x2+rx*cos rad,y2+ry*sin rad) 
                                         where rad = atan2' (y1-y2) (x1-x2)
                Path _ _ _ ps  -> head $ f $ mkLines ps
                Slice _ _ _ _  -> head hull
                Text_ _ _ _ _  -> mindist p1 hull
                Tree _ _       -> mindist p1 hull
                _ | isWidg w   -> head hull
                  | isPict w   -> mindist p1 hull
                Bunch w _      -> hullCross line w
                Fast w         -> hullCross line w
                Repeat w       -> hullCross line w
                w              -> p2
      where hull = f $ concat $ getFrameLns w
            f ls = if null ps then [p2] else map get ps
                   where ps = filter just $ map (crossing (line,p2)) $ addSuc ls

-- used by buildAndTrimPaths,convexPath

-- crossing line1 line2 returns the crossing point of line1 with line2.

crossing :: (Line_,Point) -> (Line_,Point) -> Maybe Point
crossing ((p1@(x1, y1), p2@(x2, _)), p5) ((p3@(x3, y3), p4@(x4, _)), p6)
                           | x1 == x2 = if x3 == x4 then onLine else enclosed q1
                           | x3 == x4 = enclosed q2
                           | a1 == a2 = do guard $ b1 == b2; onLine
                           | True = enclosed q
        where a1 = slope p1 p2
              a2 = slope p3 p4
              b1 = y1-a1*x1     -- p1, p2 and q2 solve y = a1*x+b1
              b2 = y3-a2*x3     -- p3, p4 and q1 solve y = a2*x+b2
              a = a1-a2
              q = ((b2-b1)/a,(a1*b2-a2*b1)/a)  -- q solves both equations
              q1 = (x1,a2*x1+b2)
              q2 = (x3,a1*x3+b1)
              enclosed p = do guard $ inFrame p1 p p2 && inFrame p3 p p4; next p
              onLine | inFrame p1 p3 p2 = next p3
                     | inFrame p1 p4 p2 = next p4
                     | inFrame p3 p1 p4 = next p1
                     | True             = do guard $ inFrame p3 p2 p4; next p2
              next p = do guard $ (p /= p2 || inFrame p1 p p5) &&
                                  (p /= p4 || inFrame p3 p p6)
                          Just p

-- used by crossings,hullCross,interior

-- crossings lines1 lines2 returns all triples (p,line1,line2) with line1 in
-- lines1, line2 in lines2 and crossing point p of line1 and line2.

type Crossing = (Point,(Line_,Line_))

crossings :: Lines -> Lines -> [Crossing]
crossings lines1 lines2 = [(get p,(fst line1,fst line2)) | 
                            line1 <- addSuc lines1, line2 <- addSuc lines2,
                           let p = crossing line1 line2, just p]

-- used by strands

addSuc :: Lines -> [(Line_,Point)]
addSuc [] = []
addSuc ls = zip ls (map snd $ tail ls) ++
             [(line2,if p == fst line1 then snd line1 else p)]
             where line1 = head ls; line2 = last ls; p = snd line2

-- strands pict computes the subpaths of the hulls hs of pict that enclose the
-- intersection resp. union of the elements of hs and connects them.

strands :: Picture -> ([(Widget_,Widget_,[Crossing])],[Path],[Color],
                                                      [Path],[Color])
strands pict = (hcs,map pr3 inner,innerCols,outer,map col outer)
     where hs = concatMap (hulls False) pict
           is = indices_ hs
           rev i is = if even i then is else reverse is
           hcs = [(h1,h2,cs) | i <- is, j <- rev i is, i < j,
                               let h1 = hs!!i; h2 = hs!!j
                                   cs = crossings (getLines h1) $ getLines h2,
                               notnull cs]
           inner = concatMap threadsI hcs
           innerCols = zipWith ($) (cycle [pr1,pr2]) inner
           getColor (Path0 _ c _ _ _) = c
           add ps pss = if null ps then pss else ps:pss
           threadsI (h1,h2,cs) = map f $ connect $ strands b ps1++strands c ps2
                      where f path = (getColor h1,getColor h2,path)
                            ps1 = extend h1 sucs1
                            ps2 = extend h2 sucs2
                            sucs1 p = [r | (r,((q,_),_)) <- cs, p == q]
                            sucs2 p = [r | (r,(_,(q,_))) <- cs, p == q]
                            b = interior (head ps1) $ getLines h2
                            c = interior (head ps2) $ getLines h1
                            strands b ps = add qs pss
                                where (qs,pss,_) = foldl next ([],[],b) ps
                                      next (ps,pss,b) p =
                                           if p `elem` map fst cs
                                           then if b then ([],(p:ps):pss,False)
                                                     else ([p],pss,True)
                                           else if b then (p:ps,pss,b)
                                                     else ([],pss,b)
           outer = connect $ concatMap threadsO hs
           col ps = case searchGet (shares ps . getPoints) hs of
                         Just (_,h) -> getColor h; _ -> black
           threadsO h = add qs pss
                where sucs p = [r | (h1,h2,cs) <- hcs,(r,((p1,_),(p2,_))) <- cs, 
                                    (h,p) `elem` [(h1,p1),(h2,p2)]]
                      (qs,pss,_) = foldl next ([],[],Nothing) $ extend h sucs
                      next (ps,pss,r) p | p `elem` concatMap (map fst . pr3) hcs
                                               = if just r && g (mid (get r) p)
                                                 then ([p],ps:pss,Just p)
                                                 else (p:ps,pss,Just p)
                                        | g p  = ([],add ps pss,Nothing)
                                        | True = (p:ps,pss,Nothing)
                      g p@(x,y) = any (interior p ||| any onLine) $ map getLines
                                                                  $ minus1 hs h
                           where onLine (p1@(x1,y1),p2) =
                                   inFrame p1 p p2 && y == slope p1 p2*(x-x1)+y1
                      mid p = div2 . add2 p
           extend h sucs = (concatMap f $ init ps)++[last ps]
                       where ps = getPoints h
                             f p = sort rel $ p:sucs p
                                   where rel r r' = distance p r < distance p r'
           connect (ps:pss) = case search2 ((==) (last ps) . head)
                                           ((==) (head ps) . last) pss of
                                   Just (i,True) -> g i $ init ps++pss!!i
                                   Just (i,_)    -> g i $ pss!!i++tail ps
                                   _             -> ps:connect pss
                              where g i = connect . updList pss i
           connect _        = []

-- used by dots,joinPict,outline,planarWidg,widgArea

joinPict :: Int -> PictTrans
joinPict m pict = case m of
                       6  -> pict++map center pict
                       7  -> pict++concatMap (map dot . pr3) hcs
                       8  -> pict++zipWith darkLine innerCols inner
                       9  -> pict++map whiteFill inner
                       10 -> pict++zipWith lightFill innerCols inner
                       11 -> pict++zipWith fill innerCols inner
                       12 -> pict++zipWith darkLine outerCols outer
                       13 -> pict++fillHoles light
                       14 -> zipWith lightFill outerCols rest++fillHoles id
                       _  -> pict
               where center w = Dot col p 
                                where p = coords w
                                      col = if any (inWidget p) $ minus1 pict w 
                                            then grey else black
                     dot = Dot (RGB 0 0 1) . fst
                     (hcs,inner,innerCols,outer,outerCols) = strands pict
                     whiteFill        = path0 1 white 2
                     darkLine c       = path0 2 (dark c) 0
                     lightFill c      = path0 1 (light c) 2
                     fill (RGB 0 0 0) = whiteFill
                     fill c           = path0 1 c 2
                     fillHoles f = zipWith g [0..] holes
                                   where g i = path0 1 (f $ hue 0 yellow n i) 2
                                         n = length holes
                     (holes,rest) = split hole outer
                     hole ps = any f $ minus1 outer ps
                               where f qs = all g ps
                                            where g p = interior p $ mkLines qs

-- used by scaleAndDraw,widgets

-- convexHull ps computes the convex hull of ps by splitting ps into halves and 
-- connecting the subhulls by clockwise searching for and adding an upper and a
-- lower tangent; see Preparata/Hong, CACM 20 (1977) 87-93. The auxiliary 
-- function f adds to the hull all points of ps that are located on horizontal
-- or vertical lines of the hull. (For some unknown reason, the actual algorithm
-- g does not recognize these points as part of the hull.)

convexHull :: Path -> Path
convexHull ps = f $ g ps
 where f (q@(x1,y1):qs@((x2,y2):_))
          | x1 == x2 && y1 < y2 = g [p | p@(x,y) <- ps, x == x1, y1 < y, y < y2]
          | x1 == x2 && y1 > y2 = h [p | p@(x,y) <- ps, x == x1, y1 > y, y > y2]
          | y1 == y2 && x1 < x2 = g [p | p@(x,y) <- ps, y == y1, x1 < x, x < x2]
          | y1 == y2 && x1 > x2 = h [p | p@(x,y) <- ps, y == y1, x1 > x, x > x2]
          | True                = q:f qs where g ps = q:sort (<) ps++f qs
                                               h ps = q:sort (>) ps++f qs
       f qs = qs
       g ps | lg < 3                         = ps
            | p1 == p2 && q1 == q2 || a == b = left ++ right
            | True                           = h p2 p1 left ++ h q1 q2 right
              where lg = length ps
                    (left, right) = apply2 g $ splitAt (div lg 2) ps
                    minL@((a, _) : _) = minima fst left
                    maxL = maxima fst left
                    minR = minima fst right
                    maxR@((b, _) : _) = maxima fst right
                    minY = head . minima snd
                    maxY = head . maxima snd
                    upperLeft = h (maxY minL) (maxY maxL) left
                    upperRight = h (maxY minR) (maxY maxR) right
                    lowerLeft = h (minY maxL) (minY minL) left
                    lowerRight = h (minY maxR) (minY minR) right
                    (p1,q1) = upperTangent upperLeft upperRight
                    (p2,q2) = lowerTangent lowerLeft lowerRight
       h p q ps@(_:_:_) = take (getInd qs q+1) qs
                          where qs = drop i ps++take i ps; i = getInd ps p
       h _ _ ps         = ps

upperTangent :: [(Double, Double)]
             -> [(Double, Double)] -> ((Double, Double), (Double, Double))
upperTangent ps@(p1:_) (q1:qs@(q2:_)) 
                              | slope p1 q1 < slope q1 q2  = upperTangent ps qs
upperTangent (p1:ps@(p2:_)) qs@(q1:_) 
                               | slope p1 q1 <= slope p1 p2 = upperTangent ps qs
upperTangent (p1:_) (q1:_)                                     = (p1,q1)

lowerTangent :: [(Double, Double)]
             -> [(Double, Double)] -> ((Double, Double), (Double, Double))
lowerTangent (p1:ps@(p2:_)) qs@(q1:_) 
                               | slope p1 q1 < slope p1 p2  = lowerTangent ps qs
lowerTangent ps@(p1:_) (q1:qs@(q2:_)) 
                               | slope p1 q1 <= slope q1 q2 = lowerTangent ps qs
lowerTangent (p1:_) (q1:_)                                     = (p1,q1)

convexPath :: Path -> Picture -> (Picture, Path)
convexPath ps pict = if straight ps then (h ps,ps) else (h $ last qs:qs,qs)
  where qs = convexHull $ sort (<) ps
        f p q = Path0 1 blue 0 0 [g q p,g p q]
        g p q = hullCross (p,q) $ pict!!get (search ((== q) . coords) pict)
        h ps = zipWith f ps $ tail ps

-- used by scaleAndDraw

-- TURTLE ACTIONS

rectC :: Color -> Double -> Double -> TurtleAct
rectC c b = widg . Rect (st0 c) b

halfmax :: (a -> Int) -> [a] -> Double
halfmax width = (/2) . fromInt . maximum . map width

blackText :: Sizes -> String -> TurtleAct
blackText sizes = widg . textWidget black sizes

-- alignments

drawAlignment :: Sizes -> Align_ String -> [TurtleAct]
drawAlignment sizes@(height,width) t = 
                   case t of Compl x y t -> f x t y red
                             Equal_ [x] t -> f x t x green
                             Equal_ (x:s) t -> f x (Equal_ s t) x green
                             Ins [x] t -> g t x
                             Ins (x:s) t -> g (Ins s t) x
                             Del [x] t -> h x t
                             Del (x:s) t -> h x $ Del s t
                             End s@(_:_) -> drawAlignment sizes $ Del s $ End []
                             _ -> []
     where f x t y color = JumpA bt:open:blackText sizes x:down:OpenC color:
                           JumpA ht:Move 30:JumpA ht:up:open:blackText sizes y:
                           jump t bt++Close:Close:Close:jump t bt++
                           drawAlignment sizes t where bt = halfmax width [x,y]
           g t x = acts++JumpA bt:blackText sizes x:jump t bt++Close:move t wa++
                   drawAlignment sizes t where wa = fromInt $ width x; bt = wa/2
           h x t = acts++move t wa++Close:JumpA bt:blackText sizes x:jump t bt++
                   drawAlignment sizes t where wa = fromInt $ width x; bt = wa/2
           ht = fromInt height/2
           acts = [open,down,JumpA ht,Jump 30,JumpA ht,up]

jump,move :: Eq a => Align_ a -> Double -> [TurtleAct]
jump t bt = if t == End [] then [] else [JumpA bt,Move 30]
move t bt = if t == End [] then [MoveA bt] else [MoveA bt,Move 30]

-- dissections

drawDissection :: [(Int,Int,Int,Int)] -> [TurtleAct]
drawDissection = concatMap f
      where f (x,y,b,h) = [open,Jump x',down,Jump y',up,rectC black b' h',Close]
                          where x' = 10*fromInt x+b'; y' = 10*fromInt y+h'
                                b' = 5*fromInt b; h' = 5*fromInt h

spiral :: Bool -> Color -> Int -> Double -> [TurtleAct]
spiral b c n w = concatMap f [1..n] where
                 f i = arcs++[back,Jump w] where
                       arcs = if b then [arc 180] else [up,arc 90,down,arc 90]
                       arc = widg . Arc (st0 c) w (fromInt i*w)

spiralP :: Color -> Int -> Double -> Path -> [TurtleAct]
spiralP c n w ps = concatMap f [1..n] 
                   where f i = path:jumpTo (last qs)++[back] where
                               path = widg $ path0 w c 0 $ p0:qs
                               qs = map g ps
                               g (x,y) = (if x == 0 then 0 else h x,h y)
                               h x = x*fromInt i/fromInt n

spiralT :: Int -> Color -> Int -> Double ->  [TurtleAct] -> [TurtleAct]
spiralT m c n w acts = OpenW w:concatMap f [1..n] where
                       f i = OpenC (hue m c n i):map g acts++[Draw] 
                             where g (Move x) = Move $ x*fromInt i/fromInt n
                                   g act      = act

star :: Int -> Color -> Double -> Double -> [TurtleAct]
star n c = f $ n+n where a = 180/fromInt n
                         f 0 _ _  = []
                         f n r r' = OpenC c:Jump r:Open 2:Move (-r):Turn (-a):
                                    Move r':Close:Close:Turn a:f(n-1) r' r

taichi :: Sizes -> [TermS] -> Color -> [TurtleAct]
taichi sizes s c = [open,circ c 120,down,widg $ Slice (st0 d) Pie 120 180,
                    Jump 60,back,circ d 60,circ c 12,open,jump1,down,jump2,
                    widg $ textWidget c sizes yang,Close,Jump 120,back,
                    circ c 60,circ d 12,open,jump1,down,jump2,
                    widg $ textWidget d sizes yin,Close]
                   where d = complColor c; jump1 = Jump 32; jump2 = Jump 52
                         circ c r = widg $ Oval (st0 c) r r
                         (yin,yang) = case s of t:u:_ -> (root t,root u)
                                                [t] -> (root t,"")
                                                _ -> ("","")

blossom :: (Color -> Color) -> Int -> Color -> (Color -> [TurtleAct])
                                            -> [TurtleAct]
blossom next n c acts = open:f c (n-1)++[Close]
                        where f c 0 = acts c
                              f c i = acts c++Turn a:f (next c) (i-1)
                              a = 360/fromInt n
                              
blossomD :: (Color -> Color) -> Int -> Color 
                             -> (Color -> Color -> [TurtleAct]) -> [TurtleAct]
blossomD next n c acts = open:f c (n-1)++[Close]
                         where f c 0 = acts c $ next c
                               f c i = acts c c'++Turn a:f (next c') (i-1)
                                       where c' = next c
                               a = 360/fromInt n

pie :: Char -> String -> Color -> Int -> Int -> [TermS] 
                                             -> MaybeT Cmd [TurtleAct]  
pie pmode hmode c m n ts = do factor:rs@(_:_) <- lift' $ Just ts
                              factor <- lift' $ parsePnat factor
                              rs <- lift' $ mapM parseReal rs
                              hmode <- lift' $ getHue hmode
                              let next = nextColor hmode
                                  rs' = concat $ replicate factor rs
                                  lg = length rs'; b = 360/fromInt lg
                                  act c i = widg $ Slice (st0 c) mode (rs'!!i) 
                                                 $ b+0.2
                                  f c i | i < m     = []
                                        | i >= lg-n = acts
                                        | True      = act c i:acts where
                                               acts = Turn b:f (next lg c) (i-1)
                              return $ open:f c (lg-1)++[Close] 
                           where mode = case pmode of 'A' -> Perimeter
                                                      'C' -> Chord
                                                      _ -> Pie

leafA :: Double -> Double -> Color -> Color -> [TurtleAct]
leafA r a c c' = [open,Jump y,down,Jump x,Turn $ b-180,w c,Turn $ -b,
                  Jump $ 2*x,Turn $ b+180,w c',Close] 
                 where (x,y) = successor p0 r b; b = a/2
                       w c = widg $ Slice (st0 c) Chord r a

leafC,leafD :: Double -> Double -> Color -> Color -> [TurtleAct]
leafC h b c c' = chord True h b c ++ chord False h b c'
leafD r a c c' = Open 2:OpenC c:Turn a:move:g 5
                 where g 0 = Close:OpenC c':Turn (-a):move:h 5
                       g n = Turn (-b):move:g (n-1)
                       h 0 = close2
                       h n = Turn b:move:h (n-1)
                       move = Move r; b = 2*a/5

leafS :: Double -> Double -> Color -> [TurtleAct]
leafS d a c = Open 3:OpenC c:go++back:go++[Close]
              where go = [up,move,down,Move $ 2*d,down,move,up]
                    up = Turn (-a); down = Turn a; move = Move d

chord :: Bool -> Double -> Double -> Color -> [TurtleAct]
chord left h b c = open:acts++
                   [Jump $ -r,widg $ Slice (st0 c) Chord r $ 2*a,Close]
                   where r = h^2/(2*b)+b/2; a = angle p0 (r-b,h)
                         acts = if left then [up,Jump $ 2*h,Turn $ 270+a]
                                        else [Turn a]

rhombH :: Widget_
rhombH = path0 1 green 5 [p0,(3,-2),(16,0),(3,2),p0]

rhombV :: Color -> Widget_
rhombV c = path0 1 c 5 [p0,(-6,-9),(0,-48),(6,-9),p0]

-- growing trees

mkTrunk :: Color -> String -> Widget_
mkTrunk c x = path0 1 c 2 $ p0:ps++[(90,0),p0] where
   ps = case x of "TR" -> [(45,-x1)]                                -- triangle
                  "SQ" -> [(0,-90),(90,-90)]                        -- square
                  "PE" -> [(-x2,-x3),(45,-138.49576),(x8,-x3)]      -- pentagon
                  "PS" -> [(-14.079101,-x7),(44.62784,-127.016685), -- pentagonS
                           (103.33478,-x7)]                 
                  "PY" -> [(0,-90),(36,-135),(90,-90)]              -- pytree
                  "CA" -> [(7.5,-60),(22.5,-90),(67.5,-90),
                           (82.5,-60)]                              -- cactus
                  "HE" -> [(-45,-x1),(0,-x4),(90,-x4),(135,-x1)]    -- hexagon  
                  "LB" -> [(-x2,-x3),(62.18847,-x3)]                -- rhombLB
                  "RB" -> [(27.811527,-x3),(x8,-x3)]                -- rhombRB
                  "LS" -> [(-x9,-x5),(17.188461,-x5)]               -- rhombLS
                  "RS" -> [(x9,-x6),(162.81152,-x6)]                -- rhombRS
   x1 = 77.94229;  x2 = 27.811533; x3 = 85.595085; x4 = 155.88458
   x5 = 52.900665; x6 = 52.900673; x7 = 88.89195; x8 = 117.81153; x9 = 72.81154

grow :: WidgTrans -> Color -> Widget_ -> [[TurtleAct]] -> [TurtleAct]
grow tr c w branches = widg (tr cw):concat (zipWith g branches $ getAllLines w)
                    where cw = updCol c w
                          g [] _               = []
                          g branch (p@(x,y),q) = open:Jump x:down:Jump y:Turn a:
                                                 OpenS (d/90):branch++close2
                                                 where a = angle p q-90
                                                       d = distance p q

growR :: Widget_ -> [Bool] -> WidgTrans -> Int -> [TurtleAct]
growR w bs tr n = f c n where c = getCol w
                              f _ 0 = []
                              f c i = grow tr c w $ map g bs
                                      where g True = f (nextColor 0 n c) $ i-1
                                            g _    = []

growA :: Color -> Int -> [TurtleAct] -> [Bool] -> [TurtleAct]
growA c n acts bs = f c n where
                    f _ 0 = []
                    f c i = OpenC c:Open 2:acts++close2++h acts (map g bs)
                            where g True = f (nextColor 0 n c) $ i-1
                                  g _    = []
                    h (turn:Move d:acts) (b:bs) = 
                            if null b then turn:Jump d:h acts bs
                            else turn:OpenS (d/90):b++Close:Jump d:h acts bs
                    h _ _ = []
                                                  
mkBased :: Color -> Widget_ -> Maybe Widget_
mkBased c w = do guard $ length ps > 2 && p == last ps && d /= 0
                 Just $ path0 1 c 2
                      $ map (apply2 (*(90/d)) . rotate p0 a . sub2 p) ps
              where ps@(p:qs) = getAllPoints w
                    q = last $ init qs; d = distance p q; a = -angle p q

flower :: Int -> Picture -> [TurtleAct]
flower mode (w1:w2:w3:w4:w5:_) =
            case mode of 0 -> up:jump 0.8 50 60 w1++jump 0.8 8 110 w2++
                              jump 0.8 80 120 w3++jump 0.6 12 70 w4++turn 0.8 w5
                         1 -> up:jump 0.8 72 60 w1++jump 0.8 12 110 w2++
                              jump 0.6 12 70 w3++jump 0.8 54 70 w4++turn 0.6 w5
                         _ -> up:jump 0.8 40 110 w1++jump 0.8 24 60 w2++
                              jump 0.6 43 110 w3++jump 0.6 43 70 w4++turn 0.6 w5
            where jump sc n a w = Jump n:open:Turn a:OpenS sc:widg w:close2
                  turn sc w = open:Turn 100:OpenS sc:widg w:close2
flower _ _ = []

-- fractals

data Direction = North | East | South | West

north,east,south,west :: [TurtleAct]
north = [up,Move 10,down]
east  = [Move 10]
south = [down,Move 10,up]
west  = [Move $ -10]

hilbert :: Int -> Direction -> [TurtleAct]
hilbert 0 _   = []
hilbert n dir = case dir of 
                     East -> hSouth++east++hEast++south++hEast++west++hNorth
                     West -> hNorth++west++hWest++north++hWest++east++hSouth
                     North -> hWest++north++hNorth++west++hNorth++south++hEast
                     South -> hEast++south++hSouth++east++hSouth++north++hWest
                where hEast = h East; hWest = h West; hNorth = h North
                      hSouth = h South; h = hilbert $ n-1

hilbshelf :: Int -> [a] -> [a]
hilbshelf n s = foldl f s $ indices_ s
               where f s' i = updList s' (y*2^n+x) $ s!!i 
                              where (x,y) = apply2 (round . (/10)) $ path!!i
                                    (path,_) = foldl g ([p0],0) $ hilbert n East
                     g (ps,a) act = case act of 
                                    Move d -> (ps++[successor (last ps) d a],a)
                                    Turn b -> (ps,a+b)

fern2 :: Int -> Double -> Double -> [TurtleAct]
fern2 n del rat = open:up:f n 0++[Close]
                  where f 0 _ = []
                        f n 0 = act:Draw:open:Turn 30:g del++Close:
                                open:Turn (-30):g del++Close:act<:>g 0
                                where act = Move $ rat^(n-1)
                                      g = f (n-1)
                        f n k = f (n-1) $ k-1

fractal :: Color -> String -> Int -> [TurtleAct]
fractal c "bush" n = open:up:f c n++[Close] where
                     f _ 0 = [Move 1]
                     f c i = acts<++>acts<++>acts++Draw:open:acts1++Close:
                             open:Turn (-25):acts<++>acts1<++>acts2++[Close]
                             where acts = f (nextColor 0 n c) $ i-1
                                   acts1 = acts2<++>acts2<++>acts2
                                   acts2 = Turn 25:acts
                                   open = OpenC c

fractal c "bush2" n = Open 1:up:f c n++[Close] where
                      f _ 0 = [Move 3]
                      f c i = acts<++>acts++Draw:open:Turn 20:acts<++>acts++
                              Close:open:Turn (-20):acts++Turn 20:acts++[Close]
                              where acts = f (nextColor 0 n c) $ i-1
                                    open = OpenC c

fractal c "cant" n = open:acts 0 0 where
         acts x y = if x < n' || y < n' 
                    then if even x 
                         then if even y
                              then if x > 0 
                                   then if y' < n then move (-1) 1 else move 1 0
                                   else if y' < n then move 0 1 else move 1 0
                              else if x' < n then move 1 (-1) else move 0 1
                         else if even y
                              then if y > 0 
                                   then if x' < n then move 1 (-1) else move 0 1
                                   else if x' < n then move 1 0 else move 0 1
                              else if y' < n then move (-1) 1 else move 1 0
                    else []
                    where n' = n-1; x' = x+1; y' = y+1
                          move 0 b = down:Move (fromInt b):up:Draw:acts x (y+b)
                          move a 0 = Move (fromInt a):Draw:acts (x+a) y
                          move a b = Turn c:Move d:Turn (-c):Draw:acts xa yb
                                  where xa = x+a; yb = y+b
                                        p = fromInt2 (x,y); q = fromInt2 (xa,yb)
                                        c = angle p q; d = distance p q

fractal c "dragon" n = open:f n++[Close] where
                       f 0 = [Move 10]
                       f i = Turn 45:f (i-1)++Turn (-135):g (i-1)++[Turn 45]
                       g 0 = [Turn 45,Move 10]
                       g i = f (i-1)++Turn 45:g (i-1)++[Turn (-45)]

fractal c "fern" n = open:up:f c n 1++[Close] where
                     f _ 0 _ = [Move 10]
                     f c i a = g 0.35 (a*50) (-a)++g 0.35 (-a*50) a++
                               g 0.85 (a*2.5) a where
                               g sc a b = Move 10:Draw:OpenC c:OpenS sc:Turn a:
                                          f (nextColor 0 n c) (i-1) b++close2

fractal c "gras" n = open:up:f c n++[Close] where
                     f _ 0 = [Move 6]
                     f c i = m:open++h (-25)++m:open++h 37.5++Open 1:m:h 12.5
                           where m = Move $ 2^i; open = [Draw,OpenC c]
                                 h a = Turn a:f (nextColor 0 n c) (i-1)++[Close]

fractal _ ['g','r','a','s',m] n = OpenS 6:open:up:f n++close2 where
                       f 0 = case m of 'D' -> leafD 0.5 30 green green
                                       'A' -> leafA 3 50 green green    
                                       'C' -> down:leafC 1 0.2 green green++[up]
                                       _   -> [widg $ scaleWidg 0 0.2 rhombH]
                       f i = m:Draw:up:open:acts++Close:open:down:acts++Close:
                             down:m:Draw:open:down:m<:>acts++Close:up:acts
                             where acts = f $ i-1;    m = Move $ 2^i
                                   up = Turn $ -22.5; down = Turn 22.5  

fractal c "hilb" n = f c n East where
                     f _ 0 _   = []
                     f c i dir = g sdir++draw dir++g dir++draw sdir++
                                 g dir++draw (flip dir)++g (flip sdir)
                                 where g = f (nextColor 0 n c) $ i-1
                                       sdir = swap dir
                                       draw dir = OpenC c:move dir++[Draw]
                     swap North = West; swap East = South; swap South = East
                     swap _     = North
                     flip North = South; flip East = West; flip South = North
                     flip _     = East 
                     move North = north; move East = east; move South = south
                     move _     = west

fractal _ "koch" n = f n++g n where f i = h i++g i 
                                    g i = Turn (-120):h i
                                    h 0 = [Move 1,Draw]
                                    h i = acts++Turn 60:f (i-1)++Turn 60:acts 
                                          where acts = h $ i-1

fractal c "pytreeA" n = growA c n acts [False,True,True] where
                       acts = [up,m,Turn 38.659805,Move 57.628117,Turn 91.14577,
                               Move 70.292244,Turn 50.19443,m,down,m]
                       m = Move 90

fractal c "wide" n = up:f c n++[Close] where
                    f _ 0 = [Move 3]
                    f c i = open:Turn 20:acts++open:Turn 20:acts1++Turn (-40):
                            acts1++open:Turn (-40):acts<++>acts1++g c' (i-1)
                            where acts = h c' (i-1); acts1 = f c' (i-1)++[Close]
                                  c' = next c; open = OpenC c
                    g _ 0 = [Move 3]
                    g c i = h c' (i-1)<++>f c' (i-1) where c' = next c
                    h _ 0 = [Move 3]
                    h c i = acts<++>acts where acts = h (next c) $ i-1
                    next = nextColor 0 n

polygon :: Color -> String -> WidgTrans -> Int -> [TurtleAct]
polygon c "cactus" = growR (mkTrunk c "CA") [False,True,True,True]
polygon c "hexa"   = growR (mkTrunk c "HE") $ replicate 6 True
polygon c "pytree" = growR (mkTrunk c "PY") [False,True,True]
polygon c "penta"  = growR (mkTrunk c "PE") $ replicate 5 True
polygon c "pentaS" = growR (mkTrunk c "PS") [False,True,True]

-- bars and piles

bar :: Sizes -> Double -> Double -> Color -> [TurtleAct]
bar sizes@(height,_) i h c = [open,blackText sizes $ show i,up,
                              JumpA $ fromInt height/2+3,open,Jump i,
                              rectC c i 5,Close,Jump h,rectC black h 5,Close]

colbars :: Sizes -> Color -> [TurtleAct]
colbars sizes (RGB r g b) = f r red++Jump 90:f g green++Jump 90:f b blue
                             where f c = bar sizes (abs (fromInt c)/4) 64

pile :: Int -> Int -> [TurtleAct]
pile h i = open:up:f h i++[Close]
           where f 0 _ = []
                 f h 0 = Jump 20:frame:f (h-1) 0
                 f h i = Jump 20:quad:frame:f (h-1) (i-1)
                 frame = rectC black 10 10
                 quad = rectC (light blue) 10 10

pileR :: Int -> [Int] -> [TurtleAct]
pileR h is = actsToCenter $ open:up:f h (reverse is)++[Close]
             where f 0 _      = []
                   f n (i:is) = Jump 20:quad i:frame:f (n-1) is
                   f n _      = Jump 20:frame:f (n-1) []
                   frame = rectC black 10 10
                   quad i = rectC (hue 0 green h i) 10 10

-- matrices

drawMatrix :: Sizes -> (String -> String -> [TurtleAct]) -> [String]
                    -> [String] -> (String -> Double) -> (String -> Double)
                    -> [TurtleAct]
drawMatrix sizes@(height,width) entry dom1 dom2 btf htf =
              actsToCenter $ down:open:up:rectC black bt ht:JumpA bt:
                             drawRow lineHead ht++Close:JumpA ht:concatMap h dom
              where lineHead a = [widg $ textWidget blue sizes a]
                    dom = [i | i <- dom1, any notnull $ map (entry i) dom2]
                    bt = halfmax width dom+3
                    ht = fromInt height/2+3
                    h i = JumpA ht:open:up:rectC black bt ht:lineHead i++
                          JumpA bt:drawRow (entry i) ht++[Close,JumpA ht]
                          where ht = htf i
                    drawRow entry ht = concatMap f dom2 where
                                       f j = JumpA bt:rectC black bt ht:entry j
                                             ++[JumpA bt] where bt = btf j

boolMatrix :: Sizes -> [String] -> [String] -> [(String,String)] -> [TurtleAct]
boolMatrix sizes@(height,width) dom1 dom2 ps =
                      drawMatrix sizes entry dom1 dom2 btf $ const ht
                      where entry i j = if (i,j) `elem` ps
                                        then [widg $ Oval (st0 red) m m] else []
                            m = minimum (ht:map btf dom2)-1
                            btf j = halfmax width [j]+3
                            ht = fromInt height/2+3

listMatrix :: Sizes -> Pos -> [String] -> [String] -> TriplesS -> [TurtleAct]
listMatrix sizes spread dom1 dom2 trips = 
                      textWidgMatrix sizes dom1 dom2 $ map f trips 
                      where f (a,b,cs) = (a,b,leaf $ foldl1 g cs)
                            g c d = c++'\'':d
 
termMatrix :: Sizes -> [(String,String,TermS)] -> [TurtleAct]
termMatrix sizes@(height,width) trips = drawMatrix sizes entry dom1 dom2 btf htf
       where (dom1,dom2) = sortDoms $ map (pr1 *** pr2) trips
             entry i j = [act str] where (act,str) = f i j
             f i j = colTerm $ lookupT i j trips
             btf j = halfmax width (j:map (snd . flip f j) dom1)+3
             htf _ = fromInt height/2+3
             colTerm t = (widg . textWidget col sizes,delBrackets $ showTerm0 t) 
                         where col = case parse colPre $ root t of 
                                          Just (c,_) -> c; _ -> black

-- used by linearEqs and matrix for Karnaugh diagrams

widgMatrix :: Sig -> Sizes -> Pos -> [String] -> [String] 
                                  -> [(String,String,TermS)] -> [TurtleAct]
widgMatrix sig sizes spread dom1 dom2 trips = 
                                 drawMatrix sizes entry dom1 dom2 btf htf where
     entry i j = if w == Skip then [] else [widg w] where w = f i j
     f i j = case h black t of Just w -> w
                               _ | t == V "" -> Skip
                                 | True -> g $ showTerm0 t
             where t = lookupT i j trips
     g = textWidget black sizes
     h c (F x [t]) | just tr = do w <- h c t; Just $ get tr w
                               where tr = widgTrans $ leaf x
     h _ (F x [t]) | just c  = h (get c) t where c = parse color x
     h c t                   = widgConst c sizes spread t
     htf i = (y2-y1)/2+3 where (_,y1,_,y2) = pictFrame $ g i:map (f i) dom2
     btf j = (x2-x1)/2+3 where (x1,_,x2,_) = pictFrame $ g j:map (flip f j) dom1
         
-- used by matrix

textWidgMatrix :: Sizes -> [String] -> [String] -> [(String,String,TermS)] 
                        -> [TurtleAct]
textWidgMatrix sizes dom1 dom2 trips = 
                               drawMatrix sizes entry dom1 dom2 btf htf where
     entry i j = [widg $ f i j]
     f i j = g $ showTerm0 $ lookupT i j trips
     g = textWidget black sizes 
     htf i = (y2-y1)/2+3 where (_,y1,_,y2) = pictFrame $ g i:map (f i) dom2
     btf j = (x2-x1)/2+3 where (x1,_,x2,_) = pictFrame $ g j:map (flip f j) dom1
         
-- used by listMatrix

delBrackets :: String -> String
delBrackets ('(':a@(_:_)) | last a == ')' = init a
delBrackets a = a
 
-- used by listMatrix,termMatrix

-- planes

drawPlanes :: Sizes -> Int -> Term a -> [TurtleAct]
drawPlanes sizes mode = f $ case mode of 0 -> levelTerm
                                         1 -> preordTerm
                                         2 -> heapTerm
                                         _ -> hillTerm 
  where f order = split True 100 100 . fst . order blue lab where
                  lab c n = (c,n)
                  split b dx dy (F _ ts@(_:_)) = open:acts++[Close]
                                    where acts = if b then split1 (dx/lg) dy ts
                                                      else split2 dx (dy/lg) ts
                                          lg = fromInt (length ts)
                  split _ dx dy t = [open,Jump dx',down,Jump dy',up,
                                     rectC c dx' dy', blackText sizes $ show n,
                                     Close]
                                     where dx' = dx/2; dy' = dy/2; F (c,n) _ = t
                  split1 dx dy [t]    = split False dx dy t
                  split1 dx dy (t:ts) = split False dx dy t++Jump dx:
                                        split1 dx dy ts
                  split2 dx dy [t]    = split True dx dy t
                  split2 dx dy (t:ts) = split True dx dy t++down:Jump dy:up:
                                        split2 dx dy ts

-- Widgets from strings

graphString :: Parser (Picture,[[Int]])
graphString = do tchar '('; pict <- list widgString; tchar ','
                 arcs <- list (list int); tchar ')'; return (pict,arcs)

-- used by loadGraph

widgString :: Parser Widget_
widgString = concat [do symbol "Arc"; state <- state
                        [w,r,a] <- mapM enclosed [real,real,real]
                        return $ Arc state w r a,
                     do symbol "Bunch"; w <- enclosed widgString
                        list int >>= return . Bunch w,
                     do symbol "Dot"; c <- token hexcolor; pair <- pair
                        return $ Dot c pair,
                     symbol "Fast" >> enclosed widgString >>= return . Fast,
                     do symbol "Gif"; p <- enclosed nat; b <- enclosed bool
                        file <- token quoted; hull <- enclosed widgString
                        return $ Gif p b file hull,
                     symbol "New" >> return New,
                     do symbol "Oval"; state <- state; rx <- enclosed real
                        ry <- enclosed real; return $ Oval state rx ry,
                     do symbol "Path";  w <- enclosed real; state <- state
                        m <- enclosed pnat; ps <- list pair
                        return $ Path w state m ps,
                     do symbol "Poly"; state <- state; n <- enclosed nat
                        rs <- list $ enclosed real; b <- enclosed real
                        return $ Poly state n rs b,
                     do symbol "Rect"; state <- state; b <- enclosed real
                        h <- enclosed real; return $ Rect state b h,
                     symbol "Repeat" >> enclosed widgString >>= return . Repeat,
                     symbol "Skip" >> return Skip,
                     do symbol "Slice"; state <- state; t <- arcType
                        r <- enclosed real; b <- enclosed real
                        return $ Slice state t r b,
                     do symbol "Text_"; state <- state; height <- enclosed nat
                        strs <- list $ token quoted
                        list int >>= return . Text_ state height strs,
                     do symbol "Tree"; state <- state
                        gr <- enclosed graphString; return $ Tree state gr,
                     do symbol "Tria"; state <- state; r <- enclosed real
                        return $ Tria state r,
                     do symbol "Turtle"; state <- state; sc <- enclosed real
                        acts <- list turtAct; return $ Turtle state sc acts]
   where arcType = concat [symbol "chord" >> return Chord,
                           symbol "arc" >> return Perimeter,
                           symbol "pieslice" >> return Pie]
         pair  = do tchar '('; x <- token real; tchar ','; y <- token real
                    tchar ')'; return (x,y)
         quad  = do tchar '('; x1 <- token real; tchar ','; y1 <- token real
                    tchar ','; x2 <- token real; tchar ','; y2 <- token real
                    tchar ')'; return (x1,y1,x2,y2)
         state = do tchar '('; pair <- pair; tchar ','; a <- token real
                    tchar ','; c <- token hexcolor; tchar ','; i <- enclosed int
                    tchar ')'; return (pair,a,c,i)
         node  = do tchar '('; b <- token quoted; tchar ','; pair <- pair
                    tchar ','; lg <- enclosed int; tchar ')'; return (b,pair,lg)
         turtAct = concat [symbol "Close" >> return Close,
                           symbol "Draw"  >> return Draw,
                           symbol "Jump"  >> enclosed real >>= return . Jump,
                           symbol "JumpA" >> enclosed real >>= return . JumpA,
                           symbol "Move"  >> enclosed real >>= return . Move,
                           symbol "MoveA" >> enclosed real >>= return . MoveA,
                           symbol "Open"  >> enclosed nat >>= return . Open,
                           symbol "OpenC" >> token hexcolor >>= return . OpenC,
                           symbol "OpenS" >> enclosed real >>= return . OpenS,
                           symbol "OpenW" >> enclosed real >>= return . OpenW,
                           symbol "Turn"  >> enclosed real >>= return . Turn,
                           do symbol "Widg"; b <- enclosed bool
                              enclosed widgString >>= return . Widg b]
                                       
-- used by graphString,loadWidget
