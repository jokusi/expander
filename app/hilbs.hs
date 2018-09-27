{-# LANGUAGE BangPatterns #-}
module Main where

import Prelude ()
import qualified Base.Haskell as Haskell
import Base.Gui
import Eterm (lift)
import qualified Graphics.UI.Gtk as Gtk (AttachOptions(Fill))

main :: IO ()
main = do
    initGUI -- Gtk
    paint <- painter -- paint <- painter tk
    buildPaint paint -- paint.buildPaint
    mainGUI -- Gtk

-- the PAINTER template

-- struct Painter = buildPaint :: Action
data Painter = Painter { buildPaint :: Action }

-- painter :: TkEnv -> Template Painter
painter :: Template Painter
painter = do -- template
    {- 
        (canv,font,splitBut,win,ent) 
            := (undefined,undefined,undefined,undefined,undefined)
        (widthX,widthY,scale,picture,split) := (0,0,5,[hilbert 1],True)
    -}
    canv <- canvas
    scrollCanv <- scrolledWindowNew Nothing Nothing
    -- font <- newIORef undefined
    splitMen <- menuItemNewWithLabel "No split"
    win <- windowNew
    -- scale <- newIORef 5
    numSlider <- hScaleNewWithRange 1 10 1
    scaleSlider <- hScaleNewWithRange 1 10 1
    pictureRef <- newIORef [hilbert 1]
    splitRef <- newIORef True
    fileRef <- newIORef Nothing
    -- saving is now handled different
    fileChooser <- fileChooserDialogNew (Just "Painter") (Just win)
        FileChooserActionSave
        [("_Cancel", ResponseCancel), ("_Save", ResponseAccept)]

    -- in let
    let buildPaint' = do -- buildPaint = action
            -- win0 <- tk.window [Title "Painter"] / win := win0
            -- tk.window [Title "Painter"]
            icon <- iconPixbuf
            win `gtkSet` [ windowTitle := "Painter"
                      -- win.setSize (1000,600)
                      , windowDefaultWidth := 1000
                      , windowDefaultHeight := 600
                      -- win.setPosition (60,60)
                      , windowWindowPosition := WinPosCenter
                      -- new
                      , windowIcon := Just icon
                      ]
            -- quit GUI if window is closed
            win `on` deleteEvent $ lift mainQuit >> return False
            --lab <- win.label [ Font "Helvetica 12 italic", 
            --            Background $ RGB 200 200 255, Justify LeftAlign]
            -- I skip the label, since it's not really used.
            --lab <- statusbarNew
            --widgetModifyBg lab StateNormal (Color 200 200 255)
            --statusbarPush lab 0 "Test"
            
            -- canv0 <- win.canvas [Background white]
            -- canv := canv0
            -- Not really the canvas initialisation. I need a size for a canvas.
            -- But some workaround to work with the canvas as usual.
            containerAdd scrollCanv (getDrawingArea canv)
            changeCanvasBackground white
            
            -- ent0 <- win.entry [Font "Courier 14"]
            -- ent := ent0
            -- ent.setValue "save curve to: "
            ent <- statusbarNew
            
            -- The buttons are now handled as menu:
            -- splitBut0 <- win.button [Text "no split", font12
            -- , Command setSplit]
            -- splitBut := splitBut0
            -- splitMen <- menuItemNewWithLabel "No split"
            
            --  closeBut <- win.button [Text "quit", font12, Command tk.quit]
            closeMen <- imageMenuItemNewFromStock stockClose
            closeMen `on` menuItemActivated $ mainQuit
            
            -- saveBut <- win.button [Text "save", font12, Command saveGraph]
            saveMen <- imageMenuItemNewFromStock stockSave
            saveAsMen <- imageMenuItemNewFromStock stockSaveAs
            
            -- Some more menu stuff:
            seperator <- separatorMenuItemNew 
            menuFileContent <- menuNew
            menuShellAppend menuFileContent splitMen
            menuShellAppend menuFileContent saveMen
            menuShellAppend menuFileContent saveAsMen
            menuShellAppend menuFileContent seperator
            menuShellAppend menuFileContent closeMen
            
            menuFile <- menuItemNewWithLabel "File"
            menuFile `gtkSet` [ menuItemSubmenu := menuFileContent ]
            
            menuBar <- menuBarNew
            menuShellAppend menuBar menuFile
            
            
            -- numLab <- win.label [Text "depth", font10, Anchor C]
            numLab <- labelNew $ Just "depth"
            numLab `gtkSet` [ labelJustify := JustifyLeft ]
            -- numSlider <- win.slider [Orientation Hor, From 1, To 10,
            --                          CmdInt moveNum]
            -- numSlider.setValue 1
            -- numSlider.bind [ButtonRelease 1 $ const scaleAndDraw]
            numSlider `gtkSet` [ scaleDigits := 0
                            , rangeValue := 1
                            , scaleValuePos := PosRight
                            ]
            
            -- scaleLab <- win.label [Text "size", font10, Anchor C]
            scaleLab <- labelNew $ Just "size"
            scaleLab `gtkSet` [ labelJustify := JustifyLeft ]
            -- scaleSlider <- win.slider [Orientation Hor, From 1, To 20, 
            --                           CmdInt moveScale]
            -- scaleSlider.setValue 5
            -- scaleSlider.bind [ButtonRelease 1 $ const scaleAndDraw]
            scaleSlider `gtkSet` [ scaleDigits := 0
                              , rangeValue := 5
                              , scaleValuePos := PosRight
                              ]
            
            -- vsb <- win.scrollBar [Width 12]
            -- vsb.attach canv Ver
            -- hsb <- win.scrollBar [Width 12]
            -- hsb.attach canv Hor
            -- scrollCanv <- scrolledWindowNew Nothing Nothing
            
            -- pack $ col ...
            -- Layout stuff:
            layoutSliders <- tableNew 2 4 False
            tableAttach layoutSliders numLab 0 1 0 1
                [Gtk.Fill] [Expand, Gtk.Fill] 5 0
            tableAttachDefaults layoutSliders numSlider 1 5 0 1
            tableAttach layoutSliders scaleLab 0 1 1 2
                [Gtk.Fill] [Expand, Gtk.Fill] 5 0
            tableAttachDefaults layoutSliders scaleSlider 1 5 1 2
                        
            layoutMain <- vBoxNew False 0
            boxPackStart layoutMain menuBar PackNatural 0
            --boxPackStart layoutMain lab PackNatural 0
            boxPackStart layoutMain scrollCanv PackGrow 0
            boxPackStart layoutMain layoutSliders PackNatural 0
            boxPackStart layoutMain ent PackNatural 0
            
            win `gtkSet` [ containerChild := layoutMain ]
            
            
            


            -- Moved signal linking behind functions.
            splitMen `on` menuItemActivated $ setSplit
            saveAsMen `on` menuItemActivated $ saveAsGraph
            saveMen `on` menuItemActivated $ saveGraph
            -- moveNum and scaleAndDrawe are joined together now.
            numSlider `on` valueChanged $ moveNum >> scaleAndDraw
            scaleSlider `on` valueChanged $ scaleAndDraw
            
            scaleAndDraw
            widgetShowAll win -- Gtk
        
                
        changeCanvasBackground c@(RGB r g b) = do
            let f n = fromIntegral $ n * 256
                (r', g' , b') = (f r, f g, f b)
            canv `gtkSet` [ canvasBackground := c ]
            widgetModifyBg scrollCanv StateNormal $ gtkColor r' g' b'

        
        drawWidget (Path c 0 ps) = do
            split <- readIORef splitRef
            mapM_ (\ps -> line canv (map round2 ps)
                    $ lineOpt{ lineFill = c, lineAntialias = False })
                  $ if split then splitPath ps else [ps]
            return ()            
        drawWidget w | isWidg w = drawWidget $ mkWidg w
        drawWidget _            = return ()
        
        -- moveNum n = action picture := [hilbert n]
        moveNum = do
            n <- numSlider `gtkGet` rangeValue
            writeIORef pictureRef [hilbert n]
        
        -- saveGraph = ...
        -- Save function has been reworked.
        saveGraph :: Action
        saveGraph = do
            file <- readIORef fileRef
            maybe
                saveAsGraph
                (Haskell.void . canvasSave canv)
                file
        
        saveAsGraph :: Action
        saveAsGraph = do
            response <- dialogRun $ castToDialog fileChooser
            if response == ResponseAccept
            then do file <- fileChooserGetFilename fileChooser
                    writeIORef fileRef file
                    saveGraph
                    widgetHide fileChooser
                    return ()
            else widgetHide fileChooser

        -- scaleAndDraw = ...
        scaleAndDraw = do
            --canv.clear
            picture <- readIORef pictureRef
            scale    <- scaleSlider `gtkGet` rangeValue
            let (pict1,(x1,y1,x2,y2)) = f picture 0
                f (w:pict) i = (w':pict',minmax4 (widgFrame w') bds)
                            where w' = scaleWidg scale w
                                  (pict',bds) = f pict (i+1)
                f _ _        = ([],(0,0,0,0))
                pict2 = map (transXY (5-x1) $ 5-y1) pict1
                widthX = max 100 (round $ x2-x1+10)
                widthY = max 100 (round $ y2-y1+10)
            writeIORef pictureRef $ map (scaleWidg $ 1/scale) pict2
            canv `gtkSet` [ canvasSize := (widthX, widthY) ]
            mapM_ drawWidget pict2
        
        setSplit = do
            split <- not <$> readIORef splitRef
            writeIORef splitRef split
            splitMen `gtkSet` [ menuItemLabel := 
                            if split then "No split" else "Split" ]
            scaleAndDraw

    return Painter { buildPaint = buildPaint'}

round2 :: (Double, Double) -> (Int, Int)
round2 = round Haskell.*** round

minmax4 :: (Num a, Num b, Num c, Num d, Ord a, Ord b, Ord c, Ord d) =>
    (a, b, c, d) -> (a, b, c, d) -> (a, b, c, d)
minmax4 p (0,0,0,0) = p
minmax4 (0,0,0,0) p = p
minmax4 (x1,y1,x2,y2) (x1',y1',x2',y2') = (min x1 x1',min y1 y1',
                                            max x2 x2',max y2 y2')

-- | Computes minimal and maximal coordinates for a list of points.
minmax :: (Num a, Num b, Ord a, Ord b) => [(a, b)] -> (a, b, a, b)
minmax s@((x,y):_) = foldl minmax1 (x,y,x,y) s
      where minmax1 (x1,y1,x2,y2) (x,y) =
                let !x1' = min x x1
                    !y1' = min y y1
                    !x2' = max x x2
                    !y2' = max y y2
                in (x1', y1', x2', y2')
minmax _             = (0,0,0,0)

map2 :: (a -> b) -> [(a, a)] -> [(b, b)]
map2 f = map (f Haskell.*** f)

data Widget_ = Path Color Int [Point] | Path0 State Int [Point] 
               deriving (Show,Eq)

type State = (Point,Double,Color,Int)

type Point = (Double,Double)

p0 :: Point
p0 = (0,0)

path0 :: Color -> Int -> [Point] -> Widget_
path0 c = Path0 (p0,0,c,0) 

splitPath :: [a] -> [[a]]
splitPath ps = if length ps < 101 then [ps]
                                  else take 100 ps:splitPath (drop 99 ps)

-- hilbert n and hilbertC n compute the vertices of a (colored) Hilbert curve 
-- with depth n.
hilbert :: (Eq a, Num a) => a -> Widget_
hilbert n = path0 black 0 $ gen n 2 (-2) 0 0 p0
  where gen 0 _ _  _ _  p = [p]
        gen n c c' d d' p = pict1++pict2++pict3++pict4
            where f = gen (n-1)
                  pict1 = f d d' c c' p
                  p1 = last pict1
                  pict2 = f c c' d d' (fst p1+c,snd p1+d)
                  p2 = last pict2
                  pict3 = f c c' d d' (fst p2+d,snd p2+c)
                  p3 = last pict3
                  pict4 = f (-d) (-d') (-c) (-c') (fst p3+c',snd p3+d')

isWidg :: Widget_ -> Bool
isWidg Path0{}          = True    
isWidg _                = False

getState :: Widget_ -> (Point, Double, Color, Int)
getState (Path c _ ps)       = (head ps,0,c,0)
getState (Path0 st _ _)      = st
--getState _                   = state0

updState :: (State -> State) -> Widget_ -> Widget_
updState f w@(Path _ n ps)     = Path c n ps 
                                 where (_, _, c, _) = f (getState w)
updState f (Path0 st n ps)     = Path0 (f st) n ps
--updState _ w = w

moveWidg :: Point -> Double -> Widget_ -> Widget_
moveWidg p a = updState $ \(_,_,c,i) -> (p,a,c,i)

-- mkWidg (w (p,a,c) ...) rotates widget w around p by a.
-- mkWidg is used by mkPict, points, drawWidget and hullPoints (see below).
mkWidg :: Widget_ -> Widget_
mkWidg (Path0 ((x,y),_,c,_) n ps) = Path c n $ map f ps
                                    where f (i,j) = (x+i,y+j)
mkWidg w = w

points :: Widget_ -> [Hull]
points (Path c _ ps) = [(ps,[],c)]
points w | isWidg w  = points $ mkWidg w
points w             = [([p],[],c)] where (p, _, c, _) = getState w

type Hull = ([Point],[Point],Color)

spoints :: Hull -> [Point]
spoints (ps,qs,_) = if null qs then ps else qs

-- scaleWidg sc w scales w by multiplying its vertices/radia with scale. 
-- Dots and Gifs are not scaled. scaleWidg is used by mkPict, getEnclosed,
-- scaleAndDraw, scalePict (see above), widgFrame and getWidget (see below).
scaleWidg :: Double -> Widget_ -> Widget_
scaleWidg sc (Path0 st n ps)      = Path0 st n $ map2 (*sc) ps
scaleWidg _ w                            = w

-- widgFrame w returns the leftmost-uppermost and rightmost-lowermost
-- coordinates of w. widgFrame is used by scaleAndDraw (see above), rectFrame 
-- and shelves (see below).
widgFrame :: Widget_ -> (Double, Double, Double, Double)
widgFrame (Path _ _ []) = (0,0,0,0)
widgFrame w = minmax (concatMap spoints (points w))

-- transX/transY offset w moves w offset units to the right/bottom.
transX :: Double -> Widget_ -> Widget_
transX 0 w      = w
transX offset w = moveWidg (x+offset,y) a w where ((x,y),a,_,_) = getState w

transY :: Double -> Widget_ -> Widget_
transY 0 w      = w
transY offset w = moveWidg (x,y+offset) a w where ((x,y),a,_,_) = getState w

transXY :: Double -> Double -> Widget_ -> Widget_
transXY 0 offset w        = transY offset w
transXY offset 0 w        = transX offset w
transXY offsetX offsetY w = moveWidg (x+offsetX,y+offsetY) a w
                            where ((x,y),a,_,_) = getState w
