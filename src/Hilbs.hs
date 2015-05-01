module Hilbs where
 import Tk
 import System

 get (Just a) = a
 
 isPic :: String -> Bool
 isPic file = lg > 3 && drop (lg-4) file `elem` words ".eps .gif .jpg .png .svg" 
 	      where lg = length file

 main tk = do paint <- painter tk; paint.buildPaint

-- the PAINTER template

 struct Painter = buildPaint :: Action
		  
 painter :: TkEnv -> Template Painter
 painter tk =

  template (canv,font,splitBut,win,ent) 
  		    := (undefined,undefined,undefined,undefined,undefined)
   	   (widthX,widthY,scale,picture,split) := (0,0,5,[hilbert 1],True)

  in let

	buildPaint = action
          win0 <- tk.window [Title "Painter"]
	  win := win0
 	  win.setPosition (60,60)
  	  win.setSize (1000,600)
  	  lab <- win.label [Font "Helvetica 12 italic", 
	  		    Background $ RGB 200 200 255, Justify LeftAlign]
	  canv0 <- win.canvas [Background white]
	  canv := canv0
 	  ent0 <- win.entry [Font "Courier 14"]
	  ent := ent0
	  ent.setValue "save curve to: "
          splitBut0 <- win.button [Text "no split", font12, Command setSplit]
	  splitBut := splitBut0
 	  closeBut <- win.button [Text "quit", font12, Command tk.quit]
          saveBut <- win.button [Text "save", font12, Command saveGraph]
          numLab <- win.label [Text "depth", font10, Anchor C]
 	  numSlider <- win.slider [Orientation Hor, From 1, To 10,
				   CmdInt moveNum]
	  numSlider.setValue 1
	  numSlider.bind [ButtonRelease 1 $ const scaleAndDraw]
	  scaleLab <- win.label [Text "size", font10, Anchor C]
	  scaleSlider <- win.slider [Orientation Hor, From 1, To 20, 
	                             CmdInt moveScale]
	  scaleSlider.setValue 5
	  scaleSlider.bind [ButtonRelease 1 $ const scaleAndDraw]
 	  vsb <- win.scrollBar [Width 12]
	  vsb.attach canv Ver
	  hsb <- win.scrollBar [Width 12]
	  hsb.attach canv Hor
          pack $ col [fillX lab,
	              canv <<< fillY vsb,
                      fillX hsb,
		      fillX ent,
		      fillX $ row [scaleSlider ^^^ scaleLab,
		     	           numSlider ^^^ numLab,
				   splitBut,closeBut,saveBut]]
          scaleAndDraw

        drawWidget (Path c 0 ps) = action
	  mapM (flip canv.line [Fill c]. map round2) $
	       if split then splitPath ps else [ps]
          done

-- Here is the crucial call of Tk.hs's line function. 
-- If the length of a path exceeds 100, then the call leads to a crash! 

	drawWidget w | isWidg w = drawWidget $ mkWidg w
        drawWidget _ 		= action done

        moveScale n = action scale := fromInt n

        moveNum n = action picture := [hilbert n]
	
	saveGraph = action
	  file <- ent.getValue
  	  path <- tk.getEnv "HOME"
	  let home = get path
	      dir = home ++ "/Exatest"
	  --createDirectory dir
	  let file0 = dir ++ '/':drop 15 file 
	      file1 = file0 ++ ".eps"
	      file2 = file0 ++ ".png"
	  canv.save file1
	  ent.setValue "save curve to: "
	  rawSystem "convert" [file1,file2]
	  files <- getDirectoryContents dir
	  ent.setValue $ unwords $ filter isPic files
	  done

	scaleAndDraw = action
	  canv.clear
	  let (pict1,(x1,y1,x2,y2)) = f picture 0
              f (w:pict) i = (w':pict',minmax4 (widgFrame w') bds)
	                     where w' = scaleWidg scale w
				   (pict',bds) = f pict (i+1)
              f _ _        = ([],(0,0,0,0))
              pict2 = map (transXY (5-x1) $ 5-y1) pict1
	  picture := map (scaleWidg $ 1/scale) pict2
          widthX := max 100 (round $ x2-x1+10)
	  widthY := max 100 (round $ y2-y1+10)
          canv.set [ScrollRegion (0,0) (widthX,widthY)]
	  mapM_ drawWidget pict2

	setSplit = action 
	  split := not split
	  splitBut.set [Text $ if split then "no split" else "split"]
	  scaleAndDraw

     in struct ..Painter

 round2 (x,y) = (round x,round y)

 minmax4 p (0,0,0,0) = p
 minmax4 (0,0,0,0) p = p
 minmax4 (x1,y1,x2,y2) (x1',y1',x2',y2') = (min x1 x1',min y1 y1',
 					    max x2 x2',max y2 y2')

-- minmax ps computes minimal and maximal coordinates for the point list ps.

 minmax s@((x,y):_) = foldl minmax1 (x,y,x,y) s
       where minmax1 (x1,y1,x2,y2) (x,y) = (min x x1,min y y1,max x x2,max y y2)
 minmax _ 	    = (0,0,0,0)

 map2 f = map $ \(x,y) -> (f x,f y)

 data Widget_ = Path Color Int [Point] | Path0 State Int [Point] 
                deriving (Show,Eq)

 type State = (Point,Float,Color,Int)

 type Point = (Float,Float)

 p0 :: Point
 p0 = (0,0)

 state0 :: State
 state0 = (p0,0,black,0)
 
 path0 c = Path0 (p0,0,c,0) 

 splitPath ps = if length ps < 101 then [ps]
		                   else take 100 ps:splitPath (drop 99 ps)

-- hilbert n and hilbertC n compute the vertices of a (colored) Hilbert curve 
-- with depth n.

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

 isWidg (Path0 _ _ _)          = True    
 isWidg _                      = False

 getState (Path c _ ps)       = (head ps,0,c,0)
 getState (Path0 st _ _)      = st
 getState _                   = state0
  
 updState f w@(Path _ n ps)     = Path c n ps 
				  where (_,_,c,i) = f (getState w)
 updState f (Path0 st n ps)     = Path0 (f st) n ps
 updState _ w = w

 moveWidg p a = updState $ \(_,_,c,i) -> (p,a,c,i)

-- mkWidg (w (p,a,c) ...) rotates widget w around p by a.
-- mkWidg is used by mkPict, points, drawWidget and hullPoints (see below).

 mkWidg (Path0 (p@(x,y),_,c,i) n ps) = Path c n $ map f ps where f (i,j) = (x+i,y+j)
 mkWidg w = w

 points :: Widget_ -> [Hull]
 points (Path c _ ps) = [(ps,[],c)]
 points w | isWidg w  = points $ mkWidg w
 points w             = [([p],[],c)] where (p,_,c,i) = getState w

 type Hull = ([Point],[Point],Color)

 spoints :: Hull -> [Point]
 spoints (ps,qs,_) = if null qs then ps else qs

 font10 = Font "Helvetica 10 italic"
 font12 = Font "Helvetica 12"

-- scaleWidg sc w scales w by multiplying its vertices/radia with scale. 
-- Dots and Gifs are not scaled. scaleWidg is used by mkPict, getEnclosed,
-- scaleAndDraw, scalePict (see above), widgFrame and getWidget (see below).

 scaleWidg sc (Path0 st n ps)      = Path0 st n $ map2 (*sc) ps
 scaleWidg _ w 			   = w

-- widgFrame w returns the leftmost-uppermost and rightmost-lowermost
-- coordinates of w. widgFrame is used by scaleAndDraw (see above), rectFrame 
-- and shelves (see below).

 widgFrame (Path _ _ []) = (0,0,0,0)
 widgFrame w = minmax (concatMap spoints (points w))

-- transX/transY offset w moves w offset units to the right/bottom.

 transX 0 w      = w
 transX offset w = moveWidg (x+offset,y) a w where ((x,y),a,_,_) = getState w

 transY 0 w      = w
 transY offset w = moveWidg (x,y+offset) a w where ((x,y),a,_,_) = getState w

 transXY 0 offset w        = transY offset w
 transXY offset 0 w        = transX offset w
 transXY offsetX offsetY w = moveWidg (x+offsetX,y+offsetY) a w
                             where ((x,y),a,_,_) = getState w
