module Epaint where
 import Eterm
 
--------------------------------- Copyright (c) peter.padawitz@udo.edu, May 2014

-- Epaint contains:

-- compilers of trees into pictures,
-- the painter,
-- functions generating, modifying or combining pictures.

 infixr 5 <:>, <++>
 infixl 6 &

 font9   = Font "Helvetica 9"
 font10  = Font "Helvetica 10 italic"
 font12  = Font "Helvetica 12"
 font12b = Font "Helvetica 12 bold"
 
 groove = Relief Groove
  
 mkSecs t1 t2 = (t2-t1)`div`1001500
 
 pix dir files = [dir++fileSeparator:file | file <- files, isPic file]
     where isPic file = lg > 4 && 
		        drop (lg-4) file `elem` words ".eps .gif .jpg .png .svg"
	                where lg = length file

 (&) :: String -> String -> String
 x & val = x ++ "=\"" ++ val ++ "\""

 html :: Bool -> String -> [String] -> String
 html frame dir files = 
    "<html>\n<head>\n<title>" ++ dir ++ 
    "</title>\n<script type"&"text/javascript" ++ 
    ">\nvar images = new Array(" ++ '\"':first ++ '\"':concatMap f rest ++ 
    ")\n</script>\n<script type"&"text/javascript" ++ " src"&"Painter.js" ++ 
    ">\n</script>\n</head>\n<body style"&"background-color: rgb(221,221,255)" ++
    ">\n" ++ "<input type"&"button" ++ " value"&"<" ++ "onclick"&"back()" ++ 
    "> " ++ show n ++ " picture" ++ (if n == 1 then "" else "s") ++
    " <input type"&"button" ++ " value"&">" ++ " onclick"&"forth()" ++ 
    ">\n<input type"&"button" ++ " value"&"go" ++ " onclick"&"stopGo(this)" ++ 
    ">\n<br>\n<input id"&"fileSlider" ++ " type"&"range" ++ " min"&"0" ++ 
    " max"&show (n-1) ++ " value"&"0" ++ " onchange"&"showFile(this.value)" ++ 
    ">\n<span id"&"file" ++ '>':first ++ "</span>\n<br>\n<input type"&"range" ++
    " min"&"0" ++ " max"&"2000" ++ " value"&"1000" ++ 
    " onchange"&"showTime(this.value)" ++ ">\n<span id"&"time" ++ 
    ">1000</span> millisecs\n<br><br><br>\n<" ++ open ++ " id"&"img" ++ 
    " src"&first ++ " width"&width ++ " height"&height ++ close ++ 
    ">\n</body>\n</html>"
  where n = length files
        first:rest = files
        f file = ",\"" ++ file ++ "\""
        (open,width,height,close) = 
	 if frame then ("iframe","1800","900"," frameborder"&"0"++">\n</iframe")
		  else ("img","600","600",">\n</img")
  	
-- the SOLVER record

 struct Solver =
   addSpec 		      :: Bool -> Action -> String -> Action
   backWin,bigWin,checkInSolver,drawCurr,forwProof,showPicts,skip,stopRun
   			      :: Action
   buildSolve                 :: Pos -> Action -> Action
   enterPT                    :: Int -> [Step] -> Action
   enterText         	      :: String -> Action
   enterFormulas     	      :: [TermS] -> Action
   enterTree         	      :: Bool -> TermS -> Action
   getEntry,getSolver,getText :: Request String
   getFont                    :: Request TkFont
   getSignatureR     	      :: Request Sig
   getTree           	      :: Request (Maybe TermS)
   isSolPos          	      :: Int -> Request Bool
   labBlue,labRed,labGreen    :: String -> Action
   narrow	     	      :: Action -> Action
   setCurrInSolve     	      :: Int -> Action -> Action
   setForw,setQuit	      :: [ButtonOpt] -> Action
   setNewTrees        	      :: [TermS] -> String -> Action
   setSubst           	      :: (String -> TermS,[String]) -> Action
   simplify 	              :: Bool -> Action -> Action
   
 data Step = ApplySubst | ApplySubstTo String TermS | ApplyTransitivity | 
 	     BuildKripke Int | CollapseStep | ComposePointers | CopySubtrees | 
 	     CreateIndHyp | CreateInvariant Bool | DecomposeAtom | 
 	     DeriveMode Bool Bool | EvaluateTrees | ExpandTree Bool Int |
 	     FlattenImpl | Generalize [TermS] | Induction Bool Int |
 	     Mark [[Int]] | Match Int | Minimize | Narrow Int Bool | 
 	     NegateAxioms [String] [String] | RandomLabels | RandomTree | 
 	     ReleaseNode | ReleaseSubtree | ReleaseTree | RemoveCopies | 
 	     RemoveEdges Bool | RemoveNode | RemoveOthers | RemovePath | 
 	     RemoveSubtrees | RenameVar String | ReplaceNodes String | 
 	     ReplaceOther | ReplaceSubtrees [[Int]] [TermS] | 
 	     ReplaceText String | ReplaceVar String TermS [Int] | 
 	     ReverseSubtrees | SafeEqs | SetAdmitted Bool [String] | 
 	     SetCurr String Int | SetDeriveMode | SetMatch | ShiftPattern | 
 	     ShiftQuants | ShiftSubs [[Int]] | ShowEqsOrGraph Bool Int | 
 	     ShowRelation Int | Simplify Bool Int Bool | SplitTree | 
 	     StretchConclusion | StretchPremise | SubsumeSubtrees | 
 	     Theorem Bool TermS | UnifySubtrees | POINTER Step
	     deriving Show
 
-- the RUNNER template (used by solver; see Ecom)

 struct Runner = startRun :: Int -> Action; stopRun0 :: Action
 
 runner :: TkEnv -> Action -> Template Runner
 runner tk act =
     template run := undefined
     in struct startRun millisecs = action run0 <- tk.periodic millisecs act
	                                   run := run0; run.start
	       stopRun0 = action run.stop
  	
-- the SWITCHER template (used by solver; see Ecom)

 struct Switcher = startSwitch :: Action; stopSwitch :: Action
 
 switcher :: TkEnv -> Action -> Action -> Template Switcher
 switcher tk actUp actDown =
     template (run,up) := (undefined,True)
     in let startSwitch = action run0 <- tk.periodic 1000 loop
	                         run := run0; run.start
            loop = action if up then actUp else actDown; up := not up  
	    stopSwitch = action run.stop
        in struct ..Switcher
   	
-- the OSCILLATOR template (used by painter and by solver; see Ecom)

 struct Oscillator = startOsci :: Action; stopOsci :: Action

 oscillator :: TkEnv -> (Int -> Action) -> (Int -> Action) -> Int -> Int -> Int 
               -> Template Oscillator
 oscillator tk actUp actDown lwb width upb =
     template (run,val,up) := (undefined,lwb-1,True)
     in let startOsci = action run0 <- tk.periodic 30 loop
	                       run := run0; run.start
            loop = action if up then actUp val; val := val+width
			        else actDown val; val := val-width
		          if val < lwb || val > upb then up := not up
  	    stopOsci = action run.stop
        in struct ..Oscillator
	       
-- the SCANNER template (used by painter)

 struct Scanner = startScan0 :: Int -> Picture -> Action
		  startScan  :: Int -> Action
		  addScan    :: Picture -> Action
		  stopScan0  :: Action
		  stopScan   :: Action
                  isRunning  :: Request Bool
 		    
 scanner :: TkEnv -> (Widget_ -> Action) -> Template Scanner
 scanner tk act =
     template (as,run,running) := ([],undefined,False)
     in let startScan0 delay bs = action as := bs; startScan delay
            startScan delay = action if running then run.stop
                                     run0 <- tk.periodic delay loop
	    		             run := run0; run.start; running := True
            loop = action case as of w:s -> if noRepeat w then as := s
			                    act w
					    if isFast w then loop
                                     _ -> stopScan
	    addScan bs = action as := bs++as
            stopScan0 = action stopScan; as := []
            stopScan = action if running then run.stop; running := False
            isRunning = request return running
	in struct ..Scanner
	
-- the WIDGSTORE template (not used)

 struct WidgStore = saveWidg :: String -> Widget_ -> Action
 		    loadWidg :: String -> Request Widget_
 		   
 widgStore :: TkEnv -> Template WidgStore
 widgStore tk = 
     template store := const Skip
     in struct saveWidg file w = action store := upd store file w
 	       loadWidg file = request return $ store file

-- PAINTER messages

 combi n = "The current combination is " ++ show n ++ "."

 noPictIn file = file ++ " does not contain a picture term."

 subtreesMsg solver = "The selected subtrees of " ++ solver ++ 
	              " have the following pictorial representations:"
		      
 treesMsg k 1 solver b =
 	"A single tree has a pictorial representation. It is " ++
 	("solved and " `onlyif` b) ++ "located at position " ++ show k ++ " of "
	++ solver ++ "."
 treesMsg k n solver b =
 	show n ++ " trees have pictorial representations. The one below is " ++
 	("solved and " `onlyif` b) ++ "located at position " ++ show k ++ " of "
	++ solver ++ "."

 saved "trees" file = "The trees have been saved to " ++ file ++ "."
 saved object file  = "The " ++ object ++ " has been saved to " ++ file ++ "."

 savedCode object file = "The Haskell code of the " ++ object ++ 
			 " has been saved to " ++ file ++ "."

-- the PAINTER template

 struct Painter = 
   callPaint      :: [Picture] -> [Int] -> Bool -> Bool -> Int -> String 
   		               -> Action -> Action
   labSolver      :: String -> Action
   remote         :: Action -> Action
   setButtons     :: [ButtonOpt] -> [ButtonOpt] -> [ButtonOpt] -> Action
   setCurrInPaint :: Int -> Action
   setEval        :: String -> Pos -> Action
   setFast        :: Bool -> Action
   		  
 painter :: Int -> TkEnv -> String -> Solver -> String -> Solver 
 						       -> Template Painter
 painter pheight tk solveName solve solveName2 solve2 =

   template (canv,combiBut,fastBut,edgeBut,font,lab,modeEnt,narrowBut,
   	     pictSlider,saveEnt,colorScaleSlider,simplifyD,simplifyB,spaceEnt,
	     stopBut,win) := (undefined,undefined,undefined,undefined,undefined,
	     		      undefined,undefined,undefined,undefined,undefined,
			      undefined,undefined,undefined,undefined,undefined,
			      undefined)
   	    (canvSize,colorScale,cols,curr,drawMode,grade,noOfGraphs,spread) 
	      := ((0,0),(0,[]),0,0,0,0,0,(0,0))
            (delay,oldRscale,rscale,scale,picNo) := (1,1,1,1,-1)
	    (arrangeMode,picEval,bgcolor) := ("","",white)
	    (changedWidgets,oldGraph) := (nil2,nil2)
	    (fast,connect,onlySpace,open,subtrees,isNew) 
	      := (False,False,False,False,False,True)
	    (edges,permutation,pictures,rectIndices,scans,solverMsg,treeNumbers) 
	      := ([],[],[],[],[],[],[])
	    (oldRect,osci,penpos,rect,source,target,bunchpict) 
	      := (Nothing,Nothing,Nothing,Nothing,Nothing,Nothing,Nothing)

   in let

	adaptPos p = do 
	  (leftDivWidthX,_) <- canv.xview
	  (topDivWidthY,_) <- canv.yview
	  let (b,h) = fromInt2 canvSize
	  return $ add2 p $ round2 (leftDivWidthX*b,topDivWidthY*h)

	addOrRemove = action
	  file <- saveEnt.getValue
	  let graph@(pict,arcs) = (pictures!!curr,edges!!curr)
	  if null file then
	     if just rect
	        then oldRect := rect; oldRscale := rscale
		     setCurrGraph $ removeSub graph rectIndices
		     rect := Nothing; rectIndices := []; rscale := scale
		     scaleAndDraw "The selection has been removed."
	        else setCurrGraph nil2; mapM_ (.stopScan0) scans; canv.clear 
		     labGreen "The graph has been removed."
	  else (pict',arcs') <- loadGraph file
	       let f sc pict = concatGraphs spread grade arrangeMode
					   [graph,(scalePict (1/sc) pict,arcs')]
		   msg = file ++ if null pict' then " is not a graph."
				               else " has been added."
	       case rect of 
	          Just r 
                    -> let (x,y,_,_) = widgFrame r
			   graph@(pict,_) = f rscale $ map (transXY (x,y)) pict'
		       setCurrGraph graph
		       rectIndices := getRectIndices pict rscale r
	          _ -> setCurrGraph $ f scale pict'
	       scaleAndDraw msg

        arrangeButton graph@(pict,arcs) = action 
	  mode <- modeEnt.getValue
	  case mode of
	  "perm" -> let old = permutation
	  	    permutation := nextPerm old
		    setCurrGraph $ if (isTree ||| isCenter) arrangeMode 
		                   then (permuteTree old permutation,arcs)
		                   else permutePositions graph old permutation
		    scaleAndDraw "The widgets have been permuted."
	  _ -> case mode of x:y:r | x `elem` "amrt" 
		              -> arrangeMode := [x,y]
		                 let colsNo = parse pnat r; angle = parse real r
		                 cols := if just colsNo then get colsNo 
				                        else square pict
		                 grade := if just angle then get angle else 0
		            _ -> arrangeMode := mode
	       d <- spaceEnt.getValue
	       let dist = parse real d; x = head arrangeMode
	       if notnull arrangeMode
	          then if just dist then spread := apply2 (*(get dist)) (10,10)
	                            else if x == 'm' then spread := (0,0)
                       if x `elem` "acmort" then arrangeGraph False act graph
	  where act gr = action setCurrGraph gr
	  		        scaleAndDraw "The widgets have been arranged."
	        permuteTree is ks = fold2 exchgWidgets pict ss ts
 			            where (ss,ts) = unzip $ permDiff is ks
                permutePositions graph is ks = fold2 exchgPositions graph ss ts
	                                  where (ss,ts) = unzip $ permDiff is ks

	arrangeGraph noChange act graph@(pict,arcs) = action
	  case arrangeMode of
	  "o" -> act (movePict p0 pict,arcs)
	  _ -> let graph1 = bunchesToArcs graph
	           graph2@(pict2,_) = scaleGraph scale graph1
		   f x = case parse nat x of 
		              Just i -> pict2!!i
			      _ -> if x == "<+>" then Skip else posWidg x
		   ws = wTreeToBunches arrangeMode spread grade
		               $ mapT (scaleWidg scale . f) $ graphToTree graph1
		   act' = act . scaleGraph (1/scale)
	       if isTree arrangeMode then if noChange then act graph
		                          else bunchpict := Just ws
					       act' $ onlyNodes ws
	       else bunchpict := Nothing
		    act' $ shelf graph2 cols spread 'M' True True arrangeMode

	arrangeOrCopy = action
	  case rect of
	  Just r@(Rect _ b _)
	    -> let (pict,arcs) = (pictures!!curr,edges!!curr)
		   ms = rectIndices
	           ns = indices_ pict `minus` ms
		   lg = length pict
		   translate = transXY (2*b,0)
		   vs = [pict!!n | n <- ms]
	           ws = scalePict (rscale/scale) vs
	           pict' = fold2 updList pict ms ws
		   arcs' = foldl f arcs ns ++       -- add arcs into rect
		   	   map (map g . (arcs!!)) ms-- add arcs in and from rect
		   f arcs n = updList arcs n $ is++map g (ms`meet`is)
		              where is = arcs!!n
	           g m = case search (== m) ms of Just i -> lg+i; _ -> m
	       oldRect := rect; oldRscale := rscale
	       setCurrGraph (pict'++map translate vs,arcs')
	       rect := Just $ translate r
	       rectIndices := [lg..lg+length ms-1]
	       scaleAndDraw "The selection has been copied."
	  _ -> let graph@(pict,arcs) = concatGraphs spread grade arrangeMode
	  					    $ zip pictures edges
	       (pictures,edges,noOfGraphs,curr) := ([pict],[arcs],1,0)
	       pictSlider.set [To 0]; arrangeButton graph

	buildPaint continue = action
          solver <- solve.getSolver
	  win0 <- tk.window [Title $ "Painter" ++ [last solver]]
	  win := win0
 	  win.setPosition (0,20)
--  	  win.setSize (1275,855)  		-- for 1280 x 1024, 60 Hz
-- 	  win.setSize (1020,730)  		-- for 1024 x 768, 60 Hz
--	  win.setSize (1400,820)  		-- for 1440 x 900
	  win.setSize (1400,pheight)  		
  	  canv0 <- win.canvas [Background white]
	  canv := canv0
 	  but <- win.button [Text "combis", font12, blueback, groove, 
	  		     Command combis]
	  combiBut := but
 	  but <- win.button [Text "connect/exchange", font12, blueback,
		             Command switchConnect]
	  edgeBut := but
	  but <- win.button [Text $ if fast then "slow" else "fast", font12, 
	  		     blueback, groove, Command switchFast]
          fastBut := but
  	  lab0 <- win.label [Font "Helvetica 12 italic", blueback,
			     Justify LeftAlign]
	  lab := lab0
 	  modeEnt0 <- win.entry [Font "Courier 14", Width 5]
	  modeEnt := modeEnt0
	  let f str act = win.button [Text str, font12, blueback, groove, 
	  			      Command $ remote $ act solve.showPicts]
	  buts <- zipWithM f (words "narrow/rewrite simplifyDF simplifyBF")
	  		 [solve.narrow,solve.simplify True,solve.simplify False]
 	  (narrowBut,simplifyD,simplifyB) := (buts!!0,buts!!1,buts!!2)
          buildPaint1 continue

        buildPaint1 continue = action
	  vsb <- win.scrollBar [Width 12]; vsb.attach canv Ver
	  hsb <- win.scrollBar [Width 12]; hsb.attach canv Hor
          closeBut <- win.button [Text ("back to "++ solveName), font12, groove,
			          Command close]
	  colorLab <- win.label [Text "color", font10, Anchor C]
 	  colorSlider <- win.slider [Orientation Hor, From $ -764, To 765,
	                             CmdInt moveColor]
          colorSlider.setValue 0
	  colorSlider.bind [ButtonPress 1 pressColorScale, 
			    ButtonRelease 1 releaseColor]
	  delayLab <- win.label [Text "delay", font10, Anchor C]
 	  delaySlider <- win.slider [Orientation Hor, From 1, To 300,
	                             CmdInt $ \n -> action delay := n]
	  delaySlider.setValue 1
	  delaySlider.bind [ButtonRelease 1 setDelay]
  	  modeBut <- win.button [Text "arrange/copy", font12, groove, 
  	  			 Command arrangeOrCopy]
	  modeLab <- win.label [Text "mode", font10, Anchor C]
          pictSlider0 <- win.slider [Orientation Hor, From 0, 
				     CmdInt $ \n -> action curr := n]
          pictSlider := pictSlider0
          pictSlider.bind [ButtonRelease 1 setCurr]
	  renewBut <- win.button [Text "renew", font12, groove,
	                          Command solve.showPicts]
   	  resetScaleBut <- win.button [Text "reset scale", font12, groove,
   	  			       Command resetScale]
   	  saveLab <- win.label [Text "add from/save to", font10, Anchor C]
  	  saveEnt0 <- win.entry [Font "Courier 14"]
	  saveEnt := saveEnt0
	  scaleLab <- win.label [Text "scale", font10, Anchor C]
	  scaleSlider <- win.slider [Orientation Hor, From $ -9, To 10,
				     CmdInt moveScale]
	  scaleSlider.setValue 0
	  scaleSlider.bind [ButtonPress 1 pressColorScale, 
			    ButtonRelease 1 releaseScale]
          colorScaleSlider := (colorSlider,scaleSlider)
	  solBut <- win.button [Text ("show in "++ solveName2), font12, groove,
			        Command showInSolver]
   	  spaceEnt0 <- win.entry [Font "Courier 14", Width 5]
	  spaceEnt := spaceEnt0
	  labGreen $ combi 0
	  spaceLab <- win.label [Text "space/combi", font10, Anchor C]
 	  but <- win.button [Text "stop", font12, groove,
 	  		     Command $ interrupt True]
	  stopBut := but
  	  undoBut <- win.button [Text "undo", font12, groove, Command undo]

	  pack $ col [fillX lab,
	              canv <<< fillY vsb,
		      fillX hsb,
		      fillX pictSlider0,
		      fillX $ row [scaleSlider ^^^ scaleLab,
		     	           colorSlider ^^^ colorLab,
		     	           delaySlider ^^^ delayLab,
				   fastBut ^^^ renewBut ^^^ resetScaleBut,
			           narrowBut ^^^ simplifyD ^^^ simplifyB,
				   col [modeLab <<< modeEnt <<< spaceLab
				                <<< spaceEnt <<< fillY modeBut,
				        saveLab <<< saveEnt],
				   edgeBut ^^^ combiBut,
				   closeBut ^^^ solBut,
				   undoBut ^^^ stopBut]]

	  let pb n = ButtonPress n $ pressButton n
	      mb n = Motion n $ moveButton n
	      rb n = ButtonRelease n $ releaseButton n
	  canv.bind [f n | f <- [pb,mb,rb], n <- [1,2,3]]

	  lab.bind [ButtonPress 1 $ const lab.focus,
		    KeyPress "p" mkPlanar,
		    KeyPress "t" mkTurtle,
		    KeyPress "u" unTurtle]

	  saveEnt.bind [ButtonPress 1 $ const saveEnt.focus,
			KeyPress "Up" addOrRemove,
		        KeyPress "Down" saveGraph]
			
	  (picNo,isNew) := (-1,False); resetScale; continue
	 
 	callPaint picts poss b c n str continue = action
          picts' <- mapM (mapM f) picts
	  let graphs = map onlyNodes $ filter notnull $ picts'
	  if notnull graphs then noOfGraphs := length graphs
	          		 (pictures,edges) := unzip graphs
				 font0 <- solve.getFont; font := font0
			         treeNumbers := poss; subtrees := b; open := c
				 bgcolor := case parse color str of 
				   		 Just col -> col; _ -> white
			         curr := if b then if curr < noOfGraphs 
				                      then curr else 0
 		                         else get $ search (== n) poss++Just 0
		                 if isNew then buildPaint $ newPaint continue
				          else newPaint continue
          where f :: Widget_ -> Cmd Widget_
          	f (Fast w)            = do w <- f w; return $ Fast w
                f (File_ file)        = do w <- loadWidget tk file
           				   let c = getCol w
          				   return $ Saved file $ turtle0 c 
          				   		       $ frame 0 c 1 w
          	f (Repeat w)          = do w <- f w; return $ Repeat w
          	f (Turtle st sc acts) = do acts <- mapM g acts
          				   return $ Turtle st sc acts
	        f w                   = return w
          	g :: TurtleAct -> Cmd TurtleAct
                g (Widg b w) = do w <- f w; return $ Widg b w
          	g act        = return act          	

        close = action mapM_ (.stopScan0) scans; canv.clear
		       win.iconify; solve.bigWin; solve.stopRun
		       solve.checkInSolver
		       solve.drawCurr

	combis = action
	  str <- spaceEnt.getValue
	  drawMode := case parse nat str of Just n | n < 16 -> n
	  				    _ -> (drawMode+1) `mod` 16
	  spaceEnt.setValue ""
          combiBut.set [if drawMode == 0 then blueback else redback]
	  scaleAndDraw $ combi drawMode

        switchConnect = action 
          connect := not connect
          edgeBut.set [if connect then redback else blueback]

        draw55 = drawPict . map (transXY (5,5))

	drawPict pict = action		
          if fast || all isFast pict then mapM_ drawWidget pict
	  else let lgs = length scans
	           (picts1,picts2) = splitAt lgs picts
                   g sc pict = do run <- sc.isRunning
			          if run then sc.addScan pict else h sc pict
	           h sc = sc.startScan0 delay
	       zipWithM_ g scans picts1
	       if lgp > lgs then scs <- accumulate $ replicate (lgp-lgs) 
	       					   $ scanner tk drawWidget
				 zipWithM_ h scs picts2
				 scans := scans++scs
          where picts = if New `elem` pict then f pict [] [] else [pict]
		f (New:pict) picts pict' = f pict (picts++[pict']) []
		f (w:pict) picts pict'   = f pict picts (pict'++[w])
		f _ picts pict'	         = picts++[pict']
		lgp = length picts
					
        drawText (p,c,i) x = do 
	  let col = if deleted c then bgcolor
		    else mkLight i $ case parse colPre x of 
		                          Just (c',_) | c == black -> c'
			                  _ -> c
	  canv.text (round2 p) [Text $ delQuotes x, NamedFont font, Fill col, 
	   		        Justify CenterAlign]

 	drawTree n (F cx@(x,q,lg) cts) ct nc c p = action
	  drawText (q,nc,0) x; drawTrees n x q lg cts ct nc c $ succsInd p cts
	drawTree _ (V cx@(x,q,_)) _ nc _ _ = action drawText (q,nc,0) x; done

	drawTrees n x xy lg (ct:cts) ct0 nc c (p:ps) = action
	  canv.line [q,r] [Fill c]; drawTree n ct ct0 nc c p
	  drawTrees n x xy lg cts ct0 nc c ps
	  where (z,pz,lgz) = root ct
	        v = Text_ (xy,0,black,0) n [x] [lg] 
		w = Text_ (pz,0,black,0) n [z] [lgz] 
		q = round2 $ hullCross (pz,xy) v
	        r = round2 $ hullCross (xy,pz) w
	drawTrees _ _ _ _ _ _ _ _ _ = done

	drawWidget (Arc ((x,y),a,c,i) t r b) = action
	  let out = outColor c i bgcolor
	  canv.arc (round2 (x-r,y-r)) (round2 (x+r,y+r)) $
	           [Angles $ round2 (-a,b), ArcStyle t, Outline out] ++ 
		   if t == Perimeter then [Width $ round $ r/10, Fill out]
		   		     else [fillColor c i bgcolor]
          done
	drawWidget (Fast w) = action 
	  if isPict w then mapM_ drawWidget $ mkPict w else drawWidget w
	drawWidget (Gif c p file b h) = action
	  if deleted c then drawWidget $ hull c $ Rect (p,0,c,0) b h 
	  else pic <- loadPhoto tk file
	       canv.image (round2 p) [Img pic]
	       done
	drawWidget (Oval ((x,y),0,c,i) rx ry) = action
	  canv.oval (round2 (x-rx,y-ry)) (round2 (x+rx,y+ry)) 
	  	    [Outline $ outColor c i bgcolor,fillColor c i bgcolor]
          done
        drawWidget (Path0 c i m ps) = action
	  let fill = fillColor c i bgcolor
	      out = outColor c i bgcolor
	      optsL :: Int -> [LineOpt]
	      optsL 0 = [Fill out]
	      optsL 1 = [Fill out,Smooth True]
	      optsL 2 = [Fill out,Width 2]
	      optsL _ = [Fill out,Width 2,Smooth True]
	      optsP :: Int -> [PolygonOpt]
	      optsP 4 = [Outline out,fill]
	      optsP _ = [Outline out,fill,Smooth True]
	  if m > 3 then act canv.polygon $ optsP m
	  	   else act canv.line $ optsL m
	  where act f opts = mapM_ (flip f opts . map round2) $ splitPath ps
	                  -- do flip f opts $ map round2 ps; done
	drawWidget (Repeat w)        = drawWidget w 
	drawWidget (Saved file hull) = action 
	  w <- loadWidget tk file
	  drawWidget $ moveWidg (coords hull) w
	drawWidget Skip = skip
	drawWidget (Text_ (p,_,c,i) n strs lgs) = action
	  zipWithM_ f [0..] strs where (_,_,ps) = textblock p n lgs
	  			       f k = drawText (ps!!k,c,i)
        drawWidget (Tree (p@(x,y),a,c,i) n c' ct) = action
	  drawTree n ct' ct' (outColor c i bgcolor) c' []
	  where ct' = mapT3 f ct; f (i,j) = rotate p a (i+x,j+y)
	drawWidget w | isWidg w        = drawWidget $ mkWidg w
	             | isPict w        = drawPict $ mkPict w
        drawWidget _                   = skip

	interrupt b = action 
	  if b then mapM_ (.stopScan) scans
	            stopBut.set [Text "go", Command $ interrupt False]
	       else mapM_ (\x -> x.startScan delay) scans 
	            stopBut.set [Text "stop", Command $ interrupt True]

	labColor str color = action lab.set [Text str, Background color]

	labGreen str = action if just osci then (get osci).stopOsci
	                      labColor str $ light green

	labRed str = action if just osci then (get osci).stopOsci
	                    osci0 <- oscillator tk act act 1 10 249
			    osci0.startOsci
                            osci := Just osci0
                     where act n = labColor str $ RGB 255 n 0

	labSolver str = action solverMsg := str

	loadGraph file = do
	  str <- lookupLibs tk file	 
	  if null str then solve.labRed $ file ++ " is not a file name."
			   return nil2
	  else case parse graphString $ removeComment 0 $ str `minus1` '\n' of
	            Just graph -> return graph
	            _ -> return nil2
			 
	mkPlanar = action
	  n <- saveEnt.getValue	  
	  let maxmeet = case parse pnat n of Just n -> n; _ -> 200
	      reduce = planarAll maxmeet (pictures!!curr,edges!!curr)
	  if just rect then let (graph,is) = reduce rect rectIndices rscale
	     		    rectIndices := is
			    finish graph maxmeet True
	               else finish (fst $ reduce Nothing [] scale) maxmeet False
	  where finish graph maxmeet b = action 
		  setCurrGraph graph
		  scaleAndDraw $  
		      "The " ++ (if b then "selection" else "current graph") ++
		      " has been reduced to widgets that overlap in at most " ++
		      show maxmeet ++ " pixels."
	       			 
	mkTurtle = action
	  let (pict,arcs) = (pictures!!curr,edges!!curr)
	      Rect (p@(x,y),_,_,_) b h = get rect
	      ks@(k:rest) = rectIndices
	      w = transXY p $ mkTurt (x-b,y-h) rscale $ map (pict!!) rectIndices
	  if just rect then
	     case map (pict!!) ks of
	     [Turtle _ _ _] -> labGreen "The selection is already a turtle."
	     _ -> setCurrGraph $ removeSub (updList pict k w,arcs) rest
	          rectIndices := [k]
		  scaleAndDraw "The selection has been turtled."
	  else case pict of
	       [Turtle _ _ _] -> labGreen "The picture is already a turtle."
	       _ -> setCurrGraph ([mkTurt p0 scale pict],[[]])
		    scaleAndDraw "The current graph has been turtled."
						    
       	moveButton n p@(x,y) = action
       	  if just penpos then 
       	     let (x0,y0) = get penpos
       	         q@(x1,y1) = fromInt2 (x-x0,y-y0)
       	         pict = pictures!!curr
	     if connect then                     -- draw (smooth) arc, 
	        p <- adaptPos p                  -- exchange nodes or move color
                case getWidget (fromInt2 p) scale pict of
                widget@(Just (_,w)) -> if nothing source then source := widget 
                  			                 else target := widget
                                       drawPict [lightWidg w]
	        _ -> done         
	     else case n of			 
	          1 -> let (ns,vs) = changedWidgets
			   translate = transXY q
			   ws = map translate vs
		       changedWidgets := (ns,ws)
	               if ns `shares` rectIndices then      -- move selection
		          rect := Just $ translate $ get rect
	          2 -> if just rect then	            -- enlarge selection
                          let r@(Rect (p,_,_,_) b h) = get rect
		              r' = Rect (add2 p q,0,black,0) (b+x1) $ h+y1
                          rect := Just r'; setFast True
			  draw55 [delWidg r,r']
	          _ -> let (ns,vs) = changedWidgets         -- rotate widgets
		           ws = turnPict x1 vs
	               changedWidgets := (ns,ws); setFast True
	               draw55 $ delPict vs++case rect of Just r -> r:ws; _ -> ws
	     penpos := Just p

   	moveColor n = action 
	  if n /= 0 
	     then colorScale := (n,snd colorScale)
	          let (_,ws) = changedWidgets
	          if pictSize ws < 20 then setFast True
	  		                   draw55 $ map (shiftCol n) ws
 
        moveScale n = action 
	  if n /= 0 then
	     let sc = if just rect then rscale else scale
	         (_,us) = colorScale; (is,vs) = changedWidgets
		 ws = scalePict (sc+fromInt n/10*sc) us 
             colorScale := (n,us)
	     if pictSize ws < 20
	        then changedWidgets := (is,ws)
		     setFast True
		     draw55 $ delPict vs++case rect of Just r -> r:ws; _ -> ws

	newPaint continue = action
          if open then solve.backWin; win.deiconify; win.raise 
	          else win.iconify
	  canv.set [Background bgcolor]
	  let back = [if subtrees then redback else blueback]
	  setButtons back back back
          stopBut.set [Text "stop", Command $ interrupt True]
	  pictSlider.set [To $ noOfGraphs-1]
	  pictSlider.setValue curr
	  (rect,rectIndices,changedWidgets,grade,cols) := (Nothing,[],nil2,0,5)
	  modeEnt.setValue $ if picEval == "tree" then "s" else "m15"
	  let graph@(pict,_) = (pictures!!curr,edges!!curr)
	      mode = if isTree arrangeMode then arrangeMode else "t1"
	      ws = wTreeToBunches mode spread 0 $ pictToWTree pict
	      (bunch,g) = if picEval == "tree" then (Just ws,onlyNodes ws)
	      				       else (Nothing,graph)
	  bunchpict := bunch
	  arrangeGraph True act g
	  continue
          where act (pict,arcs) = action pictures := updList pictures curr pict
	  				 edges := updList edges curr arcs
					 permutation := propNodes pict
					 scaleAndDraw ""

       	pressButton n p = action
	  mapM_ (.stopScan0) scans
	  if notnull pictures then
	     penpos := Just p
	     q <- adaptPos p
	     let p = fromInt2 q
	         (pict,arcs) = (pictures!!curr,edges!!curr)
		 f sc = scalePict sc $ map (pict!!) rectIndices
	     if not connect then 
	        case n of	                 
	          1 -> case rect of 
		       Just r | p `inRect` r                 -- move selection
                         -> changedWidgets := (rectIndices,f rscale)
		            canv.set [Cursor "dotbox"]
		       _ -> case getWidget p scale pict of
		                 (Just (n,w)) -> changedWidgets := ([n],[w])
		                      		 canv.set [Cursor "hand2"]
	                         _ -> done	             -- move widget
	          2 -> oldRect := rect; oldRscale := rscale  
		       let pict' = fold2 updList pict rectIndices $ f 
		       						  $ rscale/scale
		       if just rect then setCurrGraph (pict',arcs) 
			                 rect := Nothing
			                 rectIndices := []   -- remove selection
		       else rect := Just (Rect (p,0,black,0) 0 0)
			    canv.set [Cursor "icon"]         -- create selection
		       rscale := scale
	          _ -> changedWidgets := 
			  if just rect then (rectIndices,f rscale)
				       else (indices_ pict,scalePict scale pict)
		       canv.set [Cursor "exchange"]          -- rotate

	pressColorScale _ = action 
	  mapM_ (.stopScan0) scans
	  let pict = pictures!!curr; ws = map (pict!!) rectIndices
	  if just rect then changedWidgets := (rectIndices,scalePict rscale ws)
	                    colorScale := (0,ws)
	  else changedWidgets := (indices_ pict,scalePict scale pict)
	       colorScale := (0,pict)

      	releaseButton n _ = action
	  let graph@(pict,arcs) = (pictures!!curr,edges!!curr)
          if connect then
             if nothing source || nothing target then nada
 	     else let (s,v) = get source
		      (t,w) = get target
		      ts = arcs!!s
		      is = getSupport graph s t; redDots = just is
		      connected = redDots || t `elem` ts
		      (_,_,c,i) = getState v
		      f (p,a,_,_) = (p,a,c,i)
		      w' = updState f $ pict!!t
                  case n of
		  1 -> if arrangeMode == "paste"
			  then setDrawSwitch (updList pict t w',arcs)
			                     "The target has been colored."
		       else if connected then
		               setDrawSwitch 
		                    (if redDots then removeSub graph $ get is
			             else (pict,updList arcs s $ ts `minus1` t)) 
			            "An arc has been removed."
		            else if s == t then nada
		     	         else setDrawSwitch (pict,updList arcs s $ t:ts)
			                            "An arc has been drawn."
	          2 -> setDrawSwitch (if (isTree ||| isCenter) arrangeMode
			              then (exchgWidgets pict s t,arcs)
				      else exchgPositions graph s t)
		                     "Source and target have been exchanged."
	          _ -> if s == t && just is ||
		          s /= t && connected && all (not . isRedDot) [v,w]
		          then nada
			  else setDrawSwitch (addSmoothArc graph (s,t,v,w,ts))
			                     "A smooth arc has been drawn."
          else case n of
               2 -> case rect of
		    Just r -> rectIndices := getRectIndices pict rscale r
		              if null rectIndices then rect := Nothing; nada
	                      else scaleAndDraw "A subgraph has been selected."
		    _ -> scaleAndDraw "The selector has been removed."
	       _ -> let f = if just rect then scaleWidg $ 1/rscale
			    else transXY (-5,-5) . scaleWidg (1/scale)
			g = fold2 updList
			pair w i j = (g pict [i,j] [f w,pict!!i],
				    g arcs [i,j] $ map (map h . (arcs!!)) [j,i])
			            where h k = if k == i then j 
				                else if k == j then i else k
			graph = case changedWidgets of 
			        ([k],[w]) | nothing rect
			           -> case arrangeMode of 
			                   "back" -> pair w 0 k
					   "front" -> pair w (length pict-1) k
					   _ -> (updList pict k $ f w,arcs)
			        (ks,ws) -> (g pict ks $ map f ws,arcs)
	            setCurrGraph graph
		    scaleAndDraw "The selection has been moved or rotated."
	  (penpos,source,target) := (Nothing,Nothing,Nothing)
	  changedWidgets := nil2; canv.set [Cursor "left_ptr"]
	  where nada = scaleAndDraw "Nothing can be done."
	        setDrawSwitch graph str = action setCurrGraph graph
	        			         scaleAndDraw str; switchConnect

	releaseColor _ = action
	  let (n,_) = colorScale; (is,_) = changedWidgets
	      f i w = if i `elem` is then shiftCol n w else w
	      (pict,arcs) = (pictures!!curr,edges!!curr)
	  if n /= 0 then setCurrGraph (zipWith f [0..] pict,arcs)
			 scaleAndDraw ""; changedWidgets := nil2
			 (fst colorScaleSlider).setValue 0

	releaseScale _ = action
	  mode <- modeEnt.getValue
	  let (n,_) = colorScale
	      sc = if just rect then rscale+fromInt n/10*rscale 
	      			else scale+fromInt n/10*scale
	      f = updState $ \(p,a,c,i) -> (apply2 (*sc) p,a,c,i)
	      (pict,arcs) = (pictures!!curr,edges!!curr)
	      g p i w = if i `elem` rectIndices
                       then transXY p $ f $ transXY (neg2 p) w else w
	  if n /= 0 then 
	     case rect of Just r@(Rect (p,_,_,_) _ _)
		              -> (oldRect,oldRscale) := (rect,rscale)
		                 if mode == "s" then 
			            rect := Just $ scaleWidg sc r
			            setCurrGraph (zipWith (g p) [0..] pict,arcs)
		                 else rscale := sc
		          _ | mode == "s" -> setCurrGraph (map f pict,arcs)
		            | True        -> scale := sc
	     scaleAndDraw ""; changedWidgets := nil2
	     (snd colorScaleSlider).setValue 0

	remote act = action if subtrees then act
	                    else solve.setCurrInSolve (treeNumbers!!curr) act
	                    
	resetScale = action (oldRscale,rscale,scale) := (1,1,1)
			    
	saveGraph = action
	  if null pictures then labRed "Enter pictures!"
	  else file <- saveEnt.getValue
	       let graph@(pict,arcs) = (pictures!!curr,edges!!curr)
		   (pict1,arcs1) = subgraph graph rectIndices
		   pict2 = scalePict rscale pict1
		   (x,y,_,_) = pictFrame pict2
		   pict3 = map (transXY (-x,-y)) pict2
		   filePath = pixpath file
		   lg = length filePath
		   dir:rest = words file
		   dirPath = pixpath dir
		   n = parse nat $ concat rest
	       if null file then labRed "Enter a file name!"
	       else if notnull rest 
	               then mkdir dirPath
	                    picNo := if just n then get n else picNo+1
                            file <- savePng canv $ mkFile dirPath picNo
                            files <- getDirectoryContents dirPath
                            tk.writeFile (dirPath ++ ".html") $ html True dir
				 	 		      $ pix dir files
			    labGreen $ saved "entire graph" file
		    else let (pre,suf) = splitAt (lg-4) filePath
		             (picFile,isPng) = if lg > 3 && suf == ".png"
		   		               then (pre,True) else ("",False)
			 if isPng then savePng canv picFile
				       labGreen $ saved "entire graph" filePath
	                 else let filePath = expanderLib ++ file
	                          msg str = labGreen $ savedCode str filePath
	                      if just rect then
	                         case pict3 of 
	                         [w] -> let f (_,_,c,_) = st0 c
	                                tk.writeFile filePath $ show 
	                                                      $ updState f w
	                      	        msg "widget"
	                         _ -> tk.writeFile filePath $ show (pict3,arcs1)
			              msg "selection"
		              else tk.writeFile filePath $ show
		              			     (scalePict scale pict,arcs)
		              	   msg "entire graph"
	            
	scaleAndDraw msg = action
	  mapM_ (.stopScan0) scans; canv.clear
	  sc <- scanner tk drawWidget; scans := [sc]
	  stopBut.set [Text "stop", Command $ interrupt True]
	  n <- saveEnt.getValue	  
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
	      (pict1,bds) = foldr f ([],(0,0,0,0)) $ indices_ pict
	      f i (ws,bds) = (w:ws,minmax4 (widgFrame w) bds)
			     where w = scaleWidg (sc i) $ pict!!i
	      sc i = if i `elem` is then rscale else scale
	      (x1,y1,x2,y2) = if just rect 
	      		      then minmax4 (widgFrame $ get rect) bds else bds
	      size = apply2 (max 100 . round . (+10)) (x2-x1,y2-y1)
	      translate = transXY (-x1,-y1)
	      pict2 = map translate pict1
	      g = scaleWidg . recip . sc
          pictures := updList pictures curr $ zipWith g [0..] pict2
	  edges := updList edges curr arcs
 	  canvSize := size
	  canv.set [ScrollRegion (0,0) size]
	  let pict3 = map (transXY (5,5)) pict2
	      pict4 = h pict3
	      h = filter propNode
	      ws = if just rect then h $ map (pict3!!) is else pict4
	      (hull,qs) = convexPath (map coords ws) pict4
	      drawArrow ps = do canv.line (map round2 ps)
		                     $ if arrangeMode == "d1" then [Smooth True]
			  	       else [Arrow Last, Smooth True]
	      k = treeNumbers!!curr
	  if drawMode `elem` [0,15] then drawPict pict3
	     else case drawMode of 
	          1 -> drawPict pict4
	          2 -> drawPict $ h $ colorLevels True pict3 arcs
	          3 -> drawPict $ h $ colorLevels False pict3 arcs
	          4 -> drawPict $ pict4++hull
	          5 -> (n,wid) <- mkSizes font $ map show qs
		       let addNo x p = Text_ (p,0,dark red,0) n [x] [wid x]
		       drawPict $ pict4++hull++zipWith (addNo . show) [0..] qs
	          _ -> drawPict $ extendPict drawMode pict4
	  if arrangeMode /= "d2" 
	     then mapM_ drawArrow $ buildAndDrawPaths (pict3,arcs)
	  if just rect then let (x1,y1,x2,y2) = pictFrame $ map (pict2!!) is
                                (b,h) = (abs (x2-x1)/2,abs (y2-y1)/2)
				r = Rect ((x1+b,y1+h),0,black,0) b h
		            rect := Just r; draw55 [r]
          solver <- solve.getSolver; b <- solve.isSolPos k
	  let str1 = if subtrees then subtreesMsg solver
	                         else treesMsg k noOfGraphs solver b
	      add str = if null str then "" else '\n':str
          labGreen $ str1 ++ add solverMsg ++ add msg

	setButtons opts1 opts2 opts3 = action narrowBut.set opts1
					      simplifyD.set opts2
					      simplifyB.set opts3

	setCurr _ = action pictSlider.setValue curr; remote solve.drawCurr
                           scaleAndDraw ""

	setCurrGraph (pict,arcs) = action 
	  let graph@(pict',_) = (pictures!!curr,edges!!curr)
	  oldGraph := graph
	  pictures := updList pictures curr pict
	  edges := updList edges curr arcs
	  if length pict /= length pict' then permutation := propNodes pict

	setCurrInPaint n = action if n < length pictures 
	                             then curr := n; pictSlider.setValue n
                                          scaleAndDraw ""

	setDelay _ = action 
	  if not fast then runs <- mapM (.isRunning) scans
	                   let scs = [scans!!i | i <- indices_ scans, runs!!i]
                           if null scs then scaleAndDraw ""
				       else mapM_ (\x -> x.startScan delay) scs

	setEval eval hv = action 
	  picEval := eval
	  (arrangeMode,spread) := case take 4 eval of 
	  			       "tree" -> ("t1",fromInt2 hv)
	  		               "over" -> ("o",(0,0))
				       _ -> ("m1",(0,0))

        setFast b = action 
	  fast := b
	  if not isNew then fastBut.set [Text $ if b then "slow" else "fast"]
	
	showInSolver = action 
	  let graph = bunchesToArcs (pictures!!curr,edges!!curr)
          case rect of Just r 
	                 -> act $ scaleGraph rscale $ subgraph graph rectIndices
	               _ -> act graph
	  solve2.bigWin 
	  where act graph = solve2.enterTree False $ graphToTree graph
	  
	skip = action done

	switchFast = action setFast $ not fast; scaleAndDraw ""
	
	undo = action
          if drawMode == 0 then
	     if null $ fst oldGraph
	        then labRed "The current graph has no predecessor."
             else let (pict,_) = oldGraph
	          setCurrGraph oldGraph 
		  rect := oldRect; rscale := oldRscale
		  rectIndices := if just rect 
		                 then getRectIndices pict rscale $ get rect
				 else []
		  scaleAndDraw ""
          else drawMode := drawMode-1
	       if drawMode == 0 then combiBut.set [blueback]
	       scaleAndDraw $ combi drawMode
          		 
	unTurtle = action
	  let graph = (pictures!!curr,edges!!curr)
          if just rect 
	     then oldRect := rect
		  let (graph',n) = unTurtG graph rscale (`elem` rectIndices)
		      k = length $ fst graph
	          setCurrGraph graph'
		  rectIndices := rectIndices++[k..k+n-1]
	          scaleAndDraw "The selection has been unturtled."
	     else setCurrGraph $ fst $ unTurtG graph scale $ const True
	          scaleAndDraw "The current graph has been unturtled."
	  
      in struct ..Painter
 		   
-- the GRAPH type
 	       
 type Path  = [Point]
 type State = (Point,Float,Color,Int) -- (center,orientation,hue,lightness)

-- ([w1,...,wn],[as1,...,asn]) :: Graph represents a graph with node set 
-- {w1,...,wn} and edge set {(wi,wj) | j in asi, 1 <= i,j <= n}.
 
 data Widget_ = Arc State ArcStyleType Float Float | Bunch Widget_ [Int] | 
		-- Bunch w is denotes w together with outgoing arcs to the 
		-- widgets at positions is.
		Dot Color Point | Fast Widget_ | File_ String | 
		Gif Color Point String Float Float | New | 
		Oval State Float Float | Path State Int Path | 
		Path0 Color Int Int Path | Poly State Int [Float] Float | 
		Rect State Float Float | Repeat Widget_ | Saved String Widget_ |
		Skip | Text_ State Int [String] [Int] | 
		Tree State Int Color (Term (String,Point,Int)) | 
		-- The center of Tree .. ct agrees with the root of ct.
		Tria State Float | Turtle State Float TurtleActs | 
		WTree TermW deriving (Show,Eq)

 type TurtleActs = [TurtleAct]
 data TurtleAct  = Close | Draw | 
                   -- Close and Draw finish a polygon resp. path starting at the
		   -- preceding Open command.
 		   Jump Float | JumpA Float | Move Float | MoveA Float | 
                   -- JumpA and MoveA ignore the scale of the enclosing turtle.
		   Open Color Int | Scale Float | Turn Float | Widg Bool Widget_
		   -- The open mode `elem` [0..5] (see drawWidg Path0) 
		   -- determines the mode of the path ending when the next 
		   -- Close/Draw command is reached.
		   -- Widg False w ignores the orientation of w, Widg True w 
		   -- adds it to the orientation of the enclosing turtle.
		   deriving (Show,Eq)

 type Arcs      = [[Int]]
 type Picture   = [Widget_]
 type Graph 	= (Picture,Arcs)
 type TermW 	= Term Widget_
 type WidgTrans = Widget_ -> Widget_
 
 instance Eq ArcStyleType where Chord == Chord         = True
				Pie == Pie             = True
				Perimeter == Perimeter = True
				_ == _                 = False
		
-- Each widget (see Eterm) is turned into a picture consisting of Arcs, Dots, 
-- Gifs, horizontal or vertical Ovals, Path0s, Text_s and Trees before being 
-- drawn.

 isWTree (WTree _) = True
 isWTree _	   = False
 
 type Point  = (Float,Float)
 type Point3 = (Float,Float,Float)
 type Line_  = (Point,Point)
 type Lines  = [Line_]

 type TermWP = Term (Widget_,Point)

 instance Root Widget_ where undef = Skip

 p0 :: Point
 p0 = (0,0)
 
 st0 :: Color -> State
 st0 c = (p0,0,c,0)

 st0B :: State
 st0B = st0 black

 path0 :: Color -> Int -> Path -> Widget_
 path0 = Path . st0
 
 widg = Widg False
 
 wait = widg Skip

 noRepeat (Repeat _) = False
 noRepeat _          = True

 isFast (Fast _) = True
 isFast _        = False
 
 wfast = widg . fast

 fast (Turtle st sc acts) = Fast $ Turtle st sc $ map f acts
 			    where f (Widg b w) = Widg b $ fast w
				  f act        = act
 fast (Bunch w is)        = Bunch (fast w) is
 fast (Fast w)        	  = fast w
 fast w	  	      	  = Fast w
 
 posWidg x = Text_ st0B 0 [x] [0]
 
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

 (act:acts)<++>acts' = act<:>acts<++>acts'
 _<++>acts           = acts
 
 reduceActs (act:acts) = act<:>reduceActs acts
 reduceActs _          = []
 
 turtle0 :: Color -> TurtleActs -> Widget_
 turtle0 c = Turtle (st0 c) 1
 
 turtle0B,turtle1 :: TurtleActs -> Widget_
 turtle0B     = turtle0 black
 turtle1 acts = (case acts of Open c _:_ -> turtle0 c
 		              Widg _ w:_ -> turtle0 $ getCol w
 		              _ -> turtle0B) $ reduceActs acts
 
 up   = Turn $ -90
 down = Turn 90
 back = Turn 180

 open = Open black 0

 close2 = [Close,Close]
  
 text0 (n,width) x = Text_ st0B n strs $ map width strs where strs = words x

 (x',y') `inRect` Rect ((x,y),_,_,_) b h = x-b <= x' && x' <= x+b &&
 					   y-h <= y' && y' <= y+h
 
 onlyNodes pict = (pict,replicate (length pict) []::Arcs)
				     				     
 pictSize = sum . map f where f (Path0 _ _ _ ps) = length ps
			      f w | isWidg w     = f $ mkWidg w
			      f w | isPict w     = pictSize $ mkPict w
			      f (Bunch w _)      = f w
			      f (Fast w)         = f w
			      f (Repeat w)       = f w
			      f _	         = 1
 
 getPoints (Path0 _ _ _ ps) = ps
 getPoints _                = error "getPoints"
 
 getLines = mkLines . getPoints
 
 getAllPoints :: Widget_ -> Path
 getAllPoints (Bunch w _)      = getAllPoints w
 getAllPoints (Fast w)         = getAllPoints w
 getAllPoints (Repeat w)       = getAllPoints w
 getAllPoints (Path0 _ _ _ ps) = ps
 getAllPoints w | isWidg w     = getAllPoints $ mkWidg w
 getAllPoints w | isPict w     = concatMap getAllPoints $ mkPict w
 getAllPoints _	               = error "getAllPoints"

 isTurtle (Turtle _ _ _) = True
 isTurtle _              = False

 isWidg (Dot _ _)      = True    
 isWidg (Oval _ _ _)   = True
 isWidg (Path _ _ _)   = True
 isWidg (Poly _ m _ _) = m < 6    
 isWidg (Rect _ _ _)   = True    
 isWidg (Tria _ _)     = True    
 isWidg _	       = False

 isPict (Poly _ m _ _)     = m > 5    
 isPict (Turtle _ _ _)     = True
 isPict _                  = False    

 isTree (x:_:_) = x `elem` "art"
 isTree _       = False
 
 isCenter mode = mode == "c"
 
 removeSub,subgraph :: Graph -> [Int] -> Graph
 removeSub (pict,arcs) (i:is) = removeSub graph $ f is
 		           where graph = (context i pict,map f $ context i arcs)
		                 f = foldl g []
				 g is k = if k < i then k:is 
		      			  else if k == i then is else (k-1):is
 removeSub graph _            = graph
 subgraph graph@(pict,_)      = removeSub graph . minus (indices_ pict)
	    	      
 center,gravity :: Widget_ -> Point
 center w  = ((x1+x2)/2,(y1+y2)/2) where (x1,y1,x2,y2) = widgFrame w
 gravity w = apply2 (/(fromInt $ length qs)) $ foldl1 add2 qs 
 	     where qs = mkSet $ getFramePts True w	
	     
 actsCenter :: TurtleActs -> Point
 actsCenter acts = ((x1+x2)/2,(y1+y2)/2) 
 		   where (x1,y1,x2,y2) = turtleFrame st0B 1 acts

 shiftTo :: Point -> TurtleActs
 shiftTo (0,0) = []
 shiftTo p     = [Turn a,Jump $ distance p0 p,Turn $ -a] where a = angle p0 p
 
 getActs :: Widget_ -> TurtleActs
 getActs Skip              = []
 getActs (Turtle _ _ acts) = acts
 getActs w 		   = [widg w]
		     
 shiftWidg :: Point -> WidgTrans
 shiftWidg (0,0) w = w
 shiftWidg p w     = turtle0 (getCol w) $ shiftTo (neg2 p) ++ getActs w
   
 actsToCenter :: TurtleActs -> TurtleActs
 actsToCenter acts = shiftTo (neg2 $ actsCenter acts) ++ acts

 inCenter :: WidgTrans -> WidgTrans
 inCenter f w = turtle0 (getCol w') $ shiftTo p ++ [widg w'] 
	        where p = gravity w
		      w' = f $ shiftWidg p w
		     
 frame n c mode w = shiftTo (neg2 p) ++ [widg $ path0 c mode $ last ps:ps]
 	            where (x1,y1,x2,y2) = widgFrame w
		          p = ((x1+x2)/2,(y1+y2)/2)
			  ps = [(x2d,y1d),(x2d,y2d),(x1d,y2d),(x1d,y1d)]
			  x1d = x1-n; y1d = y1-n; x2d = x2+n; y2d = y2+n
		     
 addFrame c mode w = turtle0 c $ frame 5 c mode w ++ getActs w
	    
-- nodeLevels b graph!!n returns the length of a shortest path from a root of 
-- graph to n. nodeLevels True counts in control points and is used by shelf
-- (see below). nodeLevels False disregards control points and is used by 
-- colorLevels (see below).

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

-- colorLevels b pict arcs colors all nodes of pict on the same level with the
-- same color.

 colorLevels :: Bool -> Picture -> Arcs -> Picture
 colorLevels alternate pict arcs = map f nodes
       where nodes = indices_ pict
             levels = nodeLevels False (pict,arcs)
	     f n = if propNode w then updCol (g alternate $ levels!!n) w else w
		   where w = pict!!n
	     g True k = if odd k then complColor c else c
	     g _ k    = hue 1 c (maximum levels+1) k
	     c = case searchGet (not . isBW) $ map getCol $ filter propNode pict
	     	      of Just (_,d) -> d; _ -> red

 angle :: RealFloat a => (a,a) -> (a,a) -> a
 angle (x1,y1) (x2,y2) = atan2' (y2-y1) (x2-x1)*180/pi    
 
 atan2' 0 0 = atan2 0 1
 atan2' x y = atan2 x y
 
 slope (x1,y1) (x2,y2) = if x1 == x2 then fromInt maxBound else (y2-y1)/(x2-x1) 

-- successor moves on a circle.
-- successor p (distance p q) (angle p q) = q. 

 successor :: Floating a => (a,a) -> a -> a -> (a,a)
 successor (x,y) r a = (x+r*c,y+r*s) where (s,c) = sincos a    	   
 
 sincos a = (sin rad,cos rad) where rad = a*pi/180

-- successor2 moves on an ellipse.

 successor2 :: Floating a => (a,a) -> a -> a -> a -> (a,a)
 successor2 (x,y) rx ry a = (x+rx*c,y+ry*s) where (s,c) = sincos a    	

 distance :: Floating a => (a,a) -> (a,a) -> a
 distance (x1,y1) (x2,y2) = sqrt $ (x2-x1)^2+(y2-y1)^2
							  
 perimeter :: Path -> Float
 perimeter ps = if peri <= 0 then 0.01 else peri
                where peri = sum $ zipWith distance ps $ tail ps
		
 addPoints :: Path -> [Float] -> Path
 addPoints ps []               = ps
 addPoints (p:ps@(q:_)) (d:ds) = if d > d' then p:addPoints ps (d-d':ds)
 		                 else p:addPoints (successor p d a:ps) ds
		                 where d' = distance p q; a = angle p q
 addPoints _ _ = error "addPoints"
 		     
 adaptLength :: Int -> Path -> Path
 adaptLength n ps = if n > 0 then addPoints ps $ dps/2:replicate (n-1) dps
			     else ps
                    where dps = perimeter ps/k; k = fromInt n

 area :: Path -> Float
 area ps = abs (sum $ zipWith f ps $ tail ps++[head ps])/2
           where f (x1,y1) (x2,y2) = (x1-x2)*(y1+y2)

 mindist p (q:qs) = f (distance p q,q) qs
               where f dr@(d',r) (q:qs) = if d < d' then f (d,q) qs else f dr qs
				          where d = distance p q 
                     f (_,r) _ 	 	= r 

-- straight ps checks whether ps represents a straight line.

 straight :: Path -> Bool
 straight ps = and $ zipWith3 straight3 ps tps $ tail tps where tps = tail ps

 straight3 :: Point -> Point -> Point -> Bool
 straight3 (x1,y1) (x2,y2) (x3,y3) = x1 == x2 && x2 == x3 || 
 				     x1 /= x2 && x2 /= x3 &&
				     (y2-y1)/(x2-x1) == (y3-y2)/(x3-x2)
	      
 reduceP :: Path -> Path
 reduceP (p:ps@(q:r:s)) | straight3 p q r = reduceP $ p:r:s
                        | True            = p:reduceP ps
 reduceP ps                               = ps     
 
 mkLines :: Path -> Lines
 mkLines ps = zip qs $ tail qs where qs = reduceP ps

-- rotate q a p rotates p clockwise by a around q on the axis (0,0,1).

 rotate :: Point -> Float -> Point -> Point
 rotate _ 0 p             = p         -- sincos 0 = (0,1)
 rotate q@(i,j) a p@(x,y) = if p == q then p else (c*x1-s*y1+i,s*x1+c*y1+j)
			    where (s,c) = sincos a; x1 = x-i; y1 = y-j

-- rotateA q (a,nx,ny,nz) p rotates p clockwise by a around q on the axis
-- (nx,ny,nz).

 rotateA :: Point -> Float -> Point3 -> Point -> Point
 rotateA _ 0 _ p 		      = p
 rotateA q@(i,j) a (nx,ny,nz) p@(x,y) =
                      if p == q then p else ((t*nx*nx+c)*x1+(t*nx*ny-s*nz)*y1+i,
      		                             (t*nx*ny+s*nz)*x1+(t*ny*ny+c)*y1+j)
                      where (s,c) = sincos a; x1 = x-i; y1 = y-j; t = 1-c

 mkActs :: Picture -> [(Point,Float)] -> TurtleActs
 mkActs pict = (++[Close]) . fst . fold2 f ([open],p0) pict
               where f (acts,p) w (q,a) = (acts++acts',q) 
		       where acts' = [Turn b,Jump d,Turn $ a-b,widg w,Turn $ -a]
			     b = angle p q; d = distance p q
					      
 mkTurt :: Point -> Float -> Picture -> Widget_
 mkTurt p sc pict = Turtle st0B (1/sc) $ actsToCenter acts
		    where pict' = scalePict sc $ filter propNode pict
		          f = map $ coords***orient
			  acts = shiftTo (neg2 p) ++ mkActs pict' (f pict')

 unTurt :: Picture -> Float -> (Int -> Bool) -> (Picture,Int)
 unTurt pict sc b = (pr2***pr3) $ foldr f (length pict-1,[],0) pict
        where f w (i,pict,k) = if b i && isTurtle w 
		     	       then (i-1,ws++pict,k+length ws-1)
			       else (i-1,w:pict,k)
		           where ws = scalePict (1/sc) $ mkPict $ scaleWidg sc w

 unTurtG :: Graph -> Float -> (Int -> Bool) -> (Graph,Int)
 unTurtG (pict,_) sc b = ((pict',replicate (length pict') []),n)
 		         where (pict',n) = unTurt pict sc b

-- getRectIndices pict sc rect returns the indices of all widgets of pict within
-- rect. getRectIndices is used by addOrRemove and releaseButton and undo 
-- (see below).

 getRectIndices pict sc rect = [i | i <- indices_ scpict, 
 				    let w = scpict!!i, -- propNode w,
				    f (coords w) || any f (getFramePts True w)]
			       where scpict = scalePict sc pict
			             f = (`inRect` rect)

 splitPath :: [a] -> [[a]]
 splitPath ps = if null rs then [qs] else qs:splitPath (last qs:rs)
		where (qs,rs) = splitAt 99 ps

 textblock (x,y) n lgs = (fromInt (maximum lgs)/2,h,map f $ indices_ lgs) 
			 where h = m*fromInt (length lgs)
              	               f i = (x,y-h+m+fromInt i*k) 
			       k = fromInt n+4; m = k/2

 mkRects st@(p,_,_,_) n lg = Rect st b h where (b,h,_) = textblock p n [lg]
	         
 isRedDot (Bunch w _)           = isRedDot w
 isRedDot (Dot (RGB 255 0 0) _) = True
 isRedDot _                     = False

 isSkip (Bunch w _) = isSkip w
 isSkip Skip        = True
 isSkip _           = False

 propNode = not . (isRedDot ||| isSkip)

 propNodes pict = [i | i <- indices_ pict, propNode $ pict!!i]

 getState (Arc st _ _ _)   = st
 getState (Bunch w _)      = getState w
 getState (Dot c p)        = (p,0,c,0)
 getState (Fast w)         = getState w
 getState (Gif c p _ _ _)  = (p,0,c,0)
 getState (Oval st _ _)    = st
 getState (Path st _ _)    = st
 getState (Poly st _ _ _)  = st
 getState (Rect st _ _)    = st
 getState (Repeat w)       = getState w
 getState (Saved _ w)      = getState w
 getState (Text_ st _ _ _) = st
 getState (Tree st _ _ _)  = st
 getState (Tria st _)      = st
 getState (Turtle st _ _)  = st
 getState _ = st0B

 coords w = p where (p,_,_,_) = getState w
 
 orient w = a where (_,a,_,_) = getState w
 
 getCol w = c where (_,_,c,_) = getState w
  
 filled c = if isBW c then 0 else 4

 xcoord = fst . coords
 ycoord = snd . coords
 
 updState :: (State -> State) -> WidgTrans 
 updState f (Arc st t r a)        = Arc (f st) t r a
 updState f (Bunch w is) 	  = Bunch (updState f w) is
 updState f w@(Dot _ _)           = Dot c p where (p,_,c,_) = f $ getState w
 updState f (Fast w)     	  = Fast $ updState f w
 updState f w@(Gif _ _ file b h)  = Gif c p file b h
 				    where (p,_,c,_) = f $ getState w
 updState f (Oval st rx ry)       = Oval (f st) rx ry 
 updState f (Path st m ps)        = Path (f st) m ps
 updState f (Poly st m rs a)      = Poly (f st) m rs a
 updState f (Rect st b h)         = Rect (f st) b h
 updState f (Repeat w)   	  = Repeat $ updState f w
 updState f (Saved file w)        = Saved file $ updState f w
 updState f (Text_ st n strs lgs) = Text_ (f st) n strs lgs
 updState f (Tree st n c ct)      = Tree st' n (if d == white then white else c)
 					 ct where st'@(_,_,d,_) = f st
 updState f (Tria st r)           = Tria (f st) r
 updState f (Turtle st sc acts)   = Turtle (f st) sc $ map g acts
	                            where g (Open c m) = Open d m
						     where (_,_,d,_) = f $ st0 c
					  g (Widg b w) = Widg b $ updState f w
					  g act        = act
 updState _ w = w

-- mkWidg (w (p,a,c,i) ...) rotates widget w around p by a.
-- mkWidg is used by drawWidget and hulls.

 mkWidg :: WidgTrans
 mkWidg (Dot c p)	           = Oval (p,0,c,0) 5 5
 mkWidg (Oval (p,a,c,i) rx ry)     = Path0 c i (filled c) $ map f [0,5..360]
				     where f = rotate p a . successor2 p rx ry
 mkWidg (Path (p,a,c,i) m ps)      = Path0 c i m $ map (rotate p a . add2 p) ps
 mkWidg (Poly (p,a,c,i) m rs b)    = Path0 c i m $ last ps:ps
 		                     where ps = circlePts p a b rs
 mkWidg (Rect (p@(x,y),a,c,i) b h) = Path0 c i (filled c) $ last qs:qs
                                     where ps = [(x+b,y-h),(x+b,y+h),
				    		 (x-b,y+h),(x-b,y-h)]
                                           qs = map (rotate p a) ps
 mkWidg (Tria (p@(x,y),a,c,i) r)   = Path0 c i (filled c) $ last qs:qs
                                     where ps = [(x+lg,z),(x-lg,z),(x,y-r)]
         		                   lg = r*0.86602      -- r*3/(2*sqrt 3)
					    		       -- = sidelength/2
	                                   z = y+lg*0.57735    -- y+lg*sqrt 3/3
					   qs = map (rotate p a) ps
 
 circlePts :: Point -> Float -> Float -> [Float] -> Path
 circlePts p a inc = fst . foldl f ([],a)
                     where f (ps,a) 0 = (ps,a+inc)
                           f (ps,a) r = (successor p r a:ps,a+inc)

-- mkPict is used by convexPath, hulls and drawWidget.

-- mkPict (Poly (p,a,c,i) mode rs b) with mode > 5 computes triangles or chords 
-- of a rainbow polygon with center p, orientation a, inner color c, lightness 
-- value i, radia rs and increment angle b.

 mkPict :: Widget_ -> Picture
 
 mkPict (Poly (p,a,c,i) m (r:rs) b) = pict
   where (pict,_,_,_,_,_) = foldl f ([],successor p r a,a+b,c,1,False) $ rs++[r]
         lg = length rs+1
	 f (pict,q@(x,y),a,c,k,d) r = if r == 0 then (pict,q,a+b,c,k+1,False)
	                                        else (pict++new,p',a+b,c',1,d')
	   where p'@(x',y') = successor p r a
		 (new,c',d') = if m < 9 
			       then if d then (pict',c,False)
			            else (pict',hue (m-5) c (lg `div` 2) k,True)
			       else if m < 12
				    then (mkPict $ w c,hue (m-8) c lg k,d)
				    else if m < 15 
				         then (pict',hue (m-11) c lg k,d)
				         else (mkPict $ w $ h 1,h $ k+k,d)
		 pict' = fst $ iterate g ([],q)!!k
		 g (pict,q) = (pict++[Path0 c i 4 [p,q,q']],q')
			      where q' = add2 q $ apply2 (/n) (x'-x,y'-y)
		 h = hue (m-14) c $ 2*lg
		 n = fromInt k
	         w c' = Turtle (p,0,c,i) 1 $ Turn (a-b*(n-1)/2):leafC h d c c'
			where h = r/2; d = n*distance (h,0) (successor p0 h b)/2

-- mkPict (Turtle (p,a,c,i) sc acts) translates acts into the picture drawn by a
-- turtle that executes acts, starting out from point p with scale factor sc,
-- orientation a, color c and lightness value i.

 mkPict (Turtle (p,a,c,i) sc acts) = 
            case foldl f iniState acts of (pict,(_,c,m,_,ps):_) -> g pict c m ps
		  			  _ -> []
            where iniState = ([],[(a,c,0,sc,[p])])
	          f (pict,states@((a,c,m,sc,ps):s)) act = 
                    case act of Jump d    -> (g pict c m ps,(a,c,m,sc,[q]):s) 
		  			     where q = successor p (d*sc) a
			        JumpA d   -> (g pict c m ps,(a,c,m,sc,[q]):s)
		  		  	     where q = successor p d a
			        Move d    -> (pict,(a,c,m,sc,ps++[q]):s) 
		  			     where q = successor p (d*sc) a
	                        MoveA d   -> (pict,(a,c,m,sc,ps++[q]):s) 
		  			     where q = successor p d a
			        Turn b    -> (pict,(a+b,c,m,sc,ps):s)
			        Open c m  -> (pict,(a,c,m,sc,[p]):states)
			        Scale sc' -> (pict,(a,c,m,sc*sc',[p]):states) 
			                     -- or ps instead of [p] ?
			        Close     -> (g pict c m ps,s)
			        Draw      -> (g pict c m ps,(a,c,m,sc,[p]):s)
				Widg b w  -> (pict++[moveTurnScale b p a sc w],
			                      states)
			        _         -> (pict,states)
	            where p = last ps
  	          g pict c m ps = if length ps < 2 then pict
		   		  else pict++[Path0 c i m $ reduceP ps]

 mkPict w = [w]

-- inWidget is used by getWidget and scaleAndDraw (see below).

 inWidget :: Point -> Widget_ -> Bool
 inWidget p@(x,y) = f . coords ||| any (interior p) . getFrameLns 
                    where f (x',y') = almostEq x x' && almostEq y y'
	      
 almostEq a b = abs (a-b) < 5
 
 inFrame :: Point -> Point -> Point -> Bool
 inFrame (x1,y1) (x,y) (x2,y2) = min x1 x2 `le` x && x `le` max x1 x2 &&
			         min y1 y2 `le` y && y `le` max y1 y2
	                         where le a b = a < b || almostEq a b
	      
 onLine :: Point -> Line_ -> Bool
 onLine p@(x,y) (p1@(x1,y1),p2) = inFrame p1 p p2 &&
 			          almostEq y (slope p1 p2*(x-x1)+y1)

-- getWidget p scale pict returns a widget of pict close to p and scales it.
-- getWidget is used by selectNode (see below).

 getWidget :: Point -> Float -> Picture -> Maybe (Int,Widget_)
 getWidget p sc = searchGetR (not . isSkip &&& inWidget p) .
 		  map (transXY (5,5) . scaleWidg sc)			

-- hulls edgy w computes frame paths of w. 
-- hulls is used by dots, getFrameLns, getFramePts, extendPict, outline and
-- planarWidg.

 hulls :: Bool -> Widget_ -> Picture
 hulls edgy = f
  where f (Arc (p,a,c,i) t r b) = if r <= 0 then [] 
  					    else [Path0 c i (filled c) ps]
 	  where ps = case t of 
 	  	     Pie   -> p:g r++[p] 
		     Chord -> last qs:qs where qs = g r
	             _     -> q:g (21*r')++reverse qs where qs@(q:_) = g $ 19*r'
						            r' = r/20
		g = circlePts p a (-b/36) . replicate 37
	f (Bunch w _)  			= f w
	f (Fast w)     			= f w
        f (Gif c p _ b h)               = f $ hull c $ Rect (p,0,c,0) b h
        f (Oval (p,0,c,i) rx ry)        = [Path0 c i (filled c) $
				            map (successor2 p rx ry) [0,5..360]]
        f w@(Path0 c i m ps)            = [if edgy || even m 
				           then w else Path0 c i m $ spline ps]
	f (Repeat w)                    = f w
	f (Saved _ w)     	        = f w
        f (Text_ (p,a,c,i) n _ lgs)     = concatMap f $ zipWith g ps lgs
                                          where (_,_,ps) = textblock p n lgs
				                g p = mkRects (p,a,c,i) n
	f (Tree (p@(x,y),a,c,i) n _ ct) = concatMap f $ foldT g $ mapT3 h ct
                          where g (_,p,lg) ss = mkRects (p,a,c,i) n lg:concat ss
				h (i,j) = rotate p a (i+x,j+y)
	f w | isWidg w = f $ mkWidg w
            | isPict w = concatMap f $ mkPict w
	f _	       = [] 
	
-- getFramePts is used by getRectIndices, gravity, morphPict, turtleFrame and 
-- widgFrame.
 
 getFramePts :: Bool -> Widget_ -> Path
 getFramePts edgy = concatMap getPoints . hulls edgy

-- hull is used by drawWidget and hulls.

 hull :: Color -> Widget_ -> Widget_
 hull c = Path0 c 0 1 . getFramePts False

-- getFrameLns is used by hullCross and inWidget.

 getFrameLns :: Widget_ -> [Lines]
 getFrameLns = map getLines . hulls False

-- stringsInPict is used by showSubtreePicts and showTreePicts (see Ecom).

 stringsInPict = concatMap stringsInWidg

 stringsInWidg (Bunch w _)        = stringsInWidg w
 stringsInWidg (Fast w)		  = stringsInWidg w
 stringsInWidg (Repeat w)         = stringsInWidg w
 stringsInWidg (Text_ _ _ strs _) = strs
 stringsInWidg (Tree _ _ _ ct)    = stringsInTree ct
 stringsInWidg (Turtle _ _ acts)  = stringsInActs acts
 stringsInWidg (WTree t)          = stringsInWTree t
 stringsInWidg  _ 		  = []
 
 stringsInTree :: Term (String,Point,Int) -> [String]
 stringsInTree = foldT f where f (a,_,_) strs = delQuotes a:concat strs

 stringsInWTree = foldT f where f w strs = stringsInWidg w++concat strs

 stringsInActs acts = concatMap f acts where f (Widg _ w) = stringsInWidg w
			                     f _          = []

-- textheight is used by drawArc and drawPointer (see Ecom).

 textheight font = (ht`div`2,(ht+ht)`div`3)
	           where [_,size,_] = words font.fontName; ht = read size

-- GRAPHICAL INTERPRETERS

 loadWidget :: TkEnv -> String -> Cmd Widget_
 loadWidget tk file = do
	    str <- lookupLibs tk file	 
	    if null str then return Skip
	    else case parse widgString $ removeComment 0 $ str `minus1` '\n' of
	              Just w -> return w
	              _ -> return Skip
	              
 loadWidgetT :: TkEnv -> String -> MaybeT Cmd Picture
 loadWidgetT tk file = do w <- lift $ loadWidget tk file; return [w]

 type InterpreterT = TkEnv -> Sizes -> Pos -> TermS -> MaybeT Cmd Picture
 
 rturtle :: TurtleActs -> MaybeT Cmd Picture
 rturtle = return . single . turtle1
 
 searchPicT :: InterpreterT -> InterpreterT
 searchPicT eval tk sizes spread t = g [] $ expand 0 t [] where
      g p t = struct runT = do pict <- (eval tk sizes spread t).runT
	   		       if just pict then return pict
	   		       else case t of 
	   		            F _ ts 
	   		              -> (concatJustT $ zipWithSucs g p ts).runT
				    _ -> return Nothing
					      
 solPicT :: Sig -> InterpreterT -> InterpreterT
 solPicT sig eval tk sizes spread t = 
                      case parseSol (solAtom sig) t of
    	                   Just sol -> do let f = eval tk sizes spread . getTerm
    	               		          concatJustT $ map f sol
       		           _ -> zero

 partitionT :: Int -> InterpreterT
 partitionT _ tk _ _ (F "file" [F file []]) = loadWidgetT tk file
 partitionT mode _ sizes _ t = rturtle $ drawPartition sizes mode t

 alignmentT,dissectionT,linearEqsT,matrixT,widgetTreeT :: InterpreterT

 alignmentT tk _ _ (F "file" [F file []]) = loadWidgetT tk file
 alignmentT _ sizes _ t = case parseAlignment t of
     			       Just ali -> rturtle $ drawAlignment sizes ali
     			       _ -> zero

 dissectionT tk _ _ (F "file" [F file []]) = loadWidgetT tk file
 dissectionT _ _ _ (Hidden (Dissect quads)) = rturtle $ drawDissection quads
 dissectionT _ _ _ t = case parseList parseIntQuad t of
 			    Just quads -> rturtle $ drawDissection quads
 			    _ -> zero
 
 linearEqsT tk _ _ (F "file" [F file []]) = loadWidgetT tk file
 linearEqsT tk s p (F x [t]) | x `elem` words "bool gauss gaussI" 
 				          = linearEqsT tk s p t
 linearEqsT _ sizes p t = case parseLinEqs t of
 			       Just eqs -> rturtle $ matrixTerm sizes $ g eqs 1
 			       _ -> zero
    where g ((poly,b):eqs) n = map h poly++(str,"=",mkConst b):g eqs (n+1)
			       where h (a,x) = (str,x,mkConst a); str = show n
          g _ _              = []

 matrixT tk sizes spread = f where
    f :: TermS -> MaybeT Cmd Picture
    f (Hidden (BoolMat dom1 dom2 pairs@(_:_))) 
	 	       = rturtle $ matrixBool sizes dom1 dom2 $ deAssoc0 pairs
    f (Hidden (ListMat dom1 dom2 trips@(_:_))) 
	 	       = rturtle $ matrixList sizes dom1 dom $ map g trips where
				            g (a,b,cs) = (a,b,map leaf cs)
				            dom = mkSet [b | (_,b,_:_) <- trips]
    f (Hidden (ListMat2 dom trips@(_:_))) 
	 	       = rturtle $ matrixList sizes dom dom $ map g trips where
			                    g (a,b,cs) = (a,b,map mkStrPair cs)
    f (Hidden (ListMat2L dom trips@(_:_))) 
	 	       = rturtle $ matrixList sizes dom dom $ map g trips where
			                    g (a,b,cs) = (a,b,map mkStrLPair cs)
    f t | just u = do case u of Just bins@(bin:_) 
   	 			  -> let (arr,k,m) = karnaugh (length bin)
			                 g = binsToBinMat bins arr
					 ts = [(show i,show j,F (g i j) []) | 
					       i <- [1..k], j <- [1..m]]
           	                     rturtle $ matrixTerm sizes ts
           	                _ -> zero
		   where u = parseBins t
    f (F _ []) = zero
    f (F "file" [F file []]) = loadWidgetT tk file
    f (F "pict" [F _ ts])    = do case mapM parseConsts2Term ts of
    				  Just ts -> rturtle $ matrixWidget sizes spread 
				                     $ deAssoc3 ts
				  _ -> zero
    f (F _ ts) | just us     = rturtle $ matrixBool sizes dom1 dom2 ps where
				                    us = mapM parseConsts2 ts
				     	            ps = deAssoc2 $ get us
				     	            (dom1,dom2) = sortDoms ps
    f (F _ ts) | just us     = rturtle $ matrixList sizes dom1 dom2 trs where
			                          us = mapM parseConsts2Terms ts
				                  trs = deAssoc3 $ get us
				                  (dom1,dom2) = sortDoms2 trs
    f _                      = zero
	 
 widgetTreeT tk _ _ (F "file" [F file []]) = do w <- lift $ loadWidget tk file
 					        return [w]
 widgetTreeT _ sizes spread t = return [WTree $ f [] t] where
   f :: [Int] -> TermS -> TermW
   f p (F "<+>" ts)        = F Skip $ zipWithSucs f p ts
   f p (F "widg" ts@(_:_)) = F w $ zipWithSucs f p $ init ts where
			                 v = expand 0 t $ p++[length ts-1]
				         w = case widgets sizes spread v of
				                  Just [v] -> v
				                  _ -> text0 sizes $ showTerm0 v
   f p (F x ts)            = F (text0 sizes x) $ zipWithSucs f p ts
   f _ (V x)               = V $ if isPos x then posWidg x else text0 sizes x
   f _ _        	   = F (text0 sizes "blue_hidden") []

 type Interpreter = Sizes -> Pos -> TermS -> Maybe Picture
 
 jturtle :: TurtleActs -> Maybe Picture
 jturtle = Just . single . turtle1
 
 jfile = Just . single . File_

-- searchPic eval sizes spread t recognizes the maximal subtrees of t that are
-- interpretable by eval and combines the resulting pictures into a single one.

-- solPic sig eval sizes spread t recognizes the terms of a solution t that are
-- interpretable by eval and combines the resulting pictures into a single one.

-- searchPic and solPic are used by Ecom.

 searchPic :: Interpreter -> Interpreter
 searchPic eval sizes spread t = g [] $ expand 0 t []
                      where g p t = case eval sizes spread t of
	   		                 pict@(Just _) -> pict
					 _ -> do F _ ts <- Just t
					         concatJust $ zipWithSucs g p ts
					      
 solPic :: Sig -> Interpreter -> Interpreter
 solPic sig eval sizes spread t = do sol <- parseSol (solAtom sig) t
    			             let f = eval sizes spread . getTerm
    			             concatJust $ map f sol

 partition :: Int -> Interpreter
 partition mode sizes _ = f where f (F "file" [F file []]) = jfile file
                                  f t = jturtle $ drawPartition sizes mode t

 alignment,dissection,linearEqs,matrix,widgetTree,widgets :: Interpreter

 alignment sizes _ = f
   where f (F "file" [F file []]) = jfile file
         f t 	                  = do ali <- parseAlignment t
                                       jturtle $ drawAlignment sizes ali

 dissection _ _ (F "file" [F file []])   = jfile file
 dissection _ _ (Hidden (Dissect quads)) = jturtle $ drawDissection quads
 dissection _ _ t 	                 = do quads <- parseList parseIntQuad t
	                                      jturtle $ drawDissection quads
 linearEqs sizes _ = f
   where f (F "file" [F file []]) = jfile file
         f (F x [t]) | x `elem` words "bool gauss gaussI" = f t
         f t 			  = do eqs <- parseLinEqs t
	 			       jturtle $ matrixTerm sizes $ g eqs 1
         g ((poly,b):eqs) n = map h poly++(str,"=",mkConst b):g eqs (n+1)
			      where h (a,x) = (str,x,mkConst a); str = show n
         g _ _              = []

 matrix sizes spread = f
   where f (Hidden (BoolMat dom1 dom2 pairs@(_:_)))
	 			  = jturtle $ matrixBool sizes dom1 dom2 
				  	    $ deAssoc0 pairs
	 f (Hidden (ListMat dom1 dom2 trips@(_:_)))
	 			  = jturtle $ matrixList sizes dom1 dom 
				    	    $ map g trips
				    where g (a,b,cs) = (a,b,map leaf cs)
				          dom = mkSet [b | (_,b,_:_) <- trips]
	 f (Hidden (ListMat2 dom trips@(_:_)))
	 			  = jturtle $ matrixList sizes dom dom 
				  	    $ map g trips
			            where g (a,b,cs) = (a,b,map mkStrPair cs)
         f (Hidden (ListMat2L dom trips@(_:_)))
	 			  = jturtle $ matrixList sizes dom dom 
				  	    $ map g trips
			            where g (a,b,cs) = (a,b,map mkStrLPair cs)
   	 f t | just u             = do bins@(bin:_) <- u
	 			       let (arr,k,m) = karnaugh (length bin)
			                   g = binsToBinMat bins arr
					   ts = [(show i,show j,F (g i j) []) | 
					   	 i <- [1..k], j <- [1..m]]
           	                       jturtle $ matrixTerm sizes ts
		                    where u = parseBins t
         f (F _ [])               = Nothing
         f (F "file" [F file []]) = jfile file
         f (F "pict" [F _ ts])    = do ts <- mapM parseConsts2Term ts
	 			       jturtle $ matrixWidget sizes spread 
				               $ deAssoc3 ts
         f (F _ ts) | just us     = jturtle $ matrixBool sizes dom1 dom2 ps
				    where us = mapM parseConsts2 ts
				     	  ps = deAssoc2 $ get us
				     	  (dom1,dom2) = sortDoms ps
         f (F _ ts) | just us     = jturtle $ matrixList sizes dom1 dom2 trs
			            where us = mapM parseConsts2Terms ts
				          trs = deAssoc3 $ get us
				          (dom1,dom2) = sortDoms2 trs
         f _                      = Nothing
	 
 widgetTree _ _ (F "file" [F file []]) = jfile file
 widgetTree sizes spread t 	       = Just [WTree $ f [] t] 
  where f :: [Int] -> TermS -> TermW
        f p (F "<+>" ts)        = F Skip $ zipWithSucs f p ts
        f p (F "widg" ts@(_:_)) = F w $ zipWithSucs f p $ init ts
			          where v = expand 0 t $ p++[length ts-1]
				        w = case widgets sizes spread v of
				                 Just [v] -> v
						 _ -> text $ showTerm0 v
        f p (F x ts) = F (text x) $ zipWithSucs f p ts
	f _ (V x)    = V $ if isPos x then posWidg x else text x
	f _ _        = F (text "blue_hidden") []
        text = text0 sizes

 widgets sizes@(n,width) spread t = f black t
  where next = nextColor 1 $ depth t
        f c (F "$" [t,u]) | just tr
	                       = do [w] <- fs c u; Just [get tr w]
				 where tr = widgTrans t
        f c (F x []) | x `elem` words "TR SQ PE PY CA HE LB RB LS RS PS"
	                       = Just [mkTrunk c x]
        f c (F x [n]) | x `elem` fractals 
   			       = do n <- parsePnat n; jturtle $ fractal x n c
        f c (F "anim" [t])     = do pict <- fs c t
				    jturtle $ init $ init $ concatMap onoff pict
        f c (F "arc" [r,a])    = do r <- parseReal r; a <- parseReal a
				    Just [Arc (st0 c) Perimeter r a]
	f c (F "bar" [i,h])    = do i <- parseNat i; h <- parsePnat h
				    guard $ i <= h; jturtle $ bar sizes n i h c
 	f c (F x [t]) | z == "base"    
			       = do [w] <- fs c t 
			            w' <- mkBased (notnull mode) c w
				    Just [w']
				 where (z,mode) = splitAt 4 x
	
	-- Based widgets are polygons with a horizontal line of 90 pixels 
	-- starting in (90,0) and ending in (0,0). mkBased and mkTrunk generate
	-- based widgets.

        f c (F x [n,r,a]) | z == "blos"
	  		       = do hue:mode <- Just mode
			            hue <- parse nat [hue]
				    m <- search (== mode) leafmodes
	 		            n <- parsePnat n; r <- parseReal r
				    a <- parseReal a
				    let next1 = nextColor hue n
					next2 = nextColor hue $ 2*n
				    if m < 4 then
				       jturtle $ blossom next1 n c 
				    	       $ case m of 
					              0 -> \c -> leafD r a c c
						      1 -> \c -> leafA r a c c
						      2 -> \c -> leafC r a c c
						      _ -> leafS r a
				    else jturtle $ blossomD next2 n c
				    		 $ case m of 4 -> leafD r a
						 	     5 -> leafA r a
						 	     _ -> leafC r a
			         where (z,mode) = splitAt 4 x
        f c (F x [n]) | z == "cantP"   
	 		       = do mode <- search (== mode) pathmodes
	 			    n <- parsePnat n
				    Just [path0 c mode $ map fromInt2 $
				          take (n*n) $ iterate (cantor n) (0,0)]
	 		         where (z,mode) = splitAt 5 x
        f c (F "center" [t])   = do [w] <- fs c t; Just [shiftWidg (center w) w]
        f c (F "chord" [r,a])  = do r <- parseReal r; a <- parseReal a
				    Just [Arc (st0 c) Chord r a]
        f c (F "chordL" [h,b]) = do h <- parseReal h; b <- parseReal b
				    jturtle $ chord True h b c
        f c (F "chordR" [h,b]) = do h <- parseReal h; b <- parseReal b
				    jturtle $ chord False h b c
        f c (F "circ" [r])     = do r <- parseReal r; Just [Oval (st0 c) r r]
	f _ (F "colbars" [c])  = do c <- parseColor c
	 			    jturtle $ colbars sizes n c
 	f c (F "dark" [t])     = do pict <- fs c t
				    Just $ map (shiftLight $ -16) pict
	f c (F "$" [F "dots" [n],t])
	                       = do n <- parsePnat n; pict <- fs c t
	 			    Just $ dots n pict
 	f c (F "fadeB" [t])    = do [w] <- fs c t; jturtle $ fade False w
 	f c (F "fadeW" [t])    = do [w] <- fs c t; jturtle $ fade True w
 	f c (F "fast" [t])     = do pict <- fs c t; Just $ map fast pict
        f c (F "fern2" [n,d,r])       
	                       = do n <- parsePnat n; d <- parseReal d
	 			    r <- parseReal r; jturtle $ fern2 n c d r
        f c (F "file" [F file []]) 
        		       = jfile file
 	f c (F "flash" [t])    = do [w] <- fs c t; jturtle $ flash w
        f c (F "flipH" [t])    = do pict <- fs c t; Just $ flipPict True pict
        f c (F "flipV" [t])    = do pict <- fs c t; Just $ flipPict False pict
        f c (F "$" [F "flower" [mode],u])
	 		       = do mode <- parseNat mode; pict <- fs (next c) t
				    jturtle $ flower c mode pict
  	f c (F "fork" [t])     = do pict <- fs c t; guard $ all isTurtle pict
				    jturtle $ tail $ concatMap h pict
				 where h (Turtle _ _ as) = widg New:as
				       h _               = []
 	f c (F x [t]) | z == "frame"   
	                       = do mode <- search (== mode) pathmodes
				    pict <- fs c t
				    Just $ map (addFrame c mode) pict
				 where (z,mode) = splitAt 5 x
	f c (F "gif" [F file [],b,h]) 
			       = do b <- parseReal b; h <- parseReal h
				    Just [Gif c p0 file b h]
	f c (F "gifs" [d,n,b,h]) 
	                       = do d <- parseConst d; n <- parsePnat n
	 		            b <- parseReal b; h <- parseReal h
				    let gif i = Gif c p0 (d++fileSeparator:d++
					                  '_':show i) b h
				    Just $ map gif [1..n]
        f c (F "grav" [t])     = do [w] <- fs c t
				    Just [shiftWidg (gravity w) w]
        f c (F "$" [F "grow" [t],u])
	 		       = do [w] <- fs c t; pict <- fs (next c) u
				    jturtle $ grow id (updCol c w) 
				            $ map getActs pict
	f c (F "$" [F "growT" [t,u],v])
	 		       = do tr <- widgTrans t; [w] <- fs c u
			            pict <- fs (next c) v
				    jturtle $ grow tr (updCol c w) 
				            $ map getActs pict
	f c (F x [n]) | z == "hilbP"   
	 		       = do mode <- search (== mode) pathmodes
	 			    n <- parsePnat n
				    Just [turtle0 c $ hilbert n East]
	 			 where (z,mode) = splitAt 5 x
        f c (F x [t]) | z == "hue"     
	                       = do acts <- parseList' (parseAct c) t
			            hue <- search (== hue) huemodes
				    let acts' = mkHue (nextColor $ hue+1) c acts
				    Just [turtle0 c acts']
				 where (z,hue) = splitAt 3 x
	f c (F x [t]) | z == "join"
	 		       = do mode <- parse pnat mode
			            guard $ mode `elem` [6..14]; pict <- fs c t
				    Just [mkTurt p0 1 $ extendPict mode pict]
				 where (z,mode) = splitAt 4 x
        f c (F x [r,a]) | y == "leaf" 
	 		       = do m <- search (== mode) leafmodes
	 		            r <- parseReal r; a <- parseReal a
				    let c' = complColor c
				    jturtle $ case m of 0 -> leafD r a c c
				       		        1 -> leafA r a c c
							2 -> leafC r a c c
							3 -> leafS r a c
							4 -> leafD r a c c'
							5 -> leafA r a c c'
							_ -> leafC r a c c'
				 where (y,mode) = splitAt 4 x
 	f c (F "light" [t])    = do pict <- fs c t
	 		 	    Just $ map (shiftLight 21) pict
        f _ (F "matrix" [t])   = matrix sizes (0,0) t
        f c (F "$" [F x [n],t]) | z == "morph" 
	 		       = do hue:mode <- Just mode
			            hue <- parse nat [hue]
				    guard $ hue `elem` [1,2,3]
	 		            mode <- search (== mode) pathmodes
	 		            n <- parsePnat n; pict <- fs c t
				    Just $ morphPict mode hue n pict 
				 where (z,mode) = splitAt 5 x
        f _ (F "new" [])       = Just [New]
        f c (F "oleaf" [n])    = do n <- parsePnat n; jturtle $ oleaf n c
 	f c (F x [n,d,m]) | z == "owave" 
	 		       = do mode <- search (== mode) pathmodes
				    n <- parsePnat n; d <- parseReal d
				    m <- parseInt m
				    jturtle $ owave mode n d m c
			         where (z,mode) = splitAt 5 x
 	f c (F "outline" [t])  = do pict <- fs c t; Just $ outline pict
        f c (F "oval" [rx,ry]) = do rx <- parseReal rx; ry <- parseReal ry
				    Just [Oval (st0 c) rx ry]
	f c (F x ps) | z == "path"    
	 		       = do mode <- search (== mode) pathmodes
				    ps@((x,y):_) <- mapM parseRealReal ps
				    let h (i,j) = (i-x,j-y)
		                    Just [path0 c mode $ map h ps]
				 where (z,mode) = splitAt 4 x
	f c (F x rs@(_:_)) | z == "peaks" 
	 	               = do m:mode <- Just mode
				    mode <- search (== mode) polymodes
                                    rs <- mapM parseReal rs
				    guard $ head rs /= 0
				    jturtle $ peaks (m == 'I') mode c rs
				 where (z,mode) = splitAt 5 x
 	f c (F x (n:rs@(_:_))) | z == "pie" 
	 		       = do mode:hue <- Just mode
			            let m = case mode of 'A' -> Perimeter
				              	         'C' -> Chord
							 _ -> Pie
				    hue <- search (== hue) huemodes
			            n <- parsePnat n; rs <- mapM parseReal rs
				    jturtle $ pie m (nextColor $ hue+1) c 
				    	    $ concat $ replicate n rs
				  where (z,mode) = splitAt 3 x
	f _ (F "pile" [h,i])   = do h <- parsePnat h; i <- parseNat i
	 			    guard $ i <= h; jturtle $ pile h i
  	f _ (F "pileR" [t])    = do h:is <- parseList parseNat t
	 			    guard $ all (< h) is; jturtle $ pileR h is
  	f c (F "$" [F "place" [x,y],t])  
  			       = do [w] <- fs c t; x <- parseReal x
  			            y <- parseReal y
  			            jturtle $ shiftTo (x,y) ++ [widg w]
 	f c (F x [n,d,m]) | z == "plait" 
	 		       = do mode <- search (== mode) pathmodes
				    n <- parsePnat n; d <- parseReal d
				    m <- parsePnat m
				    jturtle $ plait mode n d m c
			         where (z,mode) = splitAt 5 x
	f c (F "$" [F "planar" [n],t])   
	                       = do maxmeet <- parsePnat n; [w] <- fs c t
				    Just [planarWidg maxmeet w]
	f c (F x (n:rs@(_:_))) | z == "poly"
	 	               = do mode <- search (== mode) polymodes
                                    n <- parsePnat n; rs <- mapM parseReal rs
				    let k = n*length rs; inc = 360/fromInt k
				    guard $ k > 1
 			            Just [Poly (st0 c) mode 
				               (take k $ cycle rs) inc] 
				 where (z,mode) = splitAt 4 x
        f c (F "pulse" [t])    = do pict <- fs c t; jturtle $ pulse pict
 	f c t 		       = g c t
	g c (F "rect" [b,h])   = do b <- parseReal b; h <- parseReal h
				    Just [Rect (st0 c) b h]
	g c (F "repeat" [t])   = do pict <- fs c t
				    Just [Repeat $ turtle0B $ map widg pict]
	g c (F "revpic" [t])   = do pict <- fs c t; Just $ reverse pict
 	g c (F "rhomb" [])     = Just [rhombV c]
 	g c (F "$" [F "rotate" [a],t]) 
	 		       = do a <- parseReal a; guard $ a /= 0
	 			    pict <- fs c t; jturtle $ rotatePict a pict
        g c (F "$" [F "scale" [sc],t]) 
	 		       = do sc <- parseReal sc; pict <- fs c t
				    Just $ scalePict sc pict
 	g c (F "$" [F x (n:s),t]) | x `elem` ["shelf","tower","shelfS","towerS"]
	                       = do n <- parsePnat n
			            pict <- fs c t
				    let k = if last x == 'S' then square pict
				    			     else n
					c = if take 5 x == "shelf" then '1' 
								   else '2'
				        h d a b = Just $ fst $ shelf (pict,[]) k 
					               (d,d) a b False ['m',c]
			            case s of 
				    d:s -> d <- parseReal d         -- spacing
					   case s of 
					   a:s -> a <- parseChar a  -- alignment
						  case s of 	    -- centering
						  b:s -> b <- parseChar b
						         h d a $ b == 'C'
					          _ -> h d a False
					   _ -> h d 'M' False
				    _ -> h 0 'M' False
        g _ (F "skip" [])      = Just [Skip]
	g c (F "slice" [r,a])  = do r <- parseReal r; a <- parseReal a
				    Just [Arc (st0 c) Pie r a]
	g c (F "smooth" [t])   = do pict <- fs c t; Just $ smooth pict
	g c (F x [d,m,n,k,t]) | z == "snow"
	 		       = do hue <- search (== mode) huemodes
			            d <- parseReal d; m <- parsePnat m
			            n <- parsePnat n; k <- parsePnat k
				    [w] <- fs c t
				    Just [mkSnow True (hue+1) d m n k w]
 			         where (z,mode) = splitAt 4 x
	g c (F "spline" [t])   = do pict <- fs c t; Just $ splinePict pict
        g c (F "star" [n,r,r'])         
	 		       = do n <- parsePnat n; r <- parseReal r
	 			    r' <- parseReal r'; jturtle $ star n c r r'
  	g c (F "$" [F "table" [n,d],t]) 
	 		       = do n <- parsePnat n; d <- parseReal d
				    pict <- fs c t; Just [table pict d n]
        g c (F "taichi" s)     = jturtle $ taichi sizes s c
	g c (F "text" ts)      = do guard $ notnull strs
				    Just [Text_ (st0 c) n strs $ map width strs]
				 where strs = words $ showTree False 
				 		    $ colHidden $ mkTup ts
        g c (F "tree" [t])     = Just [Tree st0B n c $ mapT h ct]
                                 where ct = coordTree width spread 
                                 		      (20,20) $ colHidden t
			               (_,(x,y)) = root ct
                                       h (a,(i,j)) = (a,fromInt2 (i-x,j-y),
                                       		      width a)
	g c (F "tria" [r])     = do r <- parseReal r; Just [Tria (st0 c) r]
	g c (F "$" [F "turn" [a],t])    
	 		       = do a <- parseReal a; pict <- fs c t
				    Just $ turnPict a pict
        g c (F "turt" [t])     = do acts <- parseList' (parseAct c) t
	 			    Just [turtle0 c acts]
 	g c (F x [n,d,a]) | z == "wave" 
	 		       = do mode <- search (== mode) pathmodes
				    n <- parsePnat n; d <- parseReal d
				    a <- parseReal a
				    jturtle $ wave mode n d a c
			         where (z,mode) = splitAt 4 x
        g _ (F x [t]) | just c = f (get c) t where c = parse color x
	g _ _ 		       = Nothing
	 
        fs c t = do picts <- parseList' (f c) t; Just $ concat picts
	 
 	parseAct c (V x) | isPos x = parseAct c $ getSubterm t $ getPos x
	parseAct c (F "A" [t])     = widgAct True c t
	parseAct _ (F "B" [])      = Just back
 	parseAct _ (F "C" [])      = Just Close
  	parseAct _ (F "D" [])      = Just Draw
 	parseAct _ (F "J" [d])     = do d <- parseReal d; Just $ Jump d
 	parseAct _ (F "L" [])      = Just up
        parseAct _ (F "M" [d])     = do d <- parseReal d; Just $ Move d
 	parseAct c (F "O" [])      = Just $ Open c 0
 	parseAct _ (F "O" [c])     = do c <- parseColor c; Just $ Open c 0
 	parseAct c (F "OS" [])     = Just $ Open c 1
 	parseAct _ (F "OS" [c])    = do c <- parseColor c; Just $ Open c 1
 	parseAct c (F "OF" [])     = Just $ Open c 2
 	parseAct c (F "OFS" [])    = Just $ Open c 3
 	parseAct _ (F "OF" [c])    = do c <- parseColor c; Just $ Open c 4
  	parseAct _ (F "OFS" [c])   = do c <- parseColor c; Just $ Open c 5
 	parseAct _ (F "R" [])      = Just down
	parseAct _ (F "SC" [sc])   = do sc <- parseReal sc; Just $ Scale sc
 	parseAct _ (F "T" [a])     = do a <- parseReal a; Just $ Turn a
 	parseAct c t               = widgAct False c t
	 
	widgAct b c t = do [w] <- fs c t ++ Just [text0 sizes $ showTerm0 t]
	 		   Just $ Widg b w

 huemodes   = "":words "2 3 4 5 6"
 pathmodes  = "":words "S W SW F SF"	
 polymodes  = pathmodes ++ words "R R1 R2 L L1 L2 T T1 T2 LT LT1 LT2"
 trackmodes = words "asc sym ang slo"
 leafmodes  = words "D A C S D2 A2 C2"
			    
 fractals = words "bush bush2 cant cactus dragon fern gras grasL grasA grasC" ++
	    words "grasR hexa hilb koch penta pentaS pytree pytreeA wide"

 depth (F "$" [F "flower" _,t]) = depth t+1
 depth (F "$" [F "grow" _,t])   = depth t+1
 depth (F "$" [F "growT" _,t])  = depth t+1
 depth (F _ ts)                 = maximum $ 1:map depth ts
 depth _	    	        = 1

-- The following widget transformations may occur as arguments of growT (see 
-- widgets). They do not modify the outline of a widget and can thus be applied 
-- to based widgets. 

 widgTrans :: TermS -> Maybe WidgTrans
 widgTrans t = f t
  where f (F "." [t,u])       = do tr1 <- widgTrans t; tr2 <- widgTrans u
	   		           Just $ tr1 . tr2
        f (F x [F mode []]) | init z == "trac" 
	                      = do guard $ typ `elem` trackmodes
			           m <- search (== m) pathmodes 
				   hue <- search (== hue) huemodes
				   let h = if last z == 'c' then coords
				   			    else gravity
			           Just $ track h typ m $ nextColor $ hue+1
			        where (z,hue) = splitAt 5 x
				      (typ,m) = splitAt 3 mode
        f (F x (n:s)) | z == "rainbow" 
	     		      = do n <- parsePnat n
			           hue <- search (== hue) huemodes
				   let next = nextColor (hue+1) n
			           if null s then Just $ rainbow n 0 0 next
			           else [a,d] <- mapM parseReal $ take 2 s
				        Just $ rainbow n a d next
			        where (z,hue) = splitAt 7 x
        f (F "shine" (i:s))   = do i <- parseInt i
				   guard $ abs i `elem` [1..42]
				   if null s then Just $ shine i 0 0
				             else [a,d] <- mapM parseReal s
				                  Just $ shine i a d
        f (F "inCenter" [tr]) = do tr <- widgTrans tr; Just $ inCenter tr
	f _		      = Nothing

-- wTreeToBunches is used by arrangeGraph, concatGraphs and newPaint (see below)
		    
 wTreeToBunches :: String -> Point -> Float -> TermW -> Picture
 wTreeToBunches mode spread@(hor,ver) grade t = w:ws2
   where w:ws = bunches (if head mode == 'a' then chgY 0 ct else ct) pt
         ct = F (v,p0) $ subterms $ transTree2 (-x,-y) ct0
         (pt,_) = preordTerm black (const id) t0
	 (v,(x,y)) = root ct0
	 ct0 = coordWTree (hor,ver0) (20,20) t0
         (t0,ver0) = if mode `elem` words "t2 a2 r5 r6 r7 r8"
		     then (mapT (chgPoss $ isSkip $ root t) $ addControls t,
		           ver/2) 
		     else (t,ver)
         chgPoss b (Text_ _ _ [x] _) | isPos x 
		      = posWidg $ "pos "++unwords (map show q)
                        where p = concatMap (\n->[n,0]) $ getPos x
		              q = if b then context 1 p else p
         chgPoss _ w = w
         addControls (F w ts) = F w (map h ts)
			        where h = if isSkip w then addControls else g
			              g t@(V (Text_ _ _ [x] _)) | isPos x = t
	 		              g t = F (Dot red p0) [addControls t]
	 addControls t 	     = t
         bunches :: TermWP -> Term Int -> Picture
         bunches (F (w,p) cts) (F _ pts) = Bunch (moveWidg p w) (map root pts):
				           concat (zipWith bunches cts pts)
         bunches (V (Text_ _ _ [x] _,p)) _ | isPos x 
	 			         = [Bunch (Dot red p) [root t]]
				           where t = getSubterm pt $ getPos x
 	 bunches (V (w,p)) _             = [Bunch (moveWidg p w) []]
	 chgY i (F (w,(x,y)) cts) = F (w,(x,vshift!!i)) $ map (chgY (i+1)) cts
	 chgY i (V (w,(x,y)))     = V (w,(x,vshift!!i))
	 vshift = shiftW maxminy ver0 $ map f [0..height ct-1]
         f = (widgFrame *** ycoord) . turtle0B . map (Widg True) . row
	 row n = zipWith moveWidg ps ws
	     where (ws,ps) = unzip [label ct p | p <- allPoss ct, length p == n]
         [h,c] = mode; n = parse pnat [c]; m = get n
   	 p@(xp,_) = coords w
	 ws1 = if h == 'r' && just n && m `elem` [1..8] then map (rot m) ws 
						        else ws
	 ws2 = if grade == 0 then ws1 else map rotAll ws1
	 rot 1 v = moveWidg (rotate p (grad1 z) (xp,y)) v where (z,y) = coords v
	 rot 2 v = moveTurn True (rotate p a (xp,y)) a v  where (z,y) = coords v
	 						        a = grad1 z
         rot 3 v = moveWidg (rotate p (grad2 v y) (xp,y)) v where y = ycoord v
         rot 4 v = moveTurn True (rotate p a (xp,y)) a v    where y = ycoord v
	 					                  a = grad2 v y
	 rot m v = rot (m-4) v
         rotAll v = moveWidg (rotate p grade $ coords v) v
                 -- moveTurn True (...) grade v
 	 left = op (-); right = op (+); op f w = f (xcoord w) $ rxNode w
	 (minw,maxw) = foldl f (w,w) ws
               where f uv@(u,v) w = if left w < left u then (w,v)
	     		            else if right w > right v then (u,w) else uv
	 minx = left minw-hor/2; maxx = right maxw+hor/2
	 grad1 z = case gauss eqs of 
	                Just eqs | all g eqs 
		          -> let [a,b,c] = map snd (sort (<) eqs) in a*z*z+b*z+c
		        _ -> error "gauss"
	           where g ([(1,_)],_) = True; g _ = False; c = (1,"c")
		         eqs = [([(minx*minx,"a"),(minx,"b"),c],xp-180),
		                ([(xp*xp,"a"),(xp,"b"),c],xp),
		                ([(maxx*maxx,"a"),(maxx,"b"),c],xp+180)]
	 grad2 v y = 360*fromInt (getInd v vs)/fromInt (length vs)
	             where vs = sort rel [w | w <- ws, y == ycoord w]
		  	   rel v w = xcoord v > xcoord w

 shiftW maxmin d (x:xs) = fst $ foldl f ([0],x) xs
       where f (s,(fv,cv)) w@(fw,cw) = (s++[last s+abs (rv-cv)+d+abs (cw-lw)],w) 
                                       where (rv,lw) = maxmin (fv,fw)

 maxminx ((_,_,xv,_),(xw,_,_,_)) = (xv,xw)
 maxminy ((_,_,_,yv),(_,yw,_,_)) = (yv,yw)
 
 rxNode w = (x'-x)/2 where (x,_,x',_) = widgFrame w
 			      
-- coordWTree (hor,ver) p t adds coordinates to the nodes of t such that p is 
-- the leftmost-uppermost corner of the smallest rectangle enclosing t.
-- hor is the horizontal space between adjacent subtrees. ver is the vertical 
-- space between adjacent tree levels.

 coordWTree :: Point -> Point -> TermW -> TermWP
 coordWTree _ p (V w)                       = V (w,add1 p $ rxNode w)
 coordWTree _ p (F w [])                    = F (w,add1 p $ rxNode w) []
 coordWTree spread@(hor,ver) (x,y) (F w ts) = if bdiff <= 0 then ct' 
                                              else transTree1 (bdiff/2) ct'
                     where bdiff = rxNode w-foldT f ct+x
		           f (w,(x,_)) = maximum . ((x+rxNode w):)
			   hdiff = height w+maximum (map (height . root) ts)
			   height w = y'-y where (_,y,_,y') = widgFrame w
	                   ct:cts = map (coordWTree spread (x,y+hdiff/2+ver)) ts
			   cts' = transWTrees hor [ct] cts
			   ct' = F (w,((g (head cts')+g (last cts'))/2,y)) cts'
			   g (V (_,(x,_)))   = x
			   g (F (_,(x,_)) _) = x

-- transWTrees hor cts0 cts1 orders the trees of cts0++cts1 horizontally with
-- a horizontal space of hor units between adjacent trees. transTrees takes into
-- account the possibly different heights of adjacent trees by shifting them to
-- the left or to the right such that nodes on low levels of a tree may occur
-- below a neighbour with fewer levels.
-- offset cts left computes the offset by which the trees of cts must be shifted
-- in order to avoid that they overlap a neighbour with left margins left.

 transWTrees :: Float -> [TermWP] -> [TermWP] -> [TermWP]
 transWTrees hor = f
       where f us (t:ts) = if d < 0 then f (map (transTree1 $ -d) us++[t]) ts 
                           else f (us++[transTree1 d t]) $ map (transTree1 d) ts
                           where d = maximum (map h us)+hor -- h (last us)+hor
				 h u = f (+) maximum u-f (-) minimum t
			               where f = g $ min (height t) $ height u
             f us _      = us
	     g _ op _ (V (w,(x,_)))    = h op w x
	     g 1 op _ (F (w,(x,_)) _)  = h op w x
 	     g n op m (F (w,(x,_)) ts) = m $ h op w x:map (g (n-1) op m) ts
	     h op w x = op x $ rxNode w

-- graphToTree is used by arrangeGraph and showInSolver (see below).

 graphToTree :: Graph -> TermS
 graphToTree graph = eqsToGraph [] eqs
    where (eqs,_) = relToEqs 0 $ map f $ propNodes $ fst graph
          f i = (show i,[show $ last path | k:path <- buildPaths graph, k == i])

-- MORPHING, SCALING and FRAMING

 morphPict :: Int -> Int -> Int -> Picture -> Picture
 morphPict mode m n ws = concat $ zipWith f (init ws) $ tail ws
  where f v w = map g [0..n-1]
	        where [ps,qs] = map (getFramePts False) [v,w]
		      diff = length ps-length qs
		      ps' = adaptLength (-diff) ps
		      qs' = adaptLength diff qs
		      g i = path0 (hue m (getCol v) n i) mode $ 
		      	          zipWith morph ps' qs'
		           where morph (xv,yv) (xw,yw) = (next xv xw,next yv yw)
			         next x z = (1-inc)*x+inc*z
			         inc = fromInt i/fromInt n
 
 scaleGraph :: Float -> Graph -> Graph
 scaleGraph sc (pict,arcs) = (scalePict sc pict,arcs)

 scalePict :: Float -> Picture -> Picture
 scalePict 1  = id
 scalePict sc = map $ scaleWidg sc

-- scaleWidg sc w scales w by multiplying its vertices/radia with sc. 
-- Dots, gifs and texts are not scaled. 

 scaleWidg 1  w                    = w
 scaleWidg sc (Arc st t r a)       = Arc st t (r*sc) a
 scaleWidg sc (Bunch w is)         = Bunch (scaleWidg sc w) is
 scaleWidg sc (Fast w)             = Fast $ scaleWidg sc w
 scaleWidg sc (Oval st rx ry)      = Oval st (rx*sc) $ ry*sc
 scaleWidg sc (Path st n ps)       = Path st n $ map (apply2 (*sc)) ps
 scaleWidg sc (Poly st n rs a)     = Poly st n (map (*sc) rs) a 
 scaleWidg sc (Rect st b h)        = Rect st (b*sc) $ h*sc
 scaleWidg sc (Repeat w)           = Repeat $ scaleWidg sc w
 scaleWidg sc (Tree st n c ct)     = Tree st n c $ mapT3 (apply2 (*sc)) ct
 scaleWidg sc (Tria st r)          = Tria st $ r*sc
 scaleWidg sc (Turtle st sc' acts) = Turtle st (sc*sc') acts
 scaleWidg _ w 			   = w

 pictFrame pict = foldl f (0,0,0,0) $ indices_ pict
	          where f bds = minmax4 bds . widgFrame . (pict!!)

-- widgFrame w returns the leftmost-uppermost and rightmost-lowermost
-- coordinates of the smallest rectangle that encloses w. widgFrame is used by
-- scaleAndDraw (see above), addFrame and shelf (see below).

 widgFrame (Turtle st sc acts) = turtleFrame st sc acts
 widgFrame w                   = minmax $ coords w:getFramePts True w

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
        f (ps,s@((p,a,sc):_)) (Scale sc') = (ps,(p,a,sc*sc'):s)
        f (ps,(p,a,sc):s) (Turn b)        = (ps,(p,a+b,sc):s)
        f (ps,s@(st:_)) (Widg b w)        = (g b ps st w,s)
        f (ps,s@(st:_)) _                 = (ps,st:s)
	g b ps (p,a,sc) w = if l == r then ps else l:r:ps
	                 where (l,r) = ((x1,y1),(x2,y2))
		               (x1,y1,x2,y2) = minmax $ getFramePts True 
		 				      $ moveTurnScale b p a sc w

-- PICTURE operators

 movePict :: Point -> Picture -> Picture
 movePict = map . moveWidg

 moveWidg :: Point -> WidgTrans
 moveWidg p = updState f where f (_,a,c,i) = (p,a,c,i)

-- transXY (x,y) w moves w x units to the right and y units to the bottom.

 transXY (0,0) w = w
 transXY (a,b) w = moveWidg (x+a,y+b) w where (x,y) = coords w

 turnPict :: Float -> Picture -> Picture
 turnPict = map . turnWidg

 turnWidg :: Float -> WidgTrans
 turnWidg a = updState f where f (p,b,c,i) = (p,a+b,c,i)
 
 moveTurn :: Bool -> Point -> Float -> WidgTrans
 moveTurn True p a = turnWidg a . moveWidg p 
 moveTurn _ p a    = updState f where f (_,_,c,i) = (p,a,c,i)

-- moveTurnScale is used by mkPict and widgFrame (see below).

 moveTurnScale b p a sc = scaleWidg sc . moveTurn b p a
			       
 updCol :: Color -> WidgTrans
 updCol (RGB 0 0 0) = id
 updCol c 	    = updState f where f (p,a,_,i) = (p,a,c,i)
			       
 hueCol :: Int -> Picture -> Picture
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
 
 chgColor :: (Color -> Color) -> WidgTrans
 chgColor f = updState g where g (p,a,c,i) = (p,a,f c,i)

 shiftLight :: Int -> WidgTrans
 shiftLight j = updState f where f (p,a,c,i) = (p,a,c,i+j)

 lightWidg = updState f where f (p,a,c,i) = (p,a,light c,i)

 delPict :: Picture -> Picture
 delPict = map delWidg

 delWidg = updState f where f (p,a,_,_) = (p,a,RGB 1 2 3,0)

 flipPict :: Bool -> Picture -> Picture
 flipPict hor = map f
         where f (Arc (p,a,c,i) t r b)   = Arc (p,new a,c,i) t r $ -b
	       f (Path st n ps)          = Path st n $ map h ps 
	       f (Poly (p,a,c,i) n rs b) = Poly (p,new a,c,i) n rs $ -b
               f (Tria st r) | hor       = Tria st $ -r
	       f (Tree st n c ct)        = Tree st n c $ mapT3 h ct
	       f (Turtle st sc acts)     = Turtle st sc $ if hor then map g acts
					  	          else back:map g acts
	       f (Bunch w is) = Bunch (f w) is       
	       f (Fast w)     = Fast $ f w      
	       f (Repeat w)   = Repeat $ f w
	       f w 	    = w
	       g (Turn a)   = Turn $ -a
	       g (Widg b w) = Widg b $ f w
	       g act        = act
	       h (x,y) = if hor then (x,-y) else (-x,y)
	       new a   = if hor then -a else a+180
	     
 widgArea :: Widget_ -> Float
 widgArea w = area $ if isPict w then head outer else g $ head $ hulls False w
              where (_,_,_,outer,_) = strands [w]
		    g (Path0 _ _ _ ps) = ps    

 outline :: Picture -> Picture
 outline = map $ turtle0B . acts
           where acts w = map widg $ w:if isPict w then map (f c i) outer 
				       		   else map g $ hulls False w
		          where (_,_,_,outer,_) = strands [w]
			        (_,_,c,i) = getState w
		 f c i = Path (p0,0,c,i-16) 2
		 g (Path0 c i _ ps) = f c i ps
	     
 dots :: Int -> Picture -> Picture
 dots n = map $ turtle0B . acts
  where acts w = widg w:if isPict w then concatMap (f c i) outer 
				    else concatMap g $ hulls False w
		 where (_,_,_,outer,_) = strands [w]
		       (_,_,c,i) = getState w
        f c i = h $ Oval (p0,0,c,i-16) 5 5
	g (Path0 c i _ ps) = f c i ps
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
	        f v w = sum (map area $ concat inner)
		       where (_,inner,_,_,_) =
		              strands [turtle0B $ filter (`elem` (v:w:as)) acts]
                pairs (v:ws) = [(v,w) | w <- ws, f v w > fromInt maxmeet] ++
			       pairs ws
	        pairs _      = []	
		
 -- ... = if sum (map area $ concat inner) > fromInt maxmeet then u else w
 --       where u:v:_ = mkPict w; (_,inner,_,_,_) = strands [u,v]
				  			 
 planarAll :: Int -> Graph -> Maybe Widget_ -> [Int] -> Float -> (Graph,[Int])
 planarAll maxmeet (pict,arcs) (Just rect) rectIndices rscale = (graph',is)
                        where Rect (p@(x,y),_,_,_) b h = rect
	                      k:ks = rectIndices
		              w = transXY p $ reduce $ mkTurt (x-b,y-h) rscale 
	      				             $ map (pict!!) rectIndices
			      reduce = scaleWidg (1/rscale) . planarWidg maxmeet
			      graph = removeSub (updList pict k w,arcs) ks
			      (graph'@(pict',_),n) = unTurtG graph rscale (== k)
			      m = length $ fst graph
			      is = k:[m..m+n-1]
			      (x1,y1,x2,y2) = pictFrame $ map (pict'!!) is
                              (b',h') = (abs (x2-x1)/2,abs (y2-y1)/2)
		              r = Rect ((x1+b',y1+h'),0,black,0) b' h'
 planarAll maxmeet (pict,arcs) _ _ scale = 
 			 (fst $ unTurtG graph scale $ const True,[])
                         where graph = ([reduce $ mkTurt p0 scale pict],[[]])
		               reduce = scaleWidg (1/scale) . planarWidg maxmeet
			       
 smooth :: Picture -> Picture		   -- uses Tcl's splining
 smooth = map f
         where f (Path st m ps)   | m `elem` [0,2,4] = Path st (m+1) ps
      	       f (Poly st m rs b) | m `elem` [0,2,4] = Poly st (m+1) rs b
	       f (Rect st@((x,y),_,c,_) b h) = Path st (filled c+1) $ last ps:ps
      				    where ps = [(x2,y1),(x2,y2),(x1,y2),(x1,y1)]
					  x1 = x-b; y1 = y-h; x2 = x+b; y2 = y+h
	       f (Tria st@((x,y),_,c,_) r)   = Path st (filled c+1) $ last ps:ps
      				    where ps = [(x+lg,z),(x-lg,z),(x,y-r)]
         		                  lg = r*0.86602       -- r*3/(2*sqrt 3) 
							       -- sidelength/2
	                                  z = y+lg*0.57735     -- y+lg*sqrt 3/3
	       f (Turtle st sc acts) = Turtle st sc $ map g acts
	       f (Bunch w is)        = Bunch (f w) is
	       f (Fast w)            = Fast $ f w
	       f (Repeat w)          = Repeat $ f w
	       f w                   = w
	       g (Open c m) | m `elem` [0,2,4] = Open c $ m+1
	       g (Widg b w) 		       = Widg b $ f w
	       g act        		       = act

 splinePict :: Picture -> Picture	             -- uses Expander's splining
 splinePict = map $ turtle0B . map f . hulls False
              where f (Path0 c i m ps) = widg $ Path (p0,0,c,i) m 
	      			              $ if odd m then ps else spline ps
 
 mkHue next c acts = fst $ foldl f ([],c) acts
       where n = foldl g 0 acts where g n (Widg _ _) = n+1
       				      g n (Open _ _) = n+1
       				      g n Close      = n-1
       				      g n _ 	     = n
	     f (acts,c) act = case act of 
	      		      Widg b w -> (acts++[Widg b $ updCol c w],next n c)
			      _ -> (acts++[act],c)

-- mkSnow b huemode d m n k w computes a Koch snowflake from widget w with turn 
-- mode m in {1,..,6}, depth n and the k copies of scale(i/3)(w) at level 
-- 1<=i<=n revolving around each copy of scale((i-1)/3)(w) at level i-1. 
-- The real number d should be taken from the closed interval [-1,1]. 
-- d affects the radia of the circles consisting of k copies of w.

 mkSnow :: Bool -> Int -> Float -> Int -> Int -> Int -> Widget_ -> Widget_
 mkSnow withCenter huemode d m n k w = 
       if n <= 0 then Skip else mkTurt p0 1 $ color $ if withCenter 
      						      then w:g (n-1) r [p0]
						      else g (n-1) r [p0]
       where color = if huemode < 4 then id else hueCol $ huemode-3
             ps = getFramePts False w
             r = maximum $ map (distance $ gravity w) ps
	     a = 360/fromInt k
	     pict = if isTurtle w then mkPict w else [w]
	     mkWidg [w]  = w
             mkWidg pict = shiftWidg (gravity w') w' where w' = mkTurt p0 1 pict
	     g :: Int -> Float -> Path -> Picture
	     g 0 _ _  = []
             g i r ps = zipWith3 h qs angs flips ++ g (i-1) r' qs
               where qs = concatMap circle ps 
                     r' = r/3
                     circle p@(x,y) = if odd m then s else p:s
		            where s = take k $ iterate (rotate p a) (x,y-r+d*r')
		     pict' = if huemode < 4 
		     	     then zipWith updCol (map (f . getCol) pict) pict
		             else pict
	             f col = hue huemode col n $ n-i
	             h p a b = moveWidg p $ turnWidg a $ scaleWidg (b/3^(n-i)) 
		     			  	       $ mkWidg pict'
             angs | m < 5  = zeros 
	          | m == 5 = iter++angs
	          | True   = 0:iter++concatMap f [1..n-2]
		             where f i = concatMap (g i) iter 
		      	           g 1 a = a:iter
			           g i a = g k a++f k where k = i-1
	     iter = take k $ iterate (+a) 0
	     zeros = 0:zeros
	     flips = case m of 1 -> blink
	                       2 -> 1:take k blink++flips
			       _ -> ones
	     blink = 1: -1:blink
	     ones  = 1:ones
			     
 rainbow :: Int -> Float -> Float -> (Color -> Color) -> WidgTrans
 rainbow n a d next w = turtle1 $ f w n
                        where f _ 0 = []
		              f w i = widg (scaleWidg (fromInt i/fromInt n) w):
				      Turn a:Jump d:f w' (i-1)
			              where w' = chgColor next w

 shine :: Int -> Float -> Float -> WidgTrans
 shine i a d w = turtle1 $ f w n 
                 where f w 0 = []
		       f w i = widg (scaleWidg (fromInt i/fromInt n) w):Turn a:
		       	       Jump d:f (next w) (i-1)
                       next = shiftLight $ 42 `div` i
		       n = abs i

 track :: (Widget_ -> Point) -> String -> Int -> (Int -> Color -> Color) 
 					      -> WidgTrans
 track center mode m next w = if null ps then Skip
                              else turtle1 $ map widg 
		       		           $ pr1 $ fold2 g ([],p,getCol w) qs ks
              where ps@(p:qs) = getAllPoints w
		    ks = case mode of "asc" -> indices_ ps
			     	      "sym" -> sym
				      "ang" -> h angle
				      _   -> h slope
		    n = maximum ks
		    r = center w
                    g (ws,p,c) q i = (ws++[path0 c m [p,q,r,p]],q,next n c)
                    lg1 = length ps-1
		    lg2 = lg1`div`2
		    half = [0..lg2-1]
		    sym = half++if lg1`mod`2 == 0 then reverse half
			                          else lg2:reverse half
                    h rel = map f rels
	                   where rels = fst $ foldl g ([],p) qs
				 g (is,p) q = (is++[rel p q],q)
				 set = qsort (<=) $ mkSet rels
			         f rel = case search (== rel) set of Just i -> i
								     _ -> 0
			         
 wave mode n d a c = Open c mode:Jump (-fromInt n*x):down:Jump (-5):up:
                     border a++border (-a)++[Close]
		     where (x,y) = successor p0 d a
		     	   border a = foldl1 (<++>) (replicate n acts)++
				      [down,Move 10,down]
	                              where acts = [Turn a,Move d,Turn $ -a-a,
				      		    Move d,Turn a]

-- animations
 
 onoff :: Widget_ -> TurtleActs
 onoff w = [wfast w,wait,wfast $ delWidg w]

 rotatePict a pict = take ((2*length pict+2)*round (360/abs a)) acts
	             where acts = wait:map wfast (delPict pict)++Turn a:
		     		  map wfast pict++acts

 fade b = take 168 . if b then f 42 else g 0
          where f i w = if b && i == 0 then g 42 w
	                else wfast w:wait:f (i-1) (shiftLight 1 w)
	        g i w = if not b && i == -42 then f 0 w
		        else wfast w:wait:g (i-1) (shiftLight (-1) w)

 flash = take 100 . f where f w = wfast w:wait:f (chgColor (nextColor 1 50) w)
 
 peaks b mode c rs = if b then take 103 $ f 2 else take 102 $ g (w 36) 35
	 where f i = onoff (w i)++f (i+1) 
	       g v i = wait:wfast (delWidg v):wfast wi:g wi (i-1) where wi = w i
               w i = Poly (st0 c) mode (take k $ cycle rs) $ 360/fromInt k
	             where k = i*length rs
				       
 oscillate :: (Int -> TurtleActs) -> Int -> TurtleActs
 oscillate acts n = take (6*n-2) $ f n
  	            where f 0 = g 1
		    	  f i = onoff (turtle0B $ acts i)<++>f (i-1) 
                          g i = onoff (turtle0B $ acts i)<++>g (i+1) 
 
 pulse pict = oscillate acts 20 
 	      where acts i = map (wfast . scaleWidg (fromInt i/20)) pict
 
 oleaf n c = oscillate acts $ min 33 n
 	     where acts i = leafC (fromInt n) (fromInt i*b) c c
		   b = if n < 33 then 1 else fromInt n/33
 
 owave mode n d m c = oscillate acts $ abs m
 	              where acts i = wave mode n d (fromInt $ signum m*i) c
  
 plait mode n d m c = oscillate acts $ m
 	              where acts i = wave mode n d (fromInt i) c ++
		                     wave mode n d (-fromInt i) (complColor c)

-- table pict d n displays pict as a matrix with n columns and a horizontal and
-- vertical distance of d units between the ANCHORS of adjacent widgets. 
-- table returns an action sequence.

 table pict d n = turtle0B $ concatMap g $ f pict
                  where f [] = []; f s  = take n s:f (drop n s)
	                g pict = open:concatMap h pict++[Close,down,Jump d,up]
	                         where h w = [widg w,Jump d]

-- shelf graph n (dh,dv) align scaled ... mode displays graph as a matrix with n 
-- columns and a horizontal/vertical spacing of dh/dv units between the BORDERS
-- of adjacent widgets. shelf returns a picture (scaled = True) or an action
-- sequence (scaled = False). If mode = "m2", the widget anchors are aligned
-- vertically and the columns according to the value of align (L/M/R). Otherwise
-- the widget anchors are aligned horizontally and the rows according to align.

 shelf :: Graph -> Int -> Point -> Char -> Bool -> Bool -> String -> Graph
 shelf graph@([],_) _ _ _ _ _ _ = graph
 shelf graph@(pict,_) cols d@(dh,dv) align centered scaled mode = 
  case mode of "m1" -> sh graph True False
  	       "m2" -> sh graph False False
	       "c"  -> sh graph True True 
	       _    -> graph
  where lg = length pict; is = [0..lg-1]
        rows = lg `div` cols
	upb = if isCenter mode then maximum levels
	      		       else if lg `mod` cols == 0 then rows-1 else rows
	rowIndices = [0..upb]
	levels = nodeLevels True graph
	levelRow i = [k | k <- is, levels!!k == i]
	sh graph@(pict,arcs) b center =
	 if center 
	 then case searchGet isSkip ws of
                   Just (i,w) -> (w:map (transXY (0,y)) (context i ws),arcs)
			         where y = ycoord w-ycoord (ws!!head (arcs!!i))
	           _ -> (ws,arcs)
         else (if scaled then pict1 b 
	       else [turtle0B $ if centered then actsToCenter acts else acts],
	       arcs)
         where ws = sortR (pict1 True) $ concatMap levelRow rowIndices
	       rowList pict = if isCenter mode then f 0 [] else g pict []
	                 where f i picts = if null r then picts
					   else f (i+1) $ picts++[r]
			                   where r = [pict!!k | k <- levelRow i]
			       g pict picts = if null pict then picts
			      		      else g (drop cols pict) $
					             picts++[take cols pict]
	       row = mkArray (0,upb) $ (if scaled then map $ moveWidg p0 
	       					  else id) . (rowList pict!!) 
	       pict1 b = concatMap (g b f) rowIndices 
	 	       where f x z y = moveWidg $ if b then (x+z,y) else (y,x+z)
	       acts = concat $ concatMap (g b f) rowIndices
	              where f x z y w = [open,Jump $ x',down,Jump $ y',up,
		      		         widg w,Close]
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
-- getSupport is used by releaseButton.

 getSupport :: Graph -> Int -> Int -> Maybe [Int]
 getSupport graph s t = 
       do (_,_:path@(_:_:_)) <- searchGet f $ buildPaths graph; Just $ init path
       where f path = s `elem` path && t `elem` path && g s <= g t
                      where g s = getInd s path

-- pictToWTree is used by newPaint (see above) and concatGraphs (see below).

 pictToWTree :: Picture -> TermW
 pictToWTree pict = case map f pict of [t] -> t
 				       ts -> F Skip $ zipWith g [0..] ts
	         where f (WTree t) = t
		       f w         = F w []
		       g i (F w ts) = F w (map (g i) ts)
		       g i (V (Text_ _ _ [x] _)) | take 4 x == "pos " 
				    = V $ posWidg $ "pos "++unwords (map show p)
				      where p = i:getPos x
		       g _ t        = t

-- concatGraphs is used by addOrRemove and arrangeOrCopy (see above).

 concatGraphs :: Point -> Float -> String -> [Graph] -> Graph 
 concatGraphs _ _ _ []                 = nil2
 concatGraphs _ _ _ [graph]            = graph
 concatGraphs spread grade mode graphs = (concat pictures,foldl g [] edges)
  where (pictures,edges) = unzip $ map (bunchesToArcs . f) graphs
        f graph@(pict,_) = if any isWTree pict then onlyNodes ws else graph
	             where ws = wTreeToBunches m spread grade $ pictToWTree pict
        g arcs = (arcs++) . map (map (+(length arcs)))
	m = if isTree mode then mode else "t1"

-- bunchesToArcs (pict,arcs) removes the bunches of pict and adds their edges to
-- arcs. bunchesToArcs is used by arrangeGraph, concatGraphs, scaleAndDraw and 
-- showInSolver (see above).

 bunchesToArcs graph@(pict,arcs) = (pict2,foldl removeCycles arcs1 cycles)
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

-- addSmoothArc graph (s,t,..) adds a smooth line from s to t together with the 
-- control points of the line. addSmoothArc is used by releaseButton False False 
-- and bunchesToArcs (see above).

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
		     
 arcsToBunches :: Graph -> Picture
 arcsToBunches (Bunch w is:pict,ks:arcs) 
 			        = Bunch w (is`join`ks):arcsToBunches (pict,arcs)
 arcsToBunches (w:pict,is:arcs) = Bunch w is:arcsToBunches (pict,arcs)
 arcsToBunches _                = []

-- buildAndDrawPaths graph transforms the arcs of graph into paths that do not
-- cross the borders of the widgets of pict. buildAndDrawPaths is used by 
-- scaleAndDraw.

 buildAndDrawPaths :: Graph -> [Path]
 buildAndDrawPaths graph@(pict,_) = map f $ buildPaths graph
   	           where f (n:ns) = p':ps++[q']
				    where v = pict!!n
					  w = pict!!last ns
					  p = coords v
				          ps = map (coords . (pict!!)) $ init ns
		            	          q = coords w
					  p' = hullCross (head $ ps++[q],p) v
				          q' = hullCross (last $ p:ps,q) w

-- exchgWidgets pict s t exchanges the positions of nodes s and t in the graph 
-- and in the plane. exchgWidgets is used by releaseButton and arrangeButton.

 exchgWidgets :: Picture -> Int -> Int -> Picture
 exchgWidgets pict s t = updList (updList pict s $ moveWidg (coords v) w) t
				                 $ moveWidg (coords w) v
			 where (v,w) = (pict!!s,pict!!t)

-- exchgPositions graph s t exchanges the positions of nodes s and t of graph in
-- the plane. exchgPositions is used by releaseButton and permutePositions.

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

-- buildPaths graph regards the nodes of each maximal path p of graph consisting
-- of red dots as control points of smooth lines that connect a direct
-- predecessor of p with a direct successor of p. buildPaths is used by
-- graphToTree, subgraph, releaseButton, buildAndDrawPaths and exchgPositions
-- (see above).

 buildPaths :: Graph -> Arcs
 buildPaths graph@(pict,arcs) = connect $ concatMap f $ indices_ pict
   where f i = if isSkip (pict!!i) then [] else [[i,j] | j <- arcs!!i]
 	 connect (path:paths) = connect2 path paths
         connect _            = []
	 connect2 path paths 
	    | hpath == lpath     = path:connect paths
	    | lastdot || headdot = case search2 f1 f2 paths of 
	                           Just (i,True) -> connectC (ipath++paths!!i) i
	                           Just (i,_) -> connectC (paths!!i++tpath) i
		                   _ -> connect paths
	    | True		 = path:connect paths
                         where hpath:tpath = path
			       (ipath,lpath) = (init path,last path)
			       lastdot = isRedDot (pict!!lpath)
			       headdot = isRedDot (pict!!hpath)
			       f1 path = lastdot && lpath == head path
			       f2 path = last path == hpath && headdot
		               connectC path i = connect2 path $ context i paths

 spline :: Path -> Path
 spline ps@(p:_:_:_) = if p == last ps then spline0 True $ init ps
				       else spline0 False ps
 spline ps = ps

-- spline is used by hulls and splinePict.
-- spline0 b ps uses ps as control points for constructing a closed (b = True) 
-- resp. open (b = False) B-spline with degree 3; see Paul Burke, Spline Curves 
-- (http://astronomy.swin.edu.au/~pbourke/curves/spline)
-- or Heinrich MŸller, B-Spline-Technik, Vorlesung Geometrisches Modellieren 
-- (http://ls7-www.cs.tu-dortmund.de).

 spline0 :: Bool -> Path -> Path
 spline0 b ps = first:map f [1..resolution] ++ map g [1..9] ++
  	        [if b then first else ps!!(n-1)]
         where first = f 0; n = length ps; resolution = n*6
	       f i = point $ upb*fromInt i/fromInt resolution 
               g i = point $ upb+fromInt i/10
	       upb = fromInt n-if b then 1 else 3
	       point v = foldl1 add2 $ map h [0..n-1]
	                 where h i = apply2 (*z) $ ps!!i
	                         where z | b && v < u i = blend2 u i $ v-u 0+u n 
		                         | b 	        = blend2 u i v
		     	                 | True         = blend2 t i v 
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

-- hullCross (p1,p2) w computes the crossing of line with w such that p2 agrees
-- with the coordinates of w. 
-- hullCross is used by buildAndDrawPaths, convexPath and drawTrees.

 hullCross :: Line_ -> Widget_ -> Point
 hullCross line@(p1@(x1,y1),p2@(x2,y2)) w = 
      case w of Arc _ _ _ _   -> head hull
                Oval (_,0,_,_) rx ry  -> if p1 == p2 then p2 
			                 else (x2+rx*cos rad,y2+ry*sin rad) 
			                 where rad = atan2' (y1-y2) (x1-x2)
	        Path _ _ ps   -> head $ f $ mkLines ps
		Text_ _ _ _ _ -> mindist p1 hull
		Tree _ _ _ _  -> mindist p1 hull
		_ | isWidg w  -> head hull
		  | isPict w  -> mindist p1 hull
		Bunch w _     -> hullCross line w
		Fast w        -> hullCross line w
		Repeat w      -> hullCross line w
		Saved file w  -> hullCross line w
		w             -> p2
      where hull = f $ concat $ getFrameLns w
            f ls = if null ps then [p2] else map get ps
		   where ps = filter just $ map (crossing (line,p2)) $ addSuc ls

-- crossing line1 line2 returns the crossing point of line1 with line2.
-- crossing is used by crossings, hullCross and interior.

 crossing :: (Line_,Point) -> (Line_,Point) -> Maybe Point
 crossing ((p1@(x1,y1),p2@(x2,y2)),p5) ((p3@(x3,y3),p4@(x4,y4)),p6) =
       do if x1 == x2 then if x3 == x4 then onLine else enclosed q1
	  else if x3 == x4 then enclosed q2
	       else if a1 == a2 then guard $ b1 == b2; onLine else enclosed q
       where a1 = slope p1 p2
	     a2 = slope p3 p4
	     b1 = y1-a1*x1    		      -- p1, p2 and q2 solve y = a1*x+b1
	     b2 = y3-a2*x3    		      -- p3, p4 and q1 solve y = a2*x+b2
	     a = a1-a2
	     q = ((b2-b1)/a,(a1*b2-a2*b1)/a)  -- q solves both equations
	     q1 = (x1,a2*x1+b2)
	     q2 = (x3,a1*x3+b1)
	     enclosed p = do guard $ inFrame p1 p p2 && inFrame p3 p p4; next p
	     onLine = if inFrame p1 p3 p2 then next p3 
		      else if inFrame p1 p4 p2 then next p4
		      else if inFrame p3 p1 p4 then next p1
		      else do guard $ inFrame p3 p2 p4; next p2
	     next p = do guard $ (p /= p2 || inFrame p1 p p5) &&
			 	 (p /= p4 || inFrame p3 p p6)
			 Just p

-- crossings lines1 lines2 returns all triples (p,line1,line2) with line1 in
-- lines1, line2 in lines2 and crossing point p of line1 and line2.
-- crossings is used by strands.

 type Crossing = (Point,(Line_,Line_))

 crossings :: Lines -> Lines -> [Crossing]
 crossings lines1 lines2 = [(get p,(fst line1,fst line2)) | 
 			    line1 <- addSuc lines1, line2 <- addSuc lines2,
			    let p = crossing line1 line2, just p]
 
 addSuc :: Lines -> [(Line_,Point)]
 addSuc [] = []
 addSuc ls = zip ls (map snd $ tail ls) ++
 	     [(line2,if p == fst line1 then snd line1 else p)]
 	     where line1 = head ls; line2 = last ls; p = snd line2

-- interior p lines returns True iff p is located within lines.
-- interior is used by inWidget and strands.

 interior :: Point -> Lines -> Bool
 interior p = odd . length . filter (just . crossing ((p,q),q)) . addSuc 
	      where q = (2000,snd p)

-- strands pict computes the subpaths of the hulls hs of pict that enclose the 
-- intersection resp. union of the elements of hs and connects them.
-- strands is used by dots, extendPict, outline, planarWidg and widgArea. 

 strands :: Picture -> ([(Widget_,Widget_,[Crossing])],[[Path]],[Color],
 						       [Path],[Color])
 strands pict = (hcs,inner,innerCols,outer,map col outer)
       where hs = concatMap (hulls False) pict
             is = indices_ hs
	     (inner,innerCols) = unzip $ map threadsI hcs
	     hcs = [(h1,h2,cs) | i <- is, j <- is, i < j, 
			         let h1 = hs!!i; h2 = hs!!j
			             cs = crossings (getLines h1) $ getLines h2,
			         notnull cs]
             outer = connect $ concatMap threadsO hs
	     add ps pss = if null ps then pss else ps:pss
	     threadsI (h1,h2,cs) = (inner,getColor h1)
		       where inner = connect $ strands b ps1++strands c ps2
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
             threadsO h = add qs pss
		   where sucs p = [r | (h1,h2,cs) <- hcs, 
		   		       (r,((p1,_),(p2,_))) <- cs, 
				       (h,p) `elem` [(h1,p1),(h2,p2)]]
		         (qs,pss,_) = foldl next ([],[],Nothing) $ extend h sucs
			 next (ps,pss,r) p 
			                | p `elem` concatMap (map fst . pr3) hcs
				               = if just r && g (mid (get r) p) 
					         then ([p],ps:pss,Just p)
			     	                 else (p:ps,pss,Just p)
				        | g p  = ([],add ps pss,Nothing)
				        | True = (p:ps,pss,Nothing)
			 g p = any (interior p ||| any (onLine p)) 
			           $ map getLines $ minus1 hs h
			 mid p = div2 . add2 p
 	     extend h sucs = (concatMap f $ init ps)++[last ps]
		       where ps = getPoints h
			     f p = sort rel $ p:sucs p
	     		           where rel r r' = distance p r < distance p r'
             connect (ps:pss) = case search2 ((==) (last ps) . head) 
	     				     ((==) (head ps) . last) pss of
	                             Just (i,True) -> g i $ init ps++pss!!i
	                             Just (i,_)    -> g i $ pss!!i++tail ps
				     _ -> ps:connect pss          
                                where g i = connect . updList pss i
             connect _ 	      = []	           
	     col ps = case searchGet (shares ps . getPoints) hs of
		  	   Just (_,h) -> getColor h; _ -> black
	     getColor (Path0 c _ _ _) = c
		       
-- extendPict is used by widgets and scaleAndDraw.
 
 extendPict :: Int -> Picture -> Picture
 extendPict m pict = case m of 
                          6  -> pict++map center pict
			  7  -> pict++concatMap (map dot . pr3) hcs
			  8  -> pict++zipWithL darkLine innerCols inner
			  9  -> pict++map whiteFill (concat inner)
			  10 -> pict++zipWithL lightFill innerCols inner
			  11 -> pict++evens (zipWithL fill innerCols inner)
			  12 -> pict++zipWith darkLine outerCols outer
			  13 -> pict++fillHoles light
			  _ -> zipWith lightFill outerCols rest++fillHoles id
                where center w = Dot (if any (inWidget p) $ minus1 pict w
				      then grey else black) p where p = coords w 
		      dot = Dot (RGB 0 0 1) . fst
		      (hcs,inner,innerCols,outer,outerCols) = strands pict
		      whiteFill        = path0 white 4
		      darkLine c       = path0 (dark c) 2
		      lightFill c      = path0 (light c) 4
		      fill (RGB 0 0 0) = whiteFill
		      fill c           = path0 c 4
		      fillHoles f = zipWith g [0..] holes
		                    where g i = path0 (f $ hue 1 yellow n i) 4
			                  n = length holes
		      (holes,rest) = split hole outer
		      hole ps = any f $ minus1 outer ps
		                where f qs = all g ps
				             where g p = interior p $ mkLines qs

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
	  | True 	        = q:f qs where g ps = q:sort (<) ps++f qs
	   				       h ps = q:sort (>) ps++f qs
	f qs = qs
        g ps = if lg < 3 then ps
               else if p1 == p2 && q1 == q2 || a == b then left++right
		    else h p2 p1 left++h q1 q2 right
	       where lg = length ps
	             (left,right) = apply2 g $ splitAt (div lg 2) ps
		     minL@((a,_):_) = minima fst left
		     maxL = maxima fst left; minR = minima fst right
		     maxR@((b,_):_) = maxima fst right
		     minY = head . minima snd; maxY = head . maxima snd
		     upperLeft  = h (maxY minL) (maxY maxL) left
		     upperRight = h (maxY minR) (maxY maxR) right
		     lowerLeft  = h (minY maxL) (minY minL) left
		     lowerRight = h (minY maxR) (minY minR) right
		     (p1,q1) = upperTangent upperLeft upperRight
		     (p2,q2) = lowerTangent lowerLeft lowerRight
        h p q ps@(_:_:_) = take (getInd q qs+1) qs 
			   where qs = drop i ps++take i ps; i = getInd p ps
	h _ _ ps         = ps

 upperTangent ps@(p1:_) (q1:qs@(q2:_)) 
			       | slope p1 q1 < slope q1 q2  = upperTangent ps qs
 upperTangent (p1:ps@(p2:_)) qs@(q1:_) 
 			       | slope p1 q1 <= slope p1 p2 = upperTangent ps qs
 upperTangent (p1:_) (q1:_) 				    = (p1,q1)

 lowerTangent (p1:ps@(p2:_)) qs@(q1:_) 
 			       | slope p1 q1 < slope p1 p2  = lowerTangent ps qs
 lowerTangent ps@(p1:_) (q1:qs@(q2:_)) 
 			       | slope p1 q1 <= slope q1 q2 = lowerTangent ps qs
 lowerTangent (p1:_) (q1:_) 				    = (p1,q1)

-- convexPath is used by scaleAndDraw (see above).

 convexPath ps pict = if straight ps then (h ps,ps) else (h $ last qs:qs,qs)
       where qs = convexHull $ sort (<) ps
             f p q = Path0 blue 0 0 [g q p,g p q]
             g p q = hullCross (p,q) $ pict!!get (search ((== q) . coords) pict)
	     h ps = zipWith f ps $ tail ps

-- TURTLE ACTIONS

 colText c (n,width) str = widg $ Text_ (st0 c) n [str] [width str]
 
 blackText = colText black

 rectC c b = widg . Rect (st0 c) b

 halfmax width = (/2) . fromInt . maximum . map width

-- alignments

 drawAlignment sizes@(n,width) t = 
                   case t of Compl x y t -> f x t y red
		             Equal_ [x] t -> f x t x green
			     Equal_ (x:s) t -> f x (Equal_ s t) x green
			     Ins [x] t -> g t x
			     Ins (x:s) t -> g (Ins s t) x
			     Del [x] t -> h x t
			     Del (x:s) t -> h x $ Del s t
			     End s@(_:_) -> drawAlignment sizes $ Del s $ End []
			     _ -> []
  where f x t y color = 
                 JumpA bt:open:blackText sizes x:down:moveDown ht color++
                 open:blackText sizes y:jump t bt++Close:Close:Close:jump t bt++
                 drawAlignment sizes t where bt = halfmax width [x,y]
        g t x = 
            jumpDown ht++JumpA bt:blackText sizes x:jump t bt++Close:move t wa++
	    drawAlignment sizes t where wa = fromInt $ width x; bt = wa/2
        h x t = 
	    jumpDown ht++move t wa++Close:JumpA bt:blackText sizes x:jump t bt++
	    drawAlignment sizes t where wa = fromInt $ width x; bt = wa/2
	ht = fromInt n/2

 jump t bt = if t == End [] then [] else [JumpA bt,Move 30]

 move t bt = if t == End [] then [MoveA bt] else [MoveA bt,Move 30]

 jumpDown ht = [open,down,JumpA ht,Jump 30,JumpA ht,up]

 moveDown ht color = [Open color 0,JumpA ht,Move 30,JumpA ht,up]

-- dissections

 drawDissection quads = concatMap f quads
      where f (x,y,b,h) = [open,Jump x',down,Jump y',up,rectC black b' h',Close]
                          where x' = 10*fromInt x+b'; y' = 10*fromInt y+h'
				b' = 5*fromInt b; h' = 5*fromInt h

 star n c = f $ n+n 
            where a = 180/fromInt n
	          f 0 _ _  = []
	          f n r r' = open:Jump r:Open c 4:Move (-r):Turn (-a):
                             Move r':Close:Close:Turn a:f(n-1) r' r

 taichi sizes s c = [open,circ c 120,down,widg $ Arc (st0 d) Pie 120 180,
		     Jump 60,back,circ d 60,circ c 12,open,jump1,down,jump2,
		     colText c sizes yang,Close,Jump 120,back,circ c 60,
		     circ d 12,open,jump1,down,jump2,colText d sizes yin,Close]
		    where d = complColor c; jump1 = Jump 32; jump2 = Jump 52
		          circ c r = widg $ Oval (st0 c) r r
			  (yin,yang) = case s of t:u:_ -> (root t,root u)
						 [t] -> (root t,"")
						 _ -> ("","")

 blossom next n c acts = open:f (n-1) c++[Close] 
                         where f 0 c = acts c
	                       f i c = acts c++Turn a:f (i-1) (next c)
			       a = 360/fromInt n

 blossomD next n c acts = open:f (n-1) c++[Close] 
                          where f 0 c = acts c $ next c
	                        f i c = acts c c'++Turn a:f (i-1) (next c')
			       	        where c' = next c
			        a = 360/fromInt n
			      
 pie m next c rs = open:f (n-1) c++[Close] 
                   where f 0 c = [act 0 c]
	                 f i c = act i c:Turn b:f (i-1) (next n c)
			 act i c = widg $ Arc (st0 c) m (rs!!i) $ b+0.2
			 b = 360/fromInt n
			 n = length rs

 leafD r a c c' = Open c 4:Turn a:move:g 5
                  where g 0 = Close:Open c' 4:Turn (-a):move:h 5
	                g n = Turn (-b):move:g (n-1)
	                h 0 = [Close]
			h n = Turn b:move:h (n-1)
			move = Move r; b = 2*a/5

 leafA r a c c' = [open,Jump y,down,Jump x,Turn $ b-180,w c,Turn $ -b,
 		   Jump $ 2*x,Turn $ b+180,w c',Close] 
                   where (x,y) = successor p0 r b; b = a/2
	                 w c = widg $ Arc (st0 c) Chord r a
			  
 leafC h b c c' = chord True h b c ++ chord False h b c'

 leafS d a c = Open c 5:go++back:go++[Close]
	       where go = [up,move,down,Move $ 2*d,down,move,up]
		     up = Turn (-a); down = Turn a; move = Move d

 chord left h b c = open:acts++
 		    [Jump $ -r,widg $ Arc (st0 c) Chord r $ 2*a,Close]
	            where r = h^2/(2*b)+b/2; a = angle p0 (r-b,h)
	                  acts = if left then [up,Jump $ 2*h,Turn $ 270+a]
	                                 else [Turn a]

 rhombH = path0 green 5 [p0,(3,-2),(16,0),(3,2),p0]

 rhombV c = path0 c 5 [p0,(-6,-9),(0,-48),(6,-9),p0]

-- growing trees

 mkTrunk :: Color -> String -> Widget_
 mkTrunk c x = path0 c 4 $ p0:ps++[(90,0),p0]
     where ps = case x of "TR" -> [(45,-x1)]			    -- triangle
			  "SQ" -> [(0,-90),(90,-90)]		    -- square
			  "PE" -> [(-x2,-x3),(45,-138.49576),(117.81153,-x3)]	
								    -- pentagon
			  "PS" -> [(-14.079101,-x7),(44.62784,-127.016685),
			           (103.33478,-x7)] 		    -- pentagonS
			  "PY" -> [(0,-90),(36,-135),(90,-90)]      -- pytree
			  "CA" -> [(7.5,-60),(22.5,-90),(67.5,-90),(82.5,-60)]	
								    -- cactus
	                  "HE" -> [(-45,-77.94228),(0,-x4),(90,-x4),(135,-x1)]	
								    -- hexagon
	                  "LB" -> [(-x2,-x3),(62.18847,-x3)]	    -- rhombLB
			  "RB" -> [(27.811527,-x3),(117.81152,-x3)] -- rhombRB
			  "LS" -> [(-72.81154,-x5),(17.188461,-x5)] -- rhombLS
			  "RS" -> [(72.81153,-x6),(162.81152,-x6)]  -- rhombRS
           x1 = 77.94229;  x2 = 27.811533; x3 = 85.595085; x4 = 155.88458
	   x5 = 52.900665; x6 = 52.900673; x7 = 88.89195

 grow :: WidgTrans -> Widget_ -> [TurtleActs] -> TurtleActs
 grow f w branches = widg (f w):
                     concat (zipWith g branches $ mkLines $ getAllPoints w)
                    where g [] _               = []
                          g branch (p@(x,y),q) = open:Jump x:down:Jump y:Turn a:
	   			  	         Scale (d/90):branch++close2
						 where a = angle p q-90
						       d = distance p q

 growM :: Int -> Color -> Widget_ -> [Bool] -> TurtleActs
 growM n c w bs = f n c where f 0 _ = []
                              f i c = grow id (updCol c w) $ map g bs
		                      where g True = f (i-1) $ nextColor 1 n c
				      	    g _    = []

 growA :: Color -> TurtleActs -> [TurtleActs] -> TurtleActs
 growA c acts branches = Open c 4:acts++Close:f acts branches
                where f (turn:Move d:acts) (b:bs) = turn:acts'++Jump d:f acts bs
	    	                      where acts' = if null b then []
	    			                    else Scale (d/90):b++[Close]
	              f _ _ = []

 growAM :: Int -> Color -> TurtleActs -> [Bool] -> TurtleActs
 growAM n c acts bs = f n c 
                      where f 0 _ = []
                            f i c = growA c acts $ map g $ bs
		           	    where g True = f (i-1) $ nextColor 1 n c
			                  g _    = []
						      
 mkBased :: Bool -> Color -> Widget_ -> Maybe Widget_
 mkBased b c w = do guard $ length ps > 2 && p == last ps && d /= 0
 	            Just $ path0 c 4 rs  
	   where ps@(p:_) = getAllPoints w
	         (xs,ys) = unzip ps
		 (rs,d) = basedPts
                 basedPts = (map (apply2 (*(90/d)) . rotate p0 a . sub2 p) rs,d)
		            where rs@(p:qs) = if b then ps else reverse ps
		                  q = last $ init qs
				  d = distance p q
				  a = -angle p q

 flower c mode (w1:w2:w3:w4:w5:_) = widg stick:up:
            case mode of 0 -> jump 0.8 50 60 w1++jump 0.8 8 110 w2++
	  		      jump 0.8 80 120 w3++jump 0.6 12 70 w4++turn 0.8 w5
			 1 -> jump 0.8 72 60 w1++jump 0.8 12 110 w2++
			      jump 0.6 12 70 w3++jump 0.8 54 70 w4++turn 0.6 w5
			 _ -> jump 0.8 40 110 w1++jump 0.8 24 60 w2++
			      jump 0.6 43 110 w3++jump 0.6 43 70 w4++turn 0.6 w5
	    where stick = Path (p0,0,c,-16) 4 [p0,(-4,-8),(0,-150),(4,-8),p0]
	          jump sc n a w = Jump n:open:Turn a:Scale sc:widg w:close2
		  turn sc w = open:Turn 100:Scale sc:widg w:close2
 flower _ _ _ = []

-- fractals

 data Direction = North | East | South | West

 north,east,south,west :: TurtleActs
 north = [up,Move 10,down]
 east  = [Move 10]
 south = [down,Move 10,up]
 west  = [Move $ -10]

 hilbert :: Int -> Direction -> TurtleActs
 hilbert 0 _   = []
 hilbert n dir = 
           case dir of East -> hSouth++east++hEast++south++hEast++west++hNorth
                       West -> hNorth++west++hWest++north++hWest++east++hSouth
		       North -> hWest++north++hNorth++west++hNorth++south++hEast
		       South -> hEast++south++hSouth++east++hSouth++north++hWest
           where hEast = h East; hWest = h West; hNorth = h North
                 hSouth = h South; h = hilbert $ n-1

 hilbshelf :: Int -> [a] -> [a]
 hilbshelf n s = foldl f s $ indices_ s
               where f s' i = updList s' (y*2^n+x) $ s!!i 
		 	      where (x,y) = apply2 (round . (/10)) $ hilbPath!!i
				    hilbPath = mkPath $ hilbert n East
				    mkPath = fst . foldl g ([p0],0)
	             g (ps,a) act = case act of 
				    Move d -> (ps++[successor (last ps) d a],a)
				    Turn b -> (ps,a+b)

 fern2 n c del rat = open:up:f n 0++[Close]
  	             where f 0 _ = []
                           f n 0 = act:Draw:open:Turn 30:g del++Close:
		                   open:Turn (-30):g del++Close:act<:>g 0
	                           where act = Move $ rat^(n-1)
		                         g = f (n-1)
                           f n k = f (n-1) $ k-1
			   open = Open c 0

 fractal "bush" n c = Open c 0:up:f n c++[Close]
  	           where f 0 _ = [Move 1]
                         f i c = acts<++>acts<++>acts++Draw:open:acts1++Close:
	                         open:Turn (-25):acts<++>acts1<++>acts2++[Close]
                                 where acts = f (i-1) $ nextColor 1 n c
	                               acts1 = acts2<++>acts2<++>acts2
				       acts2 = Turn 25:acts
				       open = Open c 0

 fractal "bush2" n c = Open c 0:up:f n c++[Close]
  	      where f 0 _ = [Move 3]
                    f i c = acts<++>acts++Draw:open:Turn 20:acts<++>acts++Close:
                            open:Turn (-20):acts++Turn 20:acts++[Close]
			    where acts = f (i-1) $ nextColor 1 n c
	                          open = Open c 1

 fractal "cactus" n c = growM n c (mkTrunk c "CA") [False,True,True,True]

 fractal "cant" n c = Open c 0:acts 0 0
   where acts x y = if x < n' || y < n' 
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

 fractal "dragon" n c = Open c 0:f n++[Close]
  	             where f 0 = [Move 10]
                           f i = Turn 45:f (i-1)++Turn (-135):g (i-1)++[Turn 45]
			   g 0 = [Turn 45,Move 10]
			   g i = f (i-1)++Turn 45:g (i-1)++[Turn (-45)]

 fractal "fern" n c = Open c 0:up:f n c 1++[Close]
                  where f 0 _ _ = [Move 10]
                        f i c a = g 0.35 (a*50) (-a)++g 0.35 (-a*50) a++
			          g 0.85 (a*2.5) a
			 where g sc a b = Move 10:Draw:Open c 0:Scale sc:Turn a:
				          f (i-1) (nextColor 1 n c) b++close2

 fractal "gras" n c = Open c 0:up:f n c++[Close]
  	        where f 0 _ = [Move 6]
		      f i c = m:open++h (-25)++m:open++h 37.5++Open c 1:m:h 12.5
		           where m = Move $ 2^i
			         open = [Draw,Open c 0]
				 h a = Turn a:f (i-1) (nextColor 1 n c)++[Close]

 fractal ('g':'r':'a':'s':[m]) n c = Scale 6:open++up:f n++close2
   	        where f 0 = case m of 'D' -> leafD 0.5 30 green green
                                      'A' -> leafA 3 50 green green	
				      'C' -> down:leafC 1 0.2 green green++[up]
				      _ -> [widg $ scaleWidg 0.2 rhombH]
                      f i = m:up:open++acts++Close:open++down:acts++Close:
		            down:m:open++down:m<:>acts++Close:up:acts
			    where acts = f $ i-1;    m = Move $ 2^i
                                  up = Turn $ -22.5; down = Turn 22.5	
	              open = [Draw,Open c 0]

 fractal "hexa" n c = growM n c (mkTrunk c "HE") $ replicate 6 True
				    
 fractal "hilb" n c = f n c East
                      where f 0 _ _   = []
	                    f i c dir = g sdir++draw dir++g dir++draw sdir++
			                g dir++draw (flip dir)++g (flip sdir)
	                                where g = f (i-1) $ nextColor 1 n c
				              sdir = swap dir
					      draw dir = Open c 0:m dir++[Draw]
			    swap North = West
			    swap East  = South
			    swap South = East
			    swap _     = North
			    flip North = South
			    flip East  = West
			    flip South = North
			    flip _     = East 
			    m North = north
			    m East  = east
			    m South = south
			    m West  = west

 fractal "koch" n c = Open c 0:g n++h n
  	              where f 0 = [Move 1,Draw]
		            f i = acts++Turn 60:g (i-1)++Turn 60:acts 
			          where acts = f $ i-1
		            g i = f i++h i 
			    h i = Turn (-120):f i

 fractal "penta" n c = growM n c (mkTrunk c "PE") $ replicate 5 True

 fractal "pentaS" n c = growM n c (mkTrunk c "PS") [False,True,True]
 
 fractal "pytree" n c = growM n c (mkTrunk c "PY") [False,True,True]

 fractal "pytreeA" n c = growAM n c acts [False,True,True]
            	 where acts = [up,m,Turn 38.659805,Move 57.628117,Turn 91.14577,
                               Move 70.292244,Turn 50.19443,m,down,m] 
		       m = Move 90

 fractal "wide" n c = Open c 0:up:f n c++[Close]
  	      where f 0 _ = [Move 3]
                    f i c = open:Turn 20:acts++open:Turn 20:acts1++Turn (-40):
		            acts1++open:Turn (-40):acts<++>acts1++g (i-1) c'
                            where acts = h (i-1) c'; acts1 = f (i-1) c'++[Close]
			          c' = next c; open = Open c 0
	            g 0 _ = [Move 3]
		    g i c = h (i-1) c'<++>f (i-1) c' where c' = next c
		    h 0 _ = [Move 3]
		    h i c = acts<++>acts where acts = h (i-1) $ next c
		    next = nextColor 1 n

-- bars and piles

 bar sizes size i h c = [open,blackText sizes a,up,JumpA ht,open,Jump i',
 		         rectC c i' 5,Close,Jump h',rectC black h' 5,Close]
	                where i' = fromInt i; h' = fromInt h
		              a = show i; ht = fromInt size/2+3

 colbars sizes size (RGB r g b) = f r red++Jump 20:f r green++Jump 40:f r blue
				  where f c = bar sizes size (abs c`div`4) 64

 pile h i = open:up:f h i++[Close]
            where f 0 _ = []
                  f h 0 = Jump 2:frame:f (h-1) 0
                  f h i = Jump 2:quad:frame:f (h-1) (i-1)
		  frame = rectC black 1 1
		  quad = rectC (light blue) 1 1

 pileR h is = actsToCenter $ open:up:f h (reverse is)++[Close]
              where f 0 _      = []
                    f n (i:is) = Jump 2:quad i:frame:f (n-1) is
		    f n _      = Jump 2:frame:f (n-1) []
		    frame = rectC black 1 1
		    quad i = rectC (hue 1 green h i) 1 1

-- matrices

 rectMatrix :: Sizes -> (String -> String -> TurtleActs) -> [String] 
 		     -> [String] -> (String -> Float) -> (String -> Float) 
		     -> TurtleActs
 rectMatrix sizes@(n,width) entry dom1 dom2 btf htf =
            actsToCenter $ down:open:up:rectC black bt ht:JumpA bt:  
	                   rectRow lineHead ht btf dom2++Close:JumpA ht:
			   concatMap h dom1
            where lineHead a = [colText blue sizes a]
	    	  bt = halfmax width dom1+3
		  ht = fromInt n/2+3
	          h i = JumpA ht:open:up:rectC black bt ht:lineHead i++
                        JumpA bt:rectRow (entry i) ht btf dom2++[Close,JumpA ht]
		        where ht = htf i

 rectRow entry ht btf = concatMap f
                      where f j = JumpA bt:rectC black bt ht:entry j++[JumpA bt]
	                          where bt = btf j

 matrixBool :: Sizes -> [String] -> [String] -> [(String,String)] -> TurtleActs
 matrixBool sizes@(n,width) dom1 dom2 ps = 
 		     rectMatrix sizes entry dom1 dom2 btf $ const ht
		     where entry i j = if (i,j) `elem` ps 
			               then [widg $ Oval (st0 red) m m] else [] 
			   m = minimum (ht:map btf dom2)-1
			   btf j = halfmax width [j]+3
			   ht = fromInt n/2+3

 delBrackets = f . showTerm0 where f ('(':a@(_:_)) | last a == ')' = init a
                                   f a			           = a

 matrixList :: Sizes -> [String] -> [String] -> [(String,String,[TermS])] 
 		     -> TurtleActs
 matrixList sizes@(n,width) dom1 dom2 ts = 
             rectMatrix sizes entry dom1 dom2 btf htf
	     where entry i j = open:down:JumpA back:concatMap h (f i j)++[Close]
			       where back = -(lg i j-1)*ht
	      	   h a = [blackText sizes a,JumpA $ ht+ht]
		   f i = map delBrackets . relLToFun ts i
		   lg i = max 1 . fromInt . length . f i
		   btf j = halfmax width (j:concatMap (flip f j) dom1)+3
		   htf i = maximum (map (lg i) dom2)*ht
		   ht = fromInt n/2+3

 matrixTerm :: Sizes -> [(String,String,TermS)] -> TurtleActs
 matrixTerm sizes@(n,width) ts = rectMatrix sizes entry dom1 dom2 btf htf
                  where (dom1,dom2) = sortDoms2 ts
		        entry i j = [act str] where (act,str) = f i j
			f i = colTerm . g i
		        g i j = case lookupL i j ts of Just t -> t; _ -> V""
	                btf j = halfmax width (j:map (snd . flip f j) dom1)+3
		        htf _ = fromInt n/2+3
                        colTerm t = (colText col sizes,delBrackets t) 
	                            where col = case parse colPre $ root t of 
				   	             Just (c,_) -> c; _ -> black

 matrixWidget :: Sizes -> Pos -> [(String,String,TermS)] -> TurtleActs
 matrixWidget sizes@(n,width) spread ts = rectMatrix sizes entry dom1 dom2 
 						     btf htf
               where (dom1,dom2) = sortDoms2 ts
	             entry i j = [widg $ f i j]
	             f i j = mkWidg $ case lookupL i j ts of Just t -> t
		   					     _ -> V""
	             btf j = (x2-x1)/2+3 
	                     where (x1,_,x2,_) = pictFrame $ map (flip f j) dom1
	             htf i = (y2-y1)/2+3 
	                     where (_,y1,_,y2) = pictFrame $ map (f i) dom2
	             mkWidg t = case widgets sizes spread t of
			        Just [v] -> v; _ -> text0 sizes $ showTerm0 t

-- partitions

 drawPartition sizes mode = f $ case mode of 0 -> levelTerm
		      		             1 -> preordTerm 
					     2 -> heapTerm
					     _ -> hillTerm
     where f order = split True 100 100 . fst . order blue lab 
             where lab c n = (c,n)
	           split b dx dy (F _ ts@(_:_)) = open:acts++[Close]
			             where acts = if b then split1 (dx/lg) dy ts
				                       else split2 dx (dy/lg) ts
                                           lg = fromInt (length ts)
 	           split _ dx dy t = [open,Jump dx',down,Jump dy',up,
	       		              rectC c dx' dy',
				      blackText sizes $ show n,Close]
 	                             where dx' = dx/2; dy' = dy/2; F (c,n) _ = t
	           split1 dx dy [t]    = split False dx dy t
		   split1 dx dy (t:ts) = split False dx dy t++Jump dx:
				         split1 dx dy ts
	           split2 dx dy [t]    = split True dx dy t
	           split2 dx dy (t:ts) = split True dx dy t++down:Jump dy:up:
				         split2 dx dy ts

-- STRING PARSER into widgets

-- graphString is used by loadGraph (see above).

 graphString = do symbol "("; pict <- list widgString; symbol ","
 		  arcs <- list (list int); symbol ")"; return (pict,arcs)

 widgString = concat [do symbol "Arc"; ((x,y),a,c,i) <- state; t <- arcType
		         r <- enclosed double; b <- enclosed double
		         let [x',y',r',a',b'] = map fromDouble [x,y,r,a,b]
		         return $ Arc ((x',y'),a',c,i) t r' b',
 		      do symbol "Bunch"; w <- enclosed widgString
			 is <- list int; return $ Bunch w is,
 		      do symbol "Dot"; c <- token hexcolor; (x,y) <- pair
		         let [x',y'] = map fromDouble [x,y]
		         return $ Dot c (x',y'),
 		      do symbol "Fast"; w <- enclosed widgString
		         return $ Fast w,
 		      do symbol "File_"; file <- token quoted
 		         return $ File_ file,
 		      do symbol "Gif"; c <- token hexcolor; (x,y) <- pair
 		         file <- token quoted; b <- enclosed double
 		         h <- enclosed double
		         let [x',y',b',h'] = map fromDouble [x,y,b,h]
		         return $ Gif c (x',y') file b' h',
 		      do symbol "New"; return New,
 		      do symbol "Oval"; ((x,y),a,c,i) <- state
			 rx <- enclosed double; ry <- enclosed double
		         let [x',y',a',rx',ry'] = map fromDouble [x,y,a,rx,ry]
		         return $ Oval ((x',y'),a',c,i) rx' ry',
 		      do symbol "Path"; ((x,y),a,c,i) <- state
			 n <- enclosed nat; ps <- list pair
		         let [x',y',a'] = map fromDouble [x,y,a]
		         return $ Path ((x',y'),a',c,i) n $ map fromDouble2 ps,
 		      do symbol "Poly"; ((x,y),a,c,i) <- state
			 n <- enclosed nat; rs <- list (enclosed double)
			 b <- enclosed double
		         let [x',y',a',b'] = map fromDouble [x,y,a,b]
		         return $ Poly ((x',y'),a',c,i) n 
			 	       (map fromDouble rs) b',
 		      do symbol "Rect"; ((x,y),a,c,i) <- state
			 b <- enclosed double; h <- enclosed double
		         let [x',y',a',b',h'] = map fromDouble [x,y,a,b,h]
		         return $ Rect ((x',y'),a',c,i) b' h',
 		      do symbol "Repeat"; w <- enclosed widgString
			 return $ Repeat w,
 		      do symbol "Saved"; file <- token quoted
 		         w <- enclosed widgString; return $ Saved file w,
 		      do symbol "Skip"; return Skip,
		      do symbol "Text_"; ((x,y),a,c,i) <- state 
			 n <- enclosed nat; strs <- list (token quoted)
			 lgs <- list int
		         let [x',y',a'] = map fromDouble [x,y,a]
		         return $ Text_ ((x',y'),a',c,i) n strs lgs,
 		      do symbol "Tree"; ((x,y),a,c,i) <- state
		         n <- enclosed nat; c' <- token hexcolor; ct <- ctree
		         let [x',y',a'] = map fromDouble [x,y,a]
		         return $ Tree ((x',y'),a',c,i) n c' ct,
		      do symbol "Tria"; ((x,y),a,c,i) <- state
		         r <- enclosed double
		         let [x',y',a',r'] = map fromDouble [x,y,a,r]
		         return $ Tria ((x',y'),a',c,i) r',
 		      do symbol "Turtle"; ((x,y),a,c,i) <- state
			 sc <- enclosed double; acts <- list turtleAct
		         let [x',y',a',sc'] = map fromDouble [x,y,a,sc]
		         return $ Turtle ((x',y'),a',c,i) sc' acts]
	      where arcType = concat [do symbol "chord"; return Chord,
                                      do symbol "arc"; return Perimeter,
                                      do symbol "pieslice"; return Pie]
		    pair = do symbol "("; x <- token double; symbol ","
			      y <- token double; symbol ")"; return (x,y)
 		    quad = do symbol "("; x1 <- token double; symbol ","
			      y1 <- token double; symbol ","
			      x2 <- token double; symbol ","
			      y2 <- token double; symbol ")"
			      return (x1,y1,x2,y2)
                    state = do symbol "("; (x,y) <- pair; symbol ","
                               a <- token double; symbol ","
                               c <- token hexcolor; symbol ","
                               i <- enclosed int; symbol ")"
			       return ((x,y),a,c,i)
		    node = do symbol "("; b <- token quoted; symbol ","
			      (x,y) <- pair; symbol ","; lg <- enclosed int
			      symbol ")"; return (b,(x,y),lg)
                    turtleAct = concat [do symbol "Close"; return Close,
		     			do symbol "Draw"; return Draw,
		     			do symbol "Jump"; d <- enclosed double
		        		   return $ Jump (fromDouble d),
			    	        do symbol "JumpA"; d <- enclosed double
		        		   return $ JumpA (fromDouble d),
			    	        do symbol "Move"; d <- enclosed double
 					   return $ Move (fromDouble d),
	                                do symbol "MoveA"; d <- enclosed double
 					   return $ MoveA (fromDouble d),
	                                do symbol "Open"; c <- token hexcolor
					   m <- token nat; return $ Open c m,
			    	        do symbol "Turn"; a <- enclosed double
		        		   return $ Turn (fromDouble a),
		     			do symbol "Scale"; a <- enclosed double
		        		   return $ Scale (fromDouble a),
		     			do symbol "Widg"; b <- enclosed bool
					   w <- enclosed widgString
		        		   return $ Widg b w]
                    ctree = concat [do symbol "V"; (b,(x,y),lg) <- node
		                       let [x',y'] = map fromDouble [x,y]
				       return $ V (b,(x',y'),lg),
				    do symbol "F"; (b,(x,y),lg) <- node
				       cts <- list ctree
		                       let [x',y'] = map fromDouble [x,y]
				       return $ F (b,(x',y'),lg) cts]
