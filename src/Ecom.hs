module Ecom where
 import Esolve

----------------------------- Copyright (c) peter.padawitz@udo.edu, October 2014

-- Ecom contains the main program, the solver and the enumerator.
 
 main :: TkEnv -> Cmd ()
 main tk = do
  mkdir $ home ++ fileSeparator:"ExpanderLib"
  mkdir libPix
  mv "Painter.js" libPix
  win1 <- tk.window []
  win2 <- tk.window []
  fix solve1 <- solver tk "Solver1" win1 solve2 "Solver2" enum1 paint1
      solve2 <- solver tk "Solver2" win2 solve1 "Solver1" enum2 paint2
      paint1 <- painter 820 tk "Solver1" solve1 "Solver2" solve2
      paint2 <- painter 820 tk "Solver2" solve2 "Solver1" solve1 
      enum1 <- enumerator tk solve1
      enum2 <- enumerator tk solve2
  solve1.buildSolve (0,20) solve1.skip
  solve2.buildSolve (20,20) solve1.skip
  win2.iconify

 data PossAct = Add [[Int]] | Remove [Int] | Replace [[Int]]

-- PROOFS

 struct ProofElem = msg,msgL,treeMode :: String
 		    trees 	      :: [TermS]
		    treePoss	      :: [[Int]]
		    curr	      :: Int
		 -- perms	      :: Int -> [Int]
		    varCounter	      :: String -> Int
		    newPreds	      :: ([String],[String])
		    solPositions      :: [Int]
		    substitution      :: (SubstS,[String])
		    constraints	      :: (Bool,[String])
		    joined,safe	      :: Bool

 extendMsg str proofElem = struct msg = proofElem.msg++str
 				  msgL = proofElem.msgL
				  treeMode = proofElem.treeMode
				  trees = proofElem.trees
				  treePoss = proofElem.treePoss
				  curr = proofElem.curr
			       -- perms = proofElem.perms
				  varCounter = proofElem.varCounter
				  newPreds = proofElem.newPreds
				  solPositions = proofElem.solPositions
				  substitution = proofElem.substitution
				  constraints = proofElem.constraints
				  joined = proofElem.joined
				  safe = proofElem.safe
 
 applyNRS msg = take 3 msg `elem` words "NAR REW SIM"
 
 showDeriv proof trees solPositions = concat (zipWith f (indices_ proof) proof) 
 				      ++ solsMsg
	         where f i proofElem = show i ++ ". " ++ proofElem.msg ++ "\n\n"
	               sols = map (trees!!) solPositions
                       solsMsg = if null sols then "" 
		                 else "Solutions:" ++ concatMap f sols
	                         where f t = "\n\n" ++ showTree False t

 showCurr fast t b = "\nThe current "++str++" is given by\n\n"++ showTree fast t
                     where str = if b then "formula" else "term"

 showNew fast 1 t msg n ps b = preceding msg ps b n ++ "a single " ++ str ++
 			       ",\nwhich is given by\n\n" ++ showTree fast t 
			       where str = if b then "formula" else "term"
 showNew fast k t msg n ps b = preceding msg ps b n ++ show k ++ str ++ 
 			       showCurr fast t b
			       where str = if b then " formulas." else " terms."

 showPre fast t msg n ps b = preceding msg ps b n ++ "\n\n" ++ showTree fast t

 preceding msg ps b n = msg ++ str1 ++ showPS ps ++ str2 ++ 
                        (str3 `onlyif` applyNRS msg) ++ " leads to "  
     where str1 = if last msg == '\n' then "" else " "
           str2 = if b then "formulas" else "terms"
	   str3 = " (" ++ if n == 1 then "one step)" else show n++ " steps)"
           showPS []  = ("to " `ifnot` applyNRS msg) ++ "the preceding "
           showPS ps = "at positions" ++ concatMap f ps ++ "\nof the preceding "
	   f p = '\n':show p `minus1` ' '
 
-- PROOF TERM functions

 addStep pt@(_:_) step = case (step,last pt) of
                              (DeriveMode _ _,DeriveMode _ _) -> init pt++[step]
			      (Mark _,Mark _) -> init pt++[step]
			      (Match _,Match _) -> init pt++[step]
			      _ -> pt++[step]
 addStep _ step        = [step]

 deriveStep step = case step of DeriveMode _ _ -> False
 				Mark _ 	       -> False 
				Match _        -> False
				_ 	       -> True

 command = concat [do symbol "ApplySubst"; return ApplySubst,
		   do symbol "ApplySubstTo"; x <- token quoted
		      t <- enclosed linearTerm; return $ ApplySubstTo x t,
		   do symbol "ApplyTransitivity"; return ApplyTransitivity,
		   do symbol "BuildKripke"; m <- token int
		      return $ BuildKripke m,
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
		   do symbol "Induction"; ind <- token bool; n <- token int
		      return $ Induction ind n,
		   do symbol "Mark"; ps <- list $ list int; return $ Mark ps,
		   do symbol "Match"; n <- token int; return $ Match n,
                   do symbol "Minimize"; return Minimize,
		   do symbol "Narrow"; limit <- token int; sub <- token bool
		      return $ Narrow limit sub,
                   do symbol "NegateAxioms"; ps <- list quoted
		      cps <- list quoted; return $ NegateAxioms ps cps,
		   do symbol "RandomLabels"; return RandomLabels,
		   do symbol "RandomTree"; return RandomTree,
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
		   do symbol "ShowEqsOrGraph"; b <- token bool; m <- token int
		      return $ ShowEqsOrGraph b m,
		   do symbol "ShowRelation"; m <- token int
		      return $ ShowRelation m,
		   do symbol "Simplify"; depthfirst <- token bool
		      limit <- token int; sub <- token bool
		      return $ Simplify depthfirst limit sub,
		   do symbol "SplitTree"; return SplitTree,
		   do symbol "SubsumeSubtrees"; return SubsumeSubtrees,
		   do symbol "Theorem"; b <- token bool
		      th <- enclosed linearTerm; return $ Theorem b th,
		   do symbol "UnifySubtrees"; return UnifySubtrees]

 linearTerm = concat [do symbol "F"; x <- token quoted; ts <- list linearTerm
                         return $ F x ts,
                      do symbol "V"; x <- token quoted; return $ V x]
  
-- SOLVER messages

 start = "Welcome to Expander2 (November 1, 2014)"

 startF = "Load and parse a formula!"

 startOther solve = "Load and parse a term or formula in " ++ solve ++ "!"

 alreadyRegEqs = 
              "The selected tree is already a conjunction of regular equations."

 applied b str = "Applying the " ++ s ++ str ++ "\n\n"
           where s = if b then if '!' `elem` str then "induction hypothesis\n\n"
				                 else "theorem\n\n"
		          else "axioms\n\n"

 appliedToSub str 1 = "A " ++str++" step has been applied to the selected tree."
 appliedToSub str n = show n ++ " " ++ str ++
                      " steps have been applied to the selected trees."

 arcInserted p q = "An arc from position " ++ show p ++ " to position " ++
 		    show q ++ " has been inserted."

 atomDecomposed = "The selected atom has been decomposed."

 atomNotDecomposed = "The selected atom cannot be decomposed."

 admitted :: Bool -> [String] -> String
 admitted True []  = "All axioms are admitted."
 admitted block xs = (if block then "All axioms except those for "
                               else "Only axioms for ") ++
		     showStrList xs ++ " are admitted."

 axsRemovedFor xs = "The axioms for " ++ showStrList xs ++ " have been removed."

 check rest = "\n--CHECK FROM HERE:\n" ++ rest

 circle p q = "The operation fails because the current tree contains a back " ++
   	      "pointer from position "++ show p ++" to position "++ show q ++"."

 circlesUnfolded 1 = "\nCircles were unfolded one time."
 circlesUnfolded n = "\nCircles were unfolded " ++ show n ++ " times."

 copiesRemoved = "Copies of the selected tree have been removed."

 collapsed = "The selected tree has been collapsed."
 
 complsAdded xs = "Axioms for the complement" ++ str ++ showStrList xs ++ 
 	          " have been added."
		  where str = case xs of [_] -> " of "; _ -> "s of "

 concCallsPrem 
             = "Some conclusion contains the root of the corresponding premise."

 creatingInvariant str ax 
        = str ++ " for the iterative program\n\n" ++ showTree False ax ++ "\n\n"
 
 edgesRemoved True = "Cycles have been removed."
 edgesRemoved _    = "Forward arcs have been turned into tree edges."

 dangling = "The highlighted subtree cannot be removed from its position " ++
            "because a pointer points to it."

 emptyProof = "The proof is empty."

 emptySubst = "The substitution is empty."
 
 emptyTreeDir = "The tree directory is empty."
 
 endOfProof = "The end of the derivation has been reached."

 enterNumber = "Enter the number of a formula shown in the text field!"

 enterNumbers = "Enter numbers of formulas shown in the text field!"
 
 equationRemoval safe = "Equation removal is " ++ if safe then "safe." 
 							  else "unsafe."
 
 eqsBuilt = "The selected graph has been turned into equations."
 
 eqsButMsg safe = (if safe then "safe" else "unsafe") ++ " equation removal"

 eqInverted = "The selected equation has been inverted."

 evaluated = "The selected trees have been evaluated."

 expanded = "The selected trees have been expanded."

 extendedSubst = 
   	  "The equations in the text field have been added to the substitution."

 finishedNar True 1 = "A narrowing step has been performed.\n"
 finishedNar _    1 = "A rewriting step has been performed.\n"
 finishedNar True n = show n ++ " narrowing steps have been performed.\n"
 finishedNar _ n    = show n ++ " rewriting steps have been performed.\n"
		      
 finishedSimpl 1 = "A simplification step has been performed.\n"
 finishedSimpl n = show n ++ " simplification steps have been performed.\n"
 
 flattened = "The selected clause has been flattened."
 
 formString b = if b then "formula" else "term"

 generalized = "The selected formula has been generalized with the formulas" ++
	       " in the text field."

 graphBuilt = "The selected graph has been collapsed."

 illformed = "The term or formula in the text field is not well-formed."

 illformedF = "The formula in the text field is not well-formed."

 illformedS = "The substitution in the text field is not well-formed."

 illformedSig = "The signature in the text field is not well-formed."

 illformedSM = "The signature map in the text field is not well-formed."

 illformedT = "The term in the text field is not well-formed."

 indApplied str  = str ++ " has been applied to the selected formulas."

 indHypsCreated [x] = "The induction variable is " ++ showStr x ++
                      ".\nInduction hypotheses have been added to the theorems."
		      ++ "\nGive axioms for the induction ordering >>!"

 indHypsCreated xs = "The induction variables are " ++ showStrList xs ++
     ".\nInduction hypotheses have been added to the theorems." ++
     "\nSpecify the induction ordering >> on " ++ show (length xs) ++ "-tuples!"

 iniSigMap = "The signature map is the identity."

 iniSpec = "The specification consists of built-in symbols. "

 invCreated b =
    "The selected formula has been transformed into conditions on a " ++
    (if b then "Hoare" else "subgoal") ++ " invariant INV.\nAdd axioms for INV!"

 kripkeBuilt mode b procs sts labs ats = 
    "A " ++ f mode ++ " Kripke model with " ++ 
    (if b then show procs ++ " processes, " else "") ++ show' sts "state" ++ 
    ", " ++ show' labs "label" ++ " and " ++ show' ats "atom" ++ 
    " has been built from the axioms."
    where f 0 = "cycle-free"
          f 1 = "pointer-free"
	  f _ = ""
	  show' 1 obj = "one " ++ obj
          show' n obj = show n ++ ' ':obj ++ "s"

 leavesExpanded = "The selected trees have been expanded at their leaves."

 levelMsg i = "The current tree has been collapsed at " ++
 	      (if i == 0 then "leaf level." else " the " ++ show (i+1) ++
               " lowest levels.")

 loaded file = file ++ " has been loaded into the text field."

 moved = "The selected quantifiers have been moved to the parent node."

 newCls cls file = "The " ++ cls ++ " in " ++ file ++ " have been added."

 newCurr = "The tree slider has been moved."

 newInterpreter eval draw = eval ++" is the actual widget-term interpreter. "++
			    (if null draw then "No draw function" else draw) ++
			    " is applied before painting."
 
 newPredicate str1 str2 x = "The " ++ str1 ++ ' ':x ++ 
 			    " has been turned into a " ++ str2 ++ "."

 newSig file = "The symbols in " ++ file ++ " have been added to the signature."

 newSigMap file = "The assignments in " ++ file ++ 
                  " have been added to the signature map."
        
 noApp :: String -> String
 noApp str = str ++ " is not applicable to the selected trees."
        
 noAppT :: Maybe Int -> String
 noAppT k = case k of Just n -> "Theorem no. " ++ show n ++ str
 		      _ -> "The theorem in the text field" ++ str       
	    where str = " is not applicable to the selected trees."

 noAxiomsFor xs = "There are no axioms for " ++ showStrList xs ++ "."

 nodesReplaced a = "The roots of the selected trees have been replaced by "
                   ++ showStr a ++ "."
 
 noProofIn file = file ++ " does not contain a proof term."

 notDisCon = "The theorem to be applied is not a distributed clause."

 noTheorem k = (case k of Just n -> "No. " ++ show n
                          _ -> "The clause in the text field") ++
	       " is neither an axiom nor a theorem."

 notInstantiable = 
 	        "The selected variable cannot be instantiated at this position."

 notUnifiable k = (case k of Just n -> "Theorem no. " ++ show n
                             _ -> "The theorem in the text field") ++
	          " is not unifiable with any selected redex."

 noUnifier = "The selected subtrees are not unifiable."

 ocFailed x = x ++ " cannot be unified with a term that contains " ++ x ++
	      " and is not a variable."

 onlyRew = "\nThe selected tree is a term. " ++
           "Hence formula producing axioms are not applicable!"
	      
 orderMsg str = "The nodes of the selected tree have been labelled with " ++
 		str ++ "."

 partialUnifier = "The selected trees are only partially unifiable."

 pointersComposed = "The pointers in the selected trees have been composed."
 
 posInSubst = "There is a pointer in a substitution."

 premCallsConc =
               "Some premise contains the root of the corresponding conclusion."

 proofLoaded file = "The proof term has been loaded from " ++ file ++ "."

 relationBuilt = "The selected graph has been turned into a list."

 removed = "The selected trees have been removed."

 removedOthers = "All trees except the one below have been removed."

 replacedTerm = "The selected terms have been replaced by equivalent ones."

 replaceIn solve = "The subtree has been replaced by the tree of "++solve++"."

 reversed = "The list of selected trees has been reversed."
 
 see str = "See the " ++ str ++ " in the text field."
		     
 selectCorrectSubformula = "Select an implication, a conjunction or a " ++
                           "disjunction and subterms to be replaced!"
                           
 selectSub = "Select a proper non-hidden subtree!"
 
 shifted =
      "The selected subformulas have been shifted to the premise or conclusion."
 
 sigMapError other = "The signature map does not map to the signature of " ++
                     other ++ "."

 simplifiedPar = "A simplification step has been applied to the root position "
                 ++ "of each selected tree."

 solved [n]    = "A solution is at position " ++ show n ++ "."
 solved (n:ns) = "Solutions " ++ "are at positions " ++
                 splitString 27 63 (mkRanges ns n) ++ "."
 solved _      = "There are no solutions."

 stretched = "The selected conditional equation has been stretched."

 subMsg str x = str ++ " has been substituted for " ++ x ++ "."

 subsAppliedToAll = "The substitution has been applied to all variables."

 subsAppliedTo x = "The substitution has been applied to " ++ x ++ ". "

 subsumed object = "The selected tree results from the subsumption of a " ++
 		   object ++ "."

 subtreesNarrowed k = (case k of Just n 
   				   -> if n == -1 then "Axioms are not"
                         	      else "Theorem no. " ++ show n ++ " is not"
 				 _ -> "No clause is") ++
		      " applicable to the selected trees."

 thApplied k = (case k of Just n -> if n == -1 then "Axioms have"
                         	    else "Theorem no. " ++ show n ++ " has" 
                          _ -> "The clauses in the text field have") ++
	       " been applied to the selected trees."
 
 termsStored = "Storable subterms of the selected trees have been stored."

 textInserted
            = "The tree in the text field replaces/precedes the selected trees."

 transitivityApplied 
 	      = "The transitivity axiom has been applied to the selected atoms."

 treeParsed = 
         "The text field contains a string representation of the selected tree."

 treesSimplified = "The trees are simplified."

 unified object = "The selected tree results from the unification of two " ++
 		  object ++ "s."

 unifiedT = "The selected trees have been unified. "

 wrongArity f lg = "The number in the entry field is too big. " ++ f ++
                   " has only " ++ show lg ++ " arguments."
 
 enumerators = words "alignment dissection palindrome partition"

 interpreters = words "tree matrices widgets overlay alignment dissection" ++
                ["level partition","preorder partition","heap partition",
		 "hill partition","linear equations","tree solution",
		 "matrix solution","widget solution"]

 specfiles1 = 
   words "abp account align auto1 auto2 base bool bottle bottleac bottlef" ++
   words "btree cobintree coin coregs cse cycle dna echo echoac election" ++
   words "factflow flowers FP gauss graphs hanoi hanoilab hinze infbintree" ++
   words "kino knight kripke1 kripke2"

 specfiles2 = 
   words "lazy lift liftlab list listeval listrev log log4 lr1 lr2 micro" ++
   words "microS modal modalS mutex mutexco mutexquad nat NATths needcoind" ++ 
   words "newman obdd obst partn penroseS phil philac polygons prims prog" ++
   words "prog1 prog2 progW puzzle queens"

 specfiles3 = 
   words "regeqs relalg relalgdb relalgp robot ROBOTacts sendmore set" ++
   words "shelves simpl stack STACKimpl STACKimpl2 stream trans0 trans1" ++
   words "trans1S trans2 trans2S turtles widgets zip"

 treefiles = words "copyrem mapziptup parity ROBOTsols"
{-
 pictsOf "bottle" sig     	   = (solPic sig widgets,False)
 pictsOf "robot" sig     	   = (solPic sig widgets,False)
 pictsOf "ROBOTacts" sig 	   = (solPic sig widgets,False)
 pictsOf "queens" sig    	   = (solPic sig matrix,False)
 pictsOf "knight" sig    	   = (solPic sig matrix,False)
 pictsOf ('g':'a':'u':'s':'s':_) _ = (searchPic linearEqs,False)
 pictsOf _ _   	                   = (searchPic widgets,False)
-}
-- the SOLVER template

 solver :: TkEnv -> String -> Window -> Solver -> String -> Enumerator
                 -> Painter -> Template Solver
 solver tk this win solve other enum paint =

   template (backBut,canv,canvSlider,close,deriveBut,treeSlider,ent,fastBut,
   	     font,forwBut,hideBut,interpreterBut,lab,matchBut,narrowBut,quit,
	     safeBut,simplButD,simplButB,splitBut,subToBut,tedit,treeBut,lab2)
              := (undefined,undefined,undefined,undefined,undefined,undefined,
	          undefined,undefined,undefined,undefined,undefined,undefined,
		  undefined,undefined,undefined,undefined,undefined,undefined,
		  undefined,undefined,undefined,undefined,undefined,undefined)
	    (ctree,node,penpos,subtree,isSubtree,suptree,osci)
	      := (Nothing,Nothing,Nothing,Nothing,Nothing,Nothing,Nothing)
	    (fast,firstMove,formula,showState,joined,safe,wtree)
	      := (True,True,True,True,True,True,True)
	    (checking,checkingP,simplifying,refuting,collSimpls,newTrees,
	     restore) := (False,False,False,False,False,False,False)
	    (canvSize,corner,counter,curr,curr1,hideVals,matching,proofPtr,
	     proofTPtr,picNo,stateIndex) 
	      := ((0,0),(20,20),const 0,0,0,0,0,0,0,0,0)
	    (axioms,checkers,conjects,indClauses,iniStates,matchTerm,
	     oldTreeposs,proof,proofTerm,refuteTerm,rewrites,rewritesL,
	     ruleString,simplRules,simplTerm,solPositions,specfiles,terms,
	     theorems,transRules,treeposs,trees) 
	      := ([],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],
	          [],[])
	    numberedExps := ([],True); constraints := (True,[])
	    (drawFun,picEval,treeDir) := ("","tree","")
	    signatureMap := (id,[]); newPreds := nil2; part := (id,[])
	    proofStep := ApplySubst; substitution := (V,[]); treeMode := "tree"
	    symbols := iniSymbols; rand := seed; sizeState := sizes0
	    spread := (10,30); times := (0,300); maxHeap := 100; speed := 0
	    varCounter := const 0 -- perms := \n -> [0..n-1]
	    kripke := ([],[],[],[],[],[],[])

   in let
	  
	createBut x act file = x.mButton [CLabel file, font12,
					  Command $ act file]

	buildSolve leftUpCorner continue = action
 	  win.set [Title this]
	  win.setPosition leftUpCorner
--	  win.setSize (1275,855)  		-- for 1280 x 1024, 60 Hz
--  	  win.setSize (1020,730)  		-- for 1024 x 768, 60 Hz
--	  win.setSize (1400,820)  		-- for 1440 x 900
	  win.setSize (1200,700)  		-- for 1440 x 900
	  
	  but <- win.button [Text "<---", font12, greenback, groove,
	                     Command backProof]
	  backBut := but

  	  canv0 <- win.canvas [Height 100, Background white]
	  canv := canv0
	  canv.bind [ButtonPress 1 catchSubtree,
	     	     ButtonPress 2 catchTree,
		     ButtonPress 3 catchNode,
	             Motion 1 moveSubtree,
	     	     Motion 2 moveTree,
		     Motion 3 moveNode,
	     	     ButtonRelease 1 releaseSubtree,
	     	     ButtonRelease 2 releaseTree,
		     ButtonRelease 3 releaseNode]

	  canvSlider0 <- win.slider [From $ -40, To 600, Orientation Ver,
				     CmdInt setExtension]
	  canvSlider := canvSlider0
	  canvSlider.setValue 100

	  deriveBut0 <- win.button [Text "derive", font12, blueback, groove,
	  			    Command setDeriveMode]
          deriveBut := deriveBut0

	  let act n = action curr1 := if n < length trees then n else curr
	      takeCurr _ = action setCurr newCurr curr1
	  treeSlider0 <- win.slider [Orientation Hor, From 0, CmdInt act]
	  treeSlider0.bind [ButtonRelease 1 takeCurr]
	  treeSlider := treeSlider0

 	  ent0 <- win.entry [Font "Courier 18"]
	  ent := ent0
	  ent.bind [ButtonPress 1 $ const ent.focus,
		    KeyPress "Up" $ getFileAnd loadText,
	            KeyPress "Down" $ getFileAnd saveTree,
		    KeyPress "Right" $ applyClause False False False,
		    KeyPress "Left" $ applyClause False True False,
		    KeyPress "Return" $ getFileAnd $ addSpecWithBase]

	  font0 <- tk.font "Helvetica 18 normal"
	  font := font0

	  but <- win.button [Text "--->", font12, greenback, groove,
	                     Command forwProof]
          forwBut := but

  	  but <- win.button [Text "hide", font12, groove, Command hideOrShow]
	  hideBut := but

   	  lab0 <- win.label [Text start, Font "Helvetica 12 italic", blueback,
			     Justify LeftAlign]
	  lab := lab0
	  lab.bind [KeyPress "u" $ do (testT tk 55).runT; done,
	            KeyPress "v" $ do (testT tk $ -2).runT; done,
	            ButtonPress 1 $ const lab.focus,
		    KeyPress "c" copySubtrees,
		    KeyPress "i" replaceText,
		    KeyPress "l" replaceNodes,
		    KeyPress "n" negateAxioms,
		    KeyPress "L" randomLabels,
		    KeyPress "T" randomTree,
		    KeyPress "p" removePath,
		    KeyPress "r" removeSubtrees,
		    KeyPress "s" saveProof,
		    KeyPress "t" setTreeDir,
		    KeyPress "x" showAxiomsFor,
		    KeyPress "Left" $ incrCurr False,
		    KeyPress "Right" $ incrCurr True,
                    KeyPress "Up" backProof,
		    KeyPress "Down" forwProof]
		    
   	  lab0 <- win.label [Text emptyTreeDir, Font "Helvetica 12 italic",
			     Justify RightAlign, blueback]
          lab2 := lab0

	  but <- win.button [font12, blueback, groove, Command $ setMatch True]
	  matchBut := but

  	  but <- win.button [font12, blueback, groove, Command $ narrow skip]
	  narrowBut := but

	  but <- win.button [Text "split", font12, blueback, groove,
	  		     Command splitTree]
          splitBut := but
	  
	  paint.setEval picEval spread

	  buildSolve1 continue

	buildSolve1 continue = action
          axs     <- win.menuButton [Text "axioms", font12b]
  	  axsMenu <- axs.menu []
 	  axsMenu.mButton [CLabel "remove in entry field", font12, 
			   blueback, Command $ removeClauses 0]
   	  axsMenu.mButton [CLabel ".. for symbols", font12, blueback, 
	                   Command removeAxiomsFor]
	  axsMenu.mButton [CLabel "show", font12, blueback, 
	                   Command $ showAxioms True]
	  axsMenu.mButton [CLabel $ ".. in text field of "++ other, font12, 
			   blueback, Command $ showAxioms False]
  	  axsMenu.mButton [CLabel ".. for symbols (x)", font12, blueback,
			   Command showAxiomsFor]
 	  axsMenu.mButton [CLabel "combine for symbol", font12, blueback, 
	  		   Command $ compressAxioms True]
          axsMenu.mButton [CLabel ".. in entry field", font12, 
      		           blueback, Command compressClauses]
 	  axsMenu.mButton [CLabel "invert for symbol", font12, blueback, 
                           Command $ compressAxioms False]
	  axsMenu.mButton [CLabel "negate for symbols (n)", font12, blueback, 
	  		   Command negateAxioms]
	  axsMenu.mButton [CLabel "Kleene axioms for symbols", font12, blueback,
	    		   Command kleeneAxioms]
 	  addMenu <- axsMenu.cascade [CLabel "add", font12, blueback]
	  createClsMenu 0 addMenu
	  axsMenu.mButton [CLabel "show admitted axioms", blueback, font12,
	  		   magback, Command showAdmitted]

 	  clearS <- win.button [Text "redraw", font12, groove,
			        Command redrawTree]

  	  clearT <- win.button [Text "remove text", font12, groove,
			        Command $ clearText
				        $ action numberedExps := ([],True)]

  	  downBut <- win.button [Text "parse down", font12, greenback, groove,
                                 Command parseTree]

   	  but <- win.button [Text "slow", font12, blueback, groove,
	  		     Command switchFast]
          fastBut := but

 	  fontBut  <- win.menuButton [Text "font", font12]
  	  fontMenu <- fontBut.menu []
	  let mkBut fo = fontMenu.mButton [CLabel fo, font12,
	  				   Command $ setFont fo]
	      families = words "Helvetica Times Courier"
	      mkFonts family = map (family++) [" normal"," bold"," italic"]
	  mapM_ mkBut $ concatMap mkFonts families
	  
	  fontLab <- win.label [Text "font size", Font "Helvetica 10 italic", 
	                        Anchor C]
	  fontSize <- win.slider [From 6, To 66, Orientation Hor, 
	                          CmdInt setFontSize]
	  fontSize.bind [ButtonRelease 1 drawNewCurr]
	  fontSize.setValue 18

	  graphBut  <- win.menuButton [Text "graph", font12]
 	  graphMenu <- graphBut.menu []
  	  graphMenu.mButton [CLabel "expand", font12,
	  		     Command $ expandTree False]
  	  graphMenu.mButton [CLabel "expand one", font12,
	  		     Command $ expandTree True]
  	  graphMenu.mButton [CLabel "split cycles", font12, 
	  		     Command $ removeEdges True]
  	  graphMenu.mButton [CLabel "more tree arcs", font12, 
	  		     Command $ removeEdges False]
  	  graphMenu.mButton [CLabel "compose pointers", font12,
			     Command composePointers]
 	  graphMenu.mButton [CLabel "collapse after simplify", font12, 
			     Command setCollapse]
 	  graphMenu.mButton [CLabel "collapse -->", font12, 
			     Command $ showEqsOrGraph True 4]
 	  graphMenu.mButton [CLabel "collapse level", font12, 
			     Command collapseStep]
 	  graphMenu.mButton [CLabel "collapse <--", font12, 
			     Command $ showEqsOrGraph True 5]
 	  graphMenu.mButton [CLabel "remove copies", font12, 
			     Command removeCopies]
 	  graphMenu.mButton [CLabel "show graph", font12, 
			     Command $ showEqsOrGraph True 6]
 	  graphMenu.mButton [CLabel ".. of transition system", font12, 
			     Command $ showEqsOrGraph True 0, redback]
 	  graphMenu.mButton [CLabel ".. in painter", font12,
			     Command $ initCanvas $ showEqsOrGraph True 1]
 	  graphMenu.mButton [CLabel  $ ".. in "++ other, font12,
			     Command $ showEqsOrGraph False 0]
 	  graphMenu.mButton [CLabel ".. of Kripke model", font12, 
			     Command $ showEqsOrGraph True 2, redback]
 	  graphMenu.mButton [CLabel ".. in painter", font12,
			     Command $ initCanvas $ showEqsOrGraph True 3]
 	  graphMenu.mButton [CLabel  $ ".. in "++ other, font12,
			     Command $ showEqsOrGraph False 2]
 	  graphMenu.mButton [CLabel "show (solved) equations", font12, 
      			     Command $ showEqsOrGraph True 7]
	  graphMenu.mButton [CLabel "show matrix", font12,
			     Command $ showMatrix 3]
	  graphMenu.mButton [CLabel ".. of transition system", font12,
			     Command $ initCanvas $ showMatrix 0, redback]
 	  graphMenu.mButton [CLabel ".. of atom valuation", font12, 
			     Command $ initCanvas $ showMatrix 1, redback]
 	  graphMenu.mButton [CLabel ".. of state valuation", font12, 
			     Command $ initCanvas $ showMatrix 2, redback]
	  graphMenu.mButton [CLabel "show triple matrix", font12,
			     Command $ showMatrix 4]
  	  graphMenu.mButton [CLabel "show relation", font12, 
	  		     Command $ showRelation 3]
 	  graphMenu.mButton [CLabel ".. of transition system", font12, 
	  	             Command $ showRelation 0]
 	  graphMenu.mButton [CLabel ".. of atom valuation", font12, 
	  	             Command $ showRelation 1]
 	  graphMenu.mButton [CLabel ".. of state valuation", font12, 
	  	             Command $ showRelation 2]
  	  graphMenu.mButton [CLabel "show triple relation", font12, 
	  		     Command $ showRelation 4]
	  nodesBut  <- win.menuButton [Text "nodes", font12]
 	  nodesMenu <- nodesBut.menu []
 	  nodesMenu.mButton [CLabel "greatest lower bound", font12, greenback,
			     Command showGlb]
	  nodesMenu.mButton [CLabel "hide values", font12, greenback,
			     Command $ action hideVals := 1]
	  nodesMenu.mButton [CLabel "hide widgets", font12, greenback,
			     Command $ action hideVals := 2]
	  nodesMenu.mButton [CLabel "show values & widgets", font12, greenback,
			     Command $ action hideVals := 0]
	  nodesMenu.mButton [CLabel "predecessors", font12, greenback,
			     Command showPreds]
	  nodesMenu.mButton [CLabel "successors", font12, blueback,
			     Command showSucs]
	  nodesMenu.mButton [CLabel "constructors", font12, blueback,
			     Command $ showSyms constrPositions]
	  nodesMenu.mButton [CLabel "values", font12, blueback,
	  		     Command $ showVals]
	  nodesMenu.mButton [CLabel "variables", font12, blueback,
			     Command $ showSyms varPositions]
	  nodesMenu.mButton [CLabel "free variables", font12, blueback,
	                     Command $ showSyms freePositions]
	  nodesMenu.mButton [CLabel "label roots with entry (l)", font12, 
	  		     magback, Command replaceNodes]
	  nodesMenu.mButton [CLabel "polarities", font12, 
	  		     Command showPolarities]
	  nodesMenu.mButton [CLabel "positions", font12, Command showPositions]
	  nodesMenu.mButton [CLabel "level numbers", font12, 
			     Command $ showNumbers 1]
	  nodesMenu.mButton [CLabel "preorder numbers", font12, 
			     Command $ showNumbers 2]
	  nodesMenu.mButton [CLabel "heap numbers", font12, 
			     Command $ showNumbers 3]
	  nodesMenu.mButton [CLabel "hill numbers", font12, 
			     Command $ showNumbers 4]
	  nodesMenu.mButton [CLabel "coordinates", font12, Command showCoords]
	  nodesMenu.mButton [CLabel "cycle targets", font12, 
	  		     Command showCycleTargets]

  	  horBut <- win.slider [From 0, To 100, Orientation Hor, CmdInt blowHor]
	  horBut.bind [ButtonRelease 1 drawNewCurr]
	  horBut.setValue 15
  	  
	  hsb <- win.scrollBar [Width 12]
	  hsb.attach canv Hor

	  verBut <- win.slider [From 0, To 60, Orientation Ver, CmdInt blowVer]
	  verBut.bind [ButtonRelease 1 drawShrinked]
	  verBut.setValue 35
	  
	  vsb <- win.scrollBar [Width 12]
	  vsb.attach canv Ver

 	  interpreterBut0 <- win.menuButton [Text "tree", font12]
 	  interpreterBut := interpreterBut0
  	  interpreterMenu <- interpreterBut.menu []
  	  mapM_ (createBut interpreterMenu setInterpreter) interpreters

	  minusBut <- win.button [Text "entry-1", font12, greenback, groove, 
	  			  Command $ incrEntry False]

   	  paintBut <- win.button [Text "paint", font12, blueback, groove,
	  			  Command showPicts]

	  plusBut <- win.button [Text "entry+1", font12, greenback, groove, 
	  			 Command $ incrEntry True]

 	  but <- win.button [Text "close", font12, greenback, groove, 
			     Command win.iconify]
	  close := but

 	  but <- win.button [Text "quit", font12, greenback, groove, 
			     Command tk.quit]
	  quit := but
	  
  	  saveBut <- win.button [Text "save pic", font12, groove,
			         Command $ getFileAnd saveGraph]
  	  saveButN <- win.button [Text "save pic to dir", font12, groove,
			          Command saveGraphN]
	  
	  sig     <- win.menuButton [Text "signature", font12b]
  	  sigMenu <- sig.menu []
   	  sigMenu.mButton [CLabel "admit all simplifications and axioms", 
	  		   font12, magback, Command $ setAdmitted' True []]
	  sigMenu.mButton [CLabel ".. except for symbols", font12, magback, 
	  		   Command $ setAdmitted True]
	  sigMenu.mButton [CLabel ".. for symbols", font12, magback,
			   Command $ setAdmitted False]
	  safeBut0 <- sigMenu.mButton [CLabel $ eqsButMsg False, font12, 
	  			       magback, Command switchSafe]
	  safeBut := safeBut0
	  sigMenu.mButton [CLabel "show sig", font12, blueback, Command showSig]
 	  sigMenu.mButton [CLabel "show map", font12, blueback, 
			   Command showSigMap]
 	  sigMenu.mButton [CLabel "apply map", font12, magback,
			   Command applySigMap]
 	  sigMenu.mButton [CLabel "save map to file", font12, greenback,
	                   Command $ getFileAnd saveSigMap]
 	  addMapMenu <- sigMenu.cascade [CLabel "add map", font12, greenback]
  	  addMapMenu.mButton [CLabel "STACK2IMPL", font12, greenback,
	                      Command (addSigMap "STACK2IMPL")]
  	  addMapMenu.mButton [CLabel "from text field", font12, blueback, 
			      Command addSigMapT]
 	  addMapMenu.mButton [CLabel "from file", font12, greenback,
	                      Command $ getFileAnd addSigMap]
 	  sigMenu.mButton [CLabel "remove map", font12, Command removeSigMap]

  	  simplBut <- win.button [Text "simplifyDF", font12, blueback, groove, 
				  Command $ simplify True skip]
	  simplButD := simplBut
  	  simplBut <- win.button [Text "simplifyBF", font12, blueback, groove, 
				  Command $ simplify False skip]
	  simplButB := simplBut

          spec     <- win.menuButton [Text "specification", font12b]
  	  specMenu <- spec.menu []
  	  specMenu.mButton [CLabel "set tree directory (t)", font12, 
	                    Command setTreeDir]
  	  specMenu.mButton [CLabel "re-add", font12, Command reAddSpec]
	  specMenu.mButton [CLabel "remove", font12, 
	                   Command $ removeSpec $ labGreen $ iniSpec++iniSigMap]
 	  specMenu.mButton [CLabel "build Kripke model", font12, redback, 
	                    Command $ buildKripke 2]
 	  specMenu.mButton [CLabel "build last Kripke model", font12, redback, 
	                    Command $ buildKripke 3]
 	  specMenu.mButton [CLabel "build cycle-free model", font12, 
	  		    redback, Command $ buildKripke 0]
 	  specMenu.mButton [CLabel "build pointer-free model", font12, 
	  		    redback, Command $ buildKripke 1]
 	  specMenu.mButton [CLabel "minimize", font12, redback, 
	  		    Command minimize]
	  specMenu.mButton [CLabel "save to file", font12, greenback,
			    Command $ getFileAnd saveSpec]
  	  loadMenu <- specMenu.cascade [CLabel "load text", font12, greenback]
	  createSpecMenu False loadMenu
          addMenu <- specMenu.cascade [CLabel "add", font12, greenback]
	  createSpecMenu True addMenu

	  selectBut <- win.menuButton [Text "transform selection", font12, 
                                       redback]
  	  streeMenu  <- selectBut.menu []
 	  streeMenu.mButton [CLabel "stretch premise", font12, 
			     Command $ stretch True]
 	  streeMenu.mButton [CLabel "stretch conclusion", font12,
	                     Command $ stretch False]
	  streeMenu.mButton [CLabel "instantiate", font12, Command instantiate]
  	  streeMenu.mButton [CLabel "unify", font12, Command unifySubtrees]
 	  streeMenu.mButton [CLabel "generalize", font12, Command generalize]
 	  streeMenu.mButton [CLabel "specialize", font12, redback, 
			     Command specialize]
  	  streeMenu.mButton [CLabel "decompose atom", font12, 
			     Command decomposeAtom]
	  streeMenu.mButton [CLabel "replace by other sides of in/equations",
			     font12, Command replaceSubtrees]
 	  streeMenu.mButton [CLabel "use transitivity", font12, 
	  		     Command applyTransitivity]
 	  applyM <- streeMenu.cascade [CLabel "apply clause", font12, redback]
 	  applyM.mButton [CLabel "Left to right (Left)", font12, greenback,
	                  Command $ applyClause False False False]
	  applyM.mButton [CLabel ".. and save redex", font12,
	                  Command $ applyClause False False True]
 	  applyM.mButton [CLabel "Left to right lazily", font12, greenback,
	                  Command $ applyClause True False False]
	  applyM.mButton [CLabel ".. and save redex", font12,
	                  Command $ applyClause True False True]
	  applyM.mButton [CLabel "Right to left (Right)", font12, redback,
	                  Command $ applyClause False True False]
	  applyM.mButton [CLabel ".. and save redex", font12,
	                  Command $ applyClause False True True]
	  applyM.mButton [CLabel "Right to left lazily", font12, redback,
	                  Command $ applyClause True True False]
	  applyM.mButton [CLabel ".. and save redex", font12,
	                  Command $ applyClause True True True]
	  streeMenu.mButton [CLabel "move up quantifiers", font12, 
			     Command shiftQuants]
	  streeMenu.mButton [CLabel "shift subformulas", font12, redback,
			     Command shiftSubs]
 	  streeMenu.mButton [CLabel "coinduction", font12, redback, 
	                     Command $ startInd False]
	  streeMenu.mButton [CLabel "induction", font12, redback, 
	                     Command $ startInd True]
	  streeMenu.mButton [CLabel "create Hoare invariant", font12,
	  		     magback, Command $ createInvariant True]
 	  streeMenu.mButton [CLabel "create subgoal invariant", font12,
	  		     magback, Command $ createInvariant False]
	  streeMenu.mButton [CLabel "flatten (co-)Horn clause", font12, 
	                     Command flattenImpl]
 	  streeMenu.mButton [CLabel "shift pattern to rhs", font12, 
	  		     Command shiftPattern]
 	  streeMenu.mButton [CLabel $ "replace by tree of "++ other, font12,
			     Command replaceOther]
	  streeMenu.mButton [CLabel $ "unify with tree of "++ other, font12,
			     Command unifyOther]
	  streeMenu.mButton [CLabel "build unifier", font12, 
			     Command buildUnifier]
  	  streeMenu.mButton [CLabel "subsume", font12, redback,
			     Command subsumeSubtrees]
  	  streeMenu.mButton [CLabel "evaluate", font12, redback,
			     Command evaluateTrees]
	  streeMenu.mButton [CLabel "copy (c)", font12, Command copySubtrees]
	  streeMenu.mButton [CLabel "remove (r)", font12, 
	  		     Command removeSubtrees]
	  streeMenu.mButton [CLabel "remove node", font12, Command removeNode]
	  streeMenu.mButton [CLabel "random labels (L)", font12, 
	   		     Command randomLabels]
	  streeMenu.mButton [CLabel "random tree (T)", font12,
	  		     Command randomTree]
	  streeMenu.mButton [CLabel "remove path (p)", font12, 
	  		     Command removePath]
	  streeMenu.mButton [CLabel "reverse", font12, Command reverseSubtrees]
 	  streeMenu.mButton [CLabel "insert/replace by text (i)", font12, 
			     magback, Command replaceText]

  	  subBut <- win.button [Text "set", font12, greenback, groove,
			        Command setSubtrees]

          subsBut  <- win.menuButton [Text "substitution", font12]
          subsMenu <- subsBut.menu []
	  subsMenu.mButton [CLabel "add from text field", font12, blueback, 
	  		    Command addSubst]
   	  subsMenu.mButton [CLabel "apply", font12, magback, Command applySubst]
 	  subsMenu.mButton [CLabel "rename", font12, Command renameVar]
 	  subsMenu.mButton [CLabel "remove", font12, Command removeSubst]
 	  subsMenu.mButton [CLabel "show", font12, blueback,
 	  		    Command $ showSubst True]
 	  subsMenu.mButton [CLabel  $ ".. in text field of "++ other, font12,
			    Command $ showSubst False]
 	  subsMenu.mButton [CLabel  $ ".. on canvas of "++ other, font12,
			    Command showSubstCanv]
 	  subsMenu.mButton [CLabel ".. solutions", font12, magback, 
	                    Command showSolutions]

	  but <- win.menuButton [Text "apply to", font9, blueback, groove]
 	  subToBut := but

 	  tedit0 <- win.textEditor [Height 1, Font "Courier 12"]
	  tedit := tedit0
	  tedit.bind [KeyPress "Up" parseText, 
	  	      KeyPress "Down" parseTree]

          ths     <- win.menuButton [Text "theorems", font12b]
  	  thsMenu <- ths.menu []
 	  thsMenu.mButton [CLabel "remove theorems", font12, blueback, 
			   Command removeTheorems]
   	  thsMenu.mButton [CLabel ".. in entry field", font12, blueback,
	                   Command $ removeClauses 1]
  	  thsMenu.mButton [CLabel "show theorems", font12, blueback, 
	                   Command $ showTheorems True]
	  thsMenu.mButton [CLabel $ ".. in text field of "++ other, font12,
			   blueback, Command $ showTheorems False]
  	  thsMenu.mButton [CLabel ".. for symbols", font12, blueback,
			   Command showTheoremsFor]
 	  addMenu <- thsMenu.cascade [CLabel "add theorems", font12, blueback]
	  createClsMenu 1 addMenu
	  thsMenu.mButton [CLabel "remove conjects", font12, magback,
			   Command removeConjects]
   	  thsMenu.mButton [CLabel ".. in entry field", font12, magback,
	                   Command $ removeClauses 2]
	  thsMenu.mButton [CLabel "show conjects", font12, magback, 
	                   Command showConjects]
   	  thsMenu.mButton [CLabel ".. in entry field", font12, magback,
	                   Command $ removeClauses 3]
	  thsMenu.mButton [CLabel "show terms", font12, magback, 
	                   Command showTerms]
	  thsMenu.mButton [CLabel "show induction hypotheses", font12, magback, 
	                   Command showIndClauses]
          addMenu <- thsMenu.cascade [CLabel "add conjects", font12, magback]
	  createClsMenu 2 addMenu

 	  tsb <- win.scrollBar [Width 12]
	  tsb.attach tedit0 Ver
	  
	  but <- win.menuButton [Text "load", font12, blueback]
	  treeBut := but

  	  treeMenu <- treeBut.menu []
	  enumMenu <- treeMenu.cascade [CLabel "call enumerator", font12]
  	  mapM_ (createBut enumMenu callEnum) enumerators
	  treeMenu.mButton [CLabel "remove other trees", font12, 
			    Command removeOthers]
  	  treeMenu.mButton [CLabel "show changed", font12, Command showChanged]
 	  treeMenu.mButton [CLabel "show proof", font12, blueback, 
	                    Command $ showProof True]
	  treeMenu.mButton [CLabel $ ".. in text field of "++ other, font12, 
			    blueback, Command $ showProof False]
	  treeMenu.mButton [CLabel "save proof to file (s)", font12, blueback,
			    Command saveProof]
 	  treeMenu.mButton [CLabel "show proof term", font12, magback, 
	                    Command $ showProofTerm True]
	  treeMenu.mButton [CLabel $ ".. in text field of "++ other, font12, 
			    magback, Command $ showProofTerm False]
	  treeMenu.mButton [CLabel "check proof term from file", font12, 
			    magback, Command $ checkProofF False]
	  treeMenu.mButton [CLabel ".. in painter", font12, 
			    magback, Command $ checkProofF True]
	  treeMenu.mButton [CLabel ".. from text field", font12, 
	  		    magback, Command $ checkProofT False]
	  treeMenu.mButton [CLabel ".. in painter", font12, 
			    magback, Command $ checkProofT True]
	  treeMenu.mButton [CLabel "create induction hypotheses", font12, 
			    redback, Command createIndHyp]
	  treeMenu.mButton [CLabel "save trees to file", font12, greenback,
			    Command $ getFileAnd saveTrees]
	  loadMenu <- treeMenu.cascade [CLabel "load text", font12, greenback]
	  mapM_ (createBut loadMenu loadText) treefiles
	  loadMenu.mButton [CLabel "from file (Up)", font12, greenback,
		            Command $ getFileAnd loadText]
	  
	  treeSize <- win.slider [From 1, To 1000, Orientation Hor, 
	                          CmdInt setMaxHeap]
	  treeSize.bind [ButtonRelease 1 drawNewCurr]
	  treeSize.setValue 100

  	  upBut <- win.button [Text "parse up", font12, greenback, groove, 
  	  		       Command parseText]
	  
  	  pack $col [fillX $ row [lab,lab2],
	  	     canv <<< fillY vsb,
		     fillX hsb, 
		     fillX treeSize,
		     fillX treeSlider,
		     tedit0 <<< fillY tsb, 
		     fillX ent, 
		     fillX $ fillY verBut <<<
			     col [horBut,fontSize,fontLab <<< fontBut] <<<
			     col [row [treeBut,selectBut,spec,sig,axs,ths],
				  row [col [interpreterBut,paintBut,fastBut],
				       col [splitBut <<< hideBut,
					    minusBut <<< subBut <<< plusBut],
				       col [upBut <<< clearT <<< downBut,
				            matchBut <<< narrowBut <<< simplButD 
					   	     <<< simplButB],
			               col [clearS <<< saveBut <<< saveButN,
				            graphBut <<< subsBut,
					    nodesBut <<< subToBut]]] <<<
			     fillY canvSlider <<<
              		     col [backBut,forwBut,deriveBut,close,quit]]
              		     
	  continue

-- end of buildSolve

-- The other methods of solver are listed in alphabetical order:

	adaptPos (x,y) = do 
	  (leftDivWidthX,_) <- canv.xview
	  (topDivWidthY,_) <- canv.yview
	  let (bt,ht) = fromInt2 canvSize
	  return (x+round (leftDivWidthX*bt),y+round (topDivWidthY*ht))

	addAxioms t file continue = action
          sig <- getSignature
	  let cls = filter (not . isAxiom sig) axs
	      axs = if isConjunct t then subterms t else [t]
	      newSimpls sym = foldr f [] axs
	        where f (F x [t,u]) simpls | x == sym = (t,[],u):simpls
	              f (F "==>" [c,F x [t,u]]) simpls 
		    		           | x == sym = (t,mkFactors c,u):simpls
                      f _ simpls		      = simpls
	  if null cls 
	     then solPositions := []; axioms := joinTerms axs axioms
		  simplRules := simplRules ++ newSimpls "==" ++ newSimpls "<==>"
		  transRules := transRules ++ newSimpls "->"
		  iniStates := []
		  labGreen $ newCls "axioms" file
		  continue
	  else enterFormulas cls
	       labRed "The clauses in the text field are not axioms."
	
	addClauses treetype file = action
	  str <- if text then getTextHere else lookupLibs tk file
	  let str' = removeComment 0 str
	      file' = if text then "the text field" else file
	  sig <- getSignature
	  case treetype of 0 -> case parseE (implication sig) str' of
	                             Correct t -> addAxioms t file' done
				     p -> incorrect p str' illformedF
			   1 -> case parseE (implication sig) str' of
	                       	     Correct t -> addTheorems t file' done
				     p -> incorrect p str' illformedF
			   _ -> parseConjects sig file' str' done
	  where text = null file

	addSigMap file = action str <- lookupLibs tk file
	  			parseSigMap file $ removeComment 0 str

	addSigMapT = action str <- getTextHere; parseSigMap "the text field" str

	addSpec b continue file = action
	  if not checking then
	     if b then specfiles := file:specfiles
	     str <- get
	     if null str then labRed $ file ++ " is not a file name."
	     else let (sig,axs,ths,conjs,ts) = splitSpec $ removeComment 0 str
	              act1 = action
		           sig <- getSignature
	                   if onlySpace axs then act2 sig
	                      else case parseE (implication sig) axs of
	                           Correct t -> addAxioms t file' $ f $ act2 sig
				   p -> incorrect p axs illformedF
	              act2 sig = action 
		            if onlySpace ths then act3 sig
			    else case parseE (implication sig) ths of
	                         Correct t -> addTheorems t file' $ f $ act3 sig
	                         p -> incorrect p ths illformedF
	              act3 sig = action 
		   	       if onlySpace conjs then act4 sig
		   	       else parseConjects sig file' conjs $ f $ act4 sig
	              act4 sig = action 
		   	       if onlySpace ts then f continue
		               else parseTerms sig file' ts continue
	          if onlySpace sig then act1 else parseSig file' sig $ f act1
	  where (file',get) = if null file then ("the text field",getTextHere)
	                                   else (file,lookupLibs tk file)
		f = delay 100
		onlySpace = all (`elem` " \t\n")

	addSpecWithBase "base" = addSpec True skip "base"
	addSpecWithBase file   = addSpec True (addSpec True skip file) "base"
	
	addSubst = action
	  sig <- getSignature
	  str <- getTextHere
 	  case parseE (conjunct sig) str of
	  Correct t 
	    -> if hasPos t then labRed posInSubst
	       else case eqsToSubst $ mkFactors t of
	                 Just (f,dom) -> let (g,xs) = substitution
		                         setSubst (g `andThen` f, xs `join` dom)
					 labGreen extendedSubst
		         _ -> labRed illformedS
	  p -> incorrect p str illformedS

	addText ls = action forall l <- addNo 0 $ concatMap split ls
	                           do tedit.insertLines maxBound [l]
	  where addNo :: Int -> [String] -> [String]
	        addNo _ []               = []
	        addNo n ([]:ls)          = []:addNo n ls
	        addNo 0 ((' ':l):ls)     = (" 0> " ++ l):addNo 1 ls
	        addNo n ((' ':l):ls)     = ("    " ++ l):addNo n ls
	        addNo n (('.':l):ls)     = ("   ." ++ l):addNo n ls
	        addNo n (l:ls) | n < 10  = (' ':show n ++ '>':l):f n
	                       | True    = (show n ++ '>':l):f n
                                           where f n = addNo (n+1) ls
	        split [] 		 = []
	        split l | length l <= 85 = [l]
	                | True           = take 85 l:split ('.':drop 85 l)
	
	addTheorems t file continue = action
	  sig <- getSignature
	  theorems := joinTerms (if isConjunct t then subterms t else [t])
	                        theorems
	  labGreen $ newCls "theorems" file
	  continue

	applyClause lazy invert saveRedex = action
 	  if null trees then labBlue start
	  else str <- ent.getValue
	       let (exps,b) = numberedExps
	       case parse nat str of
	            k@(Just n) | n < length exps
	              -> if b then stretchAndApply k $ exps!!n
		              else labMag "Enter formulas into the text field!"
                    _ -> sig <- getSignature
	                 str <- getTextHere
 	                 case parseE (implication sig) str of
	                      Correct cl -> stretchAndApply Nothing cl
	                      p -> incorrect p str illformedF
	  where stretchAndApply k cl = action 
	         if lazy then 
		    let zNo = varCounter "z"
                    case preStretch True (const True) cl of
	            Just (_,varps) -> setZcounter n; finish clp
			              where (clp,n) = stretchPrem zNo varps cl
		    _ -> case preStretch False (const True) cl of
	                 Just (_,varps) -> setZcounter n; finish clc
			                where (clc,n) = stretchConc zNo varps cl
		         _ -> notStretchable "The left-hand side of the theorem"
		 else finish cl
	         where finish cl = applyTheorem saveRedex k $
                                          if invert then invertClause cl else cl

	applyCoinduction limit = action
	  let t = trees!!curr
	      qs@(p:ps) = emptyOrAll treeposs
	      rs@(r:_) = map init qs
	      u = getSubterm t r
	      str = "COINDUCTION"
	      g = stretchConc $ varCounter "z"
	      getAxioms = flip noSimplsFor axioms
	  if notnull qs && any null ps then labRed $ noApp str
	  else sig <- getSignature
	       let h x = if x `elem` fst newPreds then getPrevious x else x
		   conjs@(conj:_) = map (mapT h) $ map (getSubterm t) qs
		   f = preStretch False sig.isCopred
	       if null ps && universal sig t p conj
	          then case f conj of
	               Just (x,varps)
		         -> let (conj',k) = g varps conj
	  	            setZcounter k
			    applyInd limit False str [conj'] [x] (getAxioms [x])
			    	     t p []
		       _ -> notStretchable "The conclusion"
	       else if allEqual rs && isConjunct u && universal sig t r u then
		       case mapM f conjs of
		       Just symvarpss
		         -> let (xs,varpss) = unzip symvarpss
				(conjs',ks) = unzip $ zipWith g varpss conjs
			        ys = mkSet xs
 			    varCounter := updMax varCounter "z" ks
		            applyInd limit False str conjs' ys (getAxioms ys) t
			    	     r $ restInd (subterms u) qs
		       _ -> notStretchable "Some conclusion"
	            else labRed $ noApp str

	applyDisCon k (F "|" ts) redices t ps sig msg =
	  applyDisCon k (F "<===" [F "|" ts,mkTrue]) redices t ps sig msg
	applyDisCon k (F "&" ts) redices t ps sig msg =
	  applyDisCon k (F "<===" [F "&" ts,mkTrue]) redices t ps sig msg
	applyDisCon k (F "<===" [F "|" ts,prem]) redices t ps sig msg = action
	  let pred = glbPos ps
	      u = getSubterm t pred
	      qs = map (restPos pred) ps
	  if all noQuantsOrConsts ts && polarity True t pred &&
	     isDisjunct u && all (isProp ||| isAnyQ) (sucTerms u qs) then
	     finishDisCon k False True ts prem redices t ps pred qs sig msg
	  else labRed $ noAppT k
	applyDisCon k (F "<===" [F "&" ts,prem]) redices t ps sig msg = action
	  let pred = glbPos ps
	      u = getSubterm t pred
	      qs = map (restPos pred) ps
	  if all noQuantsOrConsts ts && polarity True t pred &&
	     isConjunct u && all (isProp ||| isAllQ) (sucTerms u qs) then
	     finishDisCon k False False ts prem redices t ps pred qs sig msg
	  else labRed $ noAppT k
	applyDisCon k (F "===>" [F "&" ts,conc]) redices t ps sig msg = action
	  let pred = glbPos ps
	      u = getSubterm t pred
	      qs = map (restPos pred) ps
	  if all noQuantsOrConsts ts && polarity False t pred &&
	     isConjunct u && all (isProp ||| isAllQ) (sucTerms u qs) then
	     finishDisCon k True True ts conc redices t ps pred qs sig msg
	  else labRed $ noAppT k
	applyDisCon k (F "===>" [F "|" ts,conc]) redices t ps sig msg = action
	  let pred = glbPos ps
	      u = getSubterm t pred
	      qs = map (restPos pred) ps
	  if all noQuantsOrConsts ts && polarity False t pred &&
	     isDisjunct u && all (isProp ||| isAnyQ) (sucTerms u qs) then
	     finishDisCon k True False ts conc redices t ps pred qs sig msg
	  else labRed $ noAppT k
	  
	applyInd limit ind str conjs indsyms axs t p rest = action
	  sig <- getSignature
	  let (ps0,cps0) = newPreds
	      syms = if ind then cps0 else ps0
	      vc1 = decrVC varCounter syms
	      oldIndsyms = map getPrevious syms
	      indsyms' = indsyms `join` oldIndsyms
	      (f,vc2) = renaming vc1 indsyms'
	      axs0 = map mergeWithGuard axs
	      (axs1,vc3) = iterate h (axs0,vc2)!!limit
	      h (axs,vc) = applyToHeadOrBody sig 
	                   (((`elem` indsyms') .) . label) False axs0 axs vc
	      (newAxs,axs2) = (map mkAx conjs,map g axs1)
	      mkAx (F x [t,u]) = F x [g t,u]; mkAx _ = error "applyInd"
              -- g replaces a logical predicate r by f(r) and an equation h(t)=u
              -- with h in xs by the logical atom f(h)(t,u).
              g eq@(F "=" [F x ts,u]) = if x `elem` indsyms' 
	     			        then F (f x) $ ts++[u] else eq
              g (F x ts)              = F (f x) $ map g ts
              g t                     = t
	      rels = map f indsyms
	      crels = map mkComplSymbol rels
	      (ps',cps') = if ind then (crels,rels) else (rels,crels)
	      beqs = filter isBeq ps'
	      newAxs1 = newAxs `join` joinMap equivAxs (map f beqs)
	      (ps,cps,cs,ds,fs,hs) = symbols
	  symbols := (ps `join` ps',cps `join` cps',cs,ds,fs,hs)
	  newPreds := (ps0 `join` ps',cps0 `join` cps')
	  sig <- getSignature
	  let (cls,vc4) = applyToHeadOrBody sig (const2 True) True 
	  					newAxs axs2 vc3
	      conj = mkConjunct cls
	      xs = [x | x <- frees sig conj, noExcl x]
	      u = replace t p $ mkConjunct $ mkAll xs conj:rest
	      msg = "Adding\n\n" ++ showFactors newAxs1 ++ 
	            "\n\nto the axioms and applying " ++ str ++ " wrt\n\n" ++ 
		    showFactors axs1 ++ "\n\n"
	  indClauses := indClauses `join` newAxs1
	  axioms := axioms `join` newAxs1
	  varCounter := vc4
	  proofStep := Induction ind limit
	  maybeSimplify sig u $ makeTrees sig 
	  		      $ do setProofTerm proofStep
		                   setTreesFrame [] $ setProof True True msg [p] 
				 	            $ indApplied str

 	applyInduction limit = action
	  let t = trees!!curr
	      qs@(p:ps) = emptyOrAll treeposs
	      rs@(r:_) = map init qs
	      u = getSubterm t r
	      str = "FIXPOINT INDUCTION"
	      g = stretchPrem $ varCounter "z"
	  if notnull qs && any null ps then labRed $ noApp str
	  else sig <- getSignature
	       let h (F x ts) = if x `elem` snd newPreds 
		   		then if sig.isPred z then F z ts
			             else mkEq (F z $ init ts) $ last ts
			        else F x $ map h ts where z = getPrevious x
		   h t 	      = t
		   conjs@(conj:_) = map (h . getSubterm t) qs
		   f = preStretch True $ sig.isPred ||| sig.isDefunct
		   getAxioms ks xs = unzip $ map g $ noSimplsFor xs axioms
			where g = flatten (maximum ks) $ filter sig.isDefunct xs
	       if null ps && universal sig t p conj 
	          then case f conj of
	               Just (x,varps)
		         -> let (conj',k) = g varps conj
		    	        (axs,ms) = getAxioms [k] [x]
		            varCounter := updMax varCounter "z" ms
			    applyInd limit True str [conj'] [x] axs t p []
		       _ -> notStretchable "The premise"
               else if allEqual rs && isConjunct u && universal sig t r u then 
	       	       case mapM f conjs of
		       Just symvarpss
		         -> let (xs,varpss) = unzip symvarpss
			        (conjs',ks) = unzip $ zipWith g varpss conjs
				ys = mkSet xs
				(axs,ms) = getAxioms ks ys
		            varCounter := updMax varCounter "z" ms
			    applyInd limit True str conjs' ys axs t r $
			             restInd (subterms u) qs
		       _ -> notStretchable "Some premise"
		    else labRed $ noApp str

	applySigMap = action
	  if null trees then labBlue start
	  else sig <- getSignature
	       sig' <- solve.getSignatureR
	       case applySignatureMap sig sig' (fst signatureMap) $ trees!!curr
	            of Just t -> solve.bigWin; solve.enterTree formula t
	       	       _ -> labRed $ sigMapError other

	applySubst = action
          if null trees then labBlue start
	  else sig <- getSignature
	       let t = trees!!curr
	           (g,dom) = substitution
		   f t p = replace t p $ getSubterm t p>>>g
	       	   ts = substToEqs g dom
		   ps = emptyOrAll treeposs
		   msg = "The substitution\n\n" ++ showFactors ts ++ "\n\n"
	       trees := updList trees curr $ foldl f t ps
	       setProofTerm ApplySubst
	       setProof False False msg ps subsAppliedToAll
	       clearTreeposs; drawCurr

	applySubstTo x = action
	  if null trees then labBlue start 
	                else applySubstTo' x $ fst substitution x

	applySubstTo' x v = action
          let t = trees!!curr
	      p = emptyOrLast treeposs
	      msg = "SUBSTITUTING " ++ showTerm0 v ++ " for " ++ x
	  sig <- getSignature
	  case isAny t x p of
	  Just q | polarity True t q -> finish (q++[0]) t sig msg True
	  _ -> case isAll t x p of
	       Just q | polarity False t q -> finish (q++[0]) t sig msg True
	       _ -> finish p t sig msg False
	  where finish p t sig msg b = action
	  	        trees := updList trees curr t'
			setProofTerm $ ApplySubstTo x v
		        drawThis t' (map (p++) $ freeXPositions sig x u) "green"
			setProof b False msg [p] $ subsAppliedTo x
			where t' = replace t p $ u>>>for v x; u = getSubterm t p

 	applyTheorem saveRedex k th = action
	  sig <- getSignature
          proofStep := Theorem saveRedex th
	  let t = trees!!curr
	      ps = emptyOrAll treeposs
	      redices = map (getSubterm t) ps
	      n = length ps
              ([th'],vc) = renameApply [if saveRedex then copyRedex th else th] 
	      			       sig t varCounter
	      f t (redex:rest) (p:ps) qs vc 
                            = action case applySingle th' redex t p sig vc of
		                          Just (t,vc) -> f t rest ps (p:qs) vc
	                                  _ -> f t rest ps qs vc
	      f _ _ _ [] _  = labRed $ notUnifiable k
	      f t _ _ qs vc = action varCounter := vc
			             maybeSimplify sig t $ makeTrees sig 
				     			 $ finish qs
              str = showTree False $ case th of F "===>" [F "True" [],th] -> th 
					        F "<===" [F "False" [],th] 
				                  -> mkNot sig th
					        _ -> th 
              finish qs = action
                     setProofTerm proofStep
		     setTreesFrame [] $ setProof True True (applied True str) qs
		      		      $ thApplied k
	  if nothing k then enterText str
	  if isTaut th then varCounter := vc; f t redices ps [] vc 
	  else if n > 1 && isDisCon th && n == noOfComps th 
	          then varCounter := vc
	               applyDisCon k th' redices t ps sig $ applied True str
	       else if saveRedex || isGuarded isEquiv th || 
	               all (correctPolarity t) ps then
	               if isAxiom sig th 
		          then narrowOrRewritePar t sig k [th] saveRedex ps skip
		          else if isTheorem th then varCounter := vc
                          		            f t redices ps [] vc 
		                               else labRed $ noTheorem k
	            else labRed $ noAppT k
	  where correctPolarity t p = isHornT th && b || isCoHornT th && not b
				      where b = polarity True t p

	applyTransitivity = action
 	  if null trees || not formula then labBlue startF
	  else let t = trees!!curr
	           ps = emptyOrAll treeposs
		   redices = map (getSubterm1 t) ps
	       case redices of
	       F x [l,r]:ts
	         -> let p:qs = ps
		        n = varCounter "z"
			z = 'z':show n
			n' = n+1
		    if transitive x && null qs && polarity True t p then
		       let u = anyConj [z] [F x [l,V z],F x [V z,r]]
		       trees := updList trees curr $ replace1 t p u
		       setZcounter n'
 		    else let z' = 'z':show n'
			     u = if qs == [p++[0]]
				 then anyConj [z] [mkEq l $ V z,F x [V z,r]]
			         else if qs == [p++[1]]
				      then anyConj [z] [F x [l,V z],
				      			mkEq (V z) r]
			              else anyConj [z,z'] [mkEq l $ V z,
						           F x [V z,V z'],
					                   mkEq (V z') r]
			 trees := updList trees curr $ replace1 t p u
		         setZcounter $ n'+1
                    finish ps
	       _ -> if any null ps then labMag "Select proper subtrees!"
                    else let qs = map init ps
			     q = head qs
		             u = getSubterm t q
	                 if allEqual qs && isConjunct u then
		            case transClosure redices of
	                    Just v
			      -> if polarity False t q then
				    let us = v:removeTerms (subterms u) redices
		                        t' = replace1 t q $ mkConjunct us
				    trees := updList trees curr t'
			            finish ps
			         else labRed $ noApp "Transitivity"
		            _ -> labMag "Select composable atoms!"
                         else labRed $ noApp "Transitivity"
	  where anyConj xs = mkAny xs . F "&"
	        finish ps = action setProofTerm ApplyTransitivity
		                   setProof True False "TRANSITIVITY" ps
				   	    transitivityApplied
	            		   clearTreeposs; drawCurr

	backProof = action 
	  if restore then treeposs := oldTreeposs; restore := False; drawCurr
          else if checking then checkBackward
	       else if proofPtr < 1 then labMag emptyProof
                    else let ps = (proof!!proofPtr).treePoss
			 proofPtr := proofPtr-1; changeState proofPtr ps
	            let n = searchback deriveStep $ take proofTPtr proofTerm
		    proofTPtr := if just n then get n else 0

	backWin = action win.iconify

	bigWin = action win.deiconify; win.raise

	blowHor i = action spread := (i,snd spread) 
	                   paint.setEval picEval spread

	blowVer i = action spread := (fst spread,i)
			   paint.setEval picEval spread

	buildKripke mode = action
	  sig <- getSignature
	  str <- ent.getValue
	  let pcs = sig.isDefunct "procs"
	      noProcs = case parse pnat str of Just n -> n; _ -> 2
	  iniStates := if null iniStates
	               then [t | (F "states" _,_,t) <- simplRules] 
	               else iniStates
	  simplRules := if pcs then (leaf "procs",[],mkConsts [0..noProcs-1]):
	   			    (leaf "states",[],head iniStates):
	  			    [rule | rule@(t,_,_) <- simplRules,
	  		                    root t `notElem` ["procs","states"]]
		               else simplRules
 	  sig <- getSignature
 	  let states = simplify sig "states"
 	      atoms = simplify sig "atoms" 
 	      labels = simplify sig "labels" 
  	  kripke := (states,atoms,labels,[],[],[],[])
	  simplRules := (leaf "states",[],mkList states):
	                (leaf "atoms",[],mkList atoms):
	                (leaf "labels",[],mkList labels):
	                [rule | rule@(t,_,_) <- simplRules,
	  		        root t `notElem` ["states","atoms","labels"]]
 	  stateIndex := 0
 	  rewrites := []
 	  rewritesL := []
 	  while stateIndex < length states do
 	   sig <- getSignature
 	   let (sts,rs,rsL) = rewriteStates mode (stateIndex+1 == length states)
 	   			     sig (states!!stateIndex) rewrites rewritesL
  	       tr = pairsToInts sts sts rs
	       trL = tripsToInts sts sts sig.labels rsL
	   kripke := (sts,sig.atoms,sig.labels,tr,trL,[],[])
	   simplRules := (leaf "states",[],mkList sts):
	                 [rule | rule@(t,_,_) <- simplRules, root t /= "states"]
	   stateIndex := stateIndex+1
	   rewrites := rs
 	   rewritesL := rsL
	                
	  sig <- getSignature
	  let (rs,rsL) = rewriteAtoms sig
 	      va = pairsToInts sig.atoms sig.states rs
	      vaL = tripsToInts sig.atoms sig.states sig.labels rsL
	  kripke := (sig.states,sig.atoms,sig.labels,sig.trans,sig.transL,va,
	  	     vaL)
	  	     
	  setProofTerm $ BuildKripke mode
	  labGreen $ kripkeBuilt mode pcs noProcs (length sig.states) 
	                         (length sig.labels) $ length sig.atoms
	  where simplify sig x = case simplifyIter sig $ F x [] of 
	  						 F "[]" ts -> ts
							 _ -> []
                pairsToInts ts us ps = map f ts
 			 where f t = searchAll (`elem` (get $ lookup t ps)) us
 		tripsToInts ts us vs ps = map f ts
 	                 where f t = map (flip (g t) us) vs
 	                       g t u = searchAll (`elem` (get $ lookupL t u ps))

	buildUnifier = action if length treeposs /= 2 || any null treeposs
	                         then labMag "Select two proper subtrees!"
	                         else let t = trees!!curr
		 		          [p,q] = treeposs
		   			  u = getSubterm t p
		   			  v = getSubterm t q
	       			      unifyAct u v t t p q

	callEnum str = action
	  (formula,joined,wtree) := (False,False,False); matching := 0
	  splitBut.set [Text "join"]
	  matchBut.set [Text "match & rewrite",blueback]
	  mapM_ (\b -> b.set [blueback]) 
	  	[deriveBut,narrowBut,simplButD,simplButB]	  
	  clearTreeposs
	  let eval = if str == "palindrome" then "alignment" else str
	  setInterpreter eval
	  sig <- getSignature
	  let ts = case simplifyIter sig $ F "compl" [] of F "[]" us -> us
	  						   _ -> []
	      compl = curry $ setToFun $ zipWith f (evens ts) $ odds ts
	              where f t u = (showTerm0 t,showTerm0 u)
	      compl' = if eval == "alignment" then compl else const2 False
	  enum.buildEnum str compl'

	catchNode pt = action
	  if null treeposs then labMag "Select a target node!"
	  else (x,y) <- adaptPos pt
               case getSubtree (get ctree) x y of
               Just (p,cu) -> let z = root cu
			      if last treeposs <<= p then drawNode z cyan
	    					     else drawNode z magenta
			      node := Just (z,p)
			      canv.set [Cursor "sb_up_arrow"]
	       _ -> done

   	catchSubtree pt = action
	  if notnull trees
	     then (x,y) <- adaptPos pt
                  let Just ct = ctree
                  case getSubtree ct x y of
                  Just (p,cu) 
                     | p `elem` treeposs -> setTreeposs $ Remove p
				            drawSubtrees     -- deselect subtree
		     | True -> isSubtree := Just False       -- select subtree
		               setTreeposs (Add [p])
	                       node := Just (root cu,p)
		               penpos := Just pt
		               subtree := Just cu
		               suptree := Just ct
	   	               canv.set [Cursor "hand2"]
		               drawSubtrees 
	          _ -> if notnull treeposs		     -- deselect last
		          then setTreeposs $ Remove $ last treeposs
	                       drawSubtrees 

   	catchTree pt = action
	  if notnull trees then
	     (x,y) <- adaptPos pt
	     let Just ct = ctree
	     case getSubtree ct x y of
	          Just (p,cu) | p `elem` treeposs 
	            -> isSubtree := Just True
		       let a = root cu	  			-- cut subtree
		       node := Just (a,p); penpos := Just pt
		       subtree := Just cu
		       suptree := Just $ replace0 ct p $ V a
		       canv.set [Cursor "hand2"]
	          _ -> isSubtree := Just False
		       penpos := Just pt
		       canv.set [Cursor "crosshair"]            -- move tree
	  
	changeMode t = action 
	  sig <- getSignature
	  let b = isFormula sig t
	      str = if b then "formula" else "term"
	  if b /= formula then formula := b; treeMode := "tree"; trees := [t]
	  		       counter := upd counter 't' 1
			       curr := 0; treeSlider.set [To 0] 
			       paint.setCurrInPaint 0; treeBut.set [Text str]
			       setMatch False
			  else trees := updList trees curr t

	changeState ptr ps = action 
	  let proofElem = proof!!ptr
	  trees := proofElem.trees
	  counter := upd counter 't' $ length trees
	  treeMode := proofElem.treeMode
	  curr := proofElem.curr
       -- perms := proofElem.perms
	  varCounter := proofElem.varCounter
	  newPreds := proofElem.newPreds
	  solPositions := proofElem.solPositions
	  constraints := proofElem.constraints
	  joined := proofElem.joined
	  safe := proofElem.safe
	  setTreesFrame ps $ setSubst proofElem.substitution
	  labGreen proofElem.msgL
	  safeBut.set [CLabel $ eqsButMsg $ not safe]	  
	  splitBut.set [Text $ if joined then "split" else "join"]

	checkBackward = action 
	  if proofTPtr < 1 then labMag emptyProof
	   			paint.labSolver emptyProof
	  			enterPT proofTPtr proofTerm
	  else proofTPtr := proofTPtr-1
	       case proofTerm!!proofTPtr of 
                    Mark _ -> treeposs := []; drawCurr
		    Match _ -> matchTerm := init matchTerm
			       matching := last matchTerm
		    DeriveMode _ _ -> simplTerm := init simplTerm
			              simplifying := last simplTerm
				      refuteTerm := init refuteTerm
			              refuting := last refuteTerm
		    NegateAxioms ps1 cps1 
		      -> symbols := (minus ps ps2,minus cps cps2,cs,ds,fs,hs)
		         axioms := axioms `minus` axs
			 if proofPtr > 0 
			    then proofPtr := proofPtr-1
			         labColorToPaint green (proof!!proofPtr).msgL
		         where (ps,cps,cs,ds,fs,hs) = symbols
			       ps2 = map mkComplSymbol cps1
			       cps2 = map mkComplSymbol ps1
			       axs = noSimplsFor (ps2++cps2) axioms
	  	    _ -> if proofPtr > 0 then
		            proofPtr := proofPtr-1
		            changeState proofPtr $ (proof!!proofPtr).treePoss
	       enterPT proofTPtr proofTerm

        checkForward = action
          if proofTPtr >= length proofTerm then labMag endOfProof
	          				paint.labSolver endOfProof
	          				enterPT proofTPtr proofTerm
          else let step = proofTerm!!proofTPtr
                   k = proofPtr+1
	       if deriveStep step && k < length proof then proofPtr := k
               case step of
		    ApplySubst -> applySubst
		    ApplySubstTo x t -> applySubstTo' x t
	            ApplyTransitivity -> applyTransitivity
		    BuildKripke m -> buildKripke m
	            CollapseStep -> collapseStep
		    ComposePointers -> composePointers
		    CopySubtrees -> copySubtrees
		    CreateIndHyp -> createIndHyp
		    CreateInvariant b -> createInvariant b
		    DecomposeAtom -> decomposeAtom
		    DeriveMode s r -> simplifying := s; refuting := r
		    		      simplTerm := simplTerm++[s]
				      refuteTerm := refuteTerm++[r]
		    EvaluateTrees -> evaluateTrees
		    ExpandTree b n -> expandTree' b n
		    FlattenImpl -> flattenImpl
		    Generalize cls -> generalize' cls
		    Induction True n -> applyInduction n
		    Induction _ n -> applyCoinduction n
		    Mark ps -> treeposs := ps; drawCurr
		    Match n -> matching := n; matchTerm := matchTerm++[n]
		    Minimize -> minimize
	            Narrow limit sub -> narrow' limit sub skip
		    NegateAxioms ps cps -> negateAxioms' ps cps
		    RandomLabels -> randomLabels
		    RandomTree -> randomTree
		    ReleaseNode -> releaseNode (0,0)
		    ReleaseSubtree -> releaseSubtree (0,0)
		    ReleaseTree -> releaseTree (0,0)
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
		                 -> simplify' depthfirst limit sub skip
		    ShiftPattern -> shiftPattern
		    ShiftQuants -> shiftQuants
		    ShiftSubs ps -> shiftSubs' ps
	            ShowEqsOrGraph b m -> showEqsOrGraph b m
		    ShowRelation m -> showRelation m
		    SplitTree -> splitTree
		    StretchConclusion -> stretch False
		    StretchPremise -> stretch True
		    SubsumeSubtrees -> subsumeSubtrees
		    Theorem b th -> applyTheorem b Nothing th
		    UnifySubtrees -> unifySubtrees
	       proofTPtr := proofTPtr+1
	       enterPT proofTPtr proofTerm

	checkInSolver = action checkingP := False
			       
	checkProof pterm file file' = action
	  if null trees then labBlue start
	  else case parse (list command) $ removeComment 0 pterm of
	       Just pt@(DeriveMode s r:Match m:_)
	         -> proofTerm := pt; proofTPtr := 2; enterPT 2 pt
		    simplifying := s; simplTerm := [s]; refuting := r
		    refuteTerm := [r]; matching := m; matchTerm := [m]
		    treeposs := [[]]
		    initialize $ showTree fast $ trees!!curr
		    quit.set [Text "stop check", redback, Command setDeriveMode]
		    labGreen $ proofLoaded file
		    if not checkingP then setInterpreter "tree"
		    runChecker
	       _ -> labRed $ noProofIn file'

	checkProofF inPainter = action 
	 str <- ent.getValue
	 case words str of 
	 [file,sp] -> pterm <- lookupLibs tk file; checking := True
	              checkingP := inPainter
	              speed := case parse pnat sp of Just k -> k*100; _ -> 100
	              checkProof pterm file file
	 [file] -> pterm <- lookupLibs tk file; checking := True
	           checkingP := inPainter; speed := 100
	  	   checkProof pterm file file
	 _ -> labMag "Enter a file name!"

	checkProofT inPainter = action 
	  pterm <- getTextHere; sp <- ent.getValue; checking := True
	  checkingP := inPainter
	  speed := case parse pnat sp of Just k -> k*100; _ -> 100
	  checkProof pterm "the text field" "The text field"

	clearTreeposs = setTreeposs $ Replace []
				       			 
 	clearText continue = action 
          lg <- tedit.lines
	  if lg < 2 then continue else tedit.deleteLine 1; clearText continue

	collapseStep = action
	  if null trees then labBlue start
	  else let t = trees!!curr
	           p = emptyOrLast treeposs
		   u = getSubterm1 t p
		   n = counter 'c'
		   (v,part') = collapseLoop True (u,part) n
		   setPr = setProof True False "COLLAPSING THE SUBTREE" [p]
	       setProofTerm CollapseStep
	       if u == v then setPr collapsed; clearTreeposs
		              counter := upd counter 'c' 0; part := (id,[])
	       else trees := updList trees curr $ replace1 t p v
	            setPr $ levelMsg n
	            drawCurr; counter := incr counter 'c'; part := part'

	composePointers = action
	  if null trees then labBlue start
	  else sig <- getSignature
	       let t = trees!!curr
		   ps = emptyOrAll treeposs
		   ts = map (composePtrs . getSubterm1 t) ps
	       trees := updList trees curr $ fold2 replace1 t ps ts
	       setProofTerm ComposePointers
	       setProof True False "COMBINING THE POINTERS OF THE TREES" ps 
	                pointersComposed
	       drawCurr

	compressAxioms b = action
	  sig <- getSignature
	  str <- ent.getValue
	  let x = if null trees || null treeposs then str
	          else label (trees!!curr) $ head treeposs
	      axs = noSimplsFor [x] axioms
	  if sig.isPred x || sig.isDefunct x || sig.isCopred x
             then if null axs then labRed $ noAxiomsFor [x]
   	          else let (th,k) = compressAll b sig (varCounter "z") axs
		       theorems := th:theorems
	               setZcounter k
	               enterFormulas [th]
	               labGreen $ newCls "theorems" "the text field"
	  else labMag "Enter a predicate, a defined function or a copredicate!"

	compressClauses = action
	  sig <- getSignature
	  str <- ent.getValue
	  let (exps,b) = numberedExps
	  case parse intRanges str of
	  Just (n:ks) | n < length exps
	    -> if b then let i = varCounter "z"
		             (th,k) = combineOne sig i ks (exps!!n) exps
			 theorems := th:theorems
			 setZcounter k
			 enterFormulas [th]
			 labGreen $ newCls "theorems" "the text field"
	            else labMag "Enter clauses into the text field!"
	  _ -> labMag $ enterNumber ++ " Enter argument positions!"

	copySubtrees = action
	  if null trees then labBlue start
	  else let ps = emptyOrAll treeposs
	           t = trees!!curr
	       if any null ps then labMag "Select proper subtrees!"
	       else trees := updList trees curr $ copy ps t
	            setProofTerm CopySubtrees
		    let b = all idempotent $ map (label t . init) ps
	            setProof b False "COPYING THE SUBTREES" ps 
	            		     "The selected tree have been copied."
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

	createClsMenu mode x = action
	  x.mButton [CLabel "from file", font12, greenback, 
		     Command $ getFileAnd act]
	  x.mButton [CLabel "from text field", font12, blueback, 
	  	     Command $ act ""]
 	  x.mButton [CLabel $ "from "++ other, font12, Command getFromOther]
	  done
	  where act = addClauses mode
	        getFromOther = action tree <- solve.getTree
	                              case tree of 
                                           Just t -> addTheorems t other done
	                                   _ -> labBlue $ startOther other

	createIndHyp = action
	  if null trees || not formula then labBlue startF
	  else if null treeposs then labMag "Select induction variables!"
	       else let t = trees!!curr
	                xs = map (label t) treeposs
	            sig <- getSignature
	            if all sig.isFovar xs && 
		       and (zipWith (isAllOrFree t) xs treeposs)
		       then let f x = V $ if x `elem` xs then '!':x else x
				desc = mkDescent (map f xs) $ map V xs
                                hyps = mkIndHyps t desc
                            trees := updList trees curr $ 
			                  mkAll (frees sig t `minus` xs) $ t>>>f
	                    indClauses := hyps; theorems := hyps++theorems
			    setProofTerm CreateIndHyp
		            setProof True False "SELECTING INDUCTION VARIABLES"
			             treeposs $ indHypsCreated xs
			    clearTreeposs; drawCurr
	 	       else labMag "Select induction variables!"

	createInvariant b = action
	  if null trees || not formula then labBlue startF
	  else sig <- getSignature
               let t = trees!!curr
	           (p,conj,i) = case treeposs of
                                [] -> ([],t,0)
				[q] | isFormula sig u -> (q,u,0) 
				    | notnull q -> ([],t,last q)		
				      where u = getSubterm t q	
			        [q,r] | notnull r -> (q,getSubterm t q,last r)
				_ -> ([],t,-1)	
	       if i > -1 && universal sig t p conj then
	          case preStretch True sig.isDefunct conj of
	          Just (f,varps)
		    -> case stretchPrem (varCounter "z") varps conj of
	  	       (F "===>" [F "=" [F _ xs,d],conc],m)
	                 -> let lg = length xs
			    if i < lg then 
                             case derivedFun sig f xs i lg axioms of
			     Just (loop,inits,ax)
                                           -- ax is f(xs)=loop(take i xs++inits) 
			       -> let n = m+length inits
				      (as,bs) = splitAt (lg-i) xs
				      cs = map newVar [m..n-1]
				      u = mkInvs b loop as bs cs inits d conc
			          trees := updList trees curr $ replace t p u
    	  		          setZcounter n
	  		          setProofTerm $ CreateInvariant b
	       		          setProof True False (creatingInvariant str ax) 
					   [p] $ invCreated b
	  		          clearTreeposs; drawCurr
			     _ -> labRed $ f ++ " is not a derived function."
                            else labRed $ wrongArity f lg
		       _ -> labRed concCallsPrem
		  _ -> notStretchable "The premise"
               else labRed $ noApp str
	  where str = if b then "HOARE INVARIANT CREATION"
	                   else "SUBGOAL INVARIANT CREATION"

	createSpecMenu add x = action
  	  mapM_ (createBut x act) specfiles1
	  x.mButton [CLabel $ if add then "from file (Return)" else "from file",
	             font12, greenback, Command $ getFileAnd act]
	  if add then x.mButton [CLabel "from text field", font12, blueback,
				 Command $ addSpecWithBase ""]
	              done
  	  y <- x.cascade [CLabel "more", font12, greenback]
  	  mapM_ (createBut y act) specfiles2
  	  z <- y.cascade [CLabel "more", font12, greenback]
  	  mapM_ (createBut z act) specfiles3
	  done
	  where act = if add then addSpecWithBase else loadText

	decomposeAtom = action
 	  if null trees || not formula then labBlue startF
	  else let t = trees!!curr
	           p = emptyOrLast treeposs
		   b = polarity True t p
		   F x [l,r] = getSubterm1 t p
		   finish u = action 
		    		  trees := updList trees curr $ replace1 t p u
		    		  setProofTerm DecomposeAtom
		    		  setProof True False "DECOMPOSING THE ATOM" [p]
				           atomDecomposed
			          clearTreeposs; drawCurr
	       sig <- getSignature
	       case x of "=" | b -> finish $ splitEq sig l r
	                 "=/=" | not b -> finish $ splitNeq sig l r 
		         _ -> labRed atomNotDecomposed
	
	delay n act = action tk.delay n $ const act; done

	draw ct = action
	  canv.clear
	  ctree := Just ct
	  let (_,_,maxx,maxy) = minmax $ foldT (bds sizeState) ct
	      size@(_,h) = (max 100 maxx,max 100 maxy)
	  canvSize := size
	  i <- canvSlider.getValue
	  if h > 100 then tedit.set [Height 0]
	  canv.set [ScrollRegion (0,0) size, Height $ min h 600]
	  canvSlider.setValue h
	  if null treeposs then drawTree ct ct black blue []
	  else drawTree2 ct ct black blue red darkGreen [] treeposs
	  if notnull treeDir then delay 100 saveGraphN'
          where bds (n,w) (a,(x,y)) pss = (x-x',y-y'):(x+x',y+y'):concat pss
                                where (x',y') = fromInt2 (halfWidth w a,n`div`2)

	drawArc (x,y) ct color = action
	  if isPos a then done
	  else let (above,below) = textheight font
	       canv.line [(x,y+below),(x',y'-above)] [Fill color]; done
	  where (a,(x',y')) = root ct
	  
	drawCurr = action drawThis (trees!!curr) [] ""

	drawNewCurr _ = action if notnull trees then drawCurr

	drawNode (a,p) c = action
	  if not $ isPos a then canv.text p [Text $ delQuotes a,NamedFont font,
	  				     Fill c',Justify CenterAlign]
			        done
	  where c' = case parse colPre a of Just (c,_) -> c; _ -> c

	drawPointer ct ac p (x,y) q = action
	  let (above,below) = textheight font
	      arc = [(x1,y1+below),(x,y-above)]
	      target z = (x',if z < y' then y'-above else y'+above)
	  if q `elem` allPoss ct then
             if q << p || y > y'+30		             -- up pointer
	        then let z = (y-y')`div`3
		         z' = (y+y')`div`2
			 (mid1,mid2) = if x < x1 then ((x-10,y+10),(x-z,z'))
				                 else ((x+10,y+10),(x+z,z'))
			 path = arc++[mid1,mid2,target y]
	  	     draw path $ if q << p then f orange else f magenta; done
	        else let z = abs $ x-x'		             -- down pointer
	                 z' = y+z`div`2
		         mid = if z < 30 then (x,z') else ((x+x')`div`2,z')
	  	     draw (arc++[mid,target z']) $ f magenta; done
	  else draw (arc++[(x-10,y+10)]) $ f red; done	     -- dangling pointer
 	  where (_,(x1,y1)) = label ct $ init p 	     -- pred of source
	        (_,(x',y')) = label ct q        	     -- target
		f color = if ac == white then white else color
		draw path color = do canv.line path [Fill color,
						     Arrow Last,Smooth True]
	
	drawShrinked _ = action 
	  if notnull trees 
	     then draw $ shrinkTree (snd corner) (snd spread) $ get ctree

	drawSubtrees = action
	  let Just ct = ctree
          drawTree3 ct ct black blue red darkGreen [] treeposs $
		    minis (<<=) $ treeposs `join` oldTreeposs

        drawThis t ps col = action 
	  let qs = if showState then []
	           else case hideVals of 0 -> treeposs
		   			 1 -> treeposs++valPositions t 
					 _ -> treeposs++widgPositions t 
	      u = cutTree maxHeap (colHidden t) ps col qs
	  sizes@(_,w) <- mkSizes font $ nodeLabels u
	  sizeState := sizes; draw $ coordTree w spread corner u

-- drawTree ct ct nc ac [] draws the nodes of ct in color nc and the arcs of ct
-- in color ac.

 	drawTree (F cx@(_,q) cts) ct nc ac p = action
			               drawNode cx nc
				       drawTrees cts $ succsInd p cts
                                       where drawTrees (ct':cts) (p:ps) = action
			                                 drawArc q ct' ac
						         drawTree ct' ct nc ac p
							 drawTrees cts ps
				             drawTrees _ _ = done

	drawTree (V cx@(a,q)) ct nc ac p 
          | isPos a = drawPointer ct ac p q $ getPos a
          | True    = drawNode cx nc

-- drawTree2 ct ct nc ac nc' ac' [] qs draws the nested ones among the subtrees
-- at positions qs alternately in (text,line)-colors (nc,ac) and (nc',ac').

  	drawTree2 ct@(V _) ct0 nc ac nc' ac' p qs
	  | any (== p) qs = drawTree ct ct0 nc' ac' p
	  | True          = drawTree ct ct0 nc ac p
	drawTree2 (F cx@(_,q) cts) ct nc ac nc' ac' p qs
          | any (== p) qs = action drawNode cx nc'
	  			   drawTrees2 q cts nc' ac' nc ac ps
	  | True          = action drawNode cx nc
	  		           drawTrees2 q cts nc ac nc' ac' ps
	                    where ps = succsInd p cts
                                  drawTrees2 q (ct':cts) nc ac nc' ac' (p:ps) = 
			    	      action drawArc q ct' ac
				    	     drawTree2 ct' ct nc ac nc' ac' p qs
					     drawTrees2 q cts nc ac nc' ac' ps
	                          drawTrees2 _ _ _ _ _ _ _ = done

-- drawTree3 ct .. rs applies drawTree2 ct .. to the subtrees of ct at positions
-- rs.

  	drawTree3 ct' ct nc ac nc' ac' p qs rs
	  | any (<<= p) rs 		= drawTree2 ct' ct nc ac nc' ac' p qs
  	drawTree3 (V _) _ _ _ _ _ _ _ _ = done
	drawTree3 (F (_,q) cts) ct nc ac nc' ac' p qs rs = 
	  		   action drawTrees3 q cts nc ac nc' ac' ps
	                   where ps = succsInd p cts
                                 drawTrees3 q (ct':cts) nc ac nc' ac' (p:ps) = 
				   action drawTree3 ct' ct nc ac nc' ac' p qs rs
	            			  drawTrees3 q cts nc ac nc' ac' ps
			         drawTrees3 _ _ _ _ _ _ _ = done
	
	enterFormulas fs = action 
	  if not checking then clearText $ addText $ lines $ showFactors fs
	                       numberedExps := (fs,True)
	
	enterTerms ts = action 
	  if not checking then clearText $ addText $ lines $ showSum ts
	         	       numberedExps := (ts,False)

	enterText str = action 
	  if not checking then clearText $ addText $ lines str
	  		       numberedExps := ([],True)

	enterPT n pt = action clearText $ addText $ lines $ show $ addPtr n pt
                              where addPtr 0 (step:pt) = POINTER step:pt
 				    addPtr n (step:pt) = step:addPtr (n-1) pt
 				    addPtr _ pt        = pt

	enterTree b t = action
	  setTime
	  formula := b; treeMode := "tree"; trees := [t]
	  counter := upd counter 't' 1
  	  proofTerm := [DeriveMode simplifying refuting, Match matching]
	  proofTPtr := 2
	  clearTreeposs
	  picNo := 0
	  sig <- getSignature
	  makeTrees sig $ action initialize $ showTree fast t
				 setTreesFrame [] $ labGreen $ objects++str
	  where objects = if b then "Formulas" else "Terms"
                str = " in the text field are displayed on the canvas."

	evaluateTrees = action
	  if null trees then labBlue start
	  else sig <- getSignature
	       let t = trees!!curr
		   ps = emptyOrAll treeposs
		   ts = map (evaluate sig . getSubterm1 t) ps
	       trees := updList trees curr $ fold2 replace1 t ps ts
	       setProofTerm EvaluateTrees
	       setProof True False "EVALUATING THE TREES" ps evaluated
	       drawCurr

	expandTree b = action
	  if null trees then labBlue start
	  else limit <- ent.getValue
	       expandTree' b $ case parse pnat limit of Just n -> n; _ -> 0

	expandTree' b limit = action
	  let t = trees!!curr
	      ps = emptyOrAll treeposs
	      f u p = replace0 u p $ (if b then expandOne else expand) limit t p 
	  trees := updList trees curr $ moreTree $ foldl f t ps
	  setProofTerm $ ExpandTree b limit
	  setProof True False "EXPANDING THE SUBTREES" ps $
	           expanded ++ circlesUnfolded limit
	  clearTreeposs; drawCurr

        finishDisCon k b c ts reduct redices t ps pred qs sig msg = action
	  case applyMany b c ts reduct redices t ps pred qs sig varCounter of
               Just (t,vc) -> maybeSimplify sig t $ action varCounter := vc
			      setProofTerm proofStep
			      setProof True True msg ps $ thApplied k
			      clearTreeposs; drawCurr
	       _ -> labRed $ notUnifiable k

	finishRelease t p step = action
	  trees := updList trees curr t
	  setProofTerm step
	  clearTreeposs; drawCurr
	  setProof False False "REPLACING THE SUBTREE" [p] 
	  		       "The selected tree has been replaced."

	flattenImpl = action
	  if null trees || not formula
	     then labMag "Load and parse a Horn or co-Horn clause!"
	     else sig <- getSignature
                  let t = trees!!curr
	              xs = if null treeposs then defuncts sig t
		           else filter sig.isDefunct $ map (label t) treeposs
		      (u,n) = flatten (varCounter "z") xs t
	          trees := updList trees curr u
	          setZcounter n
	          setProofTerm FlattenImpl
	          setProof True False "FLATTENING" [[]] flattened
	          clearTreeposs; drawCurr

        foldrM act continue (x:s) = action act (foldrM act continue s) x
        foldrM _ continue _       = continue

	forwProof = action
          if checking then checkForward
	  else let k = proofPtr+1
		   lg = length proofTerm
	       if k >= length proof then labMag endOfProof 
			            else proofPtr := k; changeState k []
	       if proofTPtr < lg
                  then let n = search deriveStep $ drop proofTPtr proofTerm
	               proofTPtr := if just n then proofTPtr+get n+1 else lg

	generalize = action
	  if null trees || not formula then labBlue startF
	  else let t = trees!!curr
	           p = emptyOrLast treeposs
	           cl = getSubterm t p
               sig <- getSignature
               if isTerm sig cl then labRed "Select a formula!"
	       else str <- ent.getValue
	            let (exps,b) = numberedExps
	            case parse intRanges str of
	            Just ns | all (< (length exps)) ns
	              -> if b then generalizeEnd t p cl $ map (exps!!) ns
		         else labMag "Enter formulas into the text field!"
                    _ -> str <- getTextHere
 	                 case parseE (implication sig) str of
	                      Correct cl' -> generalizeEnd t p cl [cl']
	                      p -> incorrect p str illformedF

	generalize' cls = action
          let t = trees!!curr
	      p = emptyOrLast treeposs
	  generalizeEnd t p (getSubterm t p) cls

	generalizeEnd t p cl cls = action 
	  trees := updList trees curr $ replace t p $ f $ cl:cls
	  enterFormulas cls
	  setProofTerm $ Generalize cls
	  setProof True False "GENERALIZING" [p] generalized
	  clearTreeposs; drawCurr
	  where f = if polarity True t p then mkConjunct else mkDisjunct

	getEntry = request ent.getValue

	getFileAnd act = action
	  file <- ent.getValue
	  if null file then labMag "Enter a file name!" else act file

        getFont = request return font

	getInterpreter = do
	  sig <- getSignature
	  return $ case picEval of "alignment"          -> alignment
			           "dissection"         -> dissection
				   "tree"               -> widgetTree
			           "linear equations"   -> linearEqs
				   "level partition"    -> partition 0
				   "preorder partition" -> partition 1
				   "heap partition"     -> partition 2
				   "hill partition"     -> partition 3
				   "matrix solution"    -> solPic sig matrix
				   "tree solution"      -> solPic sig widgetTree
				   "widget solution"    -> solPic sig widgets
				   "matrices"           -> searchPic matrix
				   _          	        -> searchPic widgets
				   
	getSignatureR = request getSignature

	getSignature = do
	  let (ps,cps,cs,ds,fs,hs) = symbols
	      (sts,ats,labs,tr,trL,va,vaL) = kripke
	      isPred       = (`elem` ps)  ||| isGet ||| isNBeq
	      isCopred     = (`elem` cps) ||| isGet ||| isBeq
	      isConstruct  = (`elem` cs)  ||| just . parse int ||| 
	                     just . parse real ||| just . parse quoted ||| 
			     just . parse (strNat "inj")
	      isDefunct    = (`elem` ds) ||| isGet
	      isFovar      = (`elem2` fs)
	      isHovar      = (`elem2` (map fst hs))
	      hovarRel x y = isHovar x &&
	      		     case lookup (base x) hs of
			          Just es@(_:_) -> isHovar y || y `elem` es
				  _ -> not $ isFovar y
	      (block,xs) = constraints
	      blocked x = if block then z `elem` xs else z `notElem` xs
	                  where z = head $ words x
	      safeEqs = safe; simpls = simplRules; transitions = transRules
	      states = sts; atoms = ats; labels = labs; trans = tr
	      transL = trL; value = va; valueL = vaL
	  return $ struct ..Sig
	  where elem2 x = shares [x,base x]
	        isGet = just . parse (strNat "get")

	getSolver = request return this

	getText = request getTextHere

	getTextHere = do lg <- tedit.lines
	                 strs <- mapM tedit.getLine [1..lg]
	                 return $ removeDot $ unlines $ map f strs
		      where f = removeCommentL . drop3

	getTree = request if null trees then labBlue start
				             return Nothing
			                else return $ Just $ trees!!curr
				
	hideOrShow = action
	  if null trees then labBlue start 
	  else drawCurr; showState := not showState
	       hideBut.set [Text $ if showState then "hide" else "show"]
	  
	incorrect p str error = action
	  case p of Partial t rest -> enterText $ showTree False t ++ check rest
	            _ -> enterText str
	  labRed error

	incrCurr b = action let next = if b then curr+1 else curr-1
	                    setCurr newCurr $ next `mod` length trees

	incrEntry b = action 
	  str <- ent.getValue
	  let k = parse nat str; f = ent.setValue . show
	  if b then case k of Just n -> f $ n+1
	  		      _ -> ent.setValue "0"
	       else case k of Just n | n > 0 -> f $ n-1
	                      _ -> ent.setValue ""
	       
	initCanvas continue = action 
	  if null trees then enterTree False $ F "see painter" []
	  		     delay 100 continue
			else continue

	initialize str = action
	  let (ps,cps,cs,ds,fs,hs) = symbols
	      (ps',cps') = newPreds
	      (block,xs) = constraints
          symbols := (minus ps ps',minus cps cps',cs,ds,fs,hs)
	  axioms := removeTerms axioms indClauses
	  theorems := removeTerms theorems indClauses
	  indClauses := []; newPreds := nil2; solPositions := []
	  varCounter := iniVarCounter symbols -- perms := \n -> [0..n-1]
	  setSubst (V,[]); part := (id,[])
	  proof := [struct msg = "Derivation of\n\n"++str++
	                         '\n':'\n':admitted block xs++
	  			 '\n':equationRemoval safe
		           msgL = ""
			   treeMode = treeMode; trees = trees; treePoss = []
			   curr = 0; varCounter = varCounter -- perms = perms
			   newPreds = nil2; solPositions = []
			   substitution = (V,[]); constraints = constraints
			   joined = joined; safe = safe]
	  (proofPtr,counter,curr) := (0,const 0,0)	
	       
	instantiate = action
	  if null trees || not formula then labBlue startF
          else sig <- getSignature
               str <- ent.getValue
	       let str' = removeComment 0 str
	       case parseE (term sig) str' of
	            Correct t -> replaceQuant t (emptyOrLast treeposs) $
	       				        labRed notInstantiable
	            p -> incorrect p str' illformedT

	isSolPos n = request return $ n `elem` solPositions
			 
	kleeneAxioms = action
	  sig <- getSignature
	  str <- ent.getValue
	  let x = if null trees || null treeposs then str
	          else label (trees!!curr) $ head treeposs
	      copred = sig.isCopred x
	      f = if copred then mkHornLoop else mkCoHornLoop
	  if copred || sig.isPred x  then
	     let axs = noSimplsFor [x] axioms
	     if null axs then labRed $ noAxiomsFor [x]
   	     else let i = V $ 'i':show (varCounter "i")
		      (axs',k) = f sig x axs i $ varCounter "z"
                      (ps,cps,cs,ds,fs,hs) = symbols
		      ps' = x:(x++"Loop"):ps
                  symbols := (ps',cps`minus1`x,cs,ds,fs,hs)
		  axioms := joinTerms axs' $ removeTerms axioms axs
                  varCounter := upd (incr varCounter "i") "z" k
	          enterFormulas axs'
	          labGreen $ if copred then newPredicate str1 str2 x
				       else newPredicate str2 str1 x
	  else labMag "Enter either a predicate or a copredicate!"
	  where (str1,str2) = ("copredicate","predicate")

	labBlue str = labColor str $ light blue

	labColor str col = action if just osci then (get osci).stopOsci
			          lab.set [Text str, Background col]

	labColorToPaint col str = action labColor str $ light col
					 paint.labSolver str

	labColorToPaintT col str = action 
	  let (time0,timeout) = times
	  if time0 == 0 then labColor str $ light col
	  else time <- tk.timeOfDay; times := (0,300)
	       labColor (str++'\n':show (mkSecs time0 time)++" sec") $ light col
	  paint.labSolver str

	labGreen str = labColor str $ light green

	labMag str = labColor str $ light magenta

	labRed str = action 
	  if just osci then (get osci).stopOsci
	  let act n = lab.set [Text str, Background $ RGB 255 n 0]
	  osci0 <- oscillator tk act act 1 10 249; osci0.startOsci
	  osci := Just osci0

   	loadText file = action 
          str <- lookupLibs tk file
	  enterText str
	  if null str then labRed $ file ++ " is not a file name." 
	  	      else labGreen $ loaded file

	makeTrees sig continue = action
	  case treeMode of
	  "tree" | joined -> continue 
		 | True   
            -> case trees of [t@(F "|" _)] -> solPositions := []
		                 	      split (mkSummands t) "summand"
			     [t@(F "&" _)] -> solPositions := []
					      split (mkFactors t) "factor"
			     [t@(F "<+>" _)] -> split (mkTerms t) "term"
			     _ -> continue
	  "summand" 
	    -> if null ts then actMore [mkFalse] "tree" else actMore ts treeMode
	       where ts = mkSummands $ F "|" trees
	  "factor" 
	    -> if null ts then actMore [mkTrue] "tree" else actMore ts treeMode
	       where ts = mkFactors $ F "&" trees
	  _ -> if null ts then actMore [mkUndef] "tree" else actMore ts treeMode 
	       where ts = mkTerms $ F "<+>" trees
	  where split = actMore . map dropHeadFromPoss
	        actMore ts mode = action 
		          newTrees := newTrees || lg /= length trees
		          curr := curr `mod` lg
			  trees := ts; counter := upd counter 't' lg
			  treeMode := if lg == 1 then "tree" else mode
			  solPositions := if formula then solPoss sig ts else []
			  continue
			  where lg = length ts
			  
	maybeSimplify sig t continue = 
	  do trees := updList trees curr $ if simplifying 
	  				   then simplifyIter sig t else t
	     continue

	minimize = action
	  sig <- getSignature
	  let is = indices_ sig.states; ks = indices_ sig.labels
	      pairs = if deterministic sig is ks then nerode sig is ks 
	      					 else bisim sig is ks
	      (states,tr,trL,va,vaL) = mkQuotient sig pairs
	      rules = case search ((== "states") . root . pr1) simplRules of 
	                   Just i -> updList simplRules i 
		                             (F "states" [],[],mkList states)
		           _ -> simplRules
	  kripke := (states,sig.atoms,sig.labels,tr,trL,va,vaL)
	  simplRules := rules
	  setProofTerm Minimize
	  labGreen $ "The Kripke model has been minimized. It has " ++ 
	  	     show (length states) ++ " states."
 
	moveNode pt = action
	  if null treeposs then labMag "Select a target node!"
	  else let f p a col1 col2 = drawNode a $ if last treeposs <<= p
	                                          then col1 else col2
	       case node of Just (z,p) -> f p z red black; done
	                    _ -> done
	       (x,y) <- adaptPos pt
               case getSubtree (get ctree) x y of 
	            Just (p,cu) -> let a = root cu
			           f p a cyan magenta
			           node := Just (a,p)
	            _ -> node := Nothing

       	moveSubtree pt@(x1,y1) = action
	  if just isSubtree && just penpos 
	     then let Just ct = ctree
		      Just cu = subtree
		      (x0,y0) = get penpos
                      cu' = transTree2 (x1-x0,y1-y0) cu
	              p = last treeposs
                  if firstMove && not (get isSubtree)
                     then drawTree cu ct black blue p
		     else drawTree cu ct white white p
		  firstMove := False
		  penpos := Just pt
		  subtree := Just cu'
		  if just node then drawNode (fst $ get node) black
   		  drawTree cu' ct red darkGreen p
	       	  (x,y) <- adaptPos pt
	   	  case getSubtree (get suptree) x y of
		       Just (p,cu) -> let a = root cu
			              drawNode a magenta
			              node := Just (a,p)
	               _ -> node := Nothing

        moveTree p@(x,y) = action
	  case isSubtree of
	  Just True -> moveSubtree p
	  Just _ -> if just penpos then let (x0,y0) = get penpos
	                                    q@(i,j) = (x-x0,y-y0)
			                draw $ transTree2 q $ get ctree
			                corner := (fst corner+i,snd corner+j)
			                penpos := Just p
	  _ -> done

	narrow continue = action 
	  if null trees then labBlue start
	  else str <- ent.getValue 
	       case parse pnat str of
	            Just limit -> narrow' limit True continue
		    _ -> case parse pnatSecs str of
		              Just n -> times := (fst times,n)
			      		narrow' (-1) True continue
		              _ -> narrow' 1 False continue

	narrow' limit sub continue = action
	  sig <- getSignature
	  ruleString := if formula then "NARROWING" else "REWRITING"
	  counter := upd counter 'd' 0
	  let t = trees!!curr
	      (block,xs) = constraints
	      axs = noSimplsFor xs axioms
	      cls = if block
	            then filter (not . isGuarded isEquiv) axioms `minus` axs 
		    else axs
	  if null treeposs then proofStep := Narrow limit True; setTime
		                narrowLoop sig cls 0 limit continue
	  else if sub then setTime; narrowSubtree t sig cls limit continue
	       else proofStep := Narrow 0 False
		    narrowOrRewritePar t sig (Just $ -1) cls False treeposs 
		    		       continue

	narrowLoop sig cls k limit continue | limit == 0 = finish k
					    | True       = action
	  let t = trees!!curr
	  case treeMode of
	  "tree" | formula ->
	                if isSol sig t then solPositions := [0]; finishNar k
	                else solPositions := []
		             if joined then mkStep t $ finish k
		             else case trees of [F "|" ts] -> split ts "summand"
			                        [F "&" ts] -> split ts "factor"
			                        _ -> mkStep t $ finish k
	         | True -> if joined then mkStep t $ finish k
		           else case trees of [F "<+>" ts] -> split ts "term"
			                      _ -> mkStep t $ finish k
	  "summand" | simplifying -> case t of F "|" ts -> actMore ts treeMode
		                    	       F "&" ts -> actMore ts "factor"
					       _ -> actMore [t] "tree"
	            | null ts -> actMore [mkFalse] "tree" 
		    | True    -> actMore ts treeMode
		                 where t = simplifyIter sig $ mkDisjunct trees
		                       ts = mkSummands $ F "|" trees
	  "factor"  | simplifying -> case t of F "|" ts -> actMore ts "summand"
		                     	       F "&" ts -> actMore ts treeMode
					       _ -> actMore [t] "tree"
	            | null ts -> actMore [mkTrue] "tree" 
		    | True    -> actMore ts treeMode
	                         where t = simplifyIter sig $ mkConjunct trees
				       ts = mkFactors $ F "&" trees
	  _ | simplifying -> case t of F "<+>" ts -> actMore ts "term"
		                       _ -> actMore [t] "tree"
	    | null ts -> actMore [mkUndef] "tree" 
	    | True    -> actMore ts treeMode
	                 where t = simplifyIter sig $ mkSum trees
			       ts = mkTerms $ F "<+>" trees
	  where finish = makeTrees sig . finishNar
                finishNar k = action 
			        setProofTerm proofStep
	          	        setProof True True ruleString [] $
			    	    finishedNar formula k ++ solved solPositions
                                setTreesFrame [] continue
	        mkStep t stop = action narrowStep sig cls limit t proceed stop 
						  formula
	        proceed t n vc = action varCounter := vc				 
		      			counter := upd counter 'd' k'
                      			trees := updList trees curr t
					narrowLoop sig cls k' (limit-n) continue
	              			where k' = k+n
	        split = actMore . map dropHeadFromPoss
		actMore ts mode = action 
		  let b n = newTrees || lg /= length trees || curr /= n
		      searchRedex (n:ns) = do newTrees := b n; curr := n
		                              mkStep (trees!!n) $ searchRedex ns
		      searchRedex _ = do newTrees := b 0; curr := 0; finish k
		      ks = drop curr is++take curr is
		  trees := ts; counter := upd counter 't' lg
	          treeMode := if lg == 1 then "tree" else mode
		  solPositions := if formula then solPoss sig ts else []
		  searchRedex $ ks `minus` solPositions
		  where lg = length ts; is = indices_ ts

	narrowOrRewritePar t sig k cls saveRedex ps continue = action
	  -- used by applyTheorem and narrow' (see above)
	  let f g = g t sig k cls saveRedex [] ps [] varCounter continue
	  if formula || ps `subset` boolPositions sig t then f narrowPar 
	  						else f rewritePar

	narrowPar t sig k cls saveRedex used (p:ps) qs vc continue = action
	  if p `notElem` positions t -- || isVarRoot sig redex
	     then narrowPar t sig k cls saveRedex used ps qs vc continue
	  else let b = matching > 1
	           apply at r = applyAxs cls1 cls3 axioms redex at r sig vc' b
	           applyR at r = applyAxsR cls1 cls3 axioms rand redex at r sig
		   			   vc' b
	       if sig.isDefunct sym then
		  case atomPosition sig t p of
		  Just (q,at,r) 
		    -> if even matching then 
                          case apply at r of
                               (Backward reds vc,used')
	                         -> proceed q mkDisjunct reds used' vc
			       (MatchFailure str,_) -> labMsg str
			       _ -> next
		       else case applyR at r of 
		       	         (Backward reds vc,used',rand')
	                           -> rand := rand'
				      proceed q mkDisjunct reds used' vc 
			         (MatchFailure str,_,_) -> labMsg str
  	                         _ -> next
  	          _ -> next
	       else if notnull p && isTerm sig redex then
	               let q = init p
	               case (getSubterm t q,last p) of
	               (at@(F "->" [_,_]),0)
	                 -> if even matching then 
                               case apply at [0] of
                                    (Backward reds vc,used')
	                              -> proceed q mkDisjunct reds used' vc
 			            (MatchFailure str,_) -> labMsg str
 	                            _ -> next
			    else case applyR at [0] of 
                                      (Backward reds vc,used',rand')
	                                -> rand := rand'
				           proceed q mkDisjunct reds used' vc
 			              (MatchFailure str,_,_) -> labMsg str
 	                              _ -> next
 	               _ -> next
	            else if sig.isPred sym then
		            if even matching then
                               case apply redex [] of
                                    (Backward reds vc,used') 
		                      -> proceed p mkDisjunct reds used' vc
			            (Forward reds vc,used') 
			              -> proceed p mkConjunct reds used' vc
			            (MatchFailure str,_) -> labMsg str
   	                            _ -> next
		            else case applyR redex [] of
                                      (Backward reds vc,used',rand') 
		                        -> rand := rand'
				           proceed p mkDisjunct reds used' vc
	                              (Forward reds vc,used',rand') 
			                -> rand := rand'
				           proceed p mkConjunct reds used' vc
			              (MatchFailure str,_,_) -> labMsg str
				      _ -> next
	                 else if sig.isCopred sym then
		                 if even matching then
                                    case apply redex [] of
                                         (Backward reds vc,used') 
		                           -> proceed p mkDisjunct reds used' vc
                                         (Forward reds vc,used') 
					   -> proceed p mkConjunct reds used' vc
			                 (MatchFailure str,_) -> labMsg str
   	                                 _ -> next
		                 else case applyR redex [] of
                                      (Backward reds vc,used',rand') 
		                        -> rand := rand'
				           proceed p mkDisjunct reds used' vc
	                              (Forward reds vc,used',rand') 
			                -> rand := rand'
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
			            (joinTerms used' used) ps (p:qs) vc continue
	        next = narrowPar t sig k cls saveRedex used ps qs vc continue
		labMsg = labColorToPaint magenta
	narrowPar _ _ k _ _ [] _ _ _ _ = 
	  labColorToPaint magenta $ subtreesNarrowed k
	narrowPar t sig k _ _ used _ qs vc continue = action
	  varCounter := vc
	  maybeSimplify sig t $ makeTrees sig $ finish $ thApplied k
	  where finish msg = action setProofTerm proofStep
			            counter := upd counter 'd' 1
				    setProof True True (applied b str) qs msg
				    setTreesFrame [] continue
	        b = length used == 1
		str = showFactors used
	 
	narrowStep sig cls limit t proceed stop nar = action
	  time <- tk.timeOfDay
	  let (time0,timeout) = times
	      m = if limit < 0 then 1 else limit
	  if mkSecs time0 time > timeout then stop
	  else if even matching then
	          let (u,n,vc) = applyLoop t m varCounter cls axioms sig nar 
		    		           matching simplifying refuting
                  if n == 0 then stop else proceed u n vc
               else let (u,n,vc,rand') = applyLoopRandom rand t m varCounter cls 
	       				     axioms sig nar matching simplifying
	            rand := rand'
                    if n == 0 then stop else proceed u n vc
 	
	narrowSubtree t sig cls limit continue = action
	  let p = emptyOrLast treeposs
	      u = getSubterm t p
	      nar = isFormula sig u
	      sn = subtreesNarrowed (Nothing :: Maybe Int)
	      (str,str') = if nar then ("NARROWING",sn)
	                          else ("REWRITING",sn++onlyRew)
	      proceed u n vc = action
	           let v = if simplifying then simplifyIter sig u else u
		   trees := updList trees curr $ replace t p v
	           varCounter := vc
	           setProofTerm $ Narrow limit True
	           counter := upd counter 'd' n
	           setProof True True str [p] $ appliedToSub (map toLower str) n
	           setTreesFrame [] continue
	      stop = action labColorToPaint magenta str'; continue
	  narrowStep sig cls limit u proceed stop nar
	
	negateAxioms = action
	  str <- ent.getValue
	  sig <- getSignature
	  let xs = if null trees || null treeposs then words str
	           else map (label $ trees!!curr) treeposs 
	      (ps,cps,cs,ds,fs,hs) = symbols
	      ps1 = filter sig.isPred $ meet xs ps
	      cps1 = filter sig.isCopred $ meet xs cps
	  negateAxioms' ps1 cps1
	
        negateAxioms' ps1 cps1 = action
	  let (ps,cps,cs,ds,fs,hs) = symbols
	      xs = ps1++cps1
	      axs1 = noSimplsFor xs axioms
	      ps2 = map mkComplSymbol cps1
	      cps2 = map mkComplSymbol ps1
	      str = complsAdded xs
	      msg = init str ++ " (see the text field)."
	  if null axs1 then labRed $ "There are no axioms for "++ showStrList xs
	     else symbols := (ps `join` ps2,cps `join` cps2,cs,ds,fs,hs)
	          sig <- getSignature
	          let axs2 = map (mkComplAxiom sig) axs1
	          axioms := axioms `join` axs2
	          enterFormulas axs2
	          if null trees then labGreen msg
		                else setProofTerm $ NegateAxioms ps1 cps1
		                     setProof True False str [] msg
	
        notStretchable str = labRed $ str ++ " cannot be stretched."
	
	parseConjects sig file conjs continue = action 
	  case parseE (implication sig) conjs of
	       Correct t -> let ts = if isConjunct t then subterms t else [t]
		            conjects := joinTerms ts conjects
                            labGreen $ newCls "conjectures" file; continue
	       p -> incorrect p conjs illformed

        parseSig file str continue = action
	  let (ps,cps,cs,ds,fs,hs) = symbols
	  case parseE (signature ([],ps,cps,cs,ds,fs,hs)) str of
	       Correct (specs,ps,cps,cs,ds,fs,hs)
	         -> symbols := (ps,cps,cs,ds,fs,hs)
	            foldrM (addSpec False) (delay 100 $ finish symbols) $
		    	                   specs `minus` specfiles
	       Partial (_,ps,cps,cs,ds,fs,hs) rest
	         -> enterText $ showSignature (ps,cps,cs,ds,fs,hs) $ check rest
	            labRed illformedSig
	       _ -> enterText str
	            labRed illformedSig
	  where finish syms = action varCounter := iniVarCounter syms
			             labGreen $ newSig file
		    		     delay 100 continue

	parseSigMap file str = action
          sig <- getSignature
          sig' <- solve.getSignatureR
	  case parseE (sigMap signatureMap sig sig') str of
	       Correct f -> signatureMap := f
	                    labGreen $ newSigMap file
	       Partial f rest -> enterText $ showSignatureMap f $ check rest
	                         labRed illformedSM
	       _ -> enterText str
	            labRed illformedSM

	parseText = action
	  str <- ent.getValue
	  let (exps,b) = numberedExps
	  case parse intRanges str of
	       Just ns | all (< (length exps)) ns
	         -> ent.setValue ""
		    let exps' = map (exps!!) ns
		    if b then enterTree True $ mkConjunct exps'
		         else enterTree False $ mkSum exps'
	       _ -> sig <- getSignature
	  	    str <- getTextHere
	            case parseE (term sig) str of
	                 Correct t -> enterTree False t
	                 _ -> case parseE (implication sig) str of
	                           Correct cl -> enterTree True cl
	                           p -> incorrect p str illformed
	
	parseTerms sig file ts continue = action 
	  case parseE (term sig) ts of
	       Correct t -> let ts = if isSum t then subterms t else [t]
	                    terms := joinTerms ts terms
	                    labGreen $ newCls "terms" file; continue
	       p -> incorrect p ts illformed
	
	parseTree = action
	  if null trees then labBlue start
	  else let t = trees!!curr
                   enter _ _ [t] = enterText $ showTree fast t
	           enter b "" ts = if b then enter True "&" ts
	                                else enter False "<+>" ts
		   enter _ x ts  = enterText $ showTree fast $ F x ts
	       if null treeposs 
                  then enter formula "" [t]; labGreen treeParsed
	          else sig <- getSignature
		       let ts@(u:us) = map (getSubterm1 t) treeposs
			   b = isFormula sig u
	               if null $ tail treeposs
			  then enter b "" [u]; labGreen treeParsed
	                  else if all (== b) $ map (isFormula sig) us
	                          then x <- ent.getValue
			               enter b x $ addNatsToPoss ts
	                               labGreen $ init treeParsed ++ "s."
			          else labMag "Select either formulas or terms!"
	  
	randomLabels = action
	  if null trees then labBlue start
	  else str <- ent.getValue
	       if null str then labRed "Enter labels!"
	       else let (t,rand') = labelRandomly rand str $ trees!!curr
	            trees := updList trees curr t
	            rand := rand'
	            setProofTerm RandomLabels
	            setProof False False "LABELING NODES" [] 
	       			         "The nodes have been labeled randomly."
	            drawCurr
		
	randomTree = action
	  str <- ent.getValue
	  if null str then labRed "Enter labels!"
	  else let (t,rand') = buildTreeRandomly rand str
	       enterTree False t
	       rand := rand'
	       setProofTerm RandomTree
	       delay 100 $ setProof False False "GENERATING A TREE" [] 
	       			    "A tree has been generated randomly."
		
	reAddSpec = action if null specfiles then labRed iniSpec
	                   else removeSpec $ addSpecWithBase $ head specfiles

	redrawTree = action if notnull treeposs then restore := True
	                               		     clearTreeposs
			    drawCurr
	
	releaseNode _ = action
	  if null treeposs then labMag "Select a target node!"
	  else let p = last treeposs
	       case node of Just (z,q) | notnull q && p /= q
	                      -> let t = replace (trees!!curr) q $ mkPos p
		                 if p `elem` allPoss t
	                            then trees := updList trees curr t
		                         let r = init q
			                 setProofTerm ReleaseNode
			                 setProof False False "INSERTING AN ARC"
                                                  [r,p] $ arcInserted r p
	                            else labRed dangling
		                 drawCurr
	  	                 node := Nothing
	                         canv.set [Cursor "left_ptr"]
	                    _ -> labMag "Select a non-root position!"

       	releaseSubtree _ = action
	  if just isSubtree then
	     let source = last treeposs
		 finish = action drawTree (get subtree) (get ctree) white white 
		 		          source; drawSubtrees
	     case node of
	          Just (_,target)
		    -> let t = trees!!curr
			   u = getSubterm1 t source
		       if source == target then finish
	                  else tk.bell; if null target then changeMode u
			       replaceQuant u target
                              	   $ finishRelease (replace2 t source t target)
			       	                   source ReleaseSubtree
                  _ -> setTreeposs $ Remove source; finish
	     resetCatch

        releaseTree _ = action
	  case isSubtree of 
          Just True -> let t = trees!!curr
	  	           p = last treeposs
			   u = getSubterm1 t p
			   z = 'z':show (varCounter "z")
			   (g,dom) = substitution
			   f t = finishRelease t p ReleaseTree
		       case node of Just (_,q) -> if p /= q then 
		       				     tk.bell; f $ replace1 t q u
				    _ -> f $ replace t p $ V z
	               setSubst (g `andThen` for u z, dom `join1` z)
		       varCounter := incr varCounter "z"
		       resetCatch
 	  Just False -> penpos := Nothing
	                canv.set [Cursor "left_ptr"]
			resetCatch
          _ -> done

	removeAxiomsFor = action 
	  str <- ent.getValue
	  let xs = if null trees || null treeposs then words str
	           else mkSet $ map (label $ trees!!curr) treeposs
	      axs = clausesFor xs axioms
	  if null axs then labRed $ noAxiomsFor xs
	              else axioms := removeTerms axioms axs
	                   labGreen $ axsRemovedFor xs

	removeClauses n = action
	  str <- ent.getValue
	  let (exps,_) = numberedExps
	  case parse intRanges str of
	       Just ns | all (< (length exps)) ns
	         -> let ts = map (exps!!) ns
		    case n of 0 -> axioms := removeTerms axioms ts
		                   showAxioms True
		              1 -> theorems := removeTerms theorems ts
				   showTheorems True
			      2 -> conjects := removeTerms conjects ts
				   showConjects
			      _ -> terms := removeTerms terms ts; showTerms
	       _ -> labMag enterNumbers

	removeConjects = action conjects := []; indClauses := []
		                labGreen $ "There are neither conjectures nor " 
		                           ++ "induction hypotheses."

	removeCopies = action
	  if null trees then labBlue start
	  else let t = trees!!curr
	           p = emptyOrLast treeposs
	       if isHidden t || null p 
	          then labMag selectSub
	          else trees := updList trees curr $ removeAllCopies t p
	               setProofTerm RemoveCopies
	               setProof True False "REMOVING COPIES of the subtree" [p]
		       	        copiesRemoved
		       clearTreeposs; drawCurr

	removeEdges b = action
	  if null trees then labBlue start
	  else trees := updList trees curr $ f $ trees!!curr
	       setProofTerm $ RemoveEdges b
               setProof False False "REMOVING EDGES" [] $ edgesRemoved b
	       clearTreeposs; drawCurr
	  where f = if b then removeCyclePtrs else moreTree
	  
	removeNode = action
	  if null trees then labBlue start
	  else let t = trees!!curr
	           p = emptyOrLast treeposs
	       if isHidden t || null p 
	          then labMag selectSub
	          else trees := updList trees curr $ removeNonRoot t p
	               setProofTerm RemoveNode
	               setProof False False "REMOVING THE NODE" [p]  
	               			   "The selected node has been removed."
		       clearTreeposs; drawCurr

	removeOthers = action
	  if null trees then labBlue start
	  else if treeMode == "tree" then labGreen "There is only one tree."
	       else solPositions := if curr `elem` solPositions then [0] else []
	            treeMode := "tree"; trees := [trees!!curr]
		    counter := upd counter 't' 1; curr := 0
	            setProofTerm RemoveOthers
	            setTreesFrame [] $ setProof (treeMode == "summand") False
	                          "REMOVING THE OTHER TREES" [] removedOthers

        removePath = action
	  if null trees || null treeposs then labMag selectSub
	  else let p = last treeposs
	       trees := updList trees curr $ removeTreePath p $ trees!!curr
	       setProofTerm RemovePath
	       setProof False False "REMOVING THE PATH" [p] 
	        "The selected subtree and its ancestor nodes have been removed."
	       clearTreeposs; drawCurr
	       
	removeSigMap = action signatureMap := (id,[]); labGreen iniSigMap

	removeSpec continue = action 
	  specfiles := []; symbols := iniSymbols; signatureMap := (id,[])
	  (axioms,simplRules,transRules,theorems,conjects,terms) 
	            := ([],[],[],[],[],[])
	  continue

	removeSubst = action setSubst (V,[]); labGreen emptySubst

	removeSubtrees = action
	  if null trees then labBlue start
	  else let t = trees!!curr
		   lg = length trees
	           ps = if null treeposs then [[]] else minis (<<=) treeposs
	       if ps == [[]] then 
	          if lg < 2 then labRed "There is at most one tree."
              	  else solPositions := shift curr solPositions
	               trees := context curr trees
		       counter := decr counter 't'
	               let b = treeMode == "summand" 
	               treeMode := if lg == 2 then "tree" else treeMode
	               curr := if curr < length trees then curr else 0
	               setProofTerm RemoveSubtrees
	               setTreesFrame [] $ setProof b False 
       				          "REMOVING THE CURRENT TREE" [] 
       				          "The current tree has been removed."
	       else if any null ps then labRed $ noApp "Subtree removal"
		    else sig <- getSignature
	                 let qs = map init ps
		             q = head qs
		             u = getSubterm t q
			     r:rs = ps
			     b = last r == 0 && null rs && isImpl u && c || 
				 allEqual qs && (isDisjunct u && c ||
					         isConjunct u && not c)
			     c = polarity True t q
			     t' = lshiftPos (foldl expandInto t ps) ps
			 trees := updList trees curr $ if b && simplifying 
			 			       then simplifyIter sig t'
			     			       else t'
		         setProofTerm RemoveSubtrees
		         setProof b True "REMOVING SUBTREES" ps removed
		         clearTreeposs; drawCurr

	removeTheorems = action theorems := []
				labGreen "There are no theorems."

	renameVar = action if null trees then labBlue start
	                                 else str <- ent.getValue
	       				      renameVar' str

	renameVar' str = action
          sig <- getSignature
	  case parse (conjunct sig) str of
	       Just (F "&" ts) -> proceed ts
	       Just t -> proceed [t]
	       _ -> labMag "Enter a conjunction of equations between variables."
	  where proceed ts = action
	           case parseRenaming ts of
	           Just f 
                     -> let t = trees!!curr
	                    ps = emptyOrAll treeposs
			    ts = map (getSubterm t) ps
			    us = map (renameAll f) ts
		        trees := updList trees curr $ fold2 replace t ps us
		        setProofTerm (RenameVar str)
		        setProof False False "RENAMING VARIABLES" ps 
		        		     "Variables have been renamed."
	                clearTreeposs; drawCurr
	           _ -> labMag "Enter equations between variables."

	replaceNodes = action
	  if null trees then labBlue start
	                else x <- ent.getValue
			     if null x then labRed "The entry field is empty."
			               else replaceNodes' x
	
	replaceNodes' x = action
	  sig <- getSignature
	  let t = trees!!curr
	      ps = emptyOrAll treeposs
	      ts = map (changeRoot . getSubterm t) ps
	      new = if sig.isFovar x then V x else F x []
	      changeRoot (V _)    = new
              changeRoot (F _ []) = new
              changeRoot (F _ ts) = F x ts 
	      changeRoot t        = t
          trees := updList trees curr $ fold2 replace0 t ps ts
	  setProofTerm $ ReplaceNodes x; drawCurr
	  setProof False False "REPLACING NODES" ps $ nodesReplaced x

	replaceOther = action 
	  tree <- solve.getTree
	  case tree of
	  Just t 
            -> let p = emptyOrLast treeposs
	       trees := updList trees curr $ replace1 (trees!!curr) p t
	       setProofTerm ReplaceOther
	       setProof False False "REPLACING A SUBTREE" [p] $ replaceIn other
	       clearTreeposs; drawCurr
	  _ -> labBlue $ startOther other

	replaceQuant u target continue = action
	  let t = trees!!curr
	      x = label t target
	  if x == root u then continue
	  else case isAny t x target of
	            Just q | polarity True t q -> replaceVar x u q
	            _ -> case isAll t x target of 
		              Just q | polarity False t q -> replaceVar x u q
			      _ -> continue

	replaceSubtrees = action
	  if null treeposs then labMag selectCorrectSubformula
	     else let t = trees!!curr
		      p:ps = case treeposs of [p] -> [[],p]; _ -> treeposs
	              u:us = map (getSubterm1 t) (p:ps)
	              ts = getOtherSides u p us ps
		  if just ts then replaceSubtrees' ps $ get ts
		             else labMag selectCorrectSubformula

	replaceSubtrees' ps ts = action
	  sig <- getSignature
	  proofStep := ReplaceSubtrees ps ts
	  let t = fold2 replace1 (trees!!curr) ps ts
	  maybeSimplify sig t $ makeTrees sig $ finish ps
	  where msg = "REPLACING THE SUBTREES"
	        finish ps = action 
                       setProofTerm proofStep
		       setTreesFrame [] $ setProof True True msg ps replacedTerm

	replaceText = action if null trees then labBlue start
	                                   else str <- getTextHere
	                                        replaceText' str

 	replaceText' str = action
	  sig <- getSignature
	  let ps = emptyOrAll treeposs
	  case parseE (term sig) str of
	       Correct u -> finish u ps
	       _ -> case parseE (implication sig) str of
	                 Correct u -> finish u ps
		         p -> incorrect p str illformed
	  where finish u ps@(p:_) = action
	            case changeTerm (trees!!curr) u ps of
		    Wellformed t 
		      -> if null p then changeMode t
		          	   else trees := updList trees curr t
		         setProofTerm $ ReplaceText str
		         setProof False False "REPLACING THE SUBTREES" ps 
				  textInserted
		         clearTreeposs; drawCurr
		    Bad str -> labMag str

	replaceVar x u quantPos = action
	  sig <- getSignature
          proofStep := ReplaceVar x u quantPos
	  let t = trees!!curr
	      F z [v] = getSubterm t quantPos
	      quant:xs = words z
	      zs = xs `join` [x | x <- frees sig u `minus` frees sig t, 
	                	  nothing $ isAny t x quantPos, 
				  nothing $ isAll t x quantPos]
	      t1 = replace t quantPos $ F (unwords $ quant:zs) [v>>>for u x]
	  maybeSimplify sig t1 $ makeTrees sig finish
	  where str = showTerm0 u
	        msg = "SUBSTITUTING " ++ str ++ " FOR " ++ x 
		finish = action setProofTerm proofStep
	          		setTreesFrame [] $ setProof True True msg []
					         $ subMsg str x

	resetCatch = action 
	  (node,penpos,subtree,suptree,isSubtree) := (Nothing,Nothing,Nothing,
	  					      Nothing,Nothing)
	  firstMove := True; canv.set [Cursor "left_ptr"]

	reverseSubtrees = action
	  if null trees then labBlue start
	  else if forsomeThereis (<<) treeposs treeposs
	          then labMag "Select non-enclosing subtrees!"
	       else let t = trees!!curr
		        ps = emptyOrAll treeposs
			x = label t $ init $ head ps
			b = allEqual (map init ps) && permutative x
	            case ps of [p] -> let u = getSubterm t p
	                                  ps = succsInd p $ subterms u
			              finish t ps $ permutative $ root u
	                       _ -> if any null ps
			               then labRed $ noApp "Subtree reversal"
	                               else finish t ps b
	  where finish t ps b = action
	  	       trees := updList trees curr $ fold2 exchange t (f ps) $ f
		     				   $ reverse ps
		       setProofTerm ReverseSubtrees
		       setProof b False "REVERSING THE SUBTREES" ps reversed
		       clearTreeposs; drawCurr
		       where f = take $ length ps`div`2

	rewritePar t sig k cls saveRedex used (p:ps) qs vc continue = action
          if p `notElem` positions t -- || isVarRoot sig redex
	     then rewritePar t sig k cls saveRedex used ps qs vc continue
          else let cls1 = filterClauses sig redex $ filter unconditional cls
	           cls2 = if saveRedex then map copyRedex cls1 else cls1
		   (cls3,vc') = renameApply cls2 sig t vc
               if even matching then
                  case applyAxsToTerm cls1 cls3 axioms redex sig vc of
	          (Sum reds vc,used')
	            -> rewritePar (replace t p $ mkSum reds) sig k cls saveRedex
		                  (joinTerms used' used) ps (p:qs) vc continue
   	          _ -> rewritePar t sig k cls saveRedex used ps qs vc' continue
               else case applyAxsToTermR cls1 cls3 axioms rand redex sig vc of
	            (Sum reds vc,used',rand')
	              -> rand := rand'
                         rewritePar (replace t p $ mkSum reds) sig k cls 
			  saveRedex (joinTerms used' used) ps (p:qs) vc continue
   	            _ -> rewritePar t sig k cls saveRedex used ps qs vc' 
		                    continue
	  where redex = getSubterm t p
	rewritePar t sig k cls saveRedex used _ qs vc continue =
	  narrowPar t sig k cls saveRedex used [] qs vc continue

	runChecker = action 
	  backBut.set skipOpts; forwBut.set skipOpts; deriveBut.set runOpts
	  let act = action checkForward; showTreePicts skip
	  runProof <- runner tk checkForward; runProof.startRun speed
	  showTreePicts $ action paint.setButtons skipOpts skipOpts runOpts
				 runProofP <- runner tk act
				 runProofP.startRun speed
				 checkers := [runProof,runProofP]
          where skipOpts = [Text "", redback, Command skip]
		runOpts = [Text "stop run", redback, Command stopRun]

	saveFile file str = 
	  tk.writeFile (expanderLib ++ file) $ "-- " ++ file ++'\n':str

	saveGraph file = action
  	  if null trees then labBlue start 
  	                else file <- savePng canv $ pixpath file
	                     lab2.set [Text $ saved "tree" $ file]

	saveGraphN = action
  	  if null trees then labBlue start
  	  		else if notnull treeDir then saveGraphN'

	saveGraphN' = action
  	  let dirPath = pixpath treeDir
	  file <- savePng canv $ mkFile dirPath picNo
	  files <- getDirectoryContents dirPath
	  tk.writeFile (dirPath ++ ".html") $ html True treeDir 
	  				    $ pix treeDir files
	  picNo := picNo+1
	  lab2.set [Text $ saved "tree" $ file]

	saveProof = action
	  if null proof then labMag $ "The proof is empty" 
	  else file <- ent.getValue
	       let filePath = expanderLib ++ file
	           pfile = filePath ++ "P"
                   tfile = filePath ++ "T"
	       write pfile $ '\n':showDeriv proof trees solPositions
	       write tfile $ show proofTerm
	       labGreen $ saved "proof" pfile ++ '\n':saved "proof term" tfile
          where write file str = tk.writeFile file $ "-- " ++ file ++ '\n':str

	saveSigMap file = action
	  saveFile file $ showSignatureMap signatureMap ""
	  labGreen $ saved "signature map" file

     	saveSpec file = action
	  saveFile file $ showSignature (minus6 symbols iniSymbols)
	      			     $ f "\naxioms:\n" showFactors axioms ++
				       f "\ntheorems:\n" showFactors theorems ++
				       f "\nconjects:\n" showFactors conjects ++
				       f "\nterms:\n" showSum terms
	  labGreen $ saved "specification" file
	  where f str g cls = if null cls then "" else str ++ g cls

     	saveTree file = action
  	  if null trees then labBlue start
	                else saveFile file $ showTree fast $ trees!!curr
			     labGreen $ saved "tree" file

     	saveTrees file = action
  	  if null trees then labBlue start
	  else saveFile file $ showTree fast $ joinTrees treeMode trees
	       labGreen $ saved "trees" file

	setAdmitted block = action 
	  str <- ent.getValue
	  setAdmitted' block $ if null trees || null treeposs then words str
	                       else map (label $ trees!!curr) treeposs
			   
        setAdmitted' block xs = action 
	  let msg = admitted block xs
	  constraints := (block,xs)
	  if null trees then labGreen msg
	                else setProofTerm $ SetAdmitted block xs
	                     setProof True False "ADMITTED" [] msg 

	setCollapse = action 
	  collSimpls := not collSimpls
	  simplButD.set [Text $ if collSimpls then "simplifyDFC" 
	  				      else "simplifyDF"] 
	  simplButB.set [Text $ if collSimpls then "simplifyBFC"
	  				      else "simplifyBF"]

	setCurr msg n = action 
	  if n /= curr then curr := n; treeSlider.setValue n
			    paint.setCurrInPaint n
	                    setProofTerm $ SetCurr msg n
			    setProof True False "MOVED" [] msg
	          	    clearTreeposs; drawCurr
		       else labColorToPaint magenta msg

        setCurrInSolve n continue = action if n < length trees 
					      then setCurr newCurr n; continue

        setDeriveMode = action	
	  if checking then mapM_ (.stopRun0) checkers; checking := False
	                   checking := False; speed := 0
			   backBut.set [Text "<---", Command backProof]
			   forwBut.set [Text "--->", Command forwProof]
			   case (simplifying,refuting) of (True,True)  -> dsr
		      	     	     	       	          (True,_)     -> ds
							  (False,True) -> dr
							  _ -> set "derive"
	                   quit.set [Text "quit", Command tk.quit, greenback]
			   setMatch False
			   paint.setButtons (f "narrow/rewrite" narrow)
	     		     	            (f "simplifyDF" $ simplify True)
					    (f "simplifyBF" $ simplify False)
		           proofTerm := take proofTPtr proofTerm
			   enterPT proofTPtr proofTerm
			   proof := take (proofPtr+1) proof;
	              else case (simplifying,refuting) of 
	                        (False,False) -> simplifying := True; ds
				(True,False) -> refuting := True; dsr
				(True,_) -> simplifying := False; dr
				_ -> refuting := False; set "derive"
	                   setProofTerm $ DeriveMode simplifying refuting
	  where f str act = [Text str, blueback, 
		             Command $ paint.remote $ act $ showTreePicts skip]
	        set str = action deriveBut.set [Text str, Command setDeriveMode]
	        ds = set "derive & simplify"
		dr = set "derive & refute"
		dsr = set "derive & simplify & refute"

	setExtension i = action 
	  if i > 0 then if i > 100 then tedit.set [Height 0]
	                canv.set [Height i]
		   else tedit.set [Height $ -i]

	setFont fo = action let [family,style] = words fo
	     		        [_,size,_] = words font.fontName
	  		    font0 <- tk.font $ unwords [family,size,style]
	  		    font := font0
			    if notnull trees then drawCurr

	setFontSize size = action 
	  let [family,_,style] = words font.fontName
	      str = show size
	      lstr = show (size-3)
	  font0 <- tk.font $ unwords [family,str,style]
	  font := font0
	  tedit.set [Font $ "Courier "++str]
	  ent.set [Font $ "Courier "++str]
	  lab.set [Font $ "Helvetica "++lstr++" italic"]
	  lab2.set [Font $ "Helvetica "++lstr++" italic"]

	setForw opts = action forwBut.set opts

	setInterpreter eval = action
	  sig <- getSignature
	  wtree := take 4 eval == "tree"
	  picEval := eval
	  interpreterBut.set [Text eval]
	  paint.setEval eval spread
	  draw <- ent.getValue
	  drawFun := if sig.isDefunct draw then draw else ""
	  labGreen $ newInterpreter eval drawFun

        setMatch chgMatch = action 
	  sig <- getSignature 
	  let nar = formula || notnull treeposs &&
	  		       treeposs `subset` boolPositions sig (trees!!curr)
              back = if notnull treeposs then redback else blueback
	      set str = matchBut.set [Text str, back]
	      f but = but.set [back]
	  if chgMatch then matching := (matching+1) `mod` (if nar then 4 else 2)
                           setProofTerm $ Match matching
          if nar then case matching of 0 -> set "match & narrow"
			               1 -> set "match & narrow1"
				       2 -> set "unify & narrow"
				       _ -> set "unify & narrow1"
		 else case matching of 0 -> set "match & rewrite"
				       _ -> set "match & rewrite1"
	  mapM_ f [deriveBut,narrowBut,simplButD,simplButB]	  

        setMaxHeap n = action maxHeap := n

	setNewTrees ts typ = action 
	  trees := ts; counter := upd counter 't' $ length ts; treeMode := typ 
	  initialize "trees"; setTreesFrame [] done

	setProof correct postSimpl msg ps labMsg = action
	  let oldProofElem = proof!!proofPtr
	      t = trees!!curr
	      n = counter 'd'
	      msg1 = msg `elem` words "ADMITTED EQS"
	      msg2 = msg `elem` words "MOVED SPLIT JOIN"
	      str = if msg1 then labMsg
	            else if msg2 then labMsg ++ showCurr fast t formula
		    else if newTrees 
		         then showNew fast (length trees) t msg n ps formula
			 else showPre fast t msg n ps formula
	      str0 = "\nThe axioms have been MATCHED against their redices."
	             `onlyif` matching < 2
	      str1 = "\nThe reducts have been simplified." `onlyif` simplifying
              str2 str = "\nFailure "++ str ++" have been removed."	
		         `onlyif` refuting	 
	      str3 = if correct then case ruleString of 
	      			     "NARROWING" -> str0++str1++str2 "atoms"
			             "REWRITING" -> str1++str2 "terms"
			             _ -> str1 `onlyif` postSimpl
		     else "\nCAUTION: This step may be semantically incorrect!"
	      (msgP,msgL) = if null str3 then (str,labMsg)
		                         else (str++'\n':str3,labMsg++str3)
	      msg3 = msgL ++ if newTrees || msg1 || msg2 || notnull msgL && 
	                        head msgL == ' ' || trees /= oldProofElem.trees 
		             then "" else "\nCAUTION: The "++ formString formula
			     	          ++" has not been modified."
	      u = joinTrees treeMode trees
	      us = map (joinTrees treeMode . (.trees)) proof
	      cycle = search (eqTerm u) us
	      i = get cycle
	      cmsg i = "\nTHIS GOAL COINCIDES WITH GOAL NO. " ++ show i
	      msg4 = if just cycle then msg3 ++ cmsg i else msg3
	  if null ruleString || n > 0 then
	     proofPtr := proofPtr+1
	     let proof' = if nothing cycle then proof
		      	  else updList proof i $ extendMsg (cmsg proofPtr)
			  		       $ proof!!i 
		 next = struct msg = if just cycle then msgP ++ cmsg i else msgP
		      	       msgL = msg4; treeMode = treeMode; trees = trees
			       treePoss = ps; curr = curr -- perms = perms
			       varCounter = varCounter; newPreds = newPreds
			       solPositions = solPositions
			       substitution = substitution
			       constraints = constraints; joined = joined
			       safe = safe
	     proof := take proofPtr proof'++[next]
	     {- case u of F x ts | just cycle && permutative x 
		         -> let n = length ts
			    perms := upd perms n $ nextPerm $ perms n
			    (curr,trees) := (0,[F x [ts!!i | i <- perms n]])
		       _ -> done -}
          else picNo := picNo-1
	  newTrees := False; ruleString := ""
	  labColorToPaint green $ show proofPtr ++ ". " ++ msg4

	setProofTerm step = action
          if not checking
             then let pt = if proofTPtr+1 < length proofTerm 
	     		   then take proofTPtr proofTerm else proofTerm
                  proofTerm := addStep pt step
	          proofTPtr := length proofTerm

	setQuit opts = action quit.set opts

	setSubst subst@(f,dom) = action
	  subToBut.set [if null dom then blueback else redback]
	  domMenu <- subToBut.menu []
	  mapM_ (createBut domMenu applySubstTo) dom
	  substitution := subst

	setSubtrees = action
	  if null trees then labBlue start
	  else str <- ent.getValue
	       let f = natToLabel $ posTree [] $ trees!!curr
	       case parse intRanges str of
	            Just ns | all (just . f) ns
		      -> let qs = map get $ map f ns
		         setTreeposs $ Add $ qs `minus` treeposs
		         drawSubtrees
			 labGreen $ case qs of
			            [q] -> "The tree at position " ++ show q ++ 
				           " has been selected."
		                    _ -> "The trees at position " ++ 
			                 init (tail $ show qs `minus1` ' ') ++
					 " have been selected."
	            _ -> labMag "Enter tree positions in heap order!"
	       
	setTime = action time <- tk.timeOfDay; times := (time,snd times)
	
	setTreeDir = action
	  dirNo <- ent.getValue	  
	  if null dirNo then lab2.set [Text emptyTreeDir]
	  else let dir:rest = words dirNo
	  	   n = parse nat $ concat rest
	  	   dirPath = pixpath dir
	  	   f i 0 = done
	  	   f i k = do system $ "rm -f "++mkFile dirPath i++".png"
	  	              f (i+1) $ k-1
	       treeDir := dir
	       lab2.set [Text $ dir++" is the current directory"]
	       picNo := if just n then get n else 0
	       mkdir dirPath
	       files <- getDirectoryContents dirPath
	       f picNo $ length files
	       files' <- getDirectoryContents dirPath
	       let files = pix dir files'
	       if notnull files
	          then tk.writeFile (dirPath ++ ".html") $ html True dir files

	setTreeposs step = action 
          oldTreeposs := treeposs
	  treeposs := case step of Add ps -> treeposs++ps
				   Remove p -> treeposs`minus1`p
				   Replace ps -> ps
          setProofTerm $ Mark treeposs
	  setMatch False

	setTreesFrame ps continue = action
	  let lg = length trees
	      str = case treeMode of "tree" -> formString formula
				     _ -> show lg ++ ' ':treeMode ++ "s"
	  treeSlider.set [To (lg-1)]; treeSlider.setValue curr
	  paint.setCurrInPaint curr; treeBut.set [Text str]
	  setTreeposs $ Replace ps
	  drawCurr; continue
	
	setZcounter n = action varCounter := upd varCounter "z" n

	shiftPattern = action
 	  if null trees || not formula then labBlue startF
	  else let [p,q] = case treeposs of [r] -> [[],r]; _ -> treeposs
	  	   r = drop (length p) q
	           t = trees!!curr
	       if null treeposs || length treeposs > 2 || not (p << q)
	          then labMag "Select a (conditional) equation and a pattern!"
	       else sig <- getSignature
                    case makeLambda sig (getSubterm1 t p) r of
		    Just cl -> trees := updList trees curr $ replace1 t p cl
		   	       setProofTerm ShiftPattern
		               setProof True False "SHIFTING A PATTERN" [[]] 
			                "A pattern has been shifted."
		               clearTreeposs; drawCurr
		    _ -> labMag "The selected pattern cannot be shifted."

	shiftQuants = action
	  if null trees then labBlue start
	  else let t = trees!!curr
		   ps = treeposs
	       if null ps || any null ps then errorMsg
	       else let qs = map init ps
			ts = map (getSubterm1 t) ps
			qvars = map (\t -> alls t++anys t) ts
                    if allEqual qs && any notnull qvars then
                       sig <- getSignature
	               let q = head qs
		           u = getSubterm1 t q
		           x = root u
		       if isF u && x `elem` words "==> Not & |" then
			  let (as,es,v,vc) = moveUp sig varCounter x 
			      			    (subterms u) $ map last ps
			      v' = simplifyIter sig v
                          finish (replace1 t q $ mkAll as $ mkAny es v') ps vc
		       else errorMsg
 		    else errorMsg
          where finish t ps vc = action 
			    trees := updList trees curr t
			    varCounter := vc
	                    setProofTerm ShiftQuants
	            	    setProof True False "MOVING UP QUANTIFIERS" ps moved
       	                    clearTreeposs; drawCurr
		errorMsg = labRed $ noApp "Move up quantifiers"

	shiftSubs = action
	  if null trees then labBlue start
	                else if null treeposs || any null treeposs 
		                then labRed $ noApp "Shift subformulas"
	       	                else shiftSubs' treeposs 

	shiftSubs' ps = action
          sig <- getSignature
	  case shiftSubformulas sig (trees!!curr) ps of
	       Just t -> trees := updList trees curr t
	                 setProofTerm $ ShiftSubs ps
	                 setProof True False "SHIFTING SUBFORMULAS" ps shifted
       	                 clearTreeposs; drawCurr
	       _ -> labRed $ noApp "Shift subformulas"

	showAdmitted = action 
	  let (block,xs) = constraints
	  if block && null xs then labGreen $ admitted True []
	  else let axs = clausesFor xs axioms
	       enterFormulas $ if block then axioms `minus` axs else axs
	       labGreen "See the admitted axioms in the text field."

	showAxioms b = action
	  if null axioms then labGreen "There are no axioms."
	  else if b then enterFormulas axioms
	                 labGreen $ see "axioms"
	            else solve.bigWin; solve.enterFormulas axioms

	showAxiomsFor = action
	  str <- ent.getValue
	  let ps = emptyOrAll treeposs
	      xs = if null trees || null treeposs && notnull str then words str
	           else mkSet $ map (label $ trees!!curr) ps
	      axs = clausesFor xs axioms
	  if null axs then labRed $ noAxiomsFor xs
	  	      else enterFormulas axs
	       		   labGreen $ see "axioms for " ++ showStrList xs

	showChanged = action
          if proofPtr <= 0 then labMag "The proof is empty."
	  else restore := True
	       let proofElem = proof!!(proofPtr-1)
	           k = proofElem.curr
		   ts = proofElem.trees
	       if k == curr then let ps = changedPoss (ts!!k) (trees!!k)
	                         setTreeposs $ Replace ps; drawCurr
			    else labMag newCurr

	showConjects = action
	  if null conjects then labGreen "There are no conjectures."
	                   else enterFormulas conjects
	                        labGreen $ see "conjectures"

        showCoords = action
          if null trees then labBlue start
	                else restore := True
	                     drawThis (cTree (trees!!curr) $ get ctree) [] ""

	showCycleTargets = action
	  if null trees then labBlue start 
	  		else restore := True
               		     let t = trees!!curr
			     drawThis t (cycleTargets t) "green"

	showEqsOrGraph b m = action
	  sig <- getSignature
	  let (sts0,ats0,labs0,tr,trL,va,vaL) = kripke
	      [sts,ats,labs] = map (map showTerm0) [sts0,ats0,labs0]
	      neValue = any notnull va
	      vaR = invertRelI ats sts va
	      vaLR = invertRelII neValue labs ats sts vaL
	      vcz = varCounter "z"
              (eqs,zn) = if null labs then relToEqs vcz $ mkPairs sts sts tr
		         else relLToEqs vcz $ mkTriples sts labs sts trL
	      bgraph = mapT f $ eqsToGraph [] eqs
	      	       where f x = if x `elem` map showTerm0 sig.labels
	      	       		   then "blue_"++x else x
	      bgraphK = if null ats then bgraph
	       	        else if neValue then addAtoms sts labs ats vaR bgraph
	       		                else addAtomsL sts labs ats vaLR bgraph
	      (str,msg) = if m == 7 then ("BUILDING EQUATIONS",eqsBuilt)
			    	    else ("BUILDING A GRAPH",graphBuilt)
	  if m < 4 then setZcounter zn
	  case m of
	       0 -> if b then enterTree False bgraph
	                 else solve.bigWin; solve.enterTree False bgraph
	       1 -> inPainter sig bgraph
	       2 -> if b then enterTree False bgraphK
	       		 else solve.bigWin; solve.enterTree False bgraphK
	       3 -> inPainter sig bgraphK
	       _ -> if null trees then labBlue start
	            else let t = trees!!curr
		    	     finish zn p u = action
	                            trees := updList trees curr $ replace1 t p u
				    if m == 7 then setZcounter zn
				    setProofTerm $ ShowEqsOrGraph b m
		                    setProof True False str [p] msg
			            clearTreeposs; drawCurr
	      	             relToEqs1 = relToEqs vcz . deAssoc1
	      	             relToEqs3 = relLToEqs vcz . deAssoc3
	      	             p:ps = emptyOrAll treeposs
	      	             u = getSubterm1 t p
	      	             (q,f,r) = if null ps then ([],id,p) 
			     	       else (p,drop $ length p,head ps)
                             (eqs,zn) = graphToEqs vcz (getSubterm1 t q) $ f r
                             is = [i | [i,1] <- map f ps]
                             x = label t r
			 case m of 
			 4 -> finish 0 p $ collapse True u
			 5 -> finish 0 p $ collapse False u
			 6 -> case parseColl parseConsts2 u of
			      Just rel -- from pairs to a graph
			        -> let (eqs,zn) = relToEqs1 rel
			           finish zn p $ eqsToGraphx x eqs
	                      _ -> case parseColl parseConsts3 u of
			           Just rel -- from triples to a graph
				     -> let (eqs,zn) = relToEqs3 rel
				   	finish zn p $ eqsToGraphx x eqs
	                           _ -> case parseRegEqs u of
				        Just eqs -- from equations to a graph
					  -> finish vcz p $ eqsToGraph is eqs
				        _ -> -- from a graph to a graph
					     finish vcz q $ eqsToGraphx x eqs  
			 _ -> case parseColl parseConsts2 u of
	                      Just rel -- from pairs to equations
			        -> let (eqs,zn) = relToEqs1 rel
				   finish zn p $ eqsToTerm eqs
	                      _ -> case parseColl parseConsts3 u of
	                           Just rel -- from triples to equations
	                             -> let (eqs,zn) = relToEqs3 rel
				        finish zn p $ eqsToTerm eqs
	                           _ -> case parseRegEqs u of
			                Just eqs -- from equations to equations
					  -> let (xs,ts) = unzipEqs eqs
					         (f,zs) = substitution
					     if "eqs" `elem` zs then
					        finish vcz p $ separateTerms 
					        	       (f "eqs") is
						substitution := 
						         (upd f "eqs" $ V "eqs",
							  zs `minus1` "eqs")
				             else let t = mkEqsConjunct xs 
				                              $ connectEqs xs ts
					          finish vcz p t
						  substitution := 
						        (upd f "eqs" t,"eqs":zs)
		                        _ -> -- from a graph to equations
					     finish vcz q $ eqsToTerm eqs
	 where inPainter sig t = action
		           let u = head $ applyDrawFun sig drawFun [t]
		               pict = widgetTree sizes0 spread u
	                   if nothing pict then labMag "The tree is empty."
	                   else sizes <- mkSizes font $ stringsInPict $ get pict
                                paint.setFast fast
			        paint.setEval "tree" spread
			        let pict = get $ widgetTree sizes spread u
			        paint.callPaint [pict] [curr] False True curr 
			     		        "white" skip

	showGlb = action
          if null treeposs then labMag "Select subtrees!"
	  else restore := True
	       drawThis (trees!!curr) [glbPos treeposs] "green"

	showIndClauses = action
	  if null indClauses then labGreen "There are no induction hypotheses."
	  else enterFormulas indClauses
	       labGreen $ see "induction hypotheses"
	 
        showMatrix m = action
	  let (sts0,ats0,labs0,tr,trL,va,vaL) = kripke
	      [sts,ats,labs] = map (map showTerm0) [sts0,ats0,labs0]
	      neValue = any notnull va
	      vaR = invertRelI ats sts va
	      vaLR = invertRelII neValue labs ats sts vaL
	      p:ps = emptyOrAll treeposs
	      t = getSubterm1 (trees!!curr) p
	      f = if null ps then id else drop $ length p
	      is = [i | [i,1] <- map f ps]
	      pict = matrix sizes0 spread t
	      u = case m of 0 -> if null labs then Hidden $ BoolMat sts sts
					                  $ mkPairs sts sts tr
		                 else Hidden $ ListMat sts labs 
		       		             $ mkTriples sts labs sts trL
		            1 -> if neValue then Hidden $ BoolMat ats sts 
		  			                $ mkPairs ats sts va
		                 else Hidden $ ListMat ats labs 
		       		             $ mkTriples ats labs sts vaL
		            2 -> if neValue then Hidden $ BoolMat sts ats 
		  			                $ mkPairs sts ats vaR
		                 else Hidden $ ListMat sts labs 
		       		             $ mkTriples sts labs ats vaLR
		            _ -> case parseRegEqs t of
		                      Just eqs -> mat m $ eqsToGraph is eqs
		                      _ -> if just pict then t else mat m t
              pict' = matrix sizes0 spread u
	  if m > 2 && null trees then labBlue start
	  else if nothing pict' then labMag "The matrix is empty."
	       else sizes <- mkSizes font $ stringsInPict $ get pict'
		    paint.setFast fast
		    paint.setEval "" spread
		    let pict' = get $ matrix sizes spread u
	            paint.callPaint [pict'] [curr] False True curr "white" skip
	  where mat 3 t = Hidden $ BoolMat dom1 dom2 ps
	  		  where ps = graphToRel t
			        (dom1,dom2) = sortDoms $ deAssoc0 ps
	        mat _ t = Hidden $ ListMat dom1 dom2 ts
	  		  where ts = graphToRel2 (evenNodes t) t
			        (dom1,dom2) = sortDoms $ map (pr1 *** pr2) ts
	
        showNumbers m = action
          if null trees then labBlue start		  
	  else restore := True
	       col <- ent.getValue
	       let t = trees!!curr
	       	   p = emptyOrLast treeposs
		   u = getSubterm1 t p
		   c = case parse color col of Just d -> d; _ -> black
		   (v,n) = order c label u
	       drawThis (replace1 t p v) [] ""
	  where label (RGB 0 0 0) n = show n
		label c n           = show c++'_':show n
		(order,str) = case m of 1 -> (levelTerm,"level numbers")
				        2 -> (preordTerm,"preorder positions")
					3 -> (heapTerm,"heap positions")
					_ -> (hillTerm,"hill positions")

	showPicts = action
	  if null trees then labBlue start
          else if checking then checkingP := True; showTreePicts skip
	       else if null treeposs then showTreePicts skip
		    	             else showSubtreePicts

        showPolarities = action
          if null trees then labBlue start
	  else restore := True
	       let t = trees!!curr
		   ps = polTree True [] t
	       drawThis (colorWith2 "green" "red" ps t) [] ""

        showPositions = action
	  if null trees then labBlue start
	  else restore := True
	       let t = trees!!curr
	       drawThis (mapT f $ posTree [] t) (pointers t) "red"
	  where f = unwords . map show

	showPreds = action
	  if null trees then labBlue start
	  else restore := True
	       let t = trees!!curr
	           ps = concatMap (nodePreds t) $ emptyOrAll treeposs
               drawThis t ps "green"

	showProof b = action
	  if null proof then labMag "The proof is empty."
	  else let str = '\n':showDeriv proof trees solPositions
               if b then enterText str; labGreen $ see "proof"
	            else solve.bigWin; solve.enterText str

	showProofTerm b = action
	  if null proofTerm then labMag "The proof term is empty."
	  else if b then enterPT proofTPtr proofTerm
	                 labGreen $ see "proof term"
	            else solve.bigWin; solve.enterPT proofTPtr proofTerm

	showRelation m = action
	  let (sts0,ats0,labs0,tr,trL,va,vaL) = kripke
	      [sts,ats,labs] = map (map showTerm0) [sts0,ats0,labs0]
	      neValue = any notnull va
	      vaR = invertRelI ats sts va
	      vaLR = invertRelII neValue labs ats sts vaL
	      t = trees!!curr
	      p:ps = emptyOrAll treeposs
	      u = getSubterm1 t p
	      f = if null ps then id else drop $ length p
	      is = [i | [i,1] <- map f ps]
	  case m of 0 -> act1 $ if null labs then mkRelConstsI sts sts tr 
			                     else mkRel2ConstsI sts labs sts trL
	            1 -> act1 $ if neValue then mkRelConstsI ats sts va
		    		           else mkRel2ConstsI ats labs sts vaL
	            2 -> act1 $ if neValue then mkRelConstsI sts ats vaR
		    	                   else mkRel2ConstsI sts labs ats vaLR
	            _ -> if null trees then labBlue start
		         else act2 t p $ case parseRegEqs u of
			                      Just eqs -> eqsToGraph is eqs
					      _ -> u
	  where act1 ts = enterTree False $ h ts
	        act2 t p u = action
	             trees := updList trees curr $ replace1 t p $ h $ f m u
 		     setProofTerm $ ShowRelation m
	             setProof True False "BUILDING A RELATION" [p] relationBuilt
	             clearTreeposs; drawCurr
		     where f 3 = mkRelConsts . graphToRel
                   	   f _ = mkRel2Consts . graphToRel2 (evenNodes u)
		g t@(F "()" ts) us = case last ts of F "[]" [] -> us
						     _ -> t:us
		h = mkList . foldr g []

	showSig = action 
	  enterText $ showSignature (minus6 symbols iniSymbols) ""
	  let (block,xs) = constraints
	  labGreen $ see "signature" ++ '\n':admitted block xs 
	  			     ++ '\n':equationRemoval safe

	showSigMap = action 
	  if null $ snd signatureMap then labGreen iniSigMap
          else enterText $ showSignatureMap signatureMap ""
	       labGreen $ see "signature map"

	showSolutions = action 
	  sig <- getSignature
	  labGreen $ solved $ if formula then solPoss sig trees else []

	showSubst b = action
	  let (f,dom) = substitution
	      fs = substToEqs f dom
	  if null dom then labGreen emptySubst
          else if b then enterFormulas fs
          		 labGreen $ see "substitution"
          	    else solve.bigWin; solve.enterFormulas fs

	showSubstCanv = action
	  let (f,dom) = substitution
	      ts = substToEqs f dom
	      typ = if length ts == 1 then "tree" else "factor"
	  if null dom then labGreen emptySubst
	              else solve.bigWin; solve.setNewTrees ts typ

	showSubtreePicts = action
	  sig <- getSignature
	  eval <- getInterpreter
	  let t = trees!!curr
	      ts = applyDrawFun sig drawFun $ map (closedSub t) treeposs
	      picts0 = map (eval sizes0 spread) ts
	      (us,picts) = unzip [(t,pict) | (t,Just pict) <- zip ts picts0]
	  if all nothing picts0 then labMag "The picture is empty."
	  else sizes <- mkSizes font $ concatMap stringsInPict picts
	       paint.setFast fast
               setTime
	       back <- ent.getValue
	       let pict = concatMap (get . eval sizes spread) us
	       paint.callPaint [pict] [] True True curr back skip

	showSucs = action
	  if null trees then labBlue start
	  else restore := True
               let t = trees!!curr
               drawThis t (concatMap (nodeSucs t) $ emptyOrAll treeposs) "green"

	showSyms f = action
	  if null trees then labBlue start
	  else restore := True
               sig <- getSignature
	       let t = trees!!curr
	           p = emptyOrLast treeposs
	       drawThis t (map (p++) $ f sig $ getSubterm t p) "green"

	showTerms = action if null terms 
			      then labGreen "There are no terms to be reduced."
	                   else enterTerms terms
	                        labGreen $ see "terms"

	showTheorems b = action
	  if null theorems then labGreen "There are no theorems."
	  else if b then enterFormulas theorems
			 labGreen $ see "theorems"
		    else solve.bigWin; solve.enterFormulas theorems

	showTheoremsFor = action
	  str <- ent.getValue
	  let xs = if null trees || null treeposs then words str
	           else map (label $ trees!!curr) treeposs
	      cls = clausesFor xs theorems
	  if null cls then labRed $ "There are no theorems for " ++ 
	  			    showStrList xs ++ "."
	  	      else enterFormulas cls
	  	           labGreen $ see "theorems for " ++ showStrList xs

	showTreePicts continue = action
	  sig <- getSignature
	  eval <- getInterpreter
	  let ts = applyDrawFun sig drawFun trees
	      picts0 = map (eval sizes0 spread) ts
	      (us,picts,poss) = unzip3 [(t,pict,pos) | 
	                      (t,Just pict,pos) <- zip3 ts picts0 $ indices_ ts]
          if all nothing picts0 then labMag "The picture is empty."
	  else sizes <- mkSizes font $ concatMap stringsInPict picts
	       paint.setFast fast
	       setTime
	       back <- ent.getValue
	       let picts = map (get . eval sizes spread) us
	       paint.callPaint picts poss False (checkingP || not checking) curr
	       		       back continue

	showVals = action
	  if null trees then labBlue start
	  else restore := True
	       let t = trees!!curr
               drawThis t (valPositions t) "green"

	simplify depthfirst continue = action
	  if null trees then labBlue start
	  else str <- ent.getValue
	       let act limit sub = simplify' depthfirst limit sub continue
	       case parse pnat str of Just limit -> act limit True
		                      _ -> act 100 False

	simplify' depthfirst limit sub continue = action 
	  ruleString := "SIMPLIFYING"
	  proofStep := Simplify depthfirst limit sub
	  sig <- getSignature
	  let t = trees!!curr
	  if null treeposs then 
	     setTime
	     let (u,n) = simplifyLoop sig depthfirst limit t
	         v = if collSimpls then collapse True u else u
	         msg = "The " ++ (if treeMode == "tree" then formString formula
		              else "previous " ++ treeMode) ++ " is simplified."
	     if n == 0 then counter := decr counter 't'
	                    if counter 't' > 0 
			       then setCurr msg $ (curr+1) `mod` length trees
			    	    continue
                               else labMag treesSimplified
			            paint.labSolver treesSimplified
	     else trees := updList trees curr v
	          makeTrees sig $ action setProofTerm proofStep
			                 counter := upd counter 'd' n
	       		                 setProof True False ruleString [] $
	                                    finishedSimpl n++solved solPositions
			                 setTreesFrame [] continue
	  else if sub then simplifySubtree t sig depthfirst limit continue
                      else simplifyPar t sig treeposs [] continue

	simplifyPar t sig (p:ps) qs continue = action
 	  case simplifyOne sig t p of
	       Just t -> simplifyPar t sig ps (p:qs) continue
	       _ -> simplifyPar t sig ps qs continue
	simplifyPar _ _ [] [] _ = labColorToPaint magenta
	            "The selected trees are simplified at their root positions."
							
	simplifyPar t _ _ qs continue = action
          trees := updList trees curr t
	  setProofTerm proofStep
	  counter := upd counter 'd' 1
	  setProof True False "SIMPLIFYING THE SUBTREES" qs simplifiedPar
	  clearTreeposs; drawCurr
          continue

	simplifySubtree t sig depthfirst limit continue = action
 	  let p = emptyOrLast treeposs
	      (u,n) = simplifyLoop sig depthfirst limit $ expand 0 t p
	      v = if collSimpls then collapse True u else u
	  if n == 0 then 
	     labColorToPaint magenta "The tree selected at last is simplified."
	     continue
          else trees := updList trees curr $ replace1 t p v
	       setProofTerm proofStep
               counter := upd counter 'd' n
               setProof True False ruleString [p] $ 
	       			   appliedToSub "simplification" n
	       clearTreeposs; drawCurr
 	       continue

        skip = action done

	specialize = action
          if null trees then labBlue start
	  else str <- ent.getValue
	       let (exps,b) = numberedExps
	       case parse nat str of
	            k@(Just n) | n < length exps
	              -> if b then finish k $ exps!!n
		              else labMag "Enter formulas into the text field!"
	            _ -> sig <- getSignature
	                 str <- getTextHere
 	                 case parseE (implication sig) str of
	                      Correct th -> finish Nothing th
	                      p -> incorrect p str illformedF
	  where finish k th = applyTheorem False k $ 
	  		           case th of F "Not" [th] -> mkHorn mkFalse th
			                      _ -> mkCoHorn mkTrue th

	splitTree = action
	  if notnull trees then 
	     sig <- getSignature
	     setProofTerm SplitTree
	     if joined then joined := False; splitBut.set [Text "join"]
                            makeTrees sig $ setTreesFrame [] 
		   		          $ setProof True False "SPLIT" []
					  $ "The tree has been split."
	     else joined := True; splitBut.set [Text "split"]
	          let t = joinTrees treeMode trees
	          treeMode := "tree"; trees := [t]; counter := upd counter 't' 1
		  curr := 0
		  solPositions := if formula && isSol sig t then [0] else [] 
	          setTreesFrame [] $ setProof True False "JOIN" [] 
		  		   $ "The trees have been joined."

	startInd ind = action
          if null trees || not formula then labBlue startF
          else limit <- ent.getValue
	       let n = case parse (do symbol "more"; pnat) limit of Just k -> k
	       							    _ -> 0
	       if n /= 0 then ent.setValue ""
	       if ind then applyInduction n else applyCoinduction n

        stopRun = action 
	  if checking then mapM_ (.stopRun0) checkers
	                   backBut.set [Text "<---", Command backProof]
			   forwBut.set [Text "--->", Command forwProof]
			   deriveBut.set runOpts
			   paint.setButtons backOpts forwOpts runOpts
	  where backOpts = [Text "<---", Command $ actInPaint backProof]
	        forwOpts = [Text "--->", Command $ actInPaint forwProof]
		runOpts = [Text "run proof", redback, Command runChecker]
                actInPaint act = action act; showTreePicts skip

	stretch prem = action
	  if null trees || not formula then labBlue startF
	  else let t = trees!!curr
		   p = emptyOrLast treeposs
		   u = getSubterm t p
		   (f,pt,str) = 
		             if prem then (stretchPrem,StretchPremise,"PREMISE")
			     else (stretchConc,StretchConclusion,"CONCLUSION")
	       case preStretch prem (const True) u of
	       Just (_,varps)
	         -> let (v,n) = f (varCounter "z") varps u
	  	    trees := updList trees curr $ replace t p v
	            setZcounter n
		    setProofTerm pt
	            setProof True False ("STRETCHING THE "++str) [p] stretched
	            clearTreeposs; drawCurr
	       _ -> notStretchable $ "The "++str

	subsumeSubtrees = action
	  if length treeposs /= 2 || any null treeposs
	     then labMag "Select two proper subtrees!"
	  else let t = trees!!curr
		   ps@[p,q] = treeposs
		   prem = getSubterm t p
		   conc = getSubterm t q
		   r = init p
		   s = init q
		   u = getSubterm t r
	       sig <- getSignature
	       if subsumes sig prem conc then
	          if r == s then
	             if isImpl u then
	                trees := updList trees curr $ replace t r mkTrue
		        finish ps "premise"
		     else if isConjunct u then
	                     let u' = F "&" $ context (last q) $ subterms u
		             trees := updList trees curr $ replace1 t r u'
		             finish ps "factor"
	                  else if isDisjunct u then
	                          let u' = F "|" $ context (last p) $ subterms u
		                  trees := updList trees curr $ replace t r u'
		                  finish ps "summand"
		               else labGreen msg
		  else labGreen msg
	       else labRed "The selected trees are not subsumable."
	  where msg = "The selected trees are subsumable."
	        finish ps str = action 
		             setProofTerm SubsumeSubtrees
		    	     setProof True False "SUBSUMPTION" ps $ subsumed str
			     clearTreeposs; drawCurr

        switchFast = action fast := not fast
	  		    fastBut.set [Text $ if fast then "slow" else "fast"]

        switchSafe = action 
	  safe := not safe
	  setProofTerm SafeEqs
	  setProof True False "EQS" [] $ equationRemoval $ not safe
	  safeBut.set [CLabel $ eqsButMsg safe]
			    
	unifyAct u u' t t' p q = action
	  restore := True
	  sig <- getSignature
	  case unify u u' t t' p q V sig [] of
	       Def (f,True)
	         -> let xs = frees sig u ++ frees sig u'
	       		dom = domSub xs f
		    if null dom then labGreen $ unifiedT ++ emptySubst
                    else if any hasPos $ map f dom then labRed posInSubst
     	                 else setSubst (f,dom)
			      labGreen $ unifiedT ++ "See substitution > show."
	       Def (_,False) -> labRed partialUnifier
	       BadOrder -> labRed noUnifier
	       Circle p q -> labRed $ circle p q
	       NoPos p -> setTreeposs $ Replace [p]; drawCurr; labRed dangling
	       NoUni -> labRed noUnifier
	       OcFailed x -> labRed $ ocFailed x

	unifyOther = action 
	  tree <- solve.getTree
	  case tree of Just t -> let p = emptyOrLast treeposs
	                             t' = trees!!curr
	                             u = getSubterm t' p
		                 unifyAct t u t t' [] p
	               _ -> labBlue $ startOther other

	unifySubtrees = action
	  if length treeposs /= 2 || any null treeposs
	     then labMag "Select two proper subtrees!"
	  else let t = trees!!curr
		   ps@[p,q] = treeposs
		   u = getSubterm1 t p
		   u' = getSubterm1 t q
		   r = init p
		   v = getSubterm1 t r
		   b = polarity True t r
	       if r == init q then
                  sig <- getSignature
	          if isConjunct v && b then
		     let xs = if null r then []
		     			else anys $ getSubterm1 t $ init r
		     case unifyS sig xs u u' of
		     Just f -> let us = map (>>>f) $ init $ subterms v
		                   t' = replace1 t r $ mkConjunct us
			       trees := updList trees curr t'
		               setProofTerm UnifySubtrees
			       setProof True False "FACTOR UNIFICATION" ps
			                $ unified "factor"
			       clearTreeposs; drawCurr
		     _ -> labRed noUnifier
	          else if isDisjunct v && not b then
		          let xs = if null r then []
		                             else alls $ getSubterm1 t $ init r
	                  case unifyS sig xs u u' of
		  	  Just f -> let us = map (>>>f) $ init $ subterms v
		                        t' = replace1 t r $ mkDisjunct us
				    trees := updList trees curr t'
		                    setProofTerm UnifySubtrees
				    setProof True False "SUMMAND UNIFICATION" ps
				             $ unified "summand"
				    clearTreeposs; drawCurr
		          _ -> labRed noUnifier
		       else labRed $ noApp "Subtree unification"
	       else labMag "Select subtrees with the same predecessor!"

      in struct ..Solver
          	       
-- ENUMERATOR messages

 badConstraint = "The constraint is not well-formed."

 howMany 1 object ""     = "There is one " ++ object ++ "."
 howMany 1 object constr = "There is one " ++ object ++ " satisfying " ++ constr
 			   ++ "."
 howMany n object ""     = "There are " ++ show n ++ " " ++ object ++ "s."
 howMany n object constr = "There are " ++ show n ++ " " ++ object ++
   		           "s satisfying " ++ constr ++ "."

 none object "" = "There is no " ++ object ++ "."
 none object c  = "There is no " ++ object ++ " satisfying " ++ c ++ "."

 startEnum object = "Enter " ++ str ++ " into the text field" ++ 
                    (case object of "palindrome" -> "!"; _ -> more)
       where str = case object of
                   "palindrome" -> "a sequence of strings"
		   "alignment" -> "two sequences of strings separated by blanks"
                   "dissection"
	             -> "the breadth > 0 and the height > 0 of a rectangle"
                   _ -> "the length of a list"
	     more = "\nand a constraint into the entry field (see the manual)!"
	     
-- the ENUMERATOR template

 struct Enumerator = buildEnum :: String -> (String -> String -> Bool) -> Action

 enumerator :: TkEnv -> Solver -> Template Enumerator

 enumerator tk solve =

   template object := ""; compl := const2 False

   in let

        buildEnum obj f = action
	  object := obj
	  compl := f
	  solve.labBlue $ startEnum obj
  	  solve.setForw [Text "go", Command $ getInput obj, redback]
	  solve.setQuit [Text $ "quit "++obj, Command finish]

	finish = action
	  solve.labBlue start
	  solve.setForw [Text "--->", Command solve.forwProof, greenback]
	  solve.setQuit [Text "quit", Command tk.quit]

	getInput "alignment" = action
	  str <- solve.getText; constr <- solve.getEntry
	  let global = notnull constr && head constr == 'g'
	      (xs,ys) = break (== '\n') str
	  if null ys then
	     solve.labRed "Enter TWO sequences of strings into the entry field!"
	  else showResult constr $ map (alignToTerm . compress) 
	                         $ mkAlign global (words xs) (words ys) compl
	getInput "palindrome" = action 
          str <- solve.getText; showResult "" $ map (alignToTerm . compress) 
	  				      $ mkPali (words str) compl
	getInput "dissection" = action
	  str <- solve.getText
	  case parse size str of
	  Just (b,h)
	    -> constr <- solve.getEntry
	       case parse (disjunct sig) constr of
	       Just t -> case dissConstr b h t of
		         Just (c,ns,c') 
			   -> showResult (showEnum t) $ mkDissects c c' ns b h
	                 _ -> solve.labRed badConstraint
	       _ -> solve.labRed badConstraint
	  _ -> solve.labBlue "Enter two numbers > 0 into the text field!"
	  where size = do b <- token pnat; h <- token pnat; return (b,h)
	getInput _ = action
	  str <- solve.getText
          case parse (token pnat) str of
	  Just n | n > 1
	    -> constr <- solve.getEntry
	       case parse (disjunct sig) constr of
	       Just t -> case partConstr t of
		         Just c -> showResult (showEnum t) $ mkPartitions c n t
	                 _ -> solve.labRed badConstraint
	       _ -> solve.labRed badConstraint
	  _ -> solve.labBlue "Enter a number > 1 into the text field!"

	showResult constr terms = action
	  if null terms then solve.labGreen $ none object constr
	                else let n = length terms
	                         typ = if n == 1 then "tree" else "term"
			     solve.setNewTrees terms typ
	            	     solve.labGreen $ howMany n object constr

      in struct ..Enumerator
      
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

