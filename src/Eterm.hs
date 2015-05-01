{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Eterm where
 import Data.Char (isLower, isUpper, isDigit, ord)
 import Data.List (zipWith4)
 import Data.Array
 import Control.Monad hiding (join)
 import Control.Monad.Trans.Maybe (MaybeT(..))
 import Control.Monad.State (StateT(..))
 import Gui
 
--------------------------------- Copyright (c) peter.padawitz@udo.edu, May 2014

-- Eterm contains:

-- basic functions on lists and other types
-- a parser of symbols and numbers
-- a parser of terms and formulas
-- a compiler of Kripke models
-- the tree type (Term a)
-- an unparser of terms and formulas
-- functions for flowtree analysis (used by the simplifier)
-- operations on formulas
-- operations on trees, tree positions and term graphs
-- substitution, unification and matching functions
-- a compiler of trees into trees with coordinates
-- functions that enumerate terms (used by the enumerator template)

 infixl 0 `onlyif`
 infixl 6 `minus`, `minus1`
 infixl 7 <<=
 infixl 8 >>>

 infixr 2 |||, `join`, `join1`
 infixr 3 &&&, `meet`
 infixr 4 ***, -+-
{- TODO port
 testT :: TkEnv -> Int -> MaybeT Cmd ()
 testT tk n = case f n of Just n -> lift $ tk.writeFile "testout" $ show n
 	         	  _ -> mzero
 	      where f n = do guard $ n > 0; Just n
-}
 get (Just x) = x
 get _        = error "get"

 just (Just _) = True
 just _        = False

 nothing = not . just
  				  
 concatJust :: [Maybe [a]] -> Maybe [a]
 concatJust s = do guard $ notnull s'; Just $ concat s'
	        where s' = [x | Just x <- s]
  				  
 concatJustT :: Monad m => [MaybeT m [a]] -> MaybeT m [a]
 concatJustT s = do s <- f s; if null s then mzero else return s
 		 where f (x:s) = MaybeT { runMaybeT = do
                                        a <- runMaybeT x
                                        as <- runMaybeT (f s)
                                        return $ if just a then a++as
 		 		    	                             else as
                                }
 		       f _     = return []

 str `onlyif` b = if b then str else ""
 str `ifnot` b  = if b then ""  else str
 
 (***) :: (a -> b) -> (a -> c) -> a -> (b,c)
 (f *** g) x = (f x,g x)

 (&&&),(|||) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
 (f &&& g) x = f x && g x
 (f ||| g) x = f x || g x

 seed = 17489   

 nextRand n = if tmp<0 then m+tmp else tmp
              where tmp = a*(n `mod` q) - r*(n `div` q)
		    a = 16807        -- = 7^5
                    m = 2147483647   -- = maxBound = 2^31-1
                    q = 127773       -- = m `div` a
                    r = 2836         -- = m `mod` a
		    			     
 type BoolFun a = a -> a -> Bool
		    
 pr1 (a,_,_) = a
 pr2 (_,b,_) = b
 pr3 (_,_,c) = c
 
 const2 = const . const
 
 const3 = const . const2

 upd :: Eq a => (a -> b) -> a -> b -> a -> b
 upd f a b x = if x == a then b else f x

 upd2 :: (Eq a,Eq b) => (a -> b -> c) -> a -> b -> c -> a -> b -> c
 upd2 f a b = upd f a . upd (f a) b
 
 incr,decr :: Eq a => (a -> Int) -> a -> a -> Int
 incr f x y = if x == y then f x+1 else f y
 decr f x y = if x == y then f x-1 else f y

 neg2 (x,y) = (-x,-y)
 
 div2 (x,y) = (x/2,y/2)

 add1 :: Num a => (a,a) -> a -> (a,a)
 add1 (x,y) a = (a+x,y)
 
 add2,sub2 :: Num a => (a,a) -> (a,a) -> (a,a)
 add2 (x,y) (a,b) = (a+x,b+y)
 sub2 (x,y) (a,b) = (a-x,b-y)
 
 apply2 f (x,y) = (f x,f y)

 fromInt = fromIntegral -- TODO port quick fix
 fromInt2 (x,y) = (fromInt x,fromInt y)

 fromDouble = id -- TODO port quick fix
 fromDouble2 (x,y) = (fromDouble x,fromDouble y)

 round2 :: (RealFrac b, Integral d, RealFrac a, Integral c) => (a,b) -> (c,d)
 round2 (x,y) = (round x,round y)
  
 square = round . sqrt . fromInt . length

 minmax4 p (0,0,0,0) = p
 minmax4 (0,0,0,0) p = p
 minmax4 (x1,y1,x2,y2) (x1',y1',x2',y2') = (min x1 x1',min y1 y1',
 					    max x2 x2',max y2 y2')

 mkArray :: Ix a => (a,a) -> (a -> b) -> Array a b
 mkArray bounds f = array bounds [(i,f i) | i <- range bounds]

-- COLORING
 isBW,deleted :: Color -> Bool
 isBW c     = c == black || c == white
 deleted c  = c == RGB 1 2 3
 
 fillColor c i bgc = Fill $ if c == black || deleted c then bgc else mkLight i c

 outColor c i bgc = if deleted c then bgc else mkLight i c

-- nextCol computes the successor of each color c c on a chromatic circle of 
-- 6*255 = 1530 equidistant pure (or hue) colors. A color c is pure if c is 
-- neither black nor white and at most one of the R-, G- and B-values of c is 
-- different from 0 and 255.

 nextCol,getHue,complColor :: Color -> Color
 
 nextCol (RGB 255 0 n) | n < 255 = RGB 255 0 (n+1)        -- n = 0   --> red
 nextCol (RGB n 0 255) | n > 0   = RGB (n-1) 0 255        -- n = 255 --> magenta
 nextCol (RGB 0 n 255) | n < 255 = RGB 0 (n+1) 255        -- n = 0   --> blue 
 nextCol (RGB 0 255 n) | n > 0   = RGB 0 255 (n-1)        -- n = 255 --> cyan 
 nextCol (RGB n 255 0) | n < 255 = RGB (n+1) 255 0        -- n = 0   --> green
 nextCol (RGB 255 n 0) | n > 0   = RGB 255 (n-1) 0        -- n = 255 --> yellow
 nextCol c | isBW c || deleted c = c 
           | True                = nextCol $ getHue c

 getHue (RGB r g b) = RGB (f 0) (f 1) (f 2) where s = [r,g,b]
		                                  low:mid:_ = qsort rel [0,1,2] 
						  rel i j = s!!i <= s!!j
						  f i | i == low = 0 
						      | i == mid = s!!i
						      | True     = 255
						      
 isHue (RGB r g b) = all (`elem` [0..255]) [r,g,b] &&
 		     [[0,255],[255,0]] `shares` [[r,g],[g,b],[b,r]]

 complColor c = iterate nextCol c!!765
  
-- hue mode col n i computes the i-th successor of c in a chromatic circle of 
-- n <= 1530 equidistant pure colors.

 hue :: Int -> Color -> Int -> Int -> Color
 hue 1 col n i = iterate nextCol col!!round (fromInt i*1530/fromInt n) 
 hue 2 col n 0 = col
 hue 2 col n i = if odd i then complColor $ hue 2 col n $ i-1
                          else nextColor 1 (n `div` 2) $ hue 2 col n $ i-2
 hue 3 col n i = if odd i then complColor d else d where d = hue 1 col n i
 hue _ col _ _ = col
		
 nextColor :: Int -> Int -> Color -> Color
 nextColor mode n col  = hue mode col n 1

-- nextLight n i c adds i/n units of white (if i is positive) resp. black (if i
-- is negative) pigment to c. If i=n resp. i=-n, then c turns white resp. black.

 nextLight :: Int -> Int -> Color -> Color
 nextLight n i (RGB x y z) = RGB (f x) (f y) (f z)
	     where f x | i > 0 = x+i*(255-x)`div`n -- i=n  --> f x = 255 (white)
		       | True  = x+i*x`div`n       -- i=-n --> f x = 0   (black)

 mkLight = nextLight 42
 light   = nextLight 3 2
 dark    = nextLight 3 $ -1

 blueback  = Background $ light blue
 greenback = Background $ light green
 magback   = Background $ light magenta
 redback   = Background $ light red

-- STRING FUNCTIONS					    

 removeCommentL ('-':'-':_) = []
 removeCommentL (x:str)     = x:removeCommentL str
 removeCommentL _           = []

 removeComment 0 ('-':'-':str) = removeComment 1 str
 removeComment 0 ('{':'-':str) = removeComment 2 str
 removeComment 0 (x:str)       = x:removeComment 0 str
 removeComment 1 ('\n':str)    = '\n':removeComment 0 str
 removeComment 1 (_:str)       = removeComment 1 str
 removeComment 2 ('-':'}':str) = removeComment 0 str
 removeComment 2 (_:str)       = removeComment 2 str
 removeComment _ _             = []

 removeDot ('\n':'\n':'.':str) = removeDot str
 removeDot ('\n':'.':str)      = removeDot str
 removeDot (x:str)             = x:removeDot str
 removeDot _                   = []

 drop3 (' ':x:'>':str) | isDigit x              = str
 drop3 (x:y:'>':str)   | isDigit x && isDigit y = str
 drop3 (' ':' ':' ':str)         	        = str
 drop3 str         	                        = str
 
 showStr x = show x `minus1` '\"'
 
 showStrList xs = show xs `minus` "[]\""

-- splitSpec is used by addSpec (see Ecom).

 splitSpec = searchSig []
  where searchSig sig []   = (sig,[],[],[],[])
        searchSig sig rest =
	   if take 7 rest == "axioms:" 
	   then searchAxioms sig [] $ drop 7 rest
	   else if take 9 rest == "theorems:" 
		then searchTheorems sig [] [] $ drop 9 rest
		else if take 9 rest == "conjects:" 
	             then searchConjects sig [] [] [] $ drop 9 rest
		     else if take 6 rest == "terms:" 
	                  then (sig,[],[],[],drop 6 rest)
		          else searchSig (sig++[head rest]) $ tail rest
        searchAxioms sig axs []   = (sig,axs,[],[],[])
        searchAxioms sig axs rest =
	   if take 9 rest == "theorems:" 
	   then searchTheorems sig axs [] $ drop 9 rest
	   else if take 9 rest == "conjects:" 
	        then searchConjects sig axs [] [] $ drop 9 rest
		else if take 6 rest == "terms:" then (sig,axs,[],[],drop 6 rest)
		     else searchAxioms sig (axs++[head rest]) $ tail rest
        searchTheorems sig axs ths []   = (sig,axs,ths,[],[])
        searchTheorems sig axs ths rest =
	   if take 9 rest == "conjects:" 
	   then searchConjects sig axs ths [] $ drop 9 rest
	   else if take 6 rest == "terms:" then (sig,axs,ths,[],drop 6 rest)
	        else searchTheorems sig axs (ths++[head rest]) $ tail rest
        searchConjects sig axs ths conjs []   = (sig,axs,ths,conjs,[])
        searchConjects sig axs ths conjs rest =
	   if take 6 rest == "terms:" then (sig,axs,ths,conjs,drop 6 rest) 
	   else searchConjects sig axs ths (conjs++[head rest]) $ tail rest

-- LIST AND SET FUNCTIONS
                
 notnull = not . null
 
 nil2 = ([],[])
 
 single x = [x]
 
 (-+-) :: Eq a => [a] -> [a] -> [a]
 s1@(_:_) -+- s2@(a:s) = if last s1 == a then init s1 -+- s else s1++s2
 s1 -+- s2             = s1++s2
  
 split :: (a -> Bool) -> [a] -> ([a],[a])
 split f (x:s) = if f x then (x:s1,s2) else (s1,x:s2) where (s1,s2) = split f s
 split _ _     = nil2

 split2 :: (a -> Bool) -> (a -> Bool) -> [a] -> Maybe ([a],[a])
 split2 f g (x:s) = do (s1,s2) <- split2 f g s
 		       if f x then Just (x:s1,s2) 
		       	      else do guard $ g x; Just (s1,x:s2) 
 split2 _ _ _     = Just nil2

 prod2 as bs = [(a,b) | a <- as, b <- bs]

 domain f s s' = [x | x <- s, f x `elem` s']

 context i s = take i s++drop (i+1) s
 
 contextM is s = [s!!i | i <- indices_ s, i `notElem` is]

 updMax f x = upd f x . maximum
 
 updL :: (Eq a,Eq b) => (a -> [b]) -> a -> b -> a -> [b]
 updL f a = upd f a . join1 (f a)

 updList s i x = take i s++x:drop (i+1) s
 
 updListM s i xs = take i s++xs++drop (i+1) s

-- upd2L is used by regToAuto and graphToRel2 (see below).

 upd2L :: (Eq a,Eq b,Eq c) => (a -> b -> [c]) -> a -> b -> c -> a -> b -> [c]
 upd2L f a b = upd f a . upd (f a) b . join1 (f a b)
 
 updAssoc :: (Eq a,Eq b) => [(a,[b])] -> a -> [b] -> [(a,[b])]
 updAssoc s a bs = case searchGet ((== a) . fst) s of 
                        Just (i,(_,cs)) -> updList s i (a,bs`join`cs)
 			_ -> (a,bs):s
 					      
 inverse :: Eq a => (a -> a) -> [a] -> a -> a
 inverse f s = h s id where h (x:s) g = h s (upd g (f x) x)
	                    h _ g     = g
 
-- getMax as pairs returns all maximal subsets bs of as such that for all
-- (a,b) in pairs, either a or b is in bs

 getMax :: Eq a => [a] -> [(a,a)] -> [[a]]
 getMax as = maxima length . foldl f [as]
             where f ass (a,b) = concat [[minus1 as b,minus1 as a] | as <- ass]

 lookupL :: (Eq a,Eq b) => a -> b -> [(a,b,c)] -> Maybe c
 lookupL a b ((x,y,z):s) = if a == x && b == y then Just z else lookupL a b s
 lookupL _ _ _           = Nothing

 lookupLM :: Eq a => a -> [(a,b,c)] -> [c]
 lookupLM a ((x,_,z):s) = if a == x then z:lookupLM a s else lookupLM a s
 lookupLM _ _           = []
 
 invertRel :: (Eq a,Eq b) => [(a,[b])] -> [b] -> [(b,[a])]	-- not used
 invertRel s = map f where f b = (b,[a | (a,bs) <- s, b `elem` bs])
 
 invertRelL :: (Eq a,Eq b,Eq c) => [(a,b,[c])] -> [c] -> [b] -> [(c,b,[a])]
 invertRelL s cs = map f . prod2 cs				-- not used
 	      where f (c,b) = (c,b,[a | (a,b',cs) <- s, b == b' && c `elem` cs])
  
-- invertRelI/LI is used by actTable, simplifyS (see Esolve), buildKripke, 
-- showEqsOrGraph, showMatrix and showRelation (see Ecom).

-- i in invertRelI as bs iss!!k iff k in iss!!i.

 invertRelI :: [a] -> [b] -> [[Int]] -> [[Int]]
 invertRelI as bs iss = if null as then [] else map f [0..length bs-1] 
 		        where f i = searchAll (i `elem`) iss
	       
-- k in (invertRelII b as bs cs isss!!i)!!j iff i in (isss!!k)!!j. 

 invertRelII :: Bool -> [a] -> [b] -> [c] -> [[[Int]]] -> [[[Int]]]
 invertRelII b as bs cs isss = if b || null as || null bs then [] 
 			       else map f [0..length cs-1]
                               where f i = map g [0..length as-1]
			                   where g j = searchAll h isss
				                   where h iss = i `elem` iss!!j

 sublist (x:s) i j | i >= j = []
 sublist (x:s) 0 j          = x:sublist s 0 (j-1)
 sublist (x:s) i j          = sublist s (i-1) (j-1)
 sublist _ _ _              = []
 
 sublists s = [sublist s i j | let n = length s-1, i <- [0..n], j <- [i+1..n]]

 isSublist s@(x:xs) (y:ys) = x == y && (isSublist xs ||| isSublist s) ys
 isSublist s _ 		   = null s

-- subsets n returns all notnull proper subsets of [0..n-1].
					    
 subsets n = concatMap (subsetsN n) [1..n-1]

-- subsetsB n k returns all subsets of [0..n-1] with at most k elements.

 subsetsB n k = concatMap (subsetsN n) [0..k]

-- subsetsN n k returns all subsets of [0..n-1] with exactly k elements.

 subsetsN _ 0 = [[]]
 subsetsN n k = mkSet [insert (<) x xs | xs <- subsetsN n (k-1), 
 				         x <- [0..n-1]`minus`xs]

 emptyOrAll ss = if null ss then [[]] else ss

 emptyOrLast ss = if null ss then [] else last ss

 indices_ :: [a] -> [Int]
 indices_ s = [0..length s-1]
 
 restInd ts ps = map (ts!!) $ indices_ ts `minus` map last ps

 xs `subset` ys = all (`elem` ys) xs

 supset s = all (`elem` s)

 shares s = any (`elem` s)

 imgsSubset,imgsShares :: Eq a => [a] -> (a -> [a]) -> [a] -> [a]
 imgsSubset xs f ys = filter (supset ys . f) xs
 imgsShares xs f ys = filter (shares ys . f) xs

 xs `eqset` ys = xs `subset` ys && ys `subset` xs
 
 disjoint xs = all (`notElem` xs)

 xs `meet` ys = [x | x <- xs, x `elem` ys]

-- related f xs ys = any (g ys) xs where g ys x = any (f x) ys 

 xs `minus1` y = [x | x <- xs, x /= y]

 xs `minus` ys = [x | x <- xs, x `notElem` ys]

 deAssoc0 = concatMap f where f (x,ys) = map (\y -> (x,y)) ys

 deAssoc1 = concatMap f where f (xs,y) = map (\x -> (x,y)) xs

 deAssoc2 = concatMap f where f (xs,ys) = concatMap g xs
                                          where g x = map (\y -> (x,y)) ys

 deAssoc3 = concatMap f where f (xs,ys,z) = concatMap g xs
                                            where g x = map (\y -> (x,y,z)) ys

 join1 :: Eq a => [a] -> a -> [a]
 join1 s@(x:s') y = if x == y then s else x:join1 s' y
 join1 _ x        = [x]

 join :: Eq a => [a] -> [a] -> [a]
 join = foldl join1

 mkSet :: Eq a => [a] -> [a]
 mkSet = join []

 distinct (x:xs) = x `notElem` xs && distinct xs
 distinct _      = True

 joinB1 :: Eq a => [[a]] -> [a] -> [[a]]
 joinB1 ss@(s:ss') s' = if eqBag (==) s s' then ss else s:joinB1 ss' s'
 joinB1 _ s	      = [s]
 
 joinB :: Eq a => [[a]] -> [[a]] -> [[a]]
 joinB = foldl joinB1

 mkBags :: Eq a => [[a]] -> [[a]]
 mkBags = joinB []

 joinM,meetM :: Eq a => [[a]] -> [a]
 joinM = foldl join []
 meetM xss = [x | x <- joinM xss, all (elem x) xss]

 joinBM :: Eq a => [[[a]]] -> [[a]]
 joinBM = foldl joinB []

 joinMap,meetMap :: Eq b => (a -> [b]) -> [a] -> [b]
 joinMap f = joinM . map f
 meetMap f = meetM . map f

 joinBMap f = joinBM . map f

 splitAndMap2 f (x:s) = if b then (x:s1,s2) else (s1,y:s2)
			where (s1,s2) = splitAndMap2 f s; (b,y) = f x
 splitAndMap2 f _     = nil2

 join6 (s1,s2,s3,s4,s5,s6) (t1,t2,t3,t4,t5,t6) =
       (join s1 t1,join s2 t2,join s3 t3,join s4 t4,join s5 t5,join s6 t6)
 
 minus6 (s1,s2,s3,s4,s5,s6) (t1,t2,t3,t4,t5,t6) =
       (minus s1 t1,minus s2 t2,minus s3 t3,minus s4 t4,minus s5 t5,minus s6 t6)
  
-- mkAcyclic/L ps qs removes all pairs resp. triples p from qs such that close a
-- cycle wrt ps++qs.

 mkAcyclic :: Eq a => [(a,[a])] -> [(a,[a])] -> [(a,[a])]
 mkAcyclic ps qs = case f [] qs of Just qs -> mkAcyclic ps qs; _ -> ps++qs
             where f qs rs = do p@(x,xs):rs <- Just rs 
	                        let y = g x xs
	                        if just y then Just $ qs++(x,xs`minus1`get y):rs
  				          else f (p:qs) rs
		   g x xs = do y:xs <- Just xs
			       if back x [] y then Just y else g x xs
		   back x xs y = x == y || y `notElem` xs && just zs && 
		   			   any (back x $ y:xs) (get zs)
					   where zs = lookup y $ ps++qs

 mkAcyclicL :: Eq a => [(a,b,[a])] -> [(a,b,[a])] -> [(a,b,[a])]
 mkAcyclicL ps qs = case f [] qs of Just qs -> mkAcyclicL ps qs; _ -> ps++qs
           where f qs rs = do p@(x,b,xs):rs <- Just rs
	                      let y = g x xs
	   		      if just y then Just $ qs++(x,b,xs`minus1`get y):rs
  				        else f (p:qs) rs
	         g x xs = do y:xs <- Just xs
			     if back x [] y then Just y else g x xs
		 back x xs y = x == y || y `notElem` xs && 
			       		 any (back x $ y:xs) zs
					 where zs = concat $ lookupLM y $ ps++qs

-- extensional equality

 eqFun eq f g s = length fs == length gs && and (zipWith eq fs gs)
	          where fs = map f s
			gs = map g s

-- generic set comparison

 subSet le s s' = all (member s') s where member s x = any (le x) s

 eqSet eq s s' = subSet eq s s' && subSet eq s' s
		
 subGraph t u = subSet le (graphToRel t) (graphToRel u) -- && size t <= size u
 	        where le (a,as) (b,bs) = a == b && as `subset` bs
		
 eqGraph t = eqSet eq (graphToRel t) . graphToRel
 	     where eq (a,as) (b,bs) = a == b && as `eqset` bs

-- generic bag equality

 eqBag eq s s' = map f s == map g s && map f s' == map g s' where f = card eq s
		       						  g = card eq s'

 card eq (x:s) y = if eq x y then card eq s y+1 else card eq s y
 card _ _ _      = 0

 allEqual (x:s) = all (\y -> x == y) s
 allEqual _     = True

 anyDiff (x:s) = any (\y -> x /= y) s
 anyDiff _     = False

 forallThereis rel xs ys = all (\x -> any (rel x) ys) xs

 forsomeThereis rel xs ys = any (\x -> any (rel x) ys) xs

 thereisForall rel xs ys = any (\x -> all (rel x) ys) xs

 foldC :: (a -> b -> a) -> BoolFun a -> a -> [b] -> a
 foldC f g a (b:bs) = if g a a' then a else foldC f g a' bs where a' = f a b
 foldC _ _ a _      = a

 fold2 f a (x:xs) (y:ys) = fold2 f (f a x y) xs ys
 fold2 _ a _ _           = a

 fold3 f a (x:xs) b (y:ys) = fold3 f a xs (f a x b y) ys
 fold3 _ _ _ b _           = b
 
 zipL ((a,b):ps) (c:cs) = (a,b,c):zipL ps cs
 zipL _ _		= []

 zipWith2 f (x:xs) (y:ys) (z:zs) = f x y z++zipWith2 f xs ys zs
 zipWith2 _ _ _ _                = []

 zipWithL f (x:xs) (ys:yss) = map (f x) ys++zipWithL f xs yss
 zipWithL _ _ _             = []
 
 pascal :: Int -> [Int]
 pascal 0 = [1]
 pascal n = zipWith (+) (s++[0]) (0:s) where s = pascal $ n-1

 cantor :: Int -> Pos -> Pos
 cantor n (x,y) = if even x then if even y
			         then if x > 0 
			              then if y' < n then (x-1,y') else (x',y)
			              else if y' < n then (0,y') else (1,y) 
			         else if x' < n then (x',y-1) else (x,y') 
			    else if even y
			         then if y > 0 
			              then if x' < n then (x',y-1) else (x,y') 
				      else if x' < n then (x',0) else (x,1)
			         else if y' < n then (x-1,y') else (x',y) 
		  where x' = x+1; y' = y+1

 cantorshelf :: Int -> [a] -> [a]
 cantorshelf n s = foldl f s $ indices_ s
                   where f s' i = updList s' (x*n+y) $ s!!i 
		                  where (x,y) = iterate (cantor n) (0,0)!!i

 snake :: Int -> [a] -> [a]
 snake n s = [s!!(x i*n+z i) | i <- indices_ s]
             where z i = if even xi then yi
	   	         else if xi == length s`div`n 
		      	      then length s`mod`n-1-yi else n-1-yi
		         where xi = x i; yi = y i
		   x i = i`div`n
		   y i = i`mod`n
 
 transpose :: Int -> [a] -> [a]
 transpose n s = [s!!(x i*n+y i) | i <- indices_ s] where x i = i`mod`n
 							  y i = i`div`n
 
 mirror :: Int -> [a] -> [a]
 mirror n s = [s!!(x i*n+y i) | i <- indices_ s] where x i = n-1-i`div`n
 						       y i = i`mod`n

 splitAndShuffle :: Int -> [a] -> [a]
 splitAndShuffle n = shuffle . f 
 	        where f s = if length s <= n then [s] else take n s:f (drop n s)

-- shuffle ss zips the lists of ss before concatenating them.

 shuffle :: [[a]] -> [a]
 shuffle = concat . foldl f [[]] where f (s:ss) (x:s') = (s++[x]):f ss s'
				       f _ (x:s)       = [x]:f [] s
				       f ss _          = ss

 revRows n s = if length s <= n then s else revRows n (drop n s)++take n s

 pal (x:xs@(_:_)) = pal (init xs) && x == last xs
 pal _            = True

 evens (x:xs) = x:odds xs
 evens _      = []

 odds (_:xs) = evens xs
 odds _      = []

-- search f s searches for the first element of s satisfying f and returns its
-- position within s.

 search :: (a -> Bool) -> [a] -> Maybe Int
 search f = g 0 where g i (a:s) = if f a then Just i else g (i+1) s
                      g _ _     = Nothing
		      
 getInd :: Eq a => a -> [a] -> Int
 getInd a = get . search (== a)
		      
 getIndices :: [TermS] -> [TermS] -> [Int]
 getIndices ts us = [getInd t us | t <- ts]

 searchGet :: (a -> Bool) -> [a] -> Maybe (Int,a)
 searchGet f = g 0 where g i (a:s) = if f a then Just (i,a) else g (i+1) s
                         g _ _     = Nothing

 searchGetR :: (a -> Bool) -> [a] -> Maybe (Int,a)
 searchGetR f s = g $ length s-1
               where g (-1) = Nothing
		     g i    = if f a then Just (i,a) else g $ i-1 where a = s!!i
                        

-- searchGet2 f g s searches for the first element x of s satisfying f and then,
-- in the rest of s, for the first element y with g x y.

 searchGet2 :: (a -> Bool) -> (a -> a -> Bool) -> [a] -> Maybe (Int,a,a)
 searchGet2 f g = h [] 0
 		  where h s i (x:s') | f x  = case searchGet (g x) $ s++s' of
			    	                   Just (_,y) -> Just (i,x,y)
				                   _ -> h (x:s) (i+1) s'
				     | True = h (x:s) (i+1) s'
			h _ _ _ = Nothing

 searchArray f ar = g 0 where g i = if f (ar!i) then Just i else g (i+1)
                              g _ = Nothing

-- searchAll f s searches all elements of s satisfying f and returns their
-- positions within s.

 searchAll :: (a -> Bool) -> [a] -> [Int]
 searchAll f s = snd $ foldr g (length s-1,[]) s
	         where g a (i,is) = (i-1,if f a then i:is else is)

 searchGetM :: (a -> Maybe b) -> [a] -> Maybe b
 searchGetM f = g 0 where g i (a:s) = if just b then b else g (i+1) s
 				      where b = f a
                          g _ _     = Nothing

 search2 f g s = h s 0 where h (x:s) i = if f x then Just (i,True) 
					        else if g x then Just (i,False) 
					                    else h s $ i+1
                             h _ _     = Nothing

 search4 f1 f2 f3 f4 s = g s 0 where g (x:s) i = if f1 x then Just (i,1) 
				                 else if f2 x then Just (i,2) 
						 else if f3 x then Just (i,3)
						 else if f4 x then Just (i,4)
						 else g s $ i+1
                                     g _ _     = Nothing

-- searchback f s searches for the first element of reverse s satisfying f and
-- returns its position within s.

 searchback f s = g s $ length s-1
             where g s@(_:_) i = if f $ last s then Just i else g (init s) $ i-1
                   g _ _       = Nothing

-- shift n ns removes n from ns and decreases the elements i > n of ns by 1.

 shift n ns = [i | i <- ns, i < n] ++ [i-1 | i <- ns, i > n]

 splitString :: Int -> Int -> String -> String
 splitString k n str = if null rest then prefix 
 		       else prefix++newBlanks k (splitString k n rest)
		       where (prefix,rest) = splitAt n str

 splitStrings :: Int -> Int -> String -> [String] -> String
 splitStrings k n init strs = 
    if null rest then prefix else prefix++newBlanks k (splitStrings k n "" rest)
    where (prefix,rest) = f (init,strs) strs
	  f sr@(str,rest) (str1:strs) = if length str2 > n then sr
				    	else f (str2,tail rest) strs
				        where str2 = str++str1++" "
	  f sr _ = sr

-- mkRanges ns n builds the syntactically smallest partition p of n:ns such that
-- all ms in p consist of successive integers.

 mkRanges ns n = f ns [] (n,n)
    where f (k:ns) part sect@(m,n) = if k == n' then f ns part (m,n')
                                                else f ns (part++[sect]) (k,k)
                                     where n' = n+1
          f _ part sect            = g (part++[sect])
          g ((m,n):sects) | m == n = show m++rest
                          | True   = show m++".."++show n++rest
	                             where rest = if null sects then []
                                                                else ',':g sects
          g _ = ""

-- mkLists s ns computes the partition of s whose i-th element has ns!!i
-- elements.

 mkLists s = f s [] where f s s' (0:ns)     = s':f s [] ns
 		          f (x:s) s' (n:ns) = f s (s'++[x]) ((n-1):ns)
		          f _ _ _           = []

-- SETS and RELATIONS translated into FUNCTIONS

 setToFun :: Eq a => [a] -> a -> Bool
 setToFun = foldl g (const False) where g f x = upd f x True

 relToFun :: Eq a => [(a,[b])] -> a -> [b]
 relToFun s a = case lookup a s of Just bs -> bs; _ -> []

 relToFunI :: Eq a => [a] -> [b] -> [[Int]] -> a -> [b]
 relToFunI as bs s a = map (bs!!) (s!!getInd a as)

 relLToFun :: (Eq a,Eq b) => [(a,b,[c])] -> a -> b -> [c]
 relLToFun s a b = case lookupL a b s of Just cs -> cs; _ -> []

 relLToFunI :: (Eq a,Eq b) => [a] -> [b] -> [c] -> [[[Int]]] -> a -> b -> [c]
 relLToFunI as bs cs s a b = map (cs!!) (s!!getInd a as!!getInd b bs)

-- minimal DNFs represented as subsets of {'0','1','#'}^n for some n > 0

 minDNF bins = f bins' $ length bins'
               where bins' = maxis leqBin bins
		     f bins n = if n' < n then f bins' n' else bins'
	                        where bins' = maxis leqBin $ mkSups [] bins
	                              n' = length bins'

 leqBin bin bin' = and $ zipWith leq bin bin'
	           where leq x y = x == y || y == '#'

-- mkSups [] bins replaces elements of bins by suprema of subsets of bins.

 mkSups bins (bin:bins') = case search f $ indices_ bin of
	                        Just i -> mkSups (updList bin i '#':bins) bins'
		                _ -> mkSups (bin:bins) bins'
	                   where f i = b /= '#' &&
		                       ((cbin `elem`) ||| any (leqBin cbin) |||
			                forallThereis leqBin (minterms cbin))
				       (bins++bins')
	                               where b = bin!!i
		                             cbin = updList bin i $
					           if b == '0' then '1' else '0'
 mkSups bins _ = bins

 minterms bin = if '#' `elem` bin then concatMap minterms [f '0',f '1']
	                          else [bin]
		where (bin1,bin2) = span (/= '#') bin
	              f x = bin1++x:tail bin2

-- funToBins (f,n) translates a function f :: {'0','1','#'}^n -> Bool into a
-- minimal DNF representing f.

 funToBins (f,n) = minDNF $ filter f $ binRange n
                   where binRange 0 = [""]
 	 	         binRange n = map ('0':) s++map ('1':) s++map ('#':) s
                                      where s = binRange $ n-1

-- KARNAUGH diagrams

-- karnaugh n is the empty Karnaugh matrix that consists of all elements of
-- {'0','1'}^n.

 karnaugh 1          = (array ((1,1),(1,2)) [((1,1),"0"),((1,2),"1")],1,2)
 karnaugh n | even n = (mkArray ((1,1),(k,m)) f,k,m)
                       where (arr,mid,m) = karnaugh (n-1)
		             k = mid*2
		             f (i,j) | i <= mid = '0':arr!(i,j)
			             | True     = '1':arr!(2*mid-i+1,j)
 karnaugh n          = (mkArray ((1,1),(k,m)) f,k,m)
                       where (arr,k,mid) = karnaugh (n-1)
		             m = mid*2
		             f (i,j) | j <= mid = '0':arr!(i,j)
			             | True     = '1':arr!(i,2*mid-j+1)

-- binsToBinMat bins n translates a DNF into an equivalent Karnaugh matrix.

 binsToBinMat bins arr i j = if any (e `leqBin`) bins then ("red_"++e) else e
		             where e = arr!(i,j)

-- OBDDs

 isObdd	(F "0" [])  = True
 isObdd	(F "1" [])  = True
 isObdd	(F x [t,u]) = just (parse (charNat 'x') x) && isObdd t && isObdd u
 isObdd (V x)       = isPos x
 isObdd _           = False

-- removeVar repeatedly applies the rule X(t,t)=t to an OBDD t.

 removeVar (F x [t,u]) = if eqTerm t' u' then t' else F x [t',u']
	                 where t' = removeVar t; u' = removeVar u
 removeVar t           = t

-- binsToObdd translates a subset of {'0','1','#'}^n into an equivalent minimal
-- OBDD.

 binsToObdd bins = binsToObddP (length bin-1) (indices_ bin) bins
                   where bin = head bins

 binsToObddP _ _ []    = mkZero
 binsToObddP n ns bins = collapse True $ removeVar $ trans 0 $ setToFun bins
            where trans i f = F ('x':show (ns!!i)) $ if i < n then [g '0',g '1'] 
	    						      else [h "0",h "1"]
			      where g a = trans (i+1) $ f . (a:) ||| f . ('#':)
			            h a = if f a || f "#" then mkOne else mkZero

-- obddToFun translates an OBDD t into the pair (f,n) consisting of the
-- characteristic function f :: {'0','1','#'}^n -> Bool of an equivalent DNF and
-- the number n of Boolean variables of t.

 obddToFun t = (f t &&& g,dim)
     where f (F "0" [])        = const False
           f (F "1" [])        = const True
	   f (F ('x':i) [t,u]) = f t &&& h '0' ||| f u &&& h '1'
	 	      	         where h a bin = bin!!read i == a
	   f (V x) | isPos x   = f $ getSubterm t $ getPos x
	   f _		       = error "obddToFun"
           varInds (F ('x':i) [t,u]) = varInds t `join` varInds u `join1` read i
           varInds _                 = []
	   dim = if null is then 0 else maximum is+1; is = varInds t
	   g bin = all (== '#') $ map (bin!!) $ [0..dim-1] `minus` is

-- SORTING and PERMUTING

 sorted :: Ord s => [s] -> Bool
 sorted (x:s@(y:_)) = x <= y && sorted s
 sorted _ 	    = True
 
 qsort rel (x:s) = qsort rel s1++x:qsort rel s2 
                   where (s1,s2) = split (`rel` x) s
 qsort _ s       = s	 
 
-- sort removes duplicates if rel is irreflexive and total

 sort rel (x:s) = sort rel [z | z <- s, rel z x]++x:
		  sort rel [z | z <- s, rel x z]
 sort _ s       = s	 

-- sortR s s' sorts s such that x precedes y if f(x) < f(y) where f(x) is the
-- element of s' at the position of x in s.

 sortR s s' = sort rel s where rel x y = s'!!getInd x s < s'!!getInd y s
					          
 sortDoms :: [(String,String)] -> ([String],[String])
 sortDoms s = (sort rel l,sort rel r) 
	      where (l,r) = unzip s
                    rel x y = if m < n then prefix (n-m) x < y 
			               else x < prefix (m-n) y   
                              where (m,n) = (length x,length y)
			            prefix n x = replicate n ' '++x
				    
 sortDoms2 :: [(String,String,a)] -> ([String],[String])
 sortDoms2 = sortDoms . map (pr1 *** pr2)

-- insertion into ordered sets

 insert r x s@(y:ys) | x == y = s
                     | r x y  = x:s
                     | True   = y:insert r x ys
 insert _ x _ 		      = [x]

-- nextPerm s computes the successor of s with respect to the reverse
-- lexicographic ordering (see Paulson, ML for the Working Programmer, p. 95f.)

 nextPerm :: Ord a => [a] -> [a]
 nextPerm s@(x:xs) = if sorted s then reverse s else next [x] xs
    where next s@(x:_) (y:ys) = if x <= y then next (y:s) ys else swap s
             where swap [x]      = y:x:ys
		   swap (x:z:xs) = if z > y then x:swap (z:xs) else y:z:xs++x:ys
 nextPerm _ = []
 
 permute ts s = ([ts!!i | i <- s],nextPerm s)
 
 intperms ns = take (product [2..length ns]) $ iterate nextPerm ns
 
 perms s = map (map (s!!)) $ intperms $ indices_ s
	   
 subperms s = []:concatMap f (indices_ s:subsets (length s))
              where f = map (map (s!!)) . intperms

-- permDiff s1 s2 computes a sequence of two-cycles that leads from permutation
-- s1 to permutation s2. 

 permDiff :: Ord a => [a] -> [a] -> [(a,a)]
 permDiff s1 s2 = mkPerm s1 -+- reverse (mkPerm s2)

-- mkPerm s computes a sequence of two-cycles that leads from s to a sorted
-- permutation of s.

 mkPerm :: Ord a => [a] -> [(a,a)]
 mkPerm = snd . f
	  where f (x:s) = insert x s1 cs where (s1,cs) = f s
                f _     = nil2
	        insert x s@(y:s') cs = if x <= y then (x:s,cs) else (y:s1,ds)
				       where (s1,ds) = insert x s' (cs++[(y,x)])
                insert x _ cs        = ([x],cs)

-- minis leq s computes the minima of s with respect to a partial order leq.

 minis,maxis :: Eq a => BoolFun a -> [a] -> [a]
 minis le = foldr f [] where f x (y:s) | le x y = f x s
				       | le y x = f y s
				       | True   = y:f x s
			     f x _              = [x]
 maxis = minis . flip

-- maxima f s returns the subset of all x in s such that f(x) agrees with the 
-- maximum of f(s).

 maxima, minima :: Ord b => (a -> b) -> [a] -> [a]
 maxima f s = [x | x <- s, f x == maximum (map f s)]
 minima f s = [x | x <- s, f x == minimum (map f s)]

-- minmax ps computes minimal and maximal coordinates of the point list ps.

 minmax ps@((x,y):_) = foldl f (x,y,x,y) ps
             where f (x1,y1,x2,y2) (x,y) = (min x x1,min y y1,max x x2,max y y2)
 minmax _ = (0,0,0,0)

-- PARSER monad
 
 newtype Parser a = P { applyPaInner :: StateT (String -> Maybe (a,String)) }
    deriving (Monad, MonadPlus)
    
 applyPa :: Parser a -> String -> Maybe (a,String)
 applyPa p = runStateT . applyPaInner

 sat p f = do x <- p; guard $ f x; return x

-- parse parser str applies parser to str and returns Nothing if str has no 
-- successful parses.

 parse :: Parser a -> String -> Maybe a
 parse parser str = do (x,[]) <- applyPa parser str; Just x

-- parseE parser str returns an error message if str has no successful parses.

 data Parse a = Correct a | Partial a String | Wrong

 parseE :: Parser a -> String -> Parse a
 parseE parser str = case applyPa parser str of Just (x,[]) -> Correct x
				 	        Just (x,rest) -> Partial x rest
				 	        _ -> Wrong

-- PARSER of symbols and numbers

 item          = P $ \cs -> do c:cs <- Just cs; Just (c,cs)

 char x        = sat item (== x)
 
 string        = mapM char

 some p        = do x <- p; xs <- many p; return $ x:xs

 many p        = some p ++ return []

 space         = many $ sat item (`elem` " \t\n")

 token p       = do space; x <- p; space; return x

-- tstring n   = token $ sequence $ replicate n item

 symbol        = token . string

 oneOf         = concat . map symbol

 enclosed p    = (do symbol "("; r <- p; symbol ")"; return r) ++ token p

 bool 	       = (do symbol "True"; return True) ++
 	         (do symbol "False"; return False)
 
 letters       = ['a'..'z']++['A'..'Z']
 
 letter        = sat item (`elem` letters)

 digit         = do d <- sat item isDigit; return $ ord d-ord '0'
 
 hexdigit      = (do d <- sat item isAToF; return $ ord d-ord 'A'+10) ++ digit
	         where isAToF c = 'A' <= c && c <= 'F'
 
 nat           = do ds <- some digit; return $ foldl1 f ds where f n d = 10*n+d

 pnat          = sat nat (> 0)
 
 pnatSecs      = do n <- pnat; char 's'; return $ toInteger n
 
 charNat x     = do char x; nat
 
 strNat x      = do string x; nat
 
 strLetters x  = do string x; s <- many letter; return $ x++s

 int           = nat ++ do char '-'; n <- nat; return $ -n

 intRange      = do i <- int; string ".."; k <- int; return [i..k]

 intRangeOrInt = intRange ++ do i <- int; return [i]
			  
 intRanges     = do is <- token intRangeOrInt
                    (do ks <- intRanges; return $ is++ks) ++ return is

 double        = doublePos ++ do char '-'; r <- doublePos; return $ -r

 doublePos     = do n <- nat; char '.'; ds <- some digit
                    let m = foldl1 f ds
			r = fromInt n+fromInt m*0.1**fromInt (length ds)
	            i <- expo; return $ r*10**fromInt i
 	         where f n d = 10*n+d
		       expo = concat [do string "e+"; nat,
 	                              do string "e-"; n <- nat; return $ -n,
 	                              do string "e"; nat,
 	                              return 0]

 real          = (do r <- double; return (fromDouble r::Float)) ++
                 (do i <- int; return $ fromInt i)

 realNeg       = sat real (< 0)

 rgbcolor      = do symbol "RGB"; r <- token int; g <- token int; b <- token int
		    return $ RGB r g b
 
 hexcolor      = do char '#'
 		    [d1,d2,d3,d4,d5,d6] <- sequence $ replicate 6 hexdigit
 		    return $ RGB (16*d1+d2) (16*d3+d4) $ 16*d5+d6

 color         = concat [do symbol "dark"; c <- color; return $ dark c,
                         do symbol "light"; c <- color; return $ light c,
                         do symbol "black"; return black,
			 do symbol "grey"; return grey,
		 	 do symbol "white"; return white,
		 	 do symbol "red"; return red,
		 	 do symbol "magenta"; return magenta,
			 do symbol "blue"; return blue,
		 	 do symbol "cyan"; return cyan,
		 	 do symbol "green"; return green,
		 	 do symbol "yellow"; return yellow,
			 do symbol "orange"; return orange,
		 	 rgbcolor,token hexcolor]

 colPre        = do col <- color; char '_'; x <- p; return (col,x)
 		 where p = P $ \x -> Just (x,[])
 
 delCol x      = case parse colPre x of Just (_,x) -> x; _ -> x

 quoted        = do char '"'; x <- many $ sat item (/= '"'); char '"'; return x

 infixWord     = do char '`'; x <- some $ sat item (/= '`'); char '`'
 		    return $ '`':x++"`"

 infixSymb     = infixWord ++ inequivalence ++ equivalence
 
 equivalence   = do str <- strLetters "~"; n <- nat; return $ str++show n
 
 inequivalence = do str <- strLetters "~/~"; n <- nat; return $ str++show n

 noBlanks      = token $ some $ sat item noDelims

 noDelims c    = c `notElem` " \t\n()[]{},`$.;:+-*<=~>/\\^#&|"

 infixChar c   = c `elem` "$.;:+-*<=~>/\\^#&|"
 
 infixToken    = token $ infixSymb ++ some (sat item infixChar)

 infixFun      = sat infixToken . functional

 infixRel      = sat infixToken . relational

 list p        = do symbol "["; (do symbol "]"; return []) ++
                                (do xs <- several p; symbol "]"; return xs)

 several p     = do x <- p; (do symbol ","; xs <- several p; return $ x:xs) ++
	                    return [x]

 curryrest sig p t = concat [do u <- p
                                curryrest sig p $ applyL t 
						$ case u of F "()" ts -> ts
					                    _ -> [u],
		             return t]

-- PARSER of formulas

 implication sig = do s <- disjunct sig
                      (do x <- oneOf $ words "<=> ==> <==> ===> <==="
		          s' <- disjunct sig; return $ F x [s,s']) ++ return s

 disjunct sig = do t <- conjunct sig; ts <- many $ do symbol "|"; conjunct sig
 	           return $ if null ts then t else F "|" $ t:ts

 conjunct sig = do t <- factor sig; ts <- many $ do symbol "&"; factor sig
 	           return $ if null ts then t else F "&" $ t:ts
		   
-- PARSER of factors

 factor sig = concat [do symbol "True"; return mkTrue,
		      do symbol "False"; return mkFalse,
		      do symbol "Not"; t <- factor sig; return $ F "Not" [t],
		      do symbol "Any"; closure "Any",
		      do symbol "All"; closure "All",
		      do t <- term sig; x <- sat (infixRel sig) arithmetical
		         u <- term sig; return $ F x [t,u],
		      relTerm sig False,
		      enclosedImpl sig]
              where closure q = do xs@(_:_) <- boundVars sig; symbol ":"
 		                   t <- factor sig; return $ mkBinder q xs t

 boundVars sig = f [] 
                 where f xs = (do x <- sat noBlanks $ isVar sig; f $ xs++[x]) ++
                              (do guard $ distinct xs; return xs)
 
 enclosedImpl sig = do symbol "("; t <- implication sig; symbol ")"; return t
 
 relTerm sig b = (do t <- singleAtom sig b; maybeComp sig t) ++
		 (do t <- singleAtom sig True; maybeInfixAtom sig False t)
 
 singleAtom sig b = concat [prefixAtom sig, if b then term sig else mzero,
 			    do t <- enclosedAtom sig b; curryrestR sig t]

 maybeInfixAtom sig b t = concat [do x <- infixRel sig; u <- relTerm sig True
			             application x t u,
		                  if b then return t else mzero]

 maybeComp sig t = (do symbol "."; u <- singleTerm sig
		       maybeComp sig $ F "." [t,u]) ++ maybeInfixAtom sig True t
				  
 application x t u = return $ if x == "$" && root t /= "_" && null (subterms t) 
        		         && not (isPos z) then F z [u] else F x [t,u]
		     where z = root t
			  
 enclosedAtom sig b = concat [enclosedSection sig True,
 			      do symbol "("; ts <- p; symbol ")"
 				 return $ mkTup ts,
			      do symbol "[]"
			         if b then return mkNil else mzero,
			      do symbol "["; ts <- p; symbol "]"
			         return $ mkList ts]
	      where p = do t <- relTerm sig b
		           (do symbol ","; ts <- p; return $ t:ts) ++ return [t]

 curryrestR sig = curryrest sig $ enclosedAtom sig True

 prefixAtom sig = concat [do x <- symbol "rel"; symbol "("
			     ts <- p []; symbol ")"; curryrestR sig $ F x ts,
			  do x <- oneOf $ words "MU NU"
			     xs@(_:_) <- boundVars sig; symbol "."
			     t <- singleAtom sig False
			     curryrestR sig $ mkBinder x xs t,
			  do x <- sat noBlanks $ relational sig
 			     curryrestR sig $ F x []]
                  where p ts = do t <- term sig; symbol ","
		  		  u <- implication sig
				  let us = ts++[t,u]
     			          (do symbol ","; p us) ++ return us

-- PARSER of terms

 terms sig = do t <- term sig; (do symbol ","; ts <- terms sig; return $ t:ts) 
 	     		       ++ return [t]

 term sig = do t <- bagTerm sig; ts <- many $ do symbol "<+>"; bagTerm sig
	       return $ if null ts then t else F "<+>" $ t:ts

 bagTerm sig = do t <- sumTerm sig; ts <- many $ do symbol "^"; sumTerm sig
		  return $ if null ts then t else F "^" $ t:ts

 sumTerm sig = do t <- prodTerm sig; maybeSum sig t

 maybeSum sig t = concat [do x <- oneOf addOps; u <- prodTerm sig
 			     maybeSum sig $ F x [t,u],
	                  do x <- infixFun sig; u <- bagTerm sig
			     application x t u,
	                  return t]
			  
 addOps = words "+ -"
 mulOps = words "** * /"

 prodTerm sig = do t <- singleTerm sig; maybeProd sig t

 maybeProd sig t = concat [do x <- oneOf mulOps; u <- singleTerm sig
 			      maybeProd sig $ F x [t,u],
 			   do x <- sat (infixFun sig) (`notElem` addOps)
			      u <- bagTerm sig; application x t u,
	                   return t]

 singleTerm sig = concat [constant sig,
			  do x <- token int; curryrestF sig $ mkConst x,
                          do symbol "pos "; p <- many $ token nat
			     return $ mkPos p,
	                  do x <- oneOf $ words "- ~"; t <- singleTerm sig
			     return $ F x [t],
	                  do symbol "()"; return mkUndef,
			  do x <- oneOf termBuilders
			     ((do symbol "$"; t <- relTerm sig False
				  curryrestF sig $ F x [t]) ++
			      (do t <- enclosedAtom sig False++enclosedImpl sig
				  curryrestF sig $ F x [t])),
		          do x <- oneOf $ words "mu nu"
			     xs@(_:_) <- boundVars sig; symbol "."
			     t <- enclosedTerm sig ++ singleTerm sig
 		             return $ mkBinder x xs t,
			  do t <- enclosedTerm sig; curryrestF sig t,
			  do x <- sat noBlanks sig.isFovar; return $ V x,
 			  do x <- sat (token $ some $ sat item
			                     $ noDelims ||| (== ' '))
			  	      $ not . declared sig
			     curryrestF sig $ F (unwords $ words x) [],
 			  do x <- sat noBlanks $ functional sig
			     curryrestF sig $ F x []]

 declared sig = functional sig ||| relational sig ||| logical

 constant sig = concat [do x <- token quoted; return $ mkConst x,
 			do x <- token double; return $ mkConst x,
			do x <- token hexcolor; return $ mkConst x,
			do RGB r g b <- rgbcolor
			   return $ F (unwords $ "RGB":map show [r,g,b]) []]

 curryrestF sig = curryrest sig $ enclosedTerm sig

 enclosedTerm sig = concat [do symbol "("; ts <- terms sig; symbol ")"
			       return $ mkTup ts,
			    enclosedSection sig False,
			    listTerm sig, setTerm sig]

 enclosedSection sig b = do symbol "("
                            concat [do x <- p
			               concat [do symbol ")"; return $ F x [],
				               do t <- termOrRelTerm sig
				                  symbol ")"
					          return $ F "rsection" 
					          	     [F x [],t]],
			            do t <- termOrRelTerm sig
				       concat [do symbol ")"; return t,
				               do x <- p; symbol ")"
				                  return $ F "lsection" 
				                  	     [t,F x []]]]
		         where p = if b then infixRel sig else infixFun sig

 listTerm sig = (do symbol "[]"; return mkNil) ++
	        (do symbol "["
		    concat [do t <- term sig; symbol ".."; u <- term sig
		               symbol "]"; return $ F "range" [t,u],
			    do ts <- terms sig; symbol "]"; return $ mkList ts])
				     
 termOrRelTerm sig = term sig ++ relTerm sig False

 setTerm sig = (do symbol "{}"; return $ F "{}" []) ++
	       (do symbol "{"; ts <- terms sig; symbol "}"; return $ F "{}" ts)

 termBuilders = words "bool curryR filterL filter flipR gaussI gauss ite" ++
                words "mapfilterL postflow solsG sols stateflow subsflow"

-- TRANSITION SYSTEMS and KRIPKE STRUCTURES

 type Pairs a = [(a,[a])]

 type Triples a b = [(a,a,[b])]
 type Triples2 a  = Triples a (a,a)
 type Triples2L a = Triples a ([a],[a])

 mkPairs :: [a] -> [a] -> [[Int]] -> Pairs a
 mkPairs dom ran = zipWith f [0..] where f i ks = (dom!!i,map (ran!!) ks)
 
 mkTriples :: [a] -> [a] -> [a] -> [[[Int]]] -> Triples a a
 mkTriples dom1 dom2 ran = concat . zipWith f [0..]
 		     where f i = zipWith g [0..]
			         where g j ks = (dom1!!i,dom2!!j,map (ran!!) ks)

-- REGULAR EXPRESSIONS and their language acceptors

 data RegExp = Const String | Sum_ RegExp RegExp | Prod RegExp RegExp | 
 	       Plus RegExp | Star RegExp
	       
 parseRegExp :: TermS -> Maybe RegExp
 parseRegExp (F a [])       = Just $ Const a
 parseRegExp (F "+" [t,u])  = do e <- parseRegExp t; f <- parseRegExp u
 				 Just $ Sum_ e f
 parseRegExp (F "*" [t,u])  = do e <- parseRegExp t; f <- parseRegExp u
 			         Just $ Prod e f
 parseRegExp (F "plus" [t]) = do e <- parseRegExp t; Just (Plus e)
 parseRegExp (F "star" [t]) = do e <- parseRegExp t
 			         Just $ Sum_ (Plus e) $ Const "eps"
 parseRegExp (F "refl" [t]) = do e <- parseRegExp t; Just $ Sum_ e $ Const "eps"
 parseRegExp _ 	            = Nothing

 type NDA = Int -> String -> [Int]
 
 regToAuto :: RegExp -> ([Int],NDA)
 regToAuto e = ([0..nextq-1],delta)
  where (delta,nextq) = eval e 0 1 (const2 []) 2
	eval :: RegExp -> Int -> Int -> NDA -> Int -> (NDA,Int)
        eval (Const a) q q' delta nextq   = (upd2L delta q a q',nextq)
        eval (Sum_ e e') q q' delta nextq = eval e' q q' delta' nextq'
		          where (delta',nextq') = eval e q q' delta nextq
        eval (Prod e e') q q' delta nextq = eval e' nextq q' delta' nextq'
		          where (delta',nextq') = eval e q nextq delta $ nextq+1
        eval (Plus e) q q' delta nextq    = (upd2L delta3 q1 "eps" q',nextq1)
		          where q1 = nextq+1
                                (delta1,nextq1) = eval e nextq q1 delta $ q1+1
		                delta2 = upd2L delta1 q "eps" nextq
 		                delta3 = upd2L delta2 q1 "eps" nextq
	eval (Star e) q q' delta nextq    = eval (Sum_ (Plus e) $ Const "eps")
						 q q' delta nextq  

 alphabet :: RegExp -> [String]	   
 alphabet (Const a)   = [a]
 alphabet (Sum_ e e') = alphabet e `join` alphabet e'
 alphabet (Prod e e') = alphabet e `join` alphabet e'
 alphabet (Plus e)    = alphabet e
 alphabet (Star e)    = alphabet e
 
-- MINIMIZATION with the Paull-Unger algorithm

 lfp,gfp :: BoolFun a -> (a -> a) -> a -> a
 lfp le f a = if fa `le` a then a else lfp le f fa where fa = f a
 gfp le f a = if a `le` fa then a else gfp le f fa where fa = f a
			  
 deterministic :: Sig -> [Int] -> [Int] -> Bool
 deterministic sig is ks = if null ks then all f is
 				      else all (flip all ks . g) is
			   where f i = length (trans sig !! i) == 1
			         g i k = length (transL sig !! i !! k) == 1

 nerode,bisim :: Sig -> [Int] -> [Int] -> [(Int,Int)]
 nerode sig is = map (\(i,j,_) -> (i,j)) . gfp subset nerodeStep 
 					 . nerode0 sig is
 bisim  sig is = map (\(i,j,_) -> (i,j)) . gfp subset bisimStep . bisim0 sig is
			 
 nerode0 :: Sig -> [Int] -> [Int] -> Triples2 Int
 nerode0 sig is ks = firstMat sig is ks f
	          where f i j = if null ks then [(min k l,max k l)]
	                                   else mkSet $ map h ks
			        where ([k],[l]) = (sig.trans!!i,sig.trans!!j)
		                      h a = (min k l,max k l) 
		                            where ([k],[l]) = (sig.transL!!i!!a,
			      			               sig.transL!!j!!a)

 bisim0 :: Sig -> [Int] -> [Int] -> Triples2L Int
 bisim0 sig is ks = firstMat sig is ks f
		    where f i j = if null ks then [(sig.trans!!i,sig.trans!!j)]
			                     else mkSet $ map h ks
		                 where h k = (sig.transL!!i!!k,sig.transL!!j!!k)

 firstMat :: Sig -> [Int] -> [Int] -> (Int -> Int -> [a]) -> Triples Int a
 firstMat sig is ks f = [(i,j,f i j) | i <- is, j <- is, i < j, 
 				       all (eq i j) $ indices_ sig.atoms]
		       where eq :: Int -> BoolFun Int
			     eq i j k = if null sig.valueL then f1 i k == f1 j k
				                           else f2 i k == f2 j k
 		             f1 i k = i `elem` sig.value!!k
		             f2 i k = map (elem i . ((sig.valueL!!k)!!)) ks
			   
 nerodeStep :: Eq a => Triples2 a -> Triples2 a
 nerodeStep trips = [trip | trip@(_,_,bs) <- trips, all r bs]
  where r (i,j) = i == j || just (lookupL i j trips) || just (lookupL j i trips)
				      
 bisimStep :: Eq a => Triples2L a -> Triples2L a
 bisimStep trips = [trip | trip@(_,_,bs) <- trips, all r bs]
   where r (is,js) = forallThereis r' is js && forallThereis r' js is
         r' i j = i == j || just (lookupL i j trips) || just (lookupL j i trips)
			    			       		  
 mkQuotient :: Sig -> [(Int,Int)] 
 		   -> ([TermS],[[Int]],[[[Int]]],[[Int]],[[[Int]]])
 mkQuotient sig pairs = (states,tr,trL,va,vaL)
   where partition = loop pairs $ map single $ indices_ sig.states
	 loop ((i,j):pairs) part = loop pairs $ if eqSet (==) si sj then part 
		  	            	        else (si++sj):minus part [si,sj]
		                 where si = f i; sj = f j
		       	               f i = snd $ get $ searchGet (elem i) part
	 loop _ part = part
	 states = map ((sig.states!!) . minimum) partition
	 oldPos i = get $ search (== (states!!i)) sig.states
	 newPos i = get $ search (elem i) partition
	 is = indices_ states; js = indices_ sig.labels; ks = indices_ sig.atoms
	 tr = map f is where f i = mkSet $ map newPos $ sig.trans!!oldPos i
	 trL = map f is 
	       where f i = map (g i) js
	             g i x = mkSet $ map newPos $ sig.transL!!oldPos i!!x
         va = map f ks where f i = mkSet $ map newPos $ sig.value!!i
	 vaL = map f ks where f i = map (g i) js
	      		      g i x = mkSet $ map newPos $ sig.valueL!!i!!x

-- LR parsing

 data ActLR  = Rule String [String] Int | Read | Error deriving (Show,Eq,Ord)
 
 data LoopLR = More [Int] [TermS] [Int] | Success TermS | NoParse

 nextLR :: Sig -> Array (Int,Int) ActLR -> [Int] -> [TermS] -> [Int] -> LoopLR
 nextLR sig acttab sts@(i:_) ts input@(k:rest) = 
     case acttab!(i,k) of Read | notnull succs -> More (head succs:sts) ts rest
     			                          where succs = sig.transL!!i!!k
                          Rule left right lg | left == "S" && length ts == lg 
                            -> Success $ F rule ts 
	                                     | lgr < length sts && notnull succs
                            -> More (head succs:is) (us++[F rule vs]) input
	                       where rule = unwords $ left:"_":right
				     lgr = length right
				     is@(i:_) = drop lgr sts
				     labs = map root sig.labels 
				     succs = sig.transL!!i!!getInd left labs
			             (us,vs) = splitAt (length ts-lg) ts
                          _ -> NoParse
 nextLR _ _ _ _ _ = NoParse

 actTable :: Sig -> (Int,Int) -> ActLR
 actTable sig (i,k) = if k `elem` nonterminals || length acts /= 1 then Error
	              else case words $ root $ sig.atoms!!head acts of 
			   ["shift"] -> Read
			   ["error"] -> Error
		           left:right 
			     -> Rule left right $ length $ meet right $
			             map (root . (sig.labels!!)) nonterminals
   	           where acts = vaLR!!i!!k
	                 vaLR = invertRelII (any notnull $ sig.value) sig.labels 
	          		            sig.atoms sig.states sig.valueL
		         is = indices_ sig.states
		         ks = indices_ sig.labels
		         nonterminals = [k | k <- ks, all (null . h k) is]
		         h k i = vaLR!!i!!k

-- linear functions and equations
 
 type LinFun = ([(Float,String)],Float)
 type LinEq  = LinFun

 combLins :: (Float -> Float -> Float) -> Float -> LinFun -> LinFun -> LinFun
 combLins f c (ps,a) (qs,b) = (comb ps qs,f a b)
            where comb ps@(p@(a,x):ps') qs@(q@(b,y):qs')
 		       | x == y               = if fab == 0 then comb ps' qs'
		       			        else (fab,x):comb ps' qs'
		       | y `elem` map snd ps' = p:comb ps' qs
		       | x `elem` map snd qs' = (b*c,y):comb ps qs'
		       | True                 = p:(b*c,y):comb ps' qs'
		       				where fab = f a b
	          comb [] ps                  = map h ps where h (a,x) = (a*c,x)
	          comb ps _                   = ps
 
 addLin = combLins (+) 1
 subLin = combLins (-) $ -1

 mulLin f (ps,b) = (map h ps,f b) where h (a,x) = (f a,x)

-- gauss solves linear equations.
 
 gauss :: [LinEq] -> Maybe [LinEq]
 gauss eqs = case gauss1 eqs of 
 	          Just eqs -> gauss $ gauss3 eqs
 		  _ -> case gauss2 eqs of Just eqs -> gauss $ gauss3 eqs
					  _ -> Just eqs
 
-- (a1*x1)+...+(an*xn)+(a*x) = b ----> (a1/a*x1)+...+(an/a*xn)+x = b/a
		   
 gauss1 :: [LinEq] -> Maybe [LinEq]
 gauss1 eqs = do (i,a) <- searchGet (/= 1) $ map (fst . last . fst) eqs
 		 Just $ updList eqs i $ mulLin (/a) $ eqs!!i

-- p+x = b & q+x = c ----> p-q = b-c & q+x = c

 gauss2 :: [LinEq] -> Maybe [LinEq]
 gauss2 eqs = do (i,eq,eq') <- searchGet2 f g eqs
                 Just $ updList eqs i $ subLin eq eq'
	      where f (ps,_)        = fst (last ps) == 1
	            g (ps,_) (qs,_) = last ps == last qs

-- x = b & eqs ----> x = b & eqs[(ps,c-a*b)/((a,x):ps,c)]

 gauss3 :: [LinEq] -> [LinEq]
 gauss3 = f []
  where f eqs (eq@([(1,x)],b):eqs') = f (map g eqs++[eq]) (map g eqs')
 		      where g eq@(ps,c) = case searchGet ((== x) . snd) ps of
		  		          Just (i,(a,_)) -> (context i ps,c-a*b) 
		  		          _ -> eq
	f eqs (eq:eqs')             = f (eqs++[eq]) eqs'
	f eqs _			    = eqs
	      	
-- TERMS, FORMULAS and REDUCTS

 data Term a = V a | F a [Term a] | Hidden Special deriving (Show,Eq,Ord)

 data Special = Dissect [(Int,Int,Int,Int)] | 
 		BoolMat [String] [String] (Pairs String) | 
 		ListMat [String] [String] (Triples String String) | 
		ListMat2 [String] (Triples2 String) | 
		ListMat2L [String] (Triples2L String) | 
		LRarr (Array (Int,Int) ActLR) |
		ERR deriving (Show,Eq,Ord)	
 
 type TermS = Term String
		
 type Simplification = (TermS,[TermS],TermS)

 class Root a where undef :: a
 
 instance Root Color 			where undef = white
 instance Root Int   			where undef = 0
 instance Root Float 			where undef = 0.0
 instance Root [a]   			where undef = []
 instance (Root a,Root b) => Root (a,b) where undef = (undef,undef)
 instance (Root a,Root b,Root c) => Root (a,b,c) 
 					where undef = (undef,undef,undef)

 isV (V _) = True
 isV _     = False

 isF (F _ _) = True
 isF _       = False

 isHidden = not . (isV ||| isF)

 root :: Root a => Term a -> a
 root (V x)   = x
 root (F x _) = x
 root t       = undef
 
 subterms (F _ ts) = ts
 subterms _        = []

 height (F _ ts) = foldl max 0 (map height ts)+1
 height t        = 1

 sizeAll (F _ ts) = sum (map sizeAll ts)+1
 sizeAll t        = 1
  
--- instance Eq a => Ord (Term a) where t <= u = sizeAll t <= sizeAll u

 size (V x)    = if isPos x then 0 else 1
 size (F _ ts) = sum (map size ts)+1
 size t        = 1

 takeT 1 (F x _)  = F x []
 takeT n (F x ts) = F x $ map (takeT $ n-1) ts
 takeT _ t        = t

 x `isin` V y    = x == y
 x `isin` F y ts = x == y || any (isin x) ts
 x `isin` _      = False

 notIn x = not . isin x

 foldT :: Root a => (a -> [b] -> b) -> Term a -> b
 foldT f (V a)    = f a []
 foldT f (F a ts) = f a $ map (foldT f) ts
 foldT f _        = f undef []
 
 andT :: Root a => (a -> Bool) -> Term a -> Bool
 andT f = foldT g where g x bs = f x && and bs
 
 isSubterm :: Eq a => Term a -> Term a -> Bool
 isSubterm t u | t == u = True
 isSubterm t (F _ ts)   = any (isSubterm t) ts
 isSubterm _ _          = False

-- nodeLabels is used by drawThis (see Ecom).

 nodeLabels = foldT f where f ('@':_) _ = ["@"]
			    f x xss     = delQuotes x:concat xss

 mapT :: (a -> b) -> Term a -> Term b
 mapT f (V a)      = V $ f a
 mapT f (F a ts)   = F (f a) $ map (mapT f) ts
 mapT _ (Hidden t) = Hidden t

 mapT2 :: (b -> c) -> Term (a,b) -> Term (a,c)
 mapT2 f (V (a,p))    = V (a,f p)
 mapT2 f (F (a,p) ts) = F (a,f p) $ map (mapT2 f) ts
 mapT2 _ (Hidden t)   = Hidden t

 transTree1 :: Num a => a -> Term (b,(a,a)) -> Term (b,(a,a))
 transTree1 = mapT2 . flip add1

 transTree2 :: Num a => (a,a) -> Term (b,(a,a)) -> Term (b,(a,a))
 transTree2 = mapT2 . add2

 mapT3 :: (b -> c) -> Term (a,b,d) -> Term (a,c,d)
 mapT3 f (V (a,p,d))    = V (a,f p,d)
 mapT3 f (F (a,p,d) ts) = F (a,f p,d) $ map (mapT3 f) ts
 mapT3 _ (Hidden t)     = Hidden t
 
 apply (F x []) t = F x [t]
 apply t u        = F "$" [t,u]

 applyL (F x []) ts = F x ts
 applyL t ts        = F "$" [t,mkTup ts]

-- colHidden is used by widgets, mkCoordTree (see Epaint) and drawThis 
-- (see Ecom).

 colHidden (F x ts)   = F x $ map colHidden ts
 	             -- if isFix x then leaf x else F x $ map colHidden ts
 colHidden (Hidden _) = leaf "blue_hidden"
 colHidden t          = t
 
 bothHidden (Hidden _) (Hidden _) = True
 bothHidden _ _     		  = False

-- delQuotes is used by nodeLabels (see above), mkSizes (see below), decXY,
-- stringInTree, drawTreeNode, drawWidg Text, halfmax (see Epaint), simplifyOne
-- (see Esolve) and drawNode (see Ecom).

 delQuotes a = if just $ parse (quoted++infixWord) b then init $ tail b else b
	       where b = delCol a

 applySignatureMap sig sig' f t@(V x) | f x /= x       = Just $ V $ f x
 			              | sig'.isFovar x = Just t
			              | True           = Nothing
 applySignatureMap sig sig' f (F x ts) =
         do ts <- mapM (applySignatureMap sig sig' f) ts
            if f x /= x then Just $ F (f x) ts
		        else do guard $ logical x ||
			                functional sig x && functional sig' x ||
					relational sig x && relational sig' x ||
					sig.isHovar x && sig'.isHovar x
			        Just $ F x ts

 defuncts sig (F x ts) = if sig.isDefunct x then x:fs else fs
 		         where fs = concatMap (defuncts sig) ts
 defuncts _ _          = []
 
 collector x = x `elem` words "^ {} []"
 
 collectors x y = collector x && collector y
 
 isEq x = x `elem` words "= =/="

 permutative x = isEq x || idempotent x || x `elem` words "^ + * ;"

 idempotent x = x `elem` words "| & \\/ /\\ <+> {}"
 
 transitive x = x `elem` words "< > = <= >=" 
 
 arithmetical x = transitive x || x == "="
 
 isEmpty (F x []) | collector x = True
 isEmpty _                      = False

 eqTerm t u 		    | t == u  = True
 eqTerm (F "<" [t,u]) (F ">" [v,w])   = eqTerm t w && eqTerm u v
 eqTerm (F ">" [t,u]) (F "<" [v,w])   = eqTerm t w && eqTerm u v
 eqTerm (F "<=" [t,u]) (F ">=" [v,w]) = eqTerm t w && eqTerm u v
 eqTerm (F ">=" [t,u]) (F "<=" [v,w]) = eqTerm t w && eqTerm u v
 eqTerm (F x [t]) (F y [u]) | binder x && binder y && opx == opy =
 	                      eqTerm (renameFree (fold2 upd id xs ys) t) u
			      where opx:xs = words x; opy:ys = words y
 eqTerm (F x ts) (F y us)   | x == y =
 	                      if idempotent x then eqSet eqTerm ts us
		              else length ts == length us &&
				   if permutative x then eqBag eqTerm ts us
                                   else eqTerms (renameVars emptySig x ts us) us
 eqTerm t u = bothHidden t u
 
 eqTerms ts us = length ts == length us && and (zipWith eqTerm ts us)
 
 renameVars sig x ts us = if lambda x then f ts us else ts
                     where f (t:t':ts) (u:_:us) = mapT chg t:mapT chg t':f ts us
 		                   where xs = allVars t; ys = allVars u
			                 chg x = case search (== x) xs of 
			     			 Just i | i < length ys -> ys!!i
						 _ -> x
			   f _ _ = []
			   allVars t = vars t `join` 
			               map (label t) (varPositions sig t)
 
 neqTerm t = not . eqTerm t

 inTerm = any . eqTerm
 
 notInTerm = all . neqTerm
 
 subsetTerm ts us = all (flip inTerm us) ts
 
 prefix (t:ts) (u:us) = eqTerm t u && prefix ts us
 prefix ts _          = null ts
 
 suffix ts@(_:_) us@(_:_) = eqTerm (last ts) (last us) && 
 			    suffix (init ts) (init us)
 suffix ts _              = null ts

 sharesTerm ts = any (flip inTerm ts)

 disjointTerm ts = all (flip notInTerm ts)
 
 distinctTerms (ts:tss) = all (null . meetTerm ts) tss && distinctTerms tss
 distinctTerms _        = True
 
 meetTerm ts us = [t | t <- ts, inTerm t us]

 joinTerm ts@(t:us) u = if eqTerm t u then ts else t:joinTerm us u
 joinTerm _         t = [t]

 joinTerms :: [TermS] -> [TermS] -> [TermS]
 joinTerms = foldl joinTerm
 
 joinTermsM :: [[TermS]] -> [TermS]
 joinTermsM = foldl joinTerms []

 joinTermMap f = foldl joinTerms [] . map f

 removeTerm (t:ts) u = if eqTerm t u then removeTerm ts u else t:removeTerm ts u
 removeTerm _ _      = []

 removeTerms = foldl removeTerm

-- sucTerms t ps returns the proper subterms of t that include a position of ps.
-- sucTerms is used by applyDisCon (see Ecom).

 sucTerms t = concatMap f . map tail where f p@(_:_) = getSubterm t p:f (init p)
		   			   f _       = []
		 
-- VARIABLES

 vars (F _ ts) = joinMap vars ts
 vars (V x)    = if isPos x then [] else [x]
 vars _        = []

 isVar sig = sig.isFovar ||| sig.isHovar
 
 mkVar sig x = if sig.isFovar x then V x else F x []

 isVarRoot sig = isV ||| sig.isHovar . getOp ||| isHidden

 allSyms b (F x [t]) | binder x = allSyms b t `join` filter b (tail $ words x)
 allSyms b (F x ts)             = if b x then us `join1` x else us
				  where us = joinMap (allSyms b) ts
 allSyms b (V x)  		= if null x || isPos x || not (b x) then [] 
 				  				    else [x]
 allSyms _ _ 		        = []

 sigVars = allSyms . isVar

 allFrees b (F x [t]) | binder x = allFrees b t `minus` tail (words x)
 allFrees b (F x ts)  | lambda x = concat $ zipWith f (evens ts) $ odds ts
 			           where f par t = g t `minus` g par
					 g = allFrees b
 allFrees b (F x ts)             = if b x then us `join1` x else us
				   where us = joinMap (allFrees b) ts
 allFrees _ (V x)  		 = if null x || isPos x then [] else [x]
 allFrees _ _  		         = []

 frees sig = allFrees sig.isHovar
 
 freesL sig = joinMap $ frees sig

 anys (F ('A':'n':'y':x) _) = words x
 anys _                     = []

 alls (F ('A':'l':'l':x) _) = words x
 alls _                     = []

 removeAny x (F ('A':'n':'y':z) [t]) = mkAny (words z `minus1` x) t
 removeAny _ t                       = t

 removeAll x (F ('A':'l':'l':z) [t]) = mkAll (words z `minus1` x) t
 removeAll _ t                       = t

 isAllQ (F ('A':'l':'l':' ':_) _) = True
 isAllQ _		          = False

 isAnyQ (F ('A':'n':'y':' ':_) _) = True
 isAnyQ _		          = False

-- isAny/isAll t x p checks whether an occurrence of x at position p of t were
-- existentially/universally quantified and, if so, returns the quantifier 
-- position.

 isAny t x = f where f p = case getSubterm t p of
                           F ('A':'n':'y':' ':z) _ | x `elem` words z -> Just p
                           F ('A':'l':'l':' ':z) _ | x `elem` words z -> Nothing
	                   _ -> do guard $ notnull p; f $ init p

 isAll t x = f where f p = case getSubterm t p of
                           F ('A':'l':'l':' ':z) _ | x `elem` words z -> Just p
			   F ('A':'n':'y':' ':z) _ | x `elem` words z -> Nothing
			   _ -> do guard $ notnull p; f $ init p

 isAnyOrFree t x = just . isAny t x ||| isFree t x

 isAllOrFree t x = just . isAll t x ||| isFree t x
 
-- isFree t x p checks whether an occurrence of x at position p of t were free.

 isFree t x = f where f p = case getSubterm t p of
                            F ('A':'l':'l':' ':z) _ | x `elem` words z -> False
                            F ('A':'n':'y':' ':z) _ | x `elem` words z -> False
	                    _ -> null p || f (init p)

-- universal sig t p u checks whether all occurrences of free variables of u
-- below position p of t are (implicitly) universally quantified at position p.
-- universal is used by applyCoinduction, applyInduction and createInvariant 
-- (see Ecom).

 universal sig t p u = polarity True t p && all f (frees sig u)
  where f x = case isAny t x p of Just q  -> cond False q
	                          _ -> case isAll t x p of Just q -> cond True q
			                                   _ -> True
         where cond b q = polarity b t q && 
		          all (p <<) [r | r <- filterPositions (== x) t, q << r]

 newVar n = V $ 'z':show n

-- UNPARSER of trees
 
 showTree True t = foldT f t
                   where f "range" [str1,str2] = '[':str1++".."++str2++"]"
                         f "lsection" [str,x]  = '(':str++x++")"
                         f "rsection" [x,str]  = '(':x++str++")" 
 			 f x []                = x
		         f "()" strs 	       = '(':g "," strs++")"
		         f "[]" strs 	       = '[':g "," strs++"]"
		         f "{}" strs           = '{':g "," strs++"}"
		         f x strs | isInfix x  = '(':g x strs++")"
		                  | isQuant x  = x++':':'(':g "," strs++")"
		                  | isFix x    = x++'.':'(':g "," strs++")"
				  | True       = x++'(':g "," strs++")"
		         g _ [str]      = str
			 g x (str:strs) = str++x++g x strs
 showTree _ t    = fst (showImpl t 0) ""

 blanks n = (replicate n ' ' ++)

 newBlanks n = ('\n':) . blanks n

 isInfix = all infixChar ||| just . parse infixSymb

 enclose f = ('(':) . f . (')':)

 showSummands cs = fst (showVer0 "| " showConjunct cs 0 True) ""

 showFactors fs = fst (showVer0 "& " showFactor fs 0 True) ""

 showSum ts = fst (showVer0 "<+> " showTerm ts 0 True) ""

 showVer0 x single (t:ts) n b = if b then (blanks lg . st . sts,m)
			        else if null ts then (h,lg+k) else (h . sts,m)
			        where lg = length x
				      (st,k) = single t (n+lg)
				      (sts,m) = showVer0 x single ts n False
				      h = newBlanks n . (x++) . st
 showVer0 _ _ _ _ _           = (id,0)

 showVer x single ts n = f ts
   where (_,g) = symPair x
	 f ts = if length ts < 2 then showHor x single ts n
	 		         else if just pair then fst $ get pair
                                      else (sts . g . newBlanks n . sus,k')
                where pair = fits ts []
	              fits ts us = do guard $ n+k < 80 && all (/= '\n') (f "")
		                      Just (stsk,us) 
                                   where stsk@(f,k) = showHor x single ts n
	              ((sts,_),us) = h (init ts) [last ts]
		      (sus,k') = f us
		      h ts us = if length ts < 2 then (showHor x single ts n,us)
		                else if just pair then get pair 
				                  else h (init ts) $ last ts:us
	      		        where pair = fits ts us
		 
 showHor x single = f 
   where mid = symPair x; b = boolean x || x == ","; c = x == "$"
         f (t:ts) n = if null ts then stk else (st . g . sts,k'+m)
                where stk@(st,k) = if b then single t n else maybeEnclosed [t] n
	              (sts,m) = f ts $ n+k'; k' = k+lgx
		      (lgx,g) = if c && 
		                   root (head ts) `elem` words "() {} [] range"
			        then (0,id) else mid
         f _ _      = (id,0)
 
 symPair x = if x `elem` words "$ . ^ , : ++ + - * ** / # <> /\\ \\/" 
 	     then (length x,(x++)) else (length x+2,((' ':x++" ")++))

-- show+ t n = (u,k) iff the string u that represents t starts at position n of
-- a line and the last line of u consists of k characters.

 showImpl (F x ds@[_,_]) | implicational x = showVer x showDisjunct ds
 showImpl d 		                   = showDisjunct d

 showDisjunct (F "|" cs) = showVer "|" showConjunct cs
 showDisjunct c          = showConjunct c

 showConjunct (F "&" fs) = showVer "&" showFactor fs
 showConjunct f          = showFactor f

 showFactor (F "Not" [impl]) n 	    = (("Not(" ++) . si . (')':),k+5)
                                      where (si,k) = showImpl impl $ n+4
 showFactor t@(F x _) n | boolean x = (enclose si,k+2)
 				      where (si,k) = showImpl t $ n+1
 showFactor t n 		    = showTerm t n

-- UNPARSER of terms

 showTerm0 t = fst (showTerm t 0) ""

 showTerm (V x) n 		   = ((x++),length x)
 showTerm (F x []) _               = if just $ parse realNeg x
 				     then ((' ':) . (x++),lg+1) else ((x++),lg)
		                     where lg = length x
 showTerm t@(F x ts) n | isInfix x = showVer x showFactor ts n
 showTerm (F x [t]) n | x `elem` termBuilders 
 				   = ((x++) . enclose st,lg+2+k)
 				     where lg = length x
				           (st,k) = showImpl t $ n+lg+1
 showTerm (F "range" [t,u]) n      = (('[':) . st . (".." ++) . su . (']':),
  				      k+m+4) where (st,k) = showTerm t (n+1)
				                   (su,m) = showTerm u (n+k+3)
 showTerm (F "lsection" [t,F x []]) n   
 				   = (('(':) . st . (x++) . (')':),k+length x) 
  				     where (st,k) = showTerm t (n+1)
 showTerm (F "rsection" [F x [],t]) n   
 				   = (('(':) . (x++) . st . (')':),k+lg) 
  				     where (st,k) = showTerm t (n+lg-1)
  				           lg = length x
 showTerm (F "[]" ts) n            = (('[':) . sts . (']':),k+2)
			             where (sts,k) = showTerms ts $ n+1
 showTerm (F "{}" ts) n            = (('{':) . sts . ('}':),k+2)
			             where (sts,k) = showTerms ts $ n+1
 showTerm (F "()" ts) n            = showEnclosed ts n
 showTerm (F "-" [t]) n            = if isInfix $ root t 
  				     then (('-':) . enclose st,k+3) 
				     else (('-':) . st,1+k)
		                     where (st,k) = showTerm t $ n+2
 showTerm (F x [t]) n | binder x   = if lg < 11 then (f . st,lg+k)
		                     else (f . newBlanks (n+1) . su,m)
				     where f = (x++) . (c:)
				           c = if isFix x then '.' else ':'
				           lg = length x+1
				           (st,k) = maybeEnclosed [t] $ n+lg
				           (su,m) = maybeEnclosed [t] $ n+1
 showTerm (F x ts) n               = ((x++) . sts,lg+k) 
 			             where lg = length x
				           (sts,k) = showEnclosed ts $ n+lg
 showTerm (Hidden _) _             = (("hidden"++),6)

 showTerms = showVer "," showFactor

 maybeEnclosed [t] | not $ isInfix $ root t = showImpl t
 maybeEnclosed ts			    = showEnclosed ts

 showEnclosed [t@(F x _)] n | x `elem` words "[] {}" = showImpl t n
 showEnclosed [t] n = (enclose st,k+2)  where (st,k)  = showImpl t $ n+1
 showEnclosed ts n  = (enclose sts,k+2) where (sts,k) = showTerms ts $ n+1

-- FLOWGRAPH ANALYSIS

 data Flow a = In (Flow a) a | Assign String TermS (Flow a) a | 
	       Ite TermS (Flow a) (Flow a) a | Fork [Flow a] a |
	       Atom a | Neg (Flow a) a | Comb Bool [Flow a] a | 
	       Mop Bool TermS (Flow a) a | Fix Bool (Flow a) a | Pointer [Int]
 
 parseFlow :: Sig -> TermS -> (TermS -> Maybe a) -> Maybe (Flow a)
 parseFlow sig t parseVal = f t
            where f (F "enter" [u,val])      = do g <- f u; val <- parseVal val
    					          Just $ In g val
 	          f (F "assign" [F ":=" [V x,e],u,val]) 
	 			             = do g <- f u; val <- parseVal val
					          Just $ Assign x e g val
                  f (F "cond" [c,u1,u2,val]) = do g1 <- f u1; g2 <- f u2
					          val <- parseVal val
						  Just $ Ite c g1 g2 val
	          f (F "fork" ts@(_:_))      = do gs <- mapM f $ init ts
		                                  val <- parseVal $ last ts
						  Just $ Fork gs val
 	          f (F "not" [u,val])        = do g <- f u; val <- parseVal val
	 				          Just $ Neg g val
 	          f (F "\\/" ts@(_:_))       = do gs <- mapM f $ init ts
		    	                          val <- parseVal $ last ts
						  Just $ Comb True gs val
 	          f (F "/\\" ts@(_:_))       = do gs <- mapM f $ init ts
		    	                          val <- parseVal $ last ts
						  Just $ Comb False gs val
 	          f (F "<>" [lab,u,val])     = do g <- f u; val <- parseVal val
					          guard $ lab == noLab ||
						  	  lab `elem` sig.labels
						  Just $ Mop True lab g val
 	          f (F "#" [lab,u,val])      = do g <- f u; val <- parseVal val
					          guard $ lab == noLab ||
						  	  lab `elem` sig.labels
						  Just $ Mop False lab g val
 	          f (F "MU" [u,val])         = do g <- f u; val <- parseVal val
					          Just $ Fix True g val
 	          f (F "NU" [u,val])         = do g <- f u; val <- parseVal val
					          Just $ Fix False g val
 	          f (V x) | isPos x          = do guard $ q `elem` positions t
				                  Just $ Pointer q
					       where q = getPos x
 	          f val 		     = do val <- parseVal val
	    				   	  Just $ Atom val
	   
 isFlowNode x = x `elem` words "enter assign cond fork not \\/ /\\ <> # MU NU"

-- fixPositions t returns all MU- resp. NU-positions p of t.

 fixPositions (F x [t,_]) | isFixF x  = []:map (0:) (fixPositions t)
 fixPositions (F x ts) | isFlowNode x = liftPoss fixPositions $ init ts
 fixPositions _                       = []

-- valPositions t returns the value positions of flowtree nodes of t.

 valPositions (F x ts) | isFlowNode x = [last $ indices_ ts]:f (init ts) 
 		       | True         = f ts where f = liftPoss valPositions
 valPositions _       		      = []

 widgPositions (F x ts) | x == "widg" = [last $ indices_ ts]:f (init ts)
		        | True        = f ts where f = liftPoss widgPositions
 widgPositions _                      = []
 
-- getVal g p returns the value at the first non-pointer position of g that is
-- reachable from p.

 getVal :: Flow a -> [Int] -> (a,[Int])
 getVal f p = h f p p where h (In g _) (0:p) q	       = h g p q
	                    h (In _ val) _ q 	       = (val,q)
		            h (Atom val) _ q 	       = (val,q)
		            h (Assign _ _ g _) (1:p) q = h g p q
		            h (Assign _ _ _ val) _ q   = (val,q)
		            h (Ite _ g _ _) (1:p) q    = h g p q
			    h (Ite _ _ g _) (2:p) q    = h g p q
			    h (Ite _ _ _ val) _ q      = (val,q)
			    h (Fork gs _) p@(_:_) q    = h' gs p q
			    h (Fork _ val) _ q	       = (val,q)
			    h (Neg g _) (0:p) q        = h g p q
			    h (Neg _ val) _ q	       = (val,q)
			    h (Comb _ gs _) p@(_:_) q  = h' gs p q
			    h (Comb _ _ val) _ q       = (val,q)
			    h (Mop _ _ g _) (1:p) q    = h g p q
			    h (Mop _ _ _ val) _ q      = (val,q)
			    h (Fix _ g _) (0:p) q      = h g p q
			    h (Fix _ _ val) _ q	       = (val,q)
			    h (Pointer p) _ _          = h f p p
			    h' (g:_) (0:p)  = h g p
			    h' (_:gs) (n:p) = h' gs ((n-1):p)
 
 progVars (In g _)         = progVars g
 progVars (Assign x _ g _) = progVars g `join1` x
 progVars (Ite _ g1 g2 _)  = progVars g1 `join` progVars g2
 progVars (Fork gs _)      = joinMap progVars gs
 progVars flow		   = []
	 
-- global model checking of state formulas (backward analysis)

 initStates :: Sig -> TermS -> Maybe TermS
 initStates sig = f
     where sts = mkList sig.states
           f (F "MU" [t])       = do t <- f t; Just $ F "MU" [t,mkNil]
           f (F "NU" [t])       = do t <- f t; Just $ F "NU" [t,sts]
           f (t@(V x))	        = do guard $ isPos x; Just t
           f (F "EX" [t])       = do t <- f t; Just $ F "<>" [noLab,t,mkUndef]
           f (F "AX" [t])       = do t <- f t; Just $ F "#" [noLab,t,mkUndef]
           f (F x [lab,t]) | x `elem` words "<> #" 
			        = do guard $ just $ search (== lab) sig.labels
	                             t <- f t; Just $ F x [lab,t,mkUndef]
           f (F x ts) | x `elem` words "not \\/ /\\"
			        = do ts <- mapM f ts; Just $ F x $ ts++[mkUndef]
	   f (F "true" [])      = Just sts
           f (F "false" [])     = Just mkNil
	   f at                 = do i <- search (== at) sig.atoms
	                             Just $ mkList $ map (sig.states!!) 
	                             		   $ sig.value!!i

 evalStates :: Sig -> Flow TermS -> [[Int]] -> (Flow TermS,Bool)
 evalStates sig flow ps = up [] flow
  where up p (Neg g val) 
             | val1 == mkUndef || any (p<<) ps = (Neg g1 val, b)
	     | True = if null ps then (Atom val2, True)
	     			 else (Neg g1 val2, b || val /= val2)
		          where q = p++[0]; (g1,b) = up q g
			        val1 = fst $ getVal flow q
		                val2 = mkList $ sig.states `minus` subterms val1
        up p (Comb c gs val)
             | any (== mkUndef) vals || any (p<<) ps = (Comb c gs1 val, or bs)
 	     | True = if null ps then (Atom val1, True)
	     			 else (Comb c gs1 val1, or bs || val /= val1)
		      where qs = succsInd p gs
		            (gs1,bs) = unzip $ zipWith up qs gs
			    vals = map (fst . getVal flow) qs
			    val1 = mkList $ foldl1 (if c then join else meet) 
			    		  $ map subterms vals
        up p (Mop c lab g val)
             | val1 == mkUndef || any (p<<) ps = (Mop c lab g1 val, b)
	     | True = if null ps then (Atom val2, True)
	     			 else (Mop c lab g1 val2, b || val /= val2)
		      where q = p++[1]; (g1,b) = up q g
			    val1 = fst $ getVal flow q
			    f True = shares; f _ = flip subset
			    val2 = mkList $ filter (f c (subterms val1) . h) 
			    		    sig.states
			    h st = map (sig.states!!) $ tr i
				   where i = get $ search (== st) sig.states
			    tr i = if lab == noLab then sig.trans!!i
		                   else sig.transL!!i!! get (search (== lab) 
				   				    sig.labels)
        up p (Fix c g val)
             | val1 == mkUndef || any (p<<) ps = (Fix c g1 val, b)
             | True = if f c subset valL val1L 
	              then if not b && p `elem` ps then (Atom val, True)
		      			           else (Fix c g1 val, b)
			   else (Fix c g1 $ mkList $ h c valL val1L, True)
		      where f True = flip; f _ = id
		     	    h True = join; h _ = meet
		     	    q = p++[0]; (g1,b) = up q g
			    val1 = fst $ getVal flow q
			    valL = subterms val; val1L = subterms val1
	up _ g = (g,False)

-- verification of postconditions (backward-all analysis)
 
 initPost :: TermS -> TermS
 initPost (F x ts) | x `elem` words "enter assign fork cond"
	    = F x (map initPost ts++[F "bool" [mkTrue]])
 initPost t = t

 evalPost :: (TermS -> TermS) -> Flow TermS -> (Flow TermS,Bool)
 evalPost simplify flow = up [] flow
   where up p (In g val) = (In g1 val1, b1 || neqTerm val val1)
 		             where q = p++[0]
		                   (g1,b1) = up q g
			           val1 = f q
         up p (Assign x e g val) = (Assign x e g1 val2, b1 || b2)
	  	             where q = p++[1]
		                   (g1,b1) = up q g
			           val1 = f q
				   (val2,b2) = mkMeet val $ val1>>>(e`for`x)
         up p (Ite c g1 g2 val) = (Ite c g3 g4 val3, b1 || b2 || b3)
	                     where q1 = p++[1]; q2 = p++[2]
		                   (g3,b1) = up q1 g1; (g4,b2) = up q2 g2
			           val1 = f q1; val2 = f q2
			           c1 = mkDisjunct [simplify c,val1]
			           c2 = mkDisjunct [c,val2]
				   (val3,b3) = mkMeet val $ mkConjunct [c1,c2]
         up p (Fork gs val) = (Fork gs1 val1, or bs || b)
 		             where qs = succsInd p gs
		                   (gs1,bs) = unzip $ zipWith up qs gs
		                   (val1,b) = mkMeet val $ mkConjunct $ map f qs
         up _ g = (g,False)
	 f = fst . getVal flow
         mkMeet val val' = if isTrue $ simplify $ mkImpl val val'
	                   then (val,False) 
	                   else (simplify $ mkConjunct [val,val'],True)

-- computation of program states (forward-any analysis)

 initSubs :: TermS -> TermS
 initSubs (F "in" [t]) = F "in" [initSubs t,mkList [mkNil]]
 initSubs (F x ts) | x `elem` words "assign ite fork con"
		       = F x (map initSubs ts++[mkNil])
 initSubs t	       = t

 evalSubs :: (TermS -> TermS) -> Flow [SubstS] -> [String] 
 					       -> (Flow [SubstS],Bool)
 evalSubs simplify flow xs = down flow False [] flow
   where down flow b p (In g val) = down flow1 (b || b1) q g
 	              where q = p++[0]
	                    (flow1,b1) = change flow q val
	 down flow b p (Assign x e g val) = down flow1 (b || b1) q g
	      	      where q = p++[1]
		            (flow1,b1) = change flow q $ map f val
		   	    f state = upd state x $ simplify $ e>>>state
         down flow b p (Ite c g1 g2 val) = down flow3 b3 q2 g2
	           where q1 = p++[1]; q2 = p++[2]
		   	 (flow1,b1) = change flow q1 $ filter (isTrue . f) val
		   	 (flow2,b2) = change flow1 q2 $ filter (isFalse . f) val
		   	 f = simplify . (c>>>)
	           	 (flow3,b3) = down flow2 (b || b1 || b2) q1 g1
         down flow b p (Fork gs val) = fold2 h (foldl f (flow,b) qs) qs gs
 	               where qs = succsInd p gs
		             f (flow,b) q = (flow1, b || b1)
			                    where (flow1,b1) = change flow q val
 		             h (flow,b) q g = down flow b q g
         down flow b _ _ = (flow,b)
         change g p val = if subSubs xs val oldVal then (g,False) 
	                                           else (rep g q,True)
                   where (oldVal,q) = getVal g p
		         newVal = joinSubs xs val oldVal
		         rep (In g val) (0:p)         = In (rep g p) val
 	                 rep (In g val) _             = In g newVal
  	 	         rep (Atom _) _	              = Atom newVal
 	                 rep (Assign x e g val) (1:p) = Assign x e (rep g p) val
 	                 rep (Assign x e g _) _       = Assign x e g newVal
 	 		 rep (Ite c g1 g2 val) (1:p)  = Ite c (rep g1 p) g2 val
 	                 rep (Ite c g1 g2 val) (2:p)  = Ite c g1 (rep g2 p) val
 	 	         rep (Ite c g1 g2 _) _        = Ite c g1 g2 newVal
 	 		 rep (Fork gs val) p@(_:_)    = Fork (rep' gs p) val
 	 		 rep (Fork gs _) _            = Fork gs newVal
	                 rep' (g:gs) (0:p)            = rep g p:gs
 	 		 rep' (g:gs) (n:p)            = g:rep' gs ((n-1):p)

-- TERM PARSER into Haskell types

 parseBins t = do s <- parseList (parse quoted . root) t
		  guard $ notnull s && allEqual (map length s) && 
		          all (all (`elem` "01#")) s	
	          Just s

 parseBool (F "0" []) = Just False
 parseBool t 	      = do F "1" [] <- Just t; Just True

 parseChar t          = do F [c] [] <- Just t; Just c

 parseConst t         = do F a [] <- Just t; Just a

 parseConsts          = parseList' parseConst

 parseConstTerms t    = do F "()" [c,ts] <- Just t
 		           c <- parseConst c; Just (c,parseTerms ts)

 parseConsts2 t       = do F "()" [cs,ds] <- Just t; cs <- parseConsts cs
 		           ds <- parseConsts ds; Just (cs,ds)

 parseConsts3 t       = do F "()" [cs,ds,es] <- Just t; cs <- parseConsts cs
 		           ds <- parseConsts ds; es <- parseConsts es
			   Just (cs,ds,es)

 parseConsts2Term t   = do F "()" [cs,ds,t] <- Just t; cs <- parseConsts cs
 			   ds <- parseConsts ds; Just (cs,ds,t)

 parseConsts2Terms t  = do F "()" [cs,ds,ts] <- Just t; cs <- parseConsts cs
 			   ds <- parseConsts ds; Just (cs,ds,getTerms ts)

 parseTerms (F x ts) | collector x = map showTerm0 ts
 parseTerms t		           = [showTerm0 t]

 getTerms (F x ts) | collector x   = ts
 getTerms t		           = [t]

 parseList parser t  = do F "[]" ts <- Just t; mapM parser ts

 parseList' parser t = parseList parser t ++ do a <- parser t; Just [a]

 parseColl parser t  = do F x ts <- Just t; guard $ collector x; mapM parser ts
 
 parseWords cw 	     = do cw <- parseConst cw; Just $ words cw

 parseNat t    	     = do a <- parseConst t; parse nat a
 
 parsePnat t   	     = do a <- parseConst t; parse pnat a
 
 parseInt t    	     = do a <- parseConst t; parse int a
 
 parseReal t   	     = do a <- parseConst t; parse real a
 
 parseDouble t 	     = do a <- parseConst t; parse double a

 parseNats     	     = parseList parseNat

 parseInts     	     = parseList' parseInt

 parseReals    	     = parseList' parseReal

 parseIntQuad t      = do F "()" [i,j,b,h] <- Just t; i <- parseInt i
 		          j <- parseInt j; b <- parseInt b; h <- parseInt h
		          Just (i,j,b,h)

 parseRealReal t     = do F "()" [r,s] <- Just t; r <- parseReal r
 			  s <- parseReal s; Just (r,s)

 parseRealPair t     = do F "()" [p,r] <- Just t; p <- parseRealReal p
 		          r <- parseReal r; Just (p,r)

 parseColor      = parse color . root

 parseRenaming r = do r <- mapM f r; Just $ fold2 upd id (map fst r) $ map snd r
		   where f t = do F "=" [V x,V y] <- Just t; Just (x,y)

 parseSubs       = parseList parseSub 
                   where parseSub s = do s <- parseList parseEq s
	   			         let (xs,ts) = unzip s
				         Just $ forL ts xs
		         parseEq t = do F "=" [V x,t] <- Just t; Just (x,t)

-- parseLinEqs recognizes conjunctions of linear equations. 

 parseLinEqs :: TermS -> Maybe [LinEq]
 parseLinEqs (F "&" ts) = mapM parseLinEq ts                                    
 parseLinEqs t          = do eq <- parseLinEq t; Just [eq]       

 parseLinEq :: TermS -> Maybe LinEq
 parseLinEq t = do F "=" [t,u] <- Just t; ps <- parseProds t; b <- parseReal u
 		   Just (ps,b)
 
 parseLin :: TermS -> Maybe LinFun
 parseLin (F "lin" [F "+" [t,u]]) | just b = do ps <- parseProds t
 					        Just (ps,get b)
				             where b = parseReal u
 parseLin (F "lin" [F "-" [t,u]]) | just b = do ps <- parseProds t
 			                        Just (ps,-get b)
				             where b = parseReal u
 parseLin t = do F "lin" [t] <- Just t; ps <- parseProds t; Just (ps,0)

 parseProds (F "+" [ts,t]) = do ps <- parseProds ts; p <- parseProd t
                                Just (ps++[p])
 parseProds (F "-" [ts,t]) = do ps <- parseProds ts; (a,x) <- parseProd t
			        Just (ps++[(-a,x)])
 parseProds t              = do p <- parseProd t; Just [p]

 parseProd (F "*" [t,V x]) = do a <- parseReal t; guard $ a /= 0; Just (a,x)
 parseProd (F "-" [V x])   = Just (-1,x)
 parseProd t 		   = do V x <- Just t; Just (1,x)

 parseRel sts t = do F "rel" [t] <- Just t
 		     rels <- parseList f t
 		     Just $ concat rels
		  where f (F "()" [t,F "[]" ts]) | (t:ts) `subset` sts  
		            = Just $ map (\u -> (t,u)) ts
			f t = do F "()" [t,u] <- Just t
 		                 guard $ t `elem` sts && u `elem` sts
				 Just [(t,u)]

-- SIGNATURES, HORN and CO-HORN CLAUSES

 iniPreds = words "_ () [] : ++ $ . == -> -/-> ~/~ <= >= < > >> true false" ++
 	    words "not /\\ \\/ `then` EX AX # <> nxt all any allany And Or" ++
	    words "disjoint filter filterL flip foldl foldr foldr1 `in`" ++
	    words "`NOTin` Nat Int Real List INV map null NOTnull nxt pred" ++
	    words "reduced `shares` `NOTshares` `sats` single `subset`" ++
	    words "prodL `NOTsubset` subst Value zipWith Not lsection rsection"
	    
 iniDefuncts = words "_ $ . ; + ++ - * ** / !! auto bag bisim branch color" ++
               words "concat count curry dnf drop filter filterL flip foldl" ++
	       words "foldr head height id init insert `join` last length" ++
	       words "list map max `meet` min minimize `mod` nextPerm obdd" ++
	       words "parse permute prodE prodL product reverse set shuffle" ++
	       words "sum tail trans transL tup uncurry upd value valueR" ++
	       words "valueL valueLR zip zipWith lsection rsection"

 iniSymbols = (">>":iniPreds, ["~"], words "() [] : 0 lin suc", iniDefuncts, 
 	       [], [])

 data Sig = Sig { isPred
                , isCopred
                , isConstruct
                , isDefunct
                , isFovar
                , isHovar
                , blocked     :: String -> Bool
                , hovarRel    :: BoolFun String
                , simpls
                , transitions :: [Simplification]
                , states
                , atoms
                , labels      :: [TermS]
                , trans
                , value       :: [[Int]]
                , transL
                , valueL      :: [[[Int]]]
                , safeEqs     :: Bool
                }

 predSig preds = Sig { isPred = (`elem` preds)
                     , isCopred = \_ -> False
                     , isConstruct = \_ -> False
                     , isDefunct = \_ -> False
                     , isFovar = \_ -> False
                     , isHovar = \_ -> False
                     , blocked = \_ -> False
                     , hovarRel = \_ _ -> False
                     , simpls = []
                     , transitions = []
                     , states = []
                     , atoms = []
                     , labels = []
                     , trans = []
                     , transL = []
                     , value = []
                     , valueL = []
                     , safeEqs = False
                     }

 emptySig = predSig []

 isSum (F "<+>" _)   = True
 isSum _ 	     = False

 isZero (F "0" [])   = True
 isZero (F "0.0" []) = True
 isZero _            = False

 isOne (F "1" [])    = True
 isOne (F "1.0" [])  = True
 isOne _             = False
  
 lambda x  	  = x `elem` words "fun rel"

 leader "" _      = False
 leader x y  	  = head (words x) == y
 
 binder   	  = isQuant ||| isFix
 
 isQuant x   	  = leader x "All" || leader x "Any"
 
 isFix            = isFixT ||| isFixF
 
 isFixT x     	  = leader x "mu" || leader x "nu"
 
 isFixF x    	  = leader x "MU" || leader x "NU"
 
 mkBinder op xs t = F (op ++ ' ':unwords (mkSet xs)) [t]

 functional sig x = sig.isConstruct x || sig.isDefunct x
 
 isBeq            = just . parse equivalence
 
 isNBeq           = just . parse inequivalence

 declaredRel sig x = sig.isPred x || sig.isCopred x || x == "=" || x == "=/="

 relational sig x = declaredRel sig x || isFixF x || x == "rel"
		    
 onlyRel sig x    = relational sig x && x `notElem` words "() [] : ++ $ ."

 implicational x  = x `elem` words "==> <==> ===> <==="
 
 boolean x 	  = implicational x || x `elem` words "| &"
 
 logical x        = boolean x || x `elem` words "True False Not" || isQuant x ||
 		    isFixF x

 isValue sig  = andT $ sig.isConstruct ||| (`elem` (words "^ {} $")) ||| isPos

 isNormal sig = andT $ sig.isConstruct ||| (`elem` (words "^ {} $")) ||| isPos
 		                       ||| isVar sig

 isFormula sig t@(F x ts) = case parse colPre x of 
			         Just (_,x) -> isFormula sig $ F x ts
			         _ -> logical x || isAtom sig t
 isFormula _ _		  = False

 isTerm sig = not . isFormula sig

 isAtom sig = relational sig . getOp
 
 isOnlyAtom sig = onlyRel sig . getOp

 getOp (F "$" [t,_]) = getOp t
 getOp t             = root t

 getOpArgs t = (getOp t,getArgs t)

 getArgs (F "$" [_,t]) = case t of F "()" ts -> ts; _ -> [t]
 getArgs (F _ ts)      = ts
 getArgs t	       = []

 updArgs (F "$" [t,_]) us = applyL t us
 updArgs (F x _) us       = F x us
 updArgs t _              = t

-- unCurry (f(t1)...(tn)) returns (f,[t1,...,tn]). unCurry is used by 
-- turnIntoUndef (see below), flatCands and (pre)Stretch(Conc/Prem) 
-- (see Esolve).

 unCurry (F "$" [t,u]) = (x,tss++[ts]) where (x,tss) = unCurry t
			      		     ts = case u of F "()" us -> us
					     		    _ -> [u]
 unCurry (F x ts)      = (x,[ts])
 unCurry t	       = (root t,[[]])

 getOpSyms (F "$" [t,_]) = foldT f t where f x xss = x:concat xss
 getOpSyms _             = []

 getHead (F "<===" [t,_]) = t
 getHead (F "===>" [t,_]) = t
 getHead t                = t

 getBody (F "<===" [_,t]) = t
 getBody (F "===>" [_,t]) = t
 getBody t                = t

 quantConst x (F y []) 		      = x == y
 quantConst x (F ('A':'n':'y':_) [t]) = quantConst x t
 quantConst x (F ('A':'l':'l':_) [t]) = quantConst x t
 quantConst _ _                       = False

 isTup (F "()" _) = True
 isTup _          = False

 isList (F "[]" _) = True
 isList _          = False

 isTrue (F "bool" [t]) = isTrue t
 isTrue (F "True" [])  = True
 isTrue _              = False

 isFalse (F "bool" [t]) = isFalse t
 isFalse (F "False" []) = True
 isFalse _              = False

 isImpl (F "==>" _) = True
 isImpl _ 	    = False

 isQDisjunct (F ('A':'l':'l':_) [t]) = isDisjunct t
 isQDisjunct t 		             = isDisjunct t

 isDisjunct (F "|" _) = True
 isDisjunct _ 	      = False

 isQConjunct (F ('A':'n':'y':_) [t]) = isConjunct t
 isQConjunct t 		             = isConjunct t

 isConjunct (F "&" _) = True
 isConjunct _         = False

 isProp = isDisjunct ||| isConjunct

 unconditional (F "<===" _) = False
 unconditional (F "===>" _) = False
 unconditional _            = True
 
 isEquiv (F "==" [_,_])   = True
 isEquiv (F "<==>" [_,_]) = True
 isEquiv _                = False
	        
 isHorn sig (F "<===" [t,_]) = isHorn sig t
 isHorn sig (F "=" [t,_])    = sig.isDefunct $ getOp t
 isHorn sig t 	             = sig.isPred $ getOp t
 isHorn _ _    	             = False

 isCoHorn sig (F "===>" [t,_]) = sig.isCopred $ getOp t
 isCoHorn _ _    	       = False
 
 isTaut (F "<===" [F "False" _,_]) = True
 isTaut (F "===>" [F "True"  _,_]) = True
 isTaut _                          = False
 
 mergeWithGuard (F "==>" [t,F "<===" [u,v]]) = mkHorn u $ mkConjunct [t,v]
 mergeWithGuard (F "==>" [t,F "===>" [u,v]]) = mkCoHorn u $ mkImpl t v
 mergeWithGuard t 			     = t

 isGuarded f (F "==>" [_,cl]) = f cl
 isGuarded f cl               = f cl

 isAxiom sig = isGuarded $ isEquiv ||| isHorn sig ||| isCoHorn sig

 isTheorem = isHornT ||| isCoHornT ||| noQuantsOrConsts

 isHornT (F "<===" [t,_]) = noQuantsOrConsts t
 isHornT t                = noQuantsOrConsts t

 isCoHornT (F "===>" [t,_]) = noQuantsOrConsts t
 isCoHornT _                = False

 noQuantsOrConsts (F "True" _)          = False
 noQuantsOrConsts (F "False" _)         = False
 noQuantsOrConsts (F ('A':'n':'y':_) _) = False
 noQuantsOrConsts (F ('A':'l':'l':_) _) = False
 noQuantsOrConsts (F _ ts)              = all noQuantsOrConsts ts
 noQuantsOrConsts _                     = True

 isDisCon (F "<===" [F "|" _,_]) = True
 isDisCon (F "<===" [F "&" _,_]) = True
 isDisCon (F "===>" [F "|" _,_]) = True
 isDisCon (F "===>" [F "&" _,_]) = True
 isDisCon (F "|" _)              = True
 isDisCon (F "&" _)              = True
 isDisCon _                      = False
 
-- copyRedex is used by applyTheorem (see Ecom).

 copyRedex (F "==>" [guard,u]) = mkImpl guard $ copyRedex u
 copyRedex (F "===>" [t,u])    = mkCoHorn t $ mkConjunct [t,u]
 copyRedex (F "<===" [t,u])    = mkHorn t $ mkDisjunct [t,u]
 copyRedex t 	               = mkHorn t t

 noOfComps (F "<===" [t,_]) = length $ subterms t
 noOfComps (F "===>" [t,_]) = length $ subterms t
 noOfComps t                = length $ subterms t
 
 makeLambda sig cl p = 
       case (cl,p) of (F "==>" [F "&" cs,F x [l,r]],[0,i,1])
    		        -> do guard $ i < length cs && rel x && xs `disjoint` zs
		              Just $ mkImpl (mkConjunct ds) (F x [l,app r arg])
		           where arg = getSubterm cl [0,i,0]
			         ds = context i cs
				 zs = freesL sig $ arg:ds
	              (F "==>" [c,F x [l,r]],[0,1])
    		        -> do guard $ rel x && xs `disjoint` frees sig arg
		              Just $ F x [l,app r arg]
		           where arg = getSubterm cl [0,0]
	              (F "==>" [c,F x [l,r]],[1,0])
    		        -> do guard $ rel x; Just $ mkImpl c $ at x l pars r
			   where (op,pars) = getOpArgs l 
	              (F x [l,r],[0])
    		        -> do guard $ rel x; Just $ at x l pars r
			   where (op,pars) = getOpArgs l 
		      _ -> Nothing
       where rel x = x `elem` words "= == ->"
             par = getSubterm cl p
             xs = frees sig par	     
	     app r = apply $ F "fun" [par,r]
	     removePars (F "$" [t,_]) = t
	     removePars (F op _)      = F op []
	     removePars t             = t
	     at x l pars r = F x [removePars l,F "fun" [mkTup pars,r]]
					 
 noSimplsFor xs = filter f where f (F "==>" [_,cl])  = f cl
			         f (F "===>" [at,_]) = f at
			         f (F "<===" [at,_]) = f at
			         f (F "<==>" _)      = False
			         f (F "==" _)        = False
			         f (F "=" [t,_])     = any (`isin` t) xs
			         f at                = any (`isin` at) xs

 clausesFor xs = filter f where f (F "==>" [_,cl])  = f cl
			        f (F "===>" [at,_]) = f at
				f (F "<===" [at,_]) = f at
				f (F "<==>" [at,_]) = f at
				f (F "==" [t,_])    = any (`isin` t) xs
				f (F "=" [t,_])     = any (`isin` t) xs
				f at                = any (`isin` at) xs

-- filterClauses sig redex filters the axioms/theorems that may be applicable to
-- redex. filterClauses is used by applyLoop/Random, getRel, getFun
-- (see Esolve), narrowPar and rewritePar (see Ecom).

 filterClauses sig redex = filter f 
             where f ax = (isAxiom sig ||| isTheorem) ax &&
		          any (flip any (anchors ax) . g) (anchors redex)
		   g x = (x ==) ||| h x ||| flip h x
	           h x y = sig.isFovar x || sig.hovarRel x y 
		   anchors (F "==>" [_,cl]) = anchors cl
		   anchors (F x [t,_]) | x `elem` words "===> <=== = == <==> ->"
		   			    = anchors t
		   anchors (F "^" ts)       = concatMap anchors ts
		   anchors t 		    = [getOp t]
						  
-- turnIntoUndef recognizes a non-rewritable/narrowable first order term/atom u 
-- and is used by applyLoop/Random (see Esolve).

 turnIntoUndef :: Sig -> TermS -> [Int] -> TermS -> Maybe TermS
 
 turnIntoUndef sig t p redex =
 	 do guard $ isF redex && and (map (all $ isNormal sig) tss)
            if x `notElem` iniPreds && sig.isPred x then Just mkFalse
            else if sig.isCopred x then Just mkTrue
                 else do guard $ c || x `notElem` iniDefuncts && sig.isDefunct x
	                 Just mkUndef
         where (x,tss) = unCurry redex
	       c = notnull p && root (getSubterm t $ init p) == "->"
	 
-- GENERATORS of terms
 
 leaf :: String -> TermS
 leaf a = F a []

 mkStrPair :: (String,String) -> TermS
 mkStrPair (a,b) = mkTup $ map leaf [a,b]

 mkStrLPair :: ([String],[String]) -> TermS
 mkStrLPair (as,bs) = mkTup $ map leaves [as,bs]

 leaves :: [String] -> TermS
 leaves = mkList' . map leaf

 mkZero = F "0" []
 mkOne  = F "1" []

 mkConst a = F (show a) []
 
 jConst :: Show a => a -> Maybe TermS
 jConst  = Just . mkConst

 jConsts :: Show a => [a] -> Maybe TermS
 jConsts = Just . mkConsts
 
 jList :: [TermS] -> Maybe TermS
 jList = Just . mkList

 mkConstPair (a,b) = mkPair (mkConst a) $ mkConst b

 mkConsts :: Show a => [a] -> TermS
 mkConsts = mkList . map mkConst
 
 mkSuc t = F "suc" [t]
 
 mkPair t u = F "()" [t,u]
  
 mkUndef = mkTup []

 mkTup [t] = t
 mkTup ts  = F "()" ts
 
 mkList = F "[]"
  
 mkNil = mkList []

 mkList' [a] = a
 mkList' as  = mkList as
 
 noLab = F "noLab" []
  
 mkGets :: [a] -> TermS -> [TermS]
 mkGets xs t = case xs of [_] -> [t]; _ -> map f $ indices_ xs
	       where f i = F ("get"++show i) [t]

 mkLin (ps,b) = F "lin" [if b < 0 then F "-" [mkProds ps,mkConst $ -b]
 		                  else if b == 0 then mkProds ps
			 	       else F "+" [mkProds ps,mkConst b]]

 mkLinEqs eqs = F "&" $ map mkLinEq eqs
 		where mkLinEq (ps,b) = F "=" [mkProds ps,mkConst b]

 mkProds [p]         = mkProd p
 mkProds ps | a < 0  = F "-" [mkProds qs,mkProd (-a,x)]
            | True   = F "+" [mkProds qs,mkProd p]
                       where (qs,p@(a,x)) = (init ps,last ps)

 mkProd (a,x) | a == 1  = V x
              | a == -1 = F "-" [V x]
              | True    = F "*" [mkConst a,V x]

-- mkFlow computes the term representation of a flowtree

 mkFlow :: Sig -> Flow a -> (a -> TermS) -> TermS
 mkFlow sig flow mkVal = f flow
    where f (In g val)         = F "enter" [f g, mkVal val]
 	  f (Assign x e g val) = F "assign" [F ":=" [V x,e],f g,mkVal val]
	  f (Ite c g1 g2 val)  = F "cond" [c,f g1,f g2,mkVal val]
	  f (Fork gs val)      = F "fork" $ map f gs++[mkVal val]
	  f (Atom val)	       = mkVal val
	  f (Neg g val)        = F "not" [f g,mkVal val]
	  f (Comb b gs val)    = F (if b then "\\/" else "/\\") $ map f gs ++
	  							  [mkVal val]
          f (Mop b lab g val)  = F (if b then "<>" else "#") [lab,f g,mkVal val]
	  f (Fix b g val)      = F (if b then "MU" else "NU") [f g,mkVal val]
          f (Pointer p)	       = mkPos p

-- mkRelConsts/I rel returns the representation of a binary relation rel as a 
-- list of type [TermS]. mkRelConsts is used by showRelation (see Ecom).

 mkRelConsts :: Pairs String -> [TermS]
 mkRelConsts = map g where g (a,[b]) = mkTup [leaf a,leaf b]
                           g (a,bs)  = mkPair (leaf a) $ leaves bs

 mkRelConstsI :: [String] -> [String] -> [[Int]] -> [TermS]
 mkRelConstsI as bs = zipWith f [0..]
 	              where f i [k] = mkPair (g i) $ leaf $ bs!!k
			    f i ks  = mkPair (g i) $ leaves $ map (bs!!) ks
			    g i = leaf $ as!!i

-- mkRel2Consts/I f dom returns the representation of a ternary relation as a 
-- list of type [TermS]. mkRel2Consts is used by matrix (see Epaint) and 
-- showList_ (see Ecom).

 mkRel2Consts :: [(String,String,[String])] -> [TermS]
 mkRel2Consts = map g where g (a,b,[c]) = mkTup $ map leaf [a,b,c]
 	                    g (a,b,cs)  = mkTup [leaf a,leaf b,leaves cs]
			    
 mkRel2ConstsI :: [String] -> [String] -> [String] -> [[[Int]]] -> [TermS]
 mkRel2ConstsI as bs cs = concat . zipWith f [0..]
	    where f i = zipWith g [0..]
    		        where g j [k] = mkTup [h1 i,h2 j,leaf $ cs!!k]
			      g j ks  = mkTup [h1 i,h2 j,leaves $ map (cs!!) ks]
			      h1 i = leaf $ as!!i
			      h2 i = leaf $ bs!!i
			      
 evenNodes (F x ts) = x:concatMap oddNodes ts
 evenNodes (V x)    = if isPos x then [] else [x]
 evenNodes _        = []

 oddNodes (F x ts) = concatMap evenNodes ts
 oddNodes _        = []

 mkSum []  = mkUndef
 mkSum [t] = t
 mkSum ts  = case mkTerms (F "<+>" ts) of [] -> mkUndef; [t] -> t
	                                  ts  -> F "<+>" ts

 mkTerms (F "<+>" ts) = joinTermMap mkTerms $ removeUndef ts
 mkTerms t            = removeUndef [t]

 removeUndef (F "()" []:ts) = removeUndef ts
 removeUndef (t:ts) 	    = t:removeUndef ts
 removeUndef _		    = []

 mkBag []  = mkNil
 mkBag [t] = t
 mkBag ts  = case mkElems (F "^" ts) of [t] -> t; ts  -> F "^" ts

 mkElems (F "^" ts) = concatMap mkElems ts
 mkElems t          = [t]

 mkApplys (x,[])   = V x
 mkApplys (x,[ts]) = F x ts
 mkApplys (x,tss)  = applyL (mkApplys (x,init tss)) $ last tss

-- GENERATORS of formulas

 mkComplSymbol "="                 = "=/="
 mkComplSymbol "->"                = "-/->"
 mkComplSymbol "-/->"              = "->"
 mkComplSymbol "=/="		   = "="
 mkComplSymbol "<="		   = ">"
 mkComplSymbol ">="		   = "<"
 mkComplSymbol "<"		   = ">="
 mkComplSymbol ">"		   = "<="
 mkComplSymbol x | just str        = "~/~"++tail (get str)
			             where str = parse equivalence x
 mkComplSymbol x | just str        = '~':drop 3 (get str)
			             where str = parse inequivalence x				     
 mkComplSymbol ('`':'n':'o':'t':x) = '`':x
 mkComplSymbol ('`':'N':'O':'T':x) = '`':x
 mkComplSymbol ('`':x@(c:_))       = if isLower c then "`NOT"++x else "`not"++x
 mkComplSymbol ('n':'o':'t':x)     = x
 mkComplSymbol ('N':'O':'T':x)     = x
 mkComplSymbol x@(c:_)             = if isLower c then "NOT"++x else "not"++x
 mkComplSymbol x                   = x

 complOccurs ts = forsomeThereis (eqTerm . F "Not" . single) ts ts

 mkTrue  = F "True" []
 mkFalse = F "False" []

 mkNot _ t | quantConst "True" t   = mkFalse
 mkNot _ t | quantConst "False" t  = mkTrue
 mkNot _ (F "Not" [t])		   = t
 mkNot sig (F "==>" [t,u])	   = mkConjunct [t,mkNot sig u]
 mkNot sig (F "|" ts)		   = mkConjunct $ map (mkNot sig) ts
 mkNot sig (F "&" ts)		   = mkDisjunct $ map (mkNot sig) ts
 mkNot sig (F ('A':'n':'y':x) [t]) = mkAll (words x) $ mkNot sig t
 mkNot sig (F ('A':'l':'l':x) [t]) = mkAny (words x) $ mkNot sig t
 -- mkNot sig (F "$" [t,u])           = F "$" [mkNot sig t,u]
 mkNot sig (F x ts) | declaredRel sig z && not (sig.isHovar x)
 				   = F z ts where z = mkComplSymbol x
 mkNot _ t             	           = F "Not" [t]

 mkImpl t u | quantConst "True" t  = u
 	    | quantConst "False" t = mkTrue
	    | quantConst "True" u  = mkTrue
	    | quantConst "False" u = F "Not" [t]
	    | eqTerm t u	   = mkTrue
	    | True	           = F "==>" [t,u]

 premise (F ('A':'l':'l':_) [t]) = premise t
 premise (F "==>" [t,_]) 	 = t
 premise t 			 = t

 conclusion (F ('A':'l':'l':_) [t]) = conclusion t
 conclusion (F "==>" [_,t]) 	    = t
 conclusion t 			    = t

 mkEq t u    = F "=" [t,u]
 mkNeq t u   = F "=/=" [t,u] 
 mkGr t u    = F ">" [t,u]
 mkTrans t u = F "->" [t,u]

-- mkEqsConjunct is used by eqsToGraph (see below) and showEqsOrGraph 7 
-- (see Ecom).
 
 mkEqsConjunct :: [String] -> [TermS] -> TermS
 mkEqsConjunct [x] [t] = mkEq (V x) $ addToPoss [1] t
 mkEqsConjunct xs ts   = f $ F "&" $ zipWith (mkEq . V) xs ts
	            where f (F x ts)        = F x $ map f ts
	                  f (V x) | isPos x = mkPos $ i:1:s where i:s = getPos x
			  f t 	            = t

-- separateTerms is used by eqsToGraph (see below) and showEqsOrGraph 7 
-- (see Ecom).

 separateTerms :: TermS -> [Int] -> TermS
 separateTerms t is = if isConjunct t then moreTree $ foldl f t is else t
 		      where f u i = replace0 u p $ expandOne 0 t p
			            where p = [i,1]
				  
 mkAny xs (F ('A':'n':'y':y) [t]) = mkAny (xs++words y) t
 mkAny xs (F "==>" [t,u]) 	  = F "==>" [mkAll xs t,mkAny xs u]
 mkAny xs (F "|" ts) 		  = F "|" $ map (mkAny xs) ts
 mkAny [] t 			  = t
 mkAny xs t 			  = mkBinder "Any" xs t

 mkAll xs (F ('A':'l':'l':y) [t]) = mkAll (xs++words y) t
 mkAll xs (F "&" ts) 		  = F "&" $ map (mkAll xs) ts
 mkAll [] t 			  = t
 mkAll xs t 		          = mkBinder "All" xs t

 mkDisjunct []  = mkFalse
 mkDisjunct [t] = t
 mkDisjunct ts  = case mkSummands (F "|" ts) of [] -> mkFalse; [t] -> t
						ts  -> F "|" ts

 mkSummands (F "|" ts) = if any isTrue ts || complOccurs ts then [mkTrue] 
 			 else joinTermMap mkSummands $ removeFalse ts
 mkSummands t 	       = removeFalse [t]

 mkConjunct []  = mkTrue
 mkConjunct [t] = t
 mkConjunct ts  = case mkFactors (F "&" ts) of [] -> mkTrue; [t] -> t
					       ts  -> F "&" ts

 mkFactors (F "&" ts) = if any isFalse ts || complOccurs ts then [mkFalse] 
                        else joinTermMap mkFactors $ removeTrue ts
 mkFactors t 	      = removeTrue [t]

 removeFalse,removeTrue :: [TermS] -> [TermS]
 removeFalse = filter $ not . quantConst "False"
 removeTrue  = filter $ not . quantConst "True"
 
 joinTrees _ [t]       = t
 joinTrees treeMode ts = case treeMode of "summand" -> F "|" $ addNatsToPoss ts
			           	  "factor" -> F "&" $ addNatsToPoss ts
					  _ -> F "<+>" $ addNatsToPoss ts

 mkHorn conc prem      	   = F "<===" [conc,prem]

 mkHornG guard conc prem   = F "==>" [guard,F "<===" [conc,prem]]

 mkCoHorn prem conc        = F "===>" [prem,conc]

 mkCoHornG guard prem conc = F "==>" [guard,F "===>" [prem,conc]]

 invertClause (F "<===" [F x [t,u],v]) | permutative x = mkHorn (F x [u,t]) v
 invertClause (F "<===" [t,u])                         = mkCoHorn u t
 invertClause (F "===>" [t,u])                         = mkHorn u t
 invertClause (F x [t,u]) | permutative x              = F x [u,t]
 invertClause t 	                               = t

-- mkIndHyps t desc constructs the induction hypothesis from a conjecture t and
-- a descent condition (see createIndHyp in Ecom).

 mkIndHyps t desc = case t of F "==>" [u,v] -> [F "<===" [v,F "&" [u,desc]],
				                F "===>" [u,F "==>" [desc,v]]]
			      _ -> [F "<===" [t,desc]]
             
 mkDescent [t] [u] = F ">>" [t,u]
 mkDescent ts us   = F ">>" [mkTup ts,mkTup us]
 
-- equivAxs is used by applyInd (see Ecom).
 
 equivAxs equiv = [F "<===" [F equiv [x,y],mkEq x y],
                   F "<===" [F equiv [x,y],F equiv [y,x]],
	           F "<===" [F equiv [x,z],F "&" (map (F equiv) [[x,y],[y,z]])]]
	          where [x,y,z] = map V (words "x y z")

-- derivedFun sig f xs axs returns Just (loop,inits[xs/ys],ax) if 
-- ax is f(ys)=loop(take i ys++inits) and ax is the only axiom for f. 
-- derivedFun is used by createInvariant (see Ecom).

 derivedFun sig f xs i lg axs =
      case clausesFor [f] axs of
           [ax@(F "=" [F _ zs,F loop inits])] | lg == length zs && all isV zs && 
				                distinct zs &&
					        drop (lg-i) zs == take i inits
	     -> Just (loop,map (>>>(forL xs $ map root zs)) $ drop i inits,ax)
           _ -> Nothing

-- mkInvs True/False constructs the conditions on a Hoare/subgoal invariant INV.
-- and is used by createInvariant (see Ecom).

 mkInvs hoare loop as bs cs inits d conc = F "&" [factor1,factor2]
          where xs = as++bs
		ys = bs++cs
		eq = F "=" [F loop ys,d]
		inv = F "INV"
	        (factor1,factor2) = if hoare 
                                    then (inv (xs++inits),
				          mkImpl (F "&" [eq,inv (xs++cs)]) conc) 
                                    else (mkImpl (inv (bs++inits++[d])) conc,
				          mkImpl eq (inv (ys++[d])))

-- transClosure ts applies rules to ts that employ the transitivity of the
-- relation between the elements of ts. 

 transClosure [t@(F _ [_,_])] = Just t
 transClosure (t:ts)          = do u <- transClosure ts
 				   (F x [l,r],F y [l',r']) <- Just (t,u)
                                   guard $ transitive x && x == y && eqTerm r l'
	                           Just $ F x [l,r']
 transClosure _               = Nothing

-- splitEq t u decomposes t=u.

 splitEq sig = f
  where f t@(F x ts) u@(F y us) = if x == y && length ts == length us
			          then mkConjunct $ zipWith f 
				  		    (renameVars sig x ts us) us
			          else mkEq t u
        f t@(V x) u@(V y)       = if x == y then mkTrue else mkEq t u
	f t u                   = mkEq t u

-- splitNeq t u decomposes t=/=u.

 splitNeq sig = f
  where f t@(F x ts) u@(F y us) = if x == y && length ts == length us
			          then mkDisjunct $ zipWith f 
				  	            (renameVars sig x ts us) us
			          else mkNeq t u
        f t@(V x) u@(V y)       = if x == y then mkFalse else mkNeq t u
	f t u                   = mkNeq t u

-- TERM POSITIONS

 allPoss (F _ ts) = []:liftPoss allPoss ts
 allPoss _        = [[]]
 
-- liftPoss lifts the term positions computed by f to term list positions.

 liftPoss :: Root a => (Term a -> [[Int]]) -> [Term a] -> [[Int]]
 liftPoss f ts = concatMap g $ indices_ ts where g i = map (i:) $ f $ ts!!i
 
-- removeTreePath p t removes the path p in the Hackendot game.
 
 removeTreePath :: [Int] -> TermS -> TermS
 removeTreePath p t = F "" $ map (getSubterm t) $ filter f $ allPoss t 
                      where f q = not (q <<= p) && (null q' || q' <<= p)
		                  where q' = init q
		    
-- buildTreeRandomly rand str generates a tree t with maximal depth 6 and
-- maximal outdegree 4 by random and labels the nodes of t by random with words 
-- of str.

 buildTreeRandomly :: Int -> String -> (TermS,Int)
 buildTreeRandomly rand str = (F "" ts,rand') where
                              xs = words str
                              (ts,rand') = f (nextRand rand) 6 $ rand `mod` 3 +1
                              f rand _ 0 = ([],rand)
                              f rand d n = (t:ts,rand2) where 
                              		   (t,rand1) = g rand $ d-1
                              		   (ts,rand2) = f rand1 d $ n-1 
	                      g rand d = (F (xs!!i) ts,rand2) where
			                 i = rand `mod` length xs
			                 rand1 = nextRand rand
			                 n = if d > 0 then rand1 `mod` 4 else 0
			                 (ts,rand2) = f (nextRand rand1) d n
		    
-- labelRandomly rand str t labels the nodes of t by random with words of str.

 labelRandomly :: Int -> String -> TermS -> (TermS,Int)
 labelRandomly rand str (F _ ts) = (F "" us,rand') where
                    	     xs = words str
                    	     (us,rand') = f rand ts
                    	     f rand (t:ts)   = (u:us,rand2) where 
 	                             	       (u,rand1) = g rand t
 	                             	       (us,rand2) = f rand1 ts
	                     f rand _        = ([],rand)
	                     g rand (F _ ts) = (F (xs!!i) us,rand') where
			              	       i = rand `mod` length xs
			                       (us,rand') = f (nextRand rand) ts
 labelRandom rand _ t = (t,rand)

-- filterPositions f t returns all positions of nodes of t whose label satisfies
-- f.

 filterPositions f t = [p | p <- allPoss t, f $ label t p]

 isPos x  = leader x "pos"

 hasPos (V x)    = isPos x
 hasPos (F x ts) = any hasPos ts
 hasPos _        = False

 getPos :: String -> [Int]
 getPos = map read . tail . words

 mkPos0 :: [Int] -> String
 mkPos0 p = "pos "++unwords (map show p)
 
 mkPos = V . mkPos0

 pointers = filterPositions isPos
 
-- connected t p q checks whether t contains a path from p to q.
-- connected is used by cycleTargets, removeCyclePtrs and expand.
 
 connected :: TermS -> [Int] -> [Int] -> Bool
 connected t p q = f t [] p
              where f t ps p = p `notElem` ps && g ps p (getSubterm t p)
                    g ps p (F x ts) = p == q || or (zipWithSucs (g $ p:ps) p ts)
		    g ps p (V x)    = p == q || isPos x && f t ps (getPos x)
		    g _ p _         = p == q    
		    
-- cycleTargets is used by showCycleTargets (see Ecom).

 cycleTargets :: TermS -> [[Int]]
 cycleTargets t = f [] t
             where f p (F _ ts) = concat $ zipWithSucs f p ts
	           f p (V x)    = if isPos x && connected t q p then [q] else []
 			          where q = getPos x
	           f _ _        = []
		    
-- removeCyclePtrs is used by removeEdges (see Ecom).
		
 removeCyclePtrs :: TermS -> TermS
 removeCyclePtrs t = case f [] t of Just p -> removeCyclePtrs $ lshiftPos t [p]
 				    _ -> t
              where f p (F _ ts) = do guard $ any just ps; head $ filter just ps
		                   where ps = zipWithSucs f p ts
		    f p (V x)    = do guard $ isPos x && connected t q p; Just p
		   	           where q = getPos x
	            f _ _        = Nothing

-- separated f t is True iff for each pointer p of t, p satisfies f or the
-- target position of p does not satisfy f. 
-- separated is used by simplifyS (see Esolve).

 separated :: ([Int] -> Bool) -> TermS -> Bool
 separated f t = all (f ||| not . f . getPos . label t) $ pointers t
		 		 
 allColls x t = all (f . root) 
                where f z = z == x || isPos z && label t (getPos z) == x

 positions = filterPositions $ not . isPos
 
 constrPositions = filterPositions . (.isConstruct)
 
 varPositions = filterPositions . isVar
 
 freePositions sig t = [p | p <- varPositions sig t, let c = leaf "CCC",
 			    label (t>>>const c) p == "CCC"]
 
 freeXPositions sig x t = [p | p <- freePositions sig t, label t p == x]

 (m:p) << (n:q) = m == n && p << q
 _     << p     = notnull p

 p <<= q = p << q || p == q

 orthos ps = and [not $ p << q | p <- ps, q <- ps]

-- succs p computes the list of successor positions of p.

 succs :: [Int] -> [Int] -> [[Int]]
 succs p = map $ \i -> p++[i]
 
 succsInd p = succs p . indices_

-- zipSucs p s zips the list of direct successor positions of p with s.

 zipSucs :: [Int] -> [a] -> [([Int],a)]
 zipSucs p = zip $ succs p [0..]

-- zipWithSucs f p s applies a binary function after zipping the list of
-- direct successor positions of p with s.

 zipWithSucs :: ([Int] -> a -> b) -> [Int] -> [a] -> [b]
 zipWithSucs f p = zipWith f $ succs p [0..]

 zipWithSucsM :: Monad m => ([Int] -> a -> m b) -> [Int] -> [a] -> m [b]
 zipWithSucsM f p = sequence . zipWithSucs f p

-- zipWithSucs2 f p as bs applies a ternary function after zipping the list of
-- direct successor positions of p with as and bs.

 zipWithSucs2 :: ([Int] -> a -> b -> c) -> [Int] -> [a] -> [b] -> [c]
 zipWithSucs2 f p = zipWith3 f $ succs p [0..]

 zipWithSucs2M :: Monad m => ([Int] -> a -> b -> m c) -> [Int] -> [a] -> [b] 
 		                   				      -> m [c]
 zipWithSucs2M f p s = sequence . zipWithSucs2 f p s
 
-- possOf t x returns the first position of t labelled with x.

 possOf :: TermS -> String -> Maybe [Int]
 possOf t x = do p:_ <- Just $ f t; Just p
              where f (F y ts)       = if x == y then [[]] else liftPoss f ts
	            f (V y) | x == y = [[]]
		    f _	             = []
 
-- closedSub t p turns the subtree of t at position p into a closed subgraph.
-- closedSub is used by showSubtreePicts.

 closedSub :: TermS -> [Int] -> TermS
 closedSub t p = dropFromPoss p $ if foldT f u then u else expand 0 t p
		 where u = getSubterm t p
		       f x bs = not (isPos x) || p <<= getPos x && and bs
 
 targets = foldT f where f x pss = if isPos x then [getPos x] else joinM pss

-- boolPositions t returns all positions of Boolean subterms of t.

 boolPositions sig t@(F _ ts) = if isFormula sig t then []:ps else ps
			      	where ps = liftPoss (boolPositions sig) ts
 boolPositions _ _            = []

-- colorWith2 c d ps t colors t at all positions of ps with c and at all other 
-- positions with d.

 colorWith2 c d ps = f [] 
                     where f p (F x ts) = F (e++'_':x) $ zipWithSucs f p ts
	    			          where e = if p `elem` ps then c else d
	                   f p t@(V x)  = if isPos x then t else V $ e++'_':x
	    			          where e = if p `elem` ps then c else d
	                   f _ t 	= t

-- changedPoss t u returns the minimal positions p of u such that the subterms
-- of t resp. u at position p differ from each other.

 changedPoss t u = g $ f [] t u
       where f p (F x ts) (F y us)
               | x == y = if m < n then concat (zipWithSucs2 f p ts $ take m us)
	                                ++ succs p [m..n-1]
	                           else concat $ zipWithSucs2 f p (take n ts) us
	       | True   = [p] where m = length ts; n = length us
             f p t u    = if t `eqTerm` u || isPos (root u) then [] else [p]
             g ([]:_) = [[]]
             g (p:ps) = if f t `eqTerm` f u then g ps else p:g ps
                        where f t = getSubterm t $ init p
	     g _      = []

-- glbPos ps returns the greatest lower bound of ps with respect to <<=.

 glbPos :: [[Int]] -> [Int]
 glbPos ps = foldl1 f ps where f (m:p) (n:q) = if m == n then m:f p q else []
 		               f _ _         = []

-- Any r: restPos p q = r  <==>  p <<= q

 restPos (m:p) (n:q) = if m == n then restPos p q else []
 restPos _ q         = q
                   			  									  
-- nodePreds t p returns the predecessor positions of position p of t. 

 nodePreds t p = if null p then ps else init p:ps
	         where ps = concatMap (nodePreds t) $ filterPositions (== x) t
	               x = "pos "++unwords (map show p)

-- nodeSucs t p returns the first non-pointer successor positions of position p
-- of t.

 nodeSucs t p = case getSubterm t p of F x ts -> zipWithSucs getNode p ts
	                               V x | isPos x -> nodeSucs t $ getPos x
	                                   | True    -> []
	        where getNode _ (V x) | isPos x = getNode p $ getSubterm t p
	        			          where p = getPos x
 		      getNode p _               = p

-- posTree [] t replaces the node entries of t by the respective node positions.
-- Pointer positions are labelled with the respective target node positions.

 posTree :: [Int] -> TermS -> Term [Int]
 posTree p t | isHidden t  = F p []
 posTree p (F _ ts)        = F p $ zipWithSucs posTree p ts
 posTree p (V x) | isPos x = V $ getPos x
                 | True    = V p

-- polarity True t p returns the polarity of the subformula at position
-- p of t. This determines the applicability of inference rules at p.

 polarity :: Bool -> TermS -> [Int] -> Bool
 polarity pol (F "===>" [t,_]) (0:p) = polarity (not pol) t p
 polarity pol (F "===>" [_,t]) (1:p) = polarity pol t p
 polarity pol (F "<===" [t,_]) (0:p) = polarity pol t p
 polarity pol (F "<===" [_,t]) (1:p) = polarity (not pol) t p
 polarity pol (F "==>" [t,_]) (0:p)  = polarity (not pol) t p
 polarity pol (F "==>" [_,t]) (1:p)  = polarity pol t p
 polarity pol (F "Not" [t]) (0:p)    = polarity (not pol) t p
 polarity pol (F x ts) (n:p)         = polarity pol (ts!!n) p
 polarity pol _ _      	             = pol

 monotone :: Sig -> [String] -> TermS -> Bool
 monotone sig xs = f True
    where f pol (F "`then`" [t,u]) = f (not pol) t && f pol u
	  f pol (F "not" [t])      = f (not pol) t
          f pol (F x ts)           = if x `elem` xs then pol else all (f pol) ts
	  f _ _ 	           = True

-- polTree True [] t replaces the node entries of t by the polarities of the
-- respective subtreees.

 polTree :: Bool -> [Int] -> TermS -> [[Int]]
 polTree pol p (F "===>" [t,u]) = if pol then p:ps1++ps2 else ps1++ps2
                                  where ps1 = polTree (not pol) (p++[0]) t
				        ps2 = polTree pol (p++[1]) u
 polTree pol p (F "<===" [t,u]) = if pol then p:ps1++ps2 else ps1++ps2
                                  where ps1 = polTree pol (p++[0]) t
				        ps2 = polTree (not pol) (p++[1]) u
 polTree pol p (F "==>" ts)     = polTree pol p (F "===>" ts)
 polTree pol p (F "Not" [t])    = if pol then p:ps else ps
                                  where ps = polTree (not pol) (p++[0]) t
 polTree pol p (F x ts)         = if pol then p:concat pss else concat pss
                                  where pss = zipWithSucs (polTree pol) p ts
 polTree pol p _      	        = if pol then [p] else []

-- natToLabel t and natToPos t turn t into a function that maps, for each node n
-- of t, the position of n in heap order to the label resp. tree position of n.

 natToLabel :: Root a => Term a -> Int -> Maybe a
 natToLabel t = mkFun [t] (const Nothing) $ -1
                where mkFun [] f _ = f
	              mkFun ts f m = mkFun (concatMap subterms ts) g n
                                     where g = fold2 upd f [m+1..n] vals
				           n = m+length ts
					   vals = map (Just . root) ts

-- level/pre/heap/hillTerm col lab t labels each node of t with its position 
-- within t with respect to level, prefix, heap or hill order. lab labels the 
-- nodes of t in accordance with the color function hue 1 col n where n is the 
-- maximum of positions of t and col is the start color.

 levelTerm,preordTerm,heapTerm,hillTerm ::
                          Color -> (Color -> Int -> b) -> Term a -> (Term b,Int)

 levelTerm col lab t = un where un@(_,n) = f 0 t
		                f i (F _ ts@(_:_)) = (F (label i) us,maximum ks)
		     		        where (us,ks) = unzip $ map (f $ i+1) ts
			        f i _= (F (label i) [],i+1)
			        label i = lab (hue 1 col n i) i

 preordTerm col lab t = un where un@(_,n) = f 0 t
		                 f i (F _ ts) = (F (label i) us,n)
					        where (us,n) = g (i+1) ts
		                 g i (t:ts) = (u:us,n) where (u,m) = f i t
				                             (us,n) = g m ts
		                 g i _      = ([],i)
	                         label i = lab (hue 1 col n i) i

 heapTerm col lab t = (u,n+1)
      where (u:_,n) = f (-1) [t]
            f i [] = ([],i)
            f i ts = (vs,k)
	             where (tss,lgs) = (concat *** map length) $ map subterms ts
			   lg = length ts
		           (us,k) = f (i+lg) tss
	                   (vs,_,_) = foldl h ([],us,i+1) lgs
	                   h (ts,us,i) lg = (ts++[F (label i) vs],ws,i+1)
				            where (vs,ws) = splitAt lg us
	    label i = lab (hue 1 col n i) i
	       
 hillTerm col lab t = un where un@(_,n) = f 0 t
		               f i (F _ ts) = (F (label i) us,maximum $ n:ns)
			    	   where (us,ns) = unzip $ zipWith f ks ts
				         lg = length ts; k = lg `div` 2
					 n = if even lg then k else k+1
					 is = [0..k-1]; js = [k-1,k-2..0]
					 ks = is++(if even lg then js else k:js)
			       f i _ = (F (label i) [],i)
			       label i = lab (hue 1 col n i) i

-- cutTree max t ps col qs hides each subtree of t whose root position is in qs 
-- or greater than max (wrt the heap order). Each subtrees of t whose root 
-- position is in ps is colored with col.

 cutTree :: Int -> TermS -> [[Int]] -> String -> [[Int]] -> TermS
 cutTree max t ps col qs = f [] $ fold2 replace (head $ cutTreeL [t] 0) qs 
 			        $ map (hide . getSubterm t) qs
    where f p (F x ts) = F (c p x) $ zipWithSucs f p ts
	  f p (V x)    = V $ c p x
	  f _ t        = t						 
          cutTreeL [] _ = []
          cutTreeL ts n = vs where (roots,tss,lgs) = unzip3 $ map g ts
	                           us = cutTreeL (concat tss) (n+length ts)
	                           (vs,_,_) = fold2 h ([],us,n+1) roots lgs
	  g t = ((root t,isV t),ts,length ts) where ts = subterms t
	  h (ts,us,n) (x,isv) lg = (ts++[if isv then V y else F y subs],
	                            drop lg us,n+1)
	              where (y,subs) = (if n < max then x else '@':x,take lg us)
          c p x = if p `elem` ps then col++'_':case parse colPre x of 
	  					    Just (_,x) -> x; _ -> x
				 else x
          hide t@(F ('@':_) _) = t
          hide (F x ts)        = F ('@':x) ts   
          hide t@(V ('@':_))   = t
          hide (V x)           = V ('@':x)
          hide t               = t

-- label t p returns the root of the subterm at position p of t.

 label t []       = root t
 label (F _ ts) p = label' ts p
 label t _        = undef

 label' (t:_) (0:p)  = label t p
 label' (_:ts) (n:p) = label' ts $ (n-1):p
 label' _ _ 	     = undef

-- getSubterm t p returns the subterm at position p of t.

 getSubterm t []       = t
 getSubterm (F _ ts) p = getSubterm' ts p
 getSubterm t _        = Hidden ERR

 getSubterm' (t:_) (0:p)  = getSubterm t p
 getSubterm' (_:ts) (n:p) = getSubterm' ts $ (n-1):p
 getSubterm' _ _	  = Hidden ERR
 
 removeAllCopies t p = f [] t where u = getSubterm t p
			            f q t | p == q = t
			                  | t == u = mkPos p
			            f p (F x ts) = F x $ zipWithSucs f p ts
				    f _ t        = t       

-- POINTER MODIFICATIONS

 dropHeadFromPoss = mapT f where f x = if isPos x then mkPos0 $ tail $ getPos x 
 						  else x

 drop2FromPoss = mapT f where f x = if isPos x then mkPos0 $ drop 2 $ getPos x 
 					       else x
 
-- dropFromPoss p t removes the prefix p from each pointer of t below p.

 dropFromPoss p = if null p then id else mapT f 
 		  where f x = if isPos x && p <<= q 
 			      then mkPos0 $ drop (length p) q else x
			      where q = getPos x

 dropFromPoss' p = if null p then id else mapT f 
 		   where f x = if isPos x
 			       then if p <<= q then mkPos0 $ drop (length p) q 
			            else "pos' "++unwords (map show q)
			       else x 
			       where q = getPos x

 drop0FromPoss = dropFromPoss [0]
 
-- getSubterm1 t p returns the subterm u at position p of t and replaces each
-- pointer p++q in u by q.

 getSubterm1 t p = dropFromPoss p $ getSubterm t p

-- addToPoss p t adds the prefix p to all pointers of t that point to subterms
-- of t.

 addToPoss p t = if null p then t else mapT f t
 	         where f x = if isPos x && q `elem` positions t
			     then mkPos0 $ p++q else x where q = getPos x

 addToPoss' p t = if null p then t else mapT f t
 	          where f x = if leader x "pos'" then mkPos0 q
			      else if isPos x then mkPos0 $ p++q else x 
			      where q = getPos x
	      
 addNatsToPoss = zipWith (addToPoss . single) [0..]

-- changePoss p q t replaces the prefix p of all pointers of t with prefix p by
-- q. changePoss is used by replace2, expand (see below) and simplify "permute" 
-- (see Esolve).

 changePoss p q = mapT f where f x = if isPos x && p <<= r
	                             then mkPos0 $ q++drop (length p) r else x
				     where r = getPos x
 						 
 changeLPoss f ts = map g ts where g t = foldl h t $ indices_ ts
 			                 where h t i = changePoss p q t
				  		       where (p,q) = f i

-- SUBTERM REPLACEMENTS

-- movePoss t p q dereferences a pointer r of u = getSubterm t p if r points to 
-- a node that is not reachable from p. If r points to a node below p, then r is 
-- replaced by q++drop (length p) r. The operation ensures that the pointers are
-- adapted correctly if when u is moved to position q of t.

-- movePoss is used by replace/1/2 and expand/One/Into/Level (see below)
 
 movePoss t p q = f $ getSubterm t p   
 		  where f (F x ts)    	    = F x $ map f ts
		        f u@(V x) | isPos x = if p <<= r 
					      then mkPos $ q++drop (length p) r 
					      else if q <<= r then expand 0 t r 
					    		      else u
					      where r = getPos x
		        f t                 = t

-- replace0 t p u replaces the subterm of t at position p by u.

-- replace0 is used by separateTerms, removeNonRoot, exchange, expand 
-- (see below), catchTree, copySubtrees and replaceNodes' (see Ecom)

 replace0 t p0 u = f t p0 where f _ []         = u
	                	f (F x ts) p   = F x $ g ts p
				g (t:ts) (0:p) = f t p:ts
				g (t:ts) (n:p) = t:g ts (n-1:p)
				g _ _          = [Hidden ERR]

-- replace t p u expands t at all pointers of t into proper subterms of the 
-- subterm v of t at position p. Pointers to the same subterm are expanded only 
-- once, the others are redirected. Afterwards v is replaced by u.

-- replace is used by collapseCycles, cutTree, expandOne, modifyDF/Random,
-- replace 1/2, unify (see here), applyAx, applyLoop/Random, applyMany, 
-- applyPar, applySingle, mkEqs (see Esolve), applyInd, applySubst,
-- applySubstTo', createInvariant, expandTree', generalizeEnd, narrowPar,
-- narrowSubtree, releaseNode, releaseTree, renameVar', replaceVar, rewriteVar,
-- stretch and subsumeSubtrees (see Ecom).

 replace t p0 u = f [] t 
                  where f p _     | p == p0 = u
	                f p (F x ts)        = F x $ zipWithSucs f p ts
			f p (V x) | isPos x && p0 << q && not (p0 <<= p)
		                            = if p == r then movePoss t q p 
				                        else mkPos r
				              where q = getPos x
				                    Just r = lookup q $ g [] t
                        f _ t = t
			g p _ | p == p0 = []
			g p (F x ts)    = concat $ zipWithSucs g p ts
			g p (V x) | isPos x && p0 << q && not (p0 <<= p) 
		     		        = [(q,p)] where q = getPos x
		        g _ t = []

-- replace1 t p u applies replace t p to u after all pointers of u into the 
-- subterm of t at position p have been expanded. 

-- replace1 is used by changeTerm (see below), simplifyOne, shiftSubformulas and
-- simplifyOne (see Esolve), applyTransitivity, collapseStep, composePointers, 
-- decomposeAtom, evaluateTrees, releaseTree, replaceOther, replaceSubtrees', 
-- shiftPattern, shiftQuants, showEqsOrGraph, showNumbers, showRelation, 
-- simplifySubtree, storeGraph, subsumeSubtrees and unifySubtrees (see Ecom).

 replace1 t p  = replace t p . addToPoss p

 replace1' t p = replace t p . addToPoss' p

-- replace2 t p u q copies the subterm at position p of t to position q of u and
-- replaces each pointer p++r in the modified term by q++r. 

-- replace2 is used by moreTree, changeTerm (see below) and releaseSubtree 
-- (see Ecom).

 replace2 t p0 u q0 = replace u q0 $ changePoss p0 q0 $ f [] $ getSubterm t p0
                      where f p (F x ts) = F x $ zipWithSucs f p ts
		            f p (V x) | isPos x && q0 << q && not (p0 <<= q)
		      		         = movePoss t q p where q = getPos x
		            f _ t        = t
			    
-- expandInto t p expands t at all pointers into the subterm of t at position p.
-- expandInto is used by removeSubtrees (see Ecom).

 expandInto t p0 = f [] t where f p (F x ts) = F x $ zipWithSucs f p ts
                                f p (V x) | isPos x && p0 <<= q 
			       	             = movePoss t q p where q = getPos x
                                f _ t        = t

-- moreTree t turns all non-tree downward edges of t into tree edges.
-- moreTree is used by eqsToGraph (see below) and removeEdges (see Ecom).

 moreTree :: TermS -> TermS
 moreTree t = case f [] t of Just (p,q) 
 			       -> moreTree $ composePtrs $ exchange t p q
			     _ -> t
              where f p (F _ ts) = concat $ zipWithSucs f p ts
 	            f p t        = do V x <- return t; let q = getPos x
		                      guard $ isPos x && length p < length q 
		             	      Just (p,q)

-- removeNonRoot t p removes the node at position p of t. removeNonRoot is used 
-- by simplify "concat" (see Esolve) and removeNode (see Ecom).

 removeNonRoot :: TermS -> [Int] -> TermS
 removeNonRoot t p = removeX $ chgPoss $ replace0 t q 
 			     $ if isV u then u 
			                else F x $ take n us++vs++drop (n+1) us
        where (q,n) = (init p,last p)
              snp = length p; np = snp-1
	      u = getSubterm t q
	      vs = subterms $ getSubterm t p
	      incr = length vs-1
	      midPoss = [r | r <- positions t, p << r]
	      rightPoss = [r | r <- positions t, q << r, n < r!!np]
	      newM r = take np r++r!!snp+n:drop (snp+1) r
	      newR r = take np r++r!!np+incr:drop snp r
	      (x,us) = (root u,subterms u)
	      chgPoss (F x ts) = F x $ map chgPoss ts
	      chgPoss (V x) | r == p			    = V "XXX"
	                    | isPos x && r `elem` midPoss   = mkPos $ newM r
		            | isPos x && r `elem` rightPoss = mkPos $ newR r
				                              where r = getPos x
              chgPoss t = t
              removeX t = lshiftPos t [p | p <- positions t, label t p == "XXX"]

 data ChangedTerm = Wellformed TermS | Bad String
 
-- changeTerm t u ps@(p:qs) replaces the subterm of t at position p by u and 
-- then replaces the leaves of u with label "_" by the subterms vs of t at 
-- positions qs. If u does not have leaves with label "_", then all v in vs are
-- replaced by u. If u has a single leaf with label "_" and ps is a list of 
-- pairwise orthogonal positions or if qs is empty, then for all v in vs, v is
-- replaced by u[v/_]. changeTerm is used by replaceText' (see Ecom).
 
 changeTerm t u ps = 
     case n of 0 -> Wellformed $ fold2 replace1 t ps $ replicate m u
	       1 | orthos ps -> Wellformed $ fold3 replace2 t ps t1 $ map g ps
	       _ -> if m == 1 
	            then Wellformed $ fold3 replace2 t (replicate n p) t2 rs
		    else if all (p <<) qs
		         then let k = m-n-1
		              in case signum k of
		                 0 -> Wellformed $ fold3 replace2 t qs t2 rs
		                 1 -> Bad $ "Add " ++ unstr k
			         _ -> Bad $ "Remove " ++ unstr (n-m+1)
			 else Bad "Select further subtrees below the first one!"
     where m = length ps; p:qs = ps
	   t1 = foldl f t ps where f t p = replace1 t p u
	   t2 = replace1 t p u; rs = map (p++) underlines
	   g p = p++head underlines
	   underlines = filterPositions (== "_") u; n = length underlines
	   unstr 1 = "an underline!"
	   unstr k = show k ++ " underlines!"

-- exchange t p q exchanges the subterms of t at position p resp. q and is used
-- by reverseSubtrees (see Ecom).

 exchange t p q = exchangePos p q $ replace0 (replace0 t p v) q u
 		  where u = getSubterm t p; v = getSubterm t q

 exchangePos p q = mapT f where f x | isPos x = 
 			             if p <<= r then g q p
   	                             else if q <<= r then g p q else x
	                             where r = getPos x
		                           g p q = mkPos0 $ p++drop (length q) r
		                f x = x

 incrPos p n = updList p n $ p!!n+1

 decrPos p n = updList p n $ p!!n-1

-- lshiftPos t ps removes map (getSubterm t) ps from t and changes the pointers
-- of t accordingly. lshiftPos is used by removeCyclePtrs, removeNonRoot 
-- (see above) and removeSubtrees (see Ecom).

 lshiftPos t = foldl f t . dec
               where f t p = mapT (g p) $ removeSubterm p t
                     g p x | isPos x && init p << q =
	                               if k < m then mkPos0 $ decrPos q n else x
		                       where q = getPos x; m = q!!n
		                             k = last p; n = length p-1
                     g _ x = x
		     dec (p:ps) = p:dec (map (f p) ps)
		                where f p q = if init p << q && p < q
			                      then decrPos q $ length p-1 else q
                     dec _      = []

-- removeSubterm t p removes the subterm at position p of t.

 removeSubterm p = head . f []
                where f q t = if p == q then [] 
		              else case t of 
			           F x ts -> [F x $ concat $ zipWithSucs f q ts]
				   _ -> [t]

-- rshiftPos p t adapts the pointer values of t to a copy of getSubterm t p.
-- rshiftPos/0 is used by copySubtrees (see Ecom).

 rshiftPos p = mapT f where f x = if isPos x 
 				  then mkPos0 $ rshiftPos0 p $ getPos x else x

 rshiftPos0 p q = if init p << q && last p <= q!!n then incrPos q n else q
		  where n = length p-1

-- atomPosition sig t p returns the position of the atom that encloses the
-- subterm of t at position p. atomPosition is used by applyPar, applyLoop, 
-- applySingle (see Esolve) and narrowPar (see Ecom).

 atomPosition :: Sig -> TermS -> [Int] -> Maybe ([Int],TermS,[Int])
 
 atomPosition sig t [] = do guard $ isOnlyAtom sig t; Just ([],t,[])
 atomPosition sig t p  = goUp t (init p) [last p]
    where goUp t p q = if null p then do guard $ isOnlyAtom sig t; Just ([],t,q)
                       else if isOnlyAtom sig u then Just (p,u,q) 
	                    else goUp t (init p) $ last p:q
		       where u = getSubterm t p

-- orPosition t p returns the position of the smallest disjunction v that
-- encloses the subterm of t at position p provided that there are only
-- existential quantifiers on the path from the root of v to p. 
-- orPosition is used by applyDisCon (see Ecom).

 orPosition t p = goUp t (init p) [last p]
    where goUp t p q = if isDisjunct u then Just (p,q)
                       else do guard $ isConjunct u || take 4 (root u) == "Any "
			       goUp t (init p) $ last p:q
		       where u = getSubterm t p

-- andPosition t p returns the position of the smallest conjunction v that
-- encloses the subterm of t at position p provided that there are only
-- universal quantifiers on the path from the root of v to p. 
-- andPosition is used by applyDisCon (see Ecom).

 andPosition t p = goUp t (init p) [last p]
       where goUp t p q = if isConjunct u then Just (p,q)
                          else if isDisjunct u || take 4 (root u) == "All "
			       then goUp t (init p) (last p:q) else Nothing
		          where u = getSubterm t p

-- boundedGraph x n t returns a subgraph of t with root x and height n.
-- NOT IN USE
 
 boundedGraph x n t = if null ps then t else h u
	              where ps = filterPositions (== x) t
		            u = f (n-1) $ getSubterm1 t $ head ps
	                    f n u = case u of F x us -> F x $ g n us; _ -> u
	                    g 0 _  = []
			    g n ts = map (f (n-1)) ts
			    h (F x ts) = F x $ map h ts
			    h (V x) | isPos x && p `notElem` positions u 
			    	       = F (label t p) [] where p = getPos x
			    h t	       = t

-- addAtoms s t adds s!!x to each state node x of t.
-- addAtoms is used by showEqsOrGraph (see Ecom).

 addAtoms :: [String] -> [String] -> [String] -> [[Int]] -> TermS -> TermS
 addAtoms sts labs ats s = if null labs then mapT f else g
                           where f x = if isPos x then x else new x
	                         g (F x ts) = F (new x) $ map h ts
				 g t        = t
				 h (F lab ts) = F lab $ map g ts
				 h t	     = t
				 new x = if x == "<+>" || null zs then x 
			                 else x ++ " sats " ++ showTerm0 u
			                 where zs = relToFunI sts ats s x
					       u = mkList $ map leaf zs

-- addAtomsL s t adds s!!x!!y to each label node y of t with state 
-- predecessor x. addAtomsL is used by showEqsOrGraph (see Ecom).

 addAtomsL :: [String] -> [String] -> [String] -> [[[Int]]] -> TermS -> TermS
 addAtomsL sts labs ats s = f 
                    where f (F x ts) = F x $ map (g x) ts
                          f t        = t
			  g x (F lab ts) = F (new x lab) $ map f ts
			  g _ t 	 = t
		          new x lab = if x == "<+>" || null zs then lab 
		                      else lab ++ " sats " ++ showTerm0 u
		 	              where zs = relLToFunI sts labs ats s x lab
				            u = mkList $ map leaf zs

-- concept ts posExas negExas computes the minimal concept wrt the feature trees
-- ts that satisfies the positive/negative examples posExas/negExas.

 concept :: [TermS] -> [[String]] -> [[String]] -> [[String]]
 concept ts posExas negExas = 
      if all (== (length ts)) $ map length $ posExas ++ negExas
      then map f $ minis r $ g (possOfTup posExas) `minus` g (possOfTup negExas)
      else [["Some example is not covered by the tuple of feature trees."]]
      where f = map root . zipWith getSubterm ts
	    r ps = and . zipWith (<<=) ps 
	    g = concatMap $ sequence . map prefixes
	    possOfTup = map (zipWith h ts) . reduceExas ts
	    h t = get . possOf t
	    prefixes p = [take n p | n <- [0..length p]]
	    
-- reduceExas ts exas combines subsets of exas covering a subconcept to single 
-- examples.
	    
 reduceExas :: [TermS] -> [[String]] -> [[String]]
 reduceExas ts exas = 
 	   if all (== (length ts)) $ map length exas
           then iterate (flip (foldl f) $ indices_ ts) exas
           else [["Some example is not covered by the tuple of feature trees."]]
      where iterate h exas = if exas == exas' then exas else iterate h exas'
      			     where exas' = h exas
            f exas i = foldl g exas $ tail $ positions t
	       where t = ts!!i
		     g exas q = foldl h exas $ filter b exas
		        where b exa = exa!!i == root (getSubterm t q)
			      p = init q
			      u = getSubterm t p
			      (x,us) = (root u,subterms u)
			      zs = map (label t) $ succsInd p us
			      h exas exa = if exas' `subset` exas 
			    	           then updList exa i x:minus exas exas'
					   else exas
					   where exas' = map f $ indices_ zs
					         f = updList exa i . (zs!!)

-- graphToRel is used by collapseCycles, eqsToGraph (see below), showMatrix and 
-- showRelation (see Ecom). graphToRel2 is used by showMatrix and showRelation 
-- (see Ecom). 
 
 graphToRel :: TermS -> Pairs String
 graphToRel t = case t of F "<+>" ts -> concatMap f ts; _ -> f t
                where dom x xss = joinM xss `join1` x
		      f t@(F x ts) = foldl g [] $ foldT dom t
                                   where g s a = if null bs then s else (a,bs):s
				          where bs = foldl (h x) (const []) ts a
                      f t = []
		      h x f (F z ts) = foldl (h z) (updL f x z) ts
		      h x f (V z)    = updL f x $ if isPos z then root u else z
				       where u = getSubterm t $ getPos z
		      h _ f _        = f

 graphToRel2 :: [String] -> TermS -> Triples String String
 graphToRel2 xs t = case t of F "<+>" ts -> concatMap f ts; _ -> f t
         where dom x xss = joinM xss `join1` x
	       (domx,domy) = split (`elem` xs) $ foldT dom t
               f t@(F x ts) = foldl g [] $ prod2 domx domy
                             where g s (a,b) = if null cs then s else (a,b,cs):s
			               where cs = foldl (h x) (const2 []) ts a b
               f _ = []
               h x f (F y ts) = foldl (h' x y) f ts
	       h _ f _        = f
	       h' x y f (F z ts) = foldl (h z) (upd2L f x y z) ts
	       h' x y f (V z)    = upd2L f x y $ if isPos z then root u else z
				   where u = getSubterm t $ getPos z
	       h' _ _ f _        = f

-- REGULAR EQUATIONS and INEQUATIONS

 data RegEq = Equal String TermS | Diff String TermS deriving (Eq,Ord)

 getVar (Equal x _) = x
 getVar (Diff x _)  = x

 getTerm (Equal _ t) = t
 getTerm (Diff _ t)  = t

 updTerm f (Equal x t) = Equal x (f t)
 updTerm f (Diff x t)  = Diff x (f t)
 
 unzipEqs = unzip . map (getVar *** getTerm)

 solEq :: Sig -> TermS -> Maybe RegEq
 solEq sig t = do (l,r) <- getEqSides t
 		  let x = root l; y = root r
		  if isV l && x `notElem` xs && isNormal sig r 
		     then Just $ Equal x r
	             else do guard $ isV r && y `notElem` xs && isNormal sig l
		             Just $ Equal y l
      	       where xs = anys t
		      
 getEqSides (F ('A':'n':'y':_) [F "=" [l,r]]) = Just (l,r)
 getEqSides (F "=" [l,r])                     = Just (l,r)
 getEqSides _ 		                      = Nothing

 solIneq :: Sig -> TermS -> Maybe RegEq
 solIneq sig t = do (l,r) <- getIneqSides t
	            let x = root l; y = root r
		    if isV l && isNormal sig r && x `notElem` xs
		       then Just $ Diff x r
	               else do guard $ isV r && isNormal sig l && y `notElem` xs
		               Just $ Diff y l
      	         where xs = alls t
		      
 getIneqSides (F ('A':'l':'l':_) [F "=/=" [l,r]]) = Just (l,r)
 getIneqSides (F "=/=" [l,r])                     = Just (l,r)
 getIneqSides _ 		                  = Nothing

 solAtom sig t | just eq = eq where eq = solEq sig t
 solAtom sig t           = solIneq sig t

-- parseSol is used by parseRegEqs, isSol (see below), solPict (see Epaint),
-- applySols and solveGuard (see Esolve).

 parseSol :: (TermS -> Maybe RegEq) -> TermS -> Maybe [RegEq]
 parseSol f t = case t of F "True" [] -> Just []
		          F "&" ts -> do eqs <- mapM f ts
			  	         let (xs,us) = unzipEqs eqs
					 guard $ distinct xs && all (g xs) us
					 Just $ map (updTerm $ mapT h) eqs
		          _ -> do eq <- f t; guard $ g [getVar eq] $ getTerm eq
		     	          Just [updTerm dropHeadFromPoss eq]
	        where g xs t = root t `notElem` xs
		      h x = if isPos x then mkPos0 $ tail $ tail $ getPos x 
		      		       else x

-- isSol is used by makeTrees, narrowLoop and splitTree (see Ecom).

 isSol sig = just . parseSol (solAtom sig) ||| isFalse

-- solPoss is used by makeTrees, narrowLoop and showSolutions (see Ecom).

 solPoss sig ts = filter (isSol sig . (ts!!)) $ indices_ ts

-- mkSubst is used by applySols, rewrite, applyAx, rewriteTerm and simplReducts 
-- (see Esolve).

 mkSubst :: [RegEq] -> SubstS
 mkSubst eqs = forL ts xs where (xs,ts) = unzipEqs eqs

-- fixToEqs replaces the bounded variables of fixpoint formulas by pointers to
-- the respective subformulas. fixToEqs is used by simplifyT . F "fixToGraph"
-- (see Esolve). Alternating fixpoints may lead to wrong results.
		   
 fixToEqs :: TermS -> Int -> (TermS,[RegEq],Int)
 fixToEqs (F x [t]) n | isFixF x = (F z [],Equal z (F mu [u]):eqs,k)
 			    where mu:y:_ = words x
				  b = y `elem` foldT f t
				  z = if b then y++show n else y
				  (u,eqs,k) = if b then fixToEqs (t>>>g) $ n+1
					           else fixToEqs t n
				  f x xss = if isFixF x then joinM xss `join1` y
				                        else joinM xss
					    where _:y:_ = words x
				  g = F z [] `for` y
 fixToEqs (F "`then`" [t,u]) n = fixToEqs (F "\\/" [F "not" [t],u]) n
 fixToEqs (F x ts) n           = (F x us,eqs,k) 
                                 where (us,eqs,k) = f ts n
                                       f (t:ts) n = (u:us,eqs++eqs',k')
					          where (u,eqs,k) = fixToEqs t n
						        (us,eqs',k') = f ts k
			               f _ n = ([],[],n)
 fixToEqs t n = (t,[],n)

-- parseRegEqs is used by simplifyS postflow/stateflow/subsflow, simplReducts 
-- (see Esolve) and showEqsOrGraph/Matrix/Relation (see Ecom).

 parseRegEqs :: TermS -> Maybe [RegEq]
 parseRegEqs t = parseSol parseRegEq t ++
                 do F x ts <- Just t; guard $ isFixT x
		    let _:zs = words x
		    case ts of [t] -> Just $ case zs of 
				   		  [z] -> [Equal z t]
				                  _ -> zipWith (f x t) [0..] zs
			       _ -> do guard $ length zs == length ts
				       Just $ zipWith Equal zs ts
                 where parseRegEq (F x [t,u])
		             | b x && null ts && isF u = Just $ Equal (root t) u
			     | b x && null us && isF t = Just $ Equal (root u) t
			      		                 where ts = subterms t
							       us = subterms u
		       parseRegEq _ = Nothing
		       b x = x == "=" || x == "<=>"
		       f x u i z = Equal z $ F ("get"++show i) [u]

-- graphToEqs n t transforms a graph into an equivalent set of regular equations
-- and is used by showEqsOrGraph (see Ecom).

 graphToEqs :: Int -> TermS -> [Int] -> ([RegEq],Int)
 graphToEqs n t p = (map f $ indices_ ps,n+length ps)
            where ps = (if null p then roots else [p]) `join` targets t
		  roots = case t of F "<+>" ts -> map single $ indices_ ts
		                    _ -> [[]]
	          f i = Equal ('z':show (n+i)) $ g i p $ getSubterm t p
		        where p = ps!!i
		              g i p _     | p `elem` context i ps = h p
		              g _ _ (V x) | isPos x               = h $ getPos x
		              g i p (F x ts) = F x $ zipWithSucs (g i) p ts
		              g _ _ t        = t
			      h p = V $ 'z':show (n+getInd p ps)

-- relToEqs n rel transforms a binary relation into an equivalent set of regular 
-- equations and is used by showEqsOrGraph (see Ecom).
	       
 relToEqs :: Int -> Pairs String -> ([RegEq],Int)
 relToEqs n rel = (map g $ indices_ ps,n+length ps)
  	         where ps = foldr f [] rel
		       f (a,bs) rel = if null bs then rel else updAssoc rel a bs
		       g i = Equal ('z':show (n+i)) $ F a $ map h bs 
		             where p@(a,bs) = ps!!i
			           h b = case search ((== b) . fst) ps of
				              Just i -> V $ 'z':show (n+i)
				              _ -> leaf b

-- relLToEqs n rel transforms a ternary relation into an equivalent set of 
-- regular equations and is used by simplifyT "auto" (see Esolve) and 
-- showEqsOrGraph (see Ecom).

 relLToEqs :: Int -> Triples String String -> ([RegEq],Int)
 relLToEqs n rel = (map g $ indices_ ts,n+length ts)
      where ts = foldr f [] rel
            f (a,b,cs) rel = if null cs then rel
		 	     else case lookup a rel of
		      		  Just bcs -> updAssoc rel a $ updAssoc bcs b cs
				  _ -> (a,[(b,cs)]):rel
            g i = Equal ('z':show (n+i)) $ F a $ map f bcs 
		             where p@(a,bcs) = ts!!i
			           f (b,cs) = F b $ map h cs
			           h c = case search ((== c) . fst) ts of
				              Just i -> V $ 'z':show (n+i)
				              _ -> F c []

 eqsToTerm :: [RegEq] -> TermS
 eqsToTerm eqs = case eqs of [eq] -> f eq
	                     _ -> F "&" $ addNatsToPoss $ map f eqs
	         where f (Equal x t) = mkEq (V x) t
		       f (Diff x t)  = mkNeq (V x) t
		
-- connectEqs xs ts replaces each occurrence in ts of a variable xs!!i by a
-- pointer to ts!!i. connectEqs is used by eqsToGraph (see below) and
-- showEqsOrGraph 7 (see Ecom).
			 
 connectEqs :: [String] -> [TermS] -> [TermS]
 connectEqs [x] [t] = [mkArc x [] t]
 connectEqs xs ts   = f 0 xs $ addNatsToPoss ts
                      where f n (x:xs) ts = f (n+1) xs $ map (mkArc x [n]) ts
			    f _ _ ts      = ts

 mkArc :: String -> [Int] -> TermS -> TermS
 mkArc x p = f where f (F z ts) = if x == z then if null ts then mkPos p
		     				 else applyL (mkPos p) ts
 					    else F z $ map f ts
		     f t@(V z)  = if x == z then mkPos p else t
		     f t        = t

-- eqsToGraph is eqs selects the maximal elements of the separated right-hand 
-- sides of eqs. 
-- eqsToGraph is used by graphToTree (see Epaint), simplifyS stateflow, 
-- simplifyT auto/postflow/subsflow (see Esolve), buildKripke, showEqsOrGraph, 
-- showMatrix and showRelation (see Ecom).

 eqsToGraph :: [Int] -> [RegEq] -> TermS
 eqsToGraph [] eqs = eqsToGraph (indices_ eqs) eqs
 eqsToGraph is eqs = case maxis subGraph vs of [t] -> t
					       ts -> F "<+>" $ addNatsToPoss ts
                 where (zs,ts) = unzipEqs eqs
	               t = mkEqsConjunct zs $ connectEqs zs ts
		       us = subterms $ separateTerms t is
	               vs = case t of F "&" _ -> map (f . (us!!)) is
	                              _ -> [dropHeadFromPoss $ getSubterm t [1]]
	               f t = drop2FromPoss $ getSubterm t [1]

 eqsToGraphx :: String -> [RegEq] -> TermS
 eqsToGraphx x eqs = eqsToGraph is eqs
 		     where is = case search ((== x) . root) $ snd 
 		     					    $ unzipEqs eqs of 
 			             Just i -> [i]
 			             _ -> []

 type Node = ([Int],String,[[Int]])
 type Partition = ([Int] -> [Int],[[Int]])
	             
-- collapse b t recognizes the common subterms of t and builds a collapsed
-- tree without common subtrees (see Huth, Ryan, Logic in Computer Science,
-- p. 334f.). collapse builds up a node partition (h,dom), starting out from
-- (id,[]) and proceeding bottom-up through the levels of t. dom is the domain
-- of h that consists of all nodes with h p =/= p. 
-- b = True  --> arrows point to the right.
-- b = False --> arrows point to the left.
 
 collapse b t = fst $ foldC (collapseLoop b) g (u,(id,[])) [0..height u-1]
		where u = collapseCycles t; g (t,_) (u,_) = t == u

 collapseLoop b (t,part) i = (setPointers t part',part')
                         where part' = chgPart part $ if b then s else reverse s
			       s = level (mkNodes t) i

-- level nodes i returns the nodes from which a leaf is reachable in i steps.

 level :: [Node] -> Int -> [Node]
 level nodes = f where f 0 = filter (null . pr3) nodes
		       f i = filter (p . pr3) nodes
		             where p = supset $ map pr1 $ f $ i-1

-- chgPart part nodes adds each node n of nodes to part by setting n and all 
-- equivalent nodes to the same h-value.
 
 chgPart :: Partition -> [Node] -> Partition
 chgPart part = f
    where f (x:s) = g x s $ f s
	  f _     = part
	  g :: Node -> [Node] -> Partition -> Partition
	  g node@(p,x,ps) ((q,y,qs):nodes) part@(h,dom) =
                if x == y && map h ps == map h qs
                then if isPos x then (upd (upd h p r) q r, p:q:dom)
		     		else (upd h p $ h q, p:filter (not . (p<<)) dom)
		else g node nodes part
		where r = getPos x
          g _ _ part = part

-- mkNodes t translates t into a list of all triples consisting of the position,
-- the label and the positions of the direct successors of each node of t.

 mkNodes :: TermS -> [Node]
 mkNodes (V x)    = [([],x,[])]
 mkNodes (F x ts) = ([],x,map (:[]) is):concatMap h is
		    where is = indices_ ts
			  h i = map g $ mkNodes $ ts!!i
		                where g (p,x,ps) = (i:p,x,map (i:) ps)
 mkNodes _        = [([],"blue_hidden",[])]

-- collapseCycles t removes all duplicates of cycles of t.

 collapseCycles t = f t [(u,v) | u@(_,p) <- cycles, v@(_,q) <- cycles, p < q]
       where cycles = foldl g [] $ cyclePoss [] t
	     g cs p = if any ((<< p) . snd) cs then cs 
		      else (getSubterm1 t p,p):[u | u@(_,q) <- cs, not $ p << q]
	     f t ((up@(u,p),(v,q)):pairs) = 
		 if eqGraph u v 
		 then f (mapT g $ replace t p w) [p | p@(v,_) <- pairs, v /= up]
		 else f t pairs
	         where w = V $ trace t $ q++getRoot u v
		       g x = if isPos x && getPos x == p then root w else x
	     f t _ = t
	     getRoot u = head . filterPositions (== (root u))
	     cyclePoss p (F _ ts) = concat $ zipWithSucs cyclePoss p ts
	     cyclePoss p (V x)    = if isPos x && q <<= p then [q] else []
 				    where q = getPos x
	     cyclePoss _ _        = []

-- trace t p redirects a pointer from p to the first non-pointer that is
-- reachable from p.

 trace t p = if isPos x then trace t $ getPos x else mkPos0 p
             where x = label t p
 
 composePtrs t = mapT f t where f x = if isPos x && isPos y 
 				      then trace t $ getPos y else x
				      where y = label t $ getPos x

-- setPointers t (h,dom) replaces each subterm of t whose position p is in dom
-- by trace t $ h p.
			     
 setPointers :: TermS -> Partition -> TermS
 setPointers t (h,dom) = f [] t
 		     where f p (F x ts) = g p $ F x $ zipWithSucs f p ts
                           f p t        = g p t
			   g p u = if p `elem` dom then V $ trace t $ h p else u

-- collapseNodes f t sets pointers from the predecessors of all leaves of t
-- whose label satisfies f to the first leaf with this property. 
			   
 collapseNodes :: (String -> Bool) -> TermS -> TermS
 collapseNodes f t = setPointers t $ chgPart (id,[]) $ filter (f . pr2) 
 				   $ mkNodes t
				   
-- collapseVars is used by axsToSimpls, simplifyF and simplifyA (see Esolve).
		    
 collapseVars :: Sig -> TermS -> TermS
 collapseVars sig = collapseNodes (isVar sig) . f
-- collapseVars sig t = collapseNodes (`elem` (frees sig $ f t)) $ f t
          where f (F x ts@(_:_)) | sig.isHovar x 
	                   = F "$" [leaf x,h ts] where h [t] = f t
						       h ts  = mkTup $ map f ts
	        f (F x ts) = F x $ map f ts
	        f t        = t

-- expand/One n t p expands getSubterm t p. Each circle of u is unfolded n 
-- times expand/One dereferences all/one pointer(s) to the same subterm except
-- pointers located below their target.

-- expand is used by closedSub (see above) and the commands "expand", 
-- showSubtreePicts, showTreePict and simplifySubtree (see Ecom).

-- expandOne is used by eqsToGraph (see above), simplifyS "stateflow" (see 
-- Esolve) and the command "expand one" (see Ecom). 

 expand n t p = f n t p $ getSubterm t p
   where f n t p (F x ts)          = F x $ zipWithSucs (f n t) p ts
	 f n t p u@(V x) | isPos x = if connected t q p 
				     then if n == 0 then u else g $ n-1 else g n
				     where q = getPos x
				           v = movePoss t q p
				           g n = f n (replace0 t p v) p v
         f _ _ _ u 		   = u

 expandOne n t p = pr1 $ f n [] t p $ getSubterm t p
  where f n ps t p (F x ts) = (F x us,m,qs)
    		             where (us,_,m,qs)= foldr g ([],length ts-1,n,ps) ts
			           g v (us,i,n,ps) = (u:us,i-1,m,qs)
					    where (u,m,qs) = f n ps t (p++[i]) v
	f n ps t p u@(V x) | isPos x = if q <<= p 
				       then if n == 0 then (u,0,ps) else g $ n-1
			               else g n
		             where q = getPos x
			           v = movePoss t q p
				   g n = case searchGet ((== q) . fst) ps of
				         Just (_,(_,r)) -> (mkPos r,n,ps)
					 _ -> f n ((q,p):ps) (replace t p v) p v
        f n ps _ _ u = (u,n,ps)

-- SUBSTITUTIONS and UNIFIERS

 type Substitution a = a -> Term a
 type SubstS 	     = Substitution String

 domSub xs f = [x | x <- xs, let t = f x, x /= root t || notnull (subterms t)]
 
 for :: Eq a => Term a -> a -> Substitution a
 for = flip $ upd V

 forL :: Eq a => [Term a] -> [a] -> Substitution a
 forL = flip $ fold2 upd V

 eqSub xs f g = eqFun eqTerm f g xs

 subSubs xs fs gs = all (\f -> any (eqSub xs f) gs) fs

 meetSubs xs fs gs = [f | f <- fs, any (eqSub xs f) gs]

 joinSubs xs fs gs = h $ fs++gs
 		     where h (f:s) = f:[g | g <- h s, not $ eqSub xs f g]
			   h _     = []

 t>>>f = h t f []
  where h c@(V x) f p 		     = if isPos x then c else addToPoss p $ f x
	h c@(F x [t]) f p | binder x = mkBinder op zs $ g $ p++[0]
			               where (zs,_,g) = renameAwayFrom f xs t c
				             op:xs = words x
	h c@(F x ts) f p | lambda x  = F x $ concat $
	  			           zipWithSucs2 g p (evens ts) $ odds ts
		        where g p par t = [g1 par,g2 p]
			       where (_,g1,g2) = renameAwayFrom f xs t c
				     xs = foldT v par
			             v x xss = if x == root (f x) 
				    	       then concat xss else x:concat xss
	h (F x []) f p = case f x of V z -> F z []     -- isV (f x) ==> x is a
		                                       -- higher-order variable.
 			             t -> addToPoss p t
 	h (F x ts) f p = case f x of V z -> F z $ g2 g0
 			             F z [] -> F z $ g2 g0
                                     t -> F "$" [addToPoss (p++[0]) t,u]
	                 where g0 t n = h t f (p++[n])
		               g1 t n = h t f (p++[1,n])
			       g2 g = zipWith g ts $ indices_ ts
			       u = case ts of [t] -> g0 t 1
			       		      _ -> mkTup $ g2 g1
	h t _ _ = t
	renameAwayFrom f xs t c = (zs, g', h (g' t) f')
	                     where zs = map g xs
			     	   g' = renameAll g
				   f' = fold2 upd f zs $ map V zs
		                   g = fst $ renaming vc toBeRenamed
		                   vc = iniVC $ allSyms b c
				   b x = any (eqBase x) toBeRenamed
				   toBeRenamed = xs `meet` ys
				   ys = joinMap (frees . f) $ domSub (frees t) f
			           frees = allFrees $ const True

 andThen f g x = f x>>>g

-- translations between formulas and substitutions

 substToEqs f = map g where g x = F "=" [V x,addToPoss [1] $ f x]

 substToIneqs f = map g where g x = F "=/=" [V x,addToPoss [1] $ f x]
 
-- eqsToSubst is used by addSubst (see Ecom).

 eqsToSubst [] 	                = Just (V,[])
 eqsToSubst (F "=" [V x,t]:eqs) = do (f,xs) <- eqsToSubst eqs
 				     Just (for t x `andThen` f,x:xs)
 eqsToSubst (F "=" [t,V x]:eqs) = do (f,xs) <- eqsToSubst eqs
 				     Just (for t x `andThen` f,x:xs)
 eqsToSubst _		        = Nothing

-- RENAMING

 type VarCounter = String -> Int

-- splitVar x splits x into its non-numerical prefix and its numerical suffix.

 splitVar x = (base,k,b) 
        where b = just $ parse infixWord x
	      (base,k) = span (not . isDigit) $ if b then init $ tail x else f x
	      f ('!':x) = x; f x = x
		 
 base = pr1 . splitVar

-- eqBase x y checks the non-numerical prefixes of x and y for equality.
		      
 eqBase :: BoolFun String
 eqBase x y = base x == base y
		       
-- renameAwayFrom sig xs ts c renames the variables of xs that occur in ts away
-- from the variables of c.

 renameAwayFrom sig xs ts c = fst $ renaming vc toBeRenamed
 	                      where vc = iniVC $ allSyms b c
			            b x = any (eqBase x) toBeRenamed
	                            toBeRenamed = xs `meet` ys
				    ys = joinMap (sigVars sig) ts

-- iniVarCounter syms initializes the index counter vc for each string in syms.
-- If there is no n such that xn is in syms, then vc x is set to 0. If n is 
-- maximal such that xn is in syms, then vc x is set to n+1. 
-- iniVarCounter is used by initialize and parseSig (see Ecom).

 iniVarCounter (ps,cps,cs,ds,fs,hs) = iniVC $ ps++cps++cs++ds++fs++map fst hs

-- iniVC xs intializes the counter of the maximal non-numerical prefixes of all
-- x in xs. iniVC is used by >>>, renameAwayFrom and iniVarCounter (see above).
 
 iniVC :: [String] -> VarCounter
 iniVC = foldl f $ const 0 
     where f vc x = upd vc base $ max (vc base) $ if null k then 0 else read k+1
	            where (base,k,_) = splitVar x
				     
-- decrVC vc xs decreases the counter vc of all x in xs and is used by applyInd
-- (see Ecom).

 decrVC :: VarCounter -> [String] -> VarCounter
 decrVC = foldl f where f vc x = upd vc z $ vc z-1 where z = base x

-- renaming vc xs renames xn in xs to x(vc(x)). The values of vc are increased 
-- accordingly. renaming is used by >>>, renameAwayFrom (see above), renameApply
-- (see below), moveUp (see Esolve) and applyInd (see Ecom).

 renaming :: VarCounter -> [String] -> (String -> String,VarCounter)
 renaming vc = foldl f (id,vc) where f (g,vc) x = (upd g x y,incr vc base)
                                       where (base,_,b) = splitVar x
					     str = base++show (vc base)
					     y = if b then '`':str++"`" else str

-- renameApply cls sig t vc computes a renaming f of the variables of t and 
-- applies f to cls. renameApply is used by applyLoop/Random and 
-- applyToHeadOrBody (see Esolve), applyTheorem, narrowPar and rewritePar
-- (see Ecom).

 renameApply cls sig t vc = (map (renameAll f) cls,vc')
                 where (f,vc') = renaming vc [x | x <- sigVars sig t, noExcl x,
  				 		  any (isin x) cls]
 
 noExcl ('!':_:_) = False; noExcl _ = True

-- renameAll f t renames each occurrence of a symbol x in t to f(x) and is used
-- by >>>, renameApply (see above), simplifyF (see Esolve) and renameVar' 
-- (see Ecom).

 renameAll f (F x [t]) | binder x = mkBinder op (map f xs) $ renameAll f t
 		         	    where op:xs = words x
 renameAll f (F x ts) 		  = F (f x) $ map (renameAll f) ts
 renameAll f (V x)    		  = V $ f x
 renameAll _ t	      		  = t

-- renameFree f t renames each free occurrence of a symbol x in t to f(x) and is
-- used by match (see below) and subsumes (see Esolve).

 renameFree f (F x [t]) | binder x 
 		       = mkBinder op xs $ renameFree (fold2 upd f xs xs) t
		         where op:xs = words x
 renameFree f (F x ts) = F (f x) $ map (renameFree f) ts
 renameFree f (V x)    = V $ f x
 renameFree _ t	       = t

 getPrevious :: String -> String
 getPrevious x = if b then '`':str++"`" else str
                 where (base,k,b) = splitVar x; n = read k
		       str = if n == 0 then base else base++show (n-1)

-- UNIFICATION of terms and formulas

-- Result returns unifiers or error messages.

 data Result a = Def a | BadOrder | Circle [Int] [Int] | NoPos [Int] | NoUni | 
		 OcFailed String | ParUni SubstS [String] | TotUni SubstS

 instance Monad Result where Def a >>= h       = h a
                      	     BadOrder >>= _    = BadOrder
  		      	     Circle p q >>= _  = Circle p q
  		      	     NoPos p >>= _     = NoPos p
  		      	     NoUni >>= _       = NoUni
  		      	     OcFailed x >>= _  = OcFailed x
  		      	     ParUni a xs >>= _ = ParUni a xs
  		      	     TotUni a >>= _    = TotUni a
  		      	     return = Def

-- unify0 is used by applyAx, applyAxToTerm and applySingle (see Esolve).

 unify0 u redex t p sig xs = case unify u redex u t [] p V sig xs of
                                  Def (f,True) -> TotUni f
				  Def (f,_) -> if all (isV . f) dom
				  	       then NoUni else ParUni f dom
					       where dom = domSub xs f
				  result -> result

-- unify u u' t t' p q f sig xs computes the extension of f by a unifier of the
-- subterms u and u' at positions p resp. q of t resp. t'. If possible,
-- variables of xs are not replaced by other variables.

-- The unifier f is inherited because it may include higher-order variable
-- instantiations that must be passed to subterms.

-- The signature sig is inherited because unify must distinguish between
-- constructs, functs and hovars.

-- The Boolean result indicates whether a total (True) or only a partial unifier
-- (False) has been found. Partial unifiers create redex instances, but not 
-- reducts. However, as soon as a partial unifier can be completed to a total
-- one, the corresponding narrowing step will indeed be executed ("needed
-- narrowing").

-- unify is used by unify0 (see above), unifyAC (see below) and unifyAct 
-- (see Ecom).

 unify t@(V x) u@(V y) _ _ _ _ f _ xs
   | x == y                   = Def (f,True)
   | not (isPos x || isPos y) = Def (andThen f g,True)
		              where g = if x `elem` xs then for t y else for u x

 unify (V x) u t t' p q f sig xs
   | isPos x   = if r == q then Def (f,True)
		 else if r << p then Circle r q
		      else if r `elem` positions t
			   then unify v u (replace t p v) t' p q f sig xs
		           else NoPos r
   | True      = if isin x u then OcFailed x else Def (andThen f $ for u x,True)
   		 where r = getPos x; v = getSubterm t r

 unify u (V x) t t' p q f sig xs = unify (V x) u t' t q p f sig xs

 unify (F x [V z]) (F y us) t t' p q f sig xs
   | not (collector x) && x == y && length us > 1 
   	       = unify (V z) (mkTup us) t t' (p++[0]) q f sig xs

 unify (F x ts) (F y [V z]) t t' p q f sig xs
   | not (collector y) && x == y && length ts > 1 
   	       = unify (mkTup ts) (V z) t t' p (q++[0]) f sig xs

 unify (F x ts) (F y us) t t' p q f sig xs =
   	                  case unifyFuns x ts y us t t' p q f sig xs of
			       BadOrder -> unifyFuns y us x ts t' t q p f sig xs
	                       result -> result

 unify t u _ _ _ _ f _ _ = if bothHidden t u then Def (f,True) else NoUni

 unifyFuns x ts y us t t' p q f sig xs
   | x == y = if b then (if permutative x then unifyBag else unify')
   			ts us t t' ps qs f sig xs else NoUni
   | sig.isHovar x && sig.isHovar y && b = if x `elem` xs then g x y else g y x
   | sig.hovarRel x y = if b then g y x
                             else if null ts 
			          then Def (andThen f $ for (F y us) x,True)
			          else NoUni
       where b = length ts == length us; dom = indices_ ts
             ps = succs p dom; qs = succs q dom
	     g x y = unify' ts us t t' ps qs (f `andThen` for (F x []) y) sig xs

 unifyFuns x _ "suc" [u] t t' p q f sig xs
   | just n              = unify (mkConst $ get n-1) u t t' [] (q++[0]) f sig xs
	                   where n = parse pnat x

 unifyFuns "[]" (u:us) ":" [v,v'] t t' p q f sig xs
	                 = unify' [u,mkList us] [v,v'] t t' (g p) (g q) f sig xs
	                   where g p = [p++[0],p++[1]]

 unifyFuns x _ y _ _ _ _ _ f sig _ = if sig.isDefunct x && not (sig.isHovar y)
				     then Def (f,False) else BadOrder

-- unify' and unifyBag try to unify lists resp. bags of trees. Both functions
-- are used by unifyFuns. unify' is also used by searchReds and applyMany 
-- (see Esolve).

 unify' [] [] _ _ _ _ f _ _ = Def (f,True)
 unify' (t:ts) (u:us) v v' (p:ps) (q:qs) f sig xs =
	                    do (f,b) <- unify (t>>>f) (u>>>f) v v' p q f sig xs
	                       let h = map (>>>f)
			       (f,c) <- unify' (h ts) (h us) v v' ps qs f sig xs
			       Def (f,b&&c)
 unify' _ _ _ _ _ _ _ _ _ = NoUni

 unifyBag [] _ _ _ _ _ f _ _ = Def (f,True)
 unifyBag (t:ts) us v v' (p:ps) qs f sig xs =
                     do (f,b,us) <- try us v v' p qs f
	                (f,c) <- unifyBag (map (>>>f) ts) us v v' ps qs f sig xs
			Def (f,b&&c)      
	             where try (u:us) v v' p (q:qs) f =
                                 case unify (t>>>f) (u>>>f) v v' p q f sig xs of
                                      Def (f,b) -> Def (f,b,map (>>>f) us)
				      _ -> do (f,b,us) <- try us v v' p qs f
		                              Def (f,b,u>>>f:us)
                           try _ _ _ _ _ _ = NoUni
 
 unifyBag _ _ _ _ _ _ _ _ _ = NoUni

-- unifyAC ts reds checks whether for all terms t in ts some term red in reds
-- unifies with t. If the check succeeds, then unifyAC returns the most general
-- unifier f and all terms of reds that were not unified with terms of ts.
-- unifyAC is used by applySingle (see Esolve).

 unifyAC (t:ts) reds f sig xs = do (f,rest) <- g reds (length reds-1)
	                           let h = map (>>>f)
	                           unifyAC (h ts) (h rest) f sig xs
                where g reds i = do guard $ i >= 0
                                    case unify t red t red [] [] f sig xs of
                                         Def (f,True) -> Just (f,context i reds)
			                 _ -> g reds (i-1)
			         where red = reds!!i
 unifyAC _ reds f _ _ = Just (f,reds)

-- unifyS sig xs t t' substitutes only variables of xs and neither dereferences
-- pointers nor finds partial unifiers (see above). 
-- unifyS is used by simplifyF (see Esolve) and unifySubtrees (see Ecom).

 unifyS sig _ (V x) (V y) | x == y = Just V
 unifyS sig xs (V x) t    | x `elem` xs && x `notIn` t = Just $ t `for` x
 unifyS sig xs t (V x)    | x `elem` xs && x `notIn` t = Just $ t `for` x
 unifyS sig xs (F x ts) (F y us)   = unifySFuns sig xs x ts y us ++
 				     unifySFuns sig xs y us x ts
 unifyS sig _ t u		   = do guard $ bothHidden t u; Just V

 unifySFuns sig xs x ts y us
   | sig.hovarRel x y && x `elem` xs = if b
        then do
            g <- unifyS' sig xs (h ts) $ h us
            Just $ f `andThen` g
        else do
            guard $ null ts
            Just $ F y us `for` x
   | x == y && b = (if permutative x then unifySBag else unifyS') sig xs ts us 
                                          where b = length ts == length us
					  	f = F y [] `for` x
						h = map (>>>f)
 unifySFuns sig xs x _ "suc" [t] | just n = unifyS sig xs (mkConst $ get n-1) t
			  	            where n = parse pnat x
 unifySFuns sig xs "[]" (t:ts) ":" [u,v]  = unifyS' sig xs [t,mkList ts] [u,v]
 unifySFuns _ _ _ _ _ _ 		  = Nothing

-- unifyS' and unifySBag try to unify lists resp. bags of trees.

 unifyS' sig xs (t:ts) (u:us) = do f <- unifyS sig xs t u
 				   let h = map (>>>f)
	   		           g <- unifyS' sig xs (h ts) $ h us
	                           Just $ f `andThen` g
 unifyS' _ _ _ _ = Just V

 unifySBag sig xs (t:ts) us = do
                            (f,us) <- try us
                            g <- unifySBag sig xs (map (>>>f) ts) us
                            Just $ f `andThen` g
                              where try us = do
                                        u:us <- Just us
                                        case unifyS sig xs t u of
                                            Just f -> Just (f,map (>>>f) us)
                                            _ -> do (f,us) <- try us
                                                    Just (f,u>>>f:us)
 unifySBag _ _ _ _ = Just V


-- MATCHING of terms and formulas

-- match sig xs t u computes a substitution f that extends u to t (t matches u).
-- Only the variables of xs are substituted. For all x in xs, the pointers of 
-- f(x) are decreased by the position of x in u. match is used by matchSubs
-- (see below), subsumes and simplifyA (see Esolve).

 match :: Sig -> [String] -> TermS -> TermS -> Maybe SubstS
 match sig xs = h []
     where g p = [p++[0],p++[1]]
           h _ (V x) (V y) | x == y  = Just V
           h p t (V y) | y `elem` xs = Just $ dropFromPoss p t `for` y
           h p t@(F x ts) (F y us) 
                | sig.hovarRel y x && y `elem` xs =
                    if b then do
                        g <- match' ps (h ts) $ h us
                        Just $ f `andThen` g
                    else do
                        guard $ null us
                        Just $ dropFromPoss p t `for` y
                | x == y && b = if permutative x then matchBag ps ts us 
                                else match' ps ts us
            where b = length ts == length us
                  f = F x [] `for` y
                  h = map (>>>f)
                  ps = succsInd p ts
           h p (F x [t]) (F y [u]) | binder x && binder y && opx == opy =
	                        h (p++[0]) (renameFree (fold2 upd id xs ys) t) u
				where opx:xs = words x; opy:ys = words y
	   h p t (F "suc" [u]) | just n = h (p++[0]) (mkConst $ get n-1) u
			  	        where n = parsePnat t
           h p (F "suc" [t]) u | just n = h (p++[0]) t $ mkConst $ get n-1
			  	        where n = parsePnat u
	   h p (F "[]" (t:ts)) (F ":" [u,v]) = match' (g p) [t,mkList ts] [u,v]
           h p (F ":" [u,v]) (F "[]" (t:ts)) = match' (g p) [u,v] [t,mkList ts]
           h _ t u 			     = do guard $ bothHidden t u; Just V
	   match' (p:ps) (t:ts) (u:us) = do f <- h p t u; g <- match' ps ts us
	   				    par f xs g $ meetVars xs us
			                 where xs = sigVars sig u
	   match' [] _ _               = Just V
	   matchBag (p:ps) (t:ts) us   = do (f,u,us) <- try us
	   				    g <- matchBag ps ts us
					    let xs = sigVars sig u
	   				    par f xs g $ meetVars xs us
			       where try us = do u:us <- Just us
	   		                         case h p t u of 
					              Just f -> Just (f,u,us)
                                                      _ -> do (f,v,us) <- try us
						              Just (f,v,u:us)
           matchBag [] _ _             = Just V
	   meetVars xs = meet xs . concatMap (sigVars sig)
	   par f xs g zs = do guard $ eqTerms (map f zs) $ map g zs
                              Just $ \x -> if x `elem` xs then f x else g x

-- matchSubs sig xs t u computes a substitution f that extends u to the subbag 
-- t' of t that matches u. It is assumed that t' is unique. The other values of
-- matchSubs are the list of all (bag) elements of t, the list of positions of 
-- the bag elements of t' within t and a bit denoting whether or not the redex t
-- has been treated as a bag. matchSubs is used by simplReducts (see Esolve).

 matchSubs :: Sig -> [String] -> TermS -> TermS 
 	                               -> Maybe (SubstS,[TermS],[Int],Bool)
 matchSubs sig xs t u = case (t,u) of
			     (F "()" [t,lab],F "()" [u,pat])
			       -> do (f,ts,is,bag) <- matchSubs sig xs t u
			             g <- match sig xs (lab>>>f) $ pat>>>f
				     Just (f `andThen` g,ts,is,bag)
                             (F "^" ts,F "^" us) | length us < length ts 
			       -> do vs <- mapM (g1 ts) us
			             let (fs,is) = unzip vs
			             Just (foldl1 andThen fs,ts,is,True)
			     (F "^" ts,_) | root u /= "^"
			       -> searchGetM (g2 ts) $ indices_ ts
			     _ -> do f <- match sig xs t u
			             Just (f,[t],[0],False)
		        where g1 ts u = searchGetM g $ indices_ ts
		                        where g i = do f <- h ts i u; Just (f,i)
		              g2 ts i = do f <- h ts i u; Just (f,ts,[i],True)
			      h ts i u = match sig xs (ts!!i) u

-- TREES with NODE COORDINATES

 type Sizes = (Int,String -> Int)
   
 sizes0 = (6,const 0)

-- mkSizes font xs takes a font and a list xs of strings and returns the actual
-- font size and a function that maps each string of xs to its width. 
-- mkSizes is used by Epaint and Ecom.

 mkSizes :: TkFont -> [String] -> Request Sizes
 mkSizes font xs = do widths <- mapM font.getTextWidth $ map delQuotes xs
 	              let f x = case lookup x $ zip xs widths of Just w -> w
		      					         _ -> 1
			  g x = if x `elem` xs then f x
			        else maximum $ 1:[f y | y <- xs, lg x == lg y]
                      return (h $ read $ words font.fontName!!1,g)
		   where lg = length . delQuotes
			 h n | n < 7  = 6
			     | n < 8  = 7
			     | n < 10 = 8
			     | n < 13 = 10
			     | n < 16 = 13
			     | True   = 16

-- coordTree w (hor,ver) p t adds coordinates to the nodes of t such that p is
-- the leftmost-uppermost corner of the smallest rectangle enclosing t.
-- w is the actual node width function, hor is the horizontal space between 
-- adjacent subtrees. ver is the vertical space between adjacent tree levels.
-- coordTree cuts off all subtrees whose root labels start with @.

 type TermSP = Term (String,Pos)

 halfWidth :: (String -> Int) -> String -> Int
 halfWidth w a = if isPos a then 4 else w a`div`2

 coordTree :: (String -> Int) -> Pos -> Pos -> TermS -> TermSP
 coordTree w _ p (V ('@':_))   = V ("@",add1 p $ halfWidth w "@")
 coordTree w _ p (V a)         = V (a,add1 p $ halfWidth w a)
 coordTree w _ p (F ('@':_) _) = F ("@",add1 p $ halfWidth w "@") []
 coordTree w _ p (F a [])      = F (a,add1 p $ halfWidth w a) []
 coordTree w spread@(hor,ver) (x,y) (F a ts) = if diff <= 0 then ct' 
 					       else transTree1 (diff`div`2) ct'
        	  where diff = halfWidth w a-foldT f ct+x
		        ct:cts = map (coordTree w spread (x,y+ver)) ts
			cts' = transTrees w hor [ct] cts
		        ct' = F (a,((g (head cts')+g (last cts'))`div`2,y)) cts'
		        f (a,(x,_)) xs = maximum $ x+halfWidth w a:xs
			g (V (_,(x,_)))   = x
			g (F (_,(x,_)) _) = x

-- transTrees w hor us vs orders the trees of us++vs horizontally with a
-- horizontal space of hor units between adjacent trees. transTrees takes into
-- account different heights of adjacent trees by shifting the trees to the left
-- or right such that parts of a tree may occur below an adjacent one.
-- offset cts left computes the offset by which the trees of cts must be shifted
-- in order to avoid that they overlap a neighbour with left margins on the left.

 transTrees :: (String -> Int) -> Int -> [TermSP] -> [TermSP] -> [TermSP]
 transTrees w hor = f 
       where f us (t:ts) = if d < 0 then f (map (transTree1 $ -d) us++[t]) ts
                           else f (us++[transTree1 d t]) $ map (transTree1 d) ts
                           where d = maximum (map h us)+hor 
	      	                 h u = f (+) maximum u-f (-) minimum t
			               where f = g $ min (height t) $ height u
             f us _      = us
	     g _ op _ (V (a,(x,_)))    = h op a x
	     g 1 op _ (F (a,(x,_)) _)  = h op a x
	     g n op m (F (a,(x,_)) ts) = m $ h op a x:map (g (n-1) op m) ts
	     h op a x = op x $ halfWidth w a

-- shrinkTree y ver t shrinks t vertically such that ver becomes the distance
-- between a node and its direct suces(0,upb)sors. y is the y-coordinate of the 
-- root.

 shrinkTree y ver (V (a,(x,_)))     = V (a,(x,y))
 shrinkTree y ver (F (a,(x,_)) cts) = F (a,(x,y)) $
				        map (shrinkTree (y+ver) ver) cts
 
-- cTree t ct replaces the node entries of t by the coordinates of ct.

 cTree (F _ ts) (F (_,p) cts) = F (show p) $ zipWith cTree ts cts
 cTree (V _) (V (_,p))        = V $ show p
 cTree _     (F (_,p) _)      = mkConst p

-- getSubtree ct x y returns the pair (ct',p) consisting of the subtree ct'
-- of ct close to position (x,y) and the tree position p of ct' within ct. 
-- getSubtree performs breadthfirst search and binary search at each tree level.

 getSubtree ct = getSubtrees [([],ct)]

 getSubtrees pcts@((_,ct):_) x y = if abs (y-y') < 10 then getSubtreeX pcts x
	  	                   else let f (p,ct) = zipSucs p (subterms ct)
		                        in getSubtrees (concatMap f pcts) x y
		                   where (_,(_,y')) = root ct
 getSubtrees _ _ _               = Nothing

 getSubtreeX [] _   = Nothing
 getSubtreeX pcts x = if abs (x-x') < 10 then Just pct
		      else if x < x' then getSubtreeX (take middle pcts) x
		     	             else getSubtreeX (drop (middle+1) pcts) x
	              where middle = length pcts`div`2
			    pct@(_,ct) = pcts!!middle
		            (_,(x',_)) = root ct

-- ENUMERATORS

 data Align_ a = Compl a a (Align_ a) | Equal_ [a] (Align_ a) | 
 		 Ins [a] (Align_ a) | Del [a] (Align_ a) | End [a] 
		 deriving (Show,Eq)

 parseAlignment (F "compl" [u,t,v]) = do t <- parseAlignment t
                                         Just $ Compl (showTerm0 u) 
					 	      (showTerm0 v) t
 parseAlignment (F "equal" (t:ts))  = do t <- parseAlignment t
                                         Just $ Equal_ (map showTerm0 ts) t
 parseAlignment (F "insert" (t:ts)) = do t <- parseAlignment t
                                         Just $ Ins (map showTerm0 ts) t
 parseAlignment (F "delete" (t:ts)) = do t <- parseAlignment t
                                         Just $ Del (map showTerm0 ts) t
 parseAlignment t 		    = do F "end" ts <- Just t
 				         Just $ End $ map showTerm0 ts

-- mkAlign global xs ys generates ALIGNMENTS of xs and ys by recursive 
-- tabulation and optimization.
 
 mkAlign :: Eq a => Bool -> [a] -> [a] -> (a -> a -> Bool) -> [Align_ a]
 mkAlign global xs ys compl = (if global then id else maxima maxmatch)
 		              $ align!(0,0)
  where lg1 = length xs; lg2 = length ys
        align = mkArray ((0,0),(lg1,lg2)) $ maxima matchcount . f
          where f (i,j) = if i == lg1 then if j == lg2 then [End []] else insert
	                  else if j == lg2 then delete 
			  else if x == y then equal++append
			  else if compl x y || compl y x then match++append 
			  				 else append
		          where x = xs!!i; y = ys!!j; ts = align!(i+1,j+1)
                                equal  = map (Equal_ [x]) ts
				match  = map (Compl x y) ts
				insert = map (Ins [y]) $ align!(i,j+1)
				delete = map (Del [x]) $ align!(i+1,j)
				append = insert++delete

-- mkPali xs recognizes locally separated PALINDROMES within xs by recursive
-- tabulation and optimization.

 mkPali :: Eq a => [a] -> (a -> a -> Bool) -> [Align_ a]
 mkPali xs compl = align!(0,lg)
  where lg = length xs
        align = mkArray ((0,0),(lg,lg)) $ maxima matchcount . f
          where f (i,j) = if i == j then [End []]
	  		  else if i+1 == j then [End [x]]
			  else if x == y then equal++append
			  else if compl x y || compl y x then match++append 
			  				 else append
		          where x = xs!!i; y = xs!!(j-1); ts = align!(i+1,j-1)
			        equal  = map (Equal_ [x]) ts 
				match  = map (Compl x y) ts
				append = map (Ins [y]) (align!(i,j-1)) ++
				         map (Del [x]) (align!(i+1,j))

 compress :: Align_ String -> Align_ String		
 compress t = case t of Equal_ xs (Equal_ ys t) -> compress $ Equal_ (xs++ys) t
 			Ins xs (Ins ys t) -> compress $ Ins (xs++ys) t
			Del xs (Del ys t) -> compress $ Del (xs++ys) t
			Equal_ xs t       -> Equal_ xs $ compress t
			Ins xs t          -> Ins xs $ compress t
			Del xs t      	  -> Del xs $ compress t
			Compl x y t 	  -> Compl x y $ compress t
			End _		  -> t

-- matchcount t computes the number of matches of t of length 1.

 matchcount :: Align_ a -> Int
 matchcount t = case t of Compl _ _ t -> matchcount t+1
 			  Equal_ _ t -> matchcount t+1
			  Ins _ t -> matchcount t
			  Del _ t -> matchcount t
			  _ -> 0

-- maxmatch t returns the length of the maximal match of t.

 maxmatch :: Align_ a -> Int
 maxmatch = f False 0 0 where f False _ n (Compl _ _ t) = f True 1 n t
                 	      f _ m n (Compl _ _ t)     = f True (m+1) n t
			      f False _ n (Equal_ _ t)  = f True 1 n t
			      f _ m n (Equal_ _ t)      = f True (m+1) n t
			      f _ m n (Ins _ t)         = f False 0 (max m n) t
			      f _ m n (Del _ t)         = f False 0 (max m n) t
			      f _ m n _	                = max m n

-- mkDissects c c' ns b h computes all DISSECTIONS d of a rectangle with
-- breadth b, height h and the cardinality among ns such that all elements of d
-- satisfy c and d satisfies c'.

 mkDissects :: ((Int,Int,Int,Int) -> Bool) -> BoolFun [(Int,Int,Int,Int)] 
	       -> [Int] -> Int -> Int -> [TermS]

 mkDissects c c' ns b h = map (Hidden . Dissect) $ joinBMap f ns
   where f n = joinBMap (flip (disSucs m) ([(0,0,b,h)],[],[]))
	                                  [max 0 (n+1-b-h)..m-1] where m = n-1
         disSucs 0 0 (top,left,inner) = if all c topleft && c' inner topleft
	                                then [topleft++inner] else []
				        where topleft = top++left
         disSucs n k trip | n == 0 = ds1                 -- n = number of splits
                          | k == 0 = ds2                 -- k = number of joins
                          | True   = ds1 `join` ds2
              where ds1 = if just trip' then disSucs n (k-1) $ get trip' else []
                          where trip' = joinHV c c' trip
	            ds2 = joinBMap (disSucs (n-1) k) $ splitV trip++splitH trip

 splitV ((0,0,b,h):top,left,inner) = if b < 2 then [] else map f [1..b-1]
	                      where f i = ((0,0,i,h):(i,0,b-i,h):top,left,inner)

 splitH ((0,0,b,h):top,left,inner) = if h < 2 then [] else map f [1..h-1]
	                      where f i = ((0,0,b,i):top,(0,i,b,h-i):left,inner)

 joinHV c c' ((0,0,b,h):(i,0,b',h'):top,left,inner)
          | h' > h && c r && c' inner [r] = Just ((0,0,b+b',h):top,left,r:inner)
		                            where r = (i,h,b',h'-h)
 joinHV c c' ((0,0,b,h):top,(0,i,b',h'):left,inner)
          | b' > b && c r && c' inner [r] = Just ((0,0,b,h+h'):top,left,r:inner)
	                                    where r = (b,i,b'-b,h')
 joinHV _ _ _                             = Nothing

-- dissection constraints

 dissConstr :: Int -> Int -> TermS -> Maybe ((Int,Int,Int,Int) -> Bool, [Int],
				             BoolFun [(Int,Int,Int,Int)])
 dissConstr b h (F "|" ts)       = do fnsgs <- mapM (dissConstr b h) ts
                                      let (fs,nss,gs) = unzip3 fnsgs
				      Just (foldl1 (|||) fs,foldl1 join nss,
				            foldl1 f gs)
				   where f g1 g2 rs rs' = g1 rs rs' || g2 rs rs'
 dissConstr b h (F "&" ts)       = do fnsgs <- mapM (dissConstr b h) ts
                                      let (fs,nss,gs) = unzip3 fnsgs
				      Just (foldl1 (&&&) fs,foldl1 meet nss,
				            foldl1 f gs)
				   where f g1 g2 rs rs' = g1 rs rs' && g2 rs rs'
 dissConstr b h (F "area" [m])   = do m <- parseNat m
                                      let f (_,_,b,h) = b*h <= m
				          n = ceiling $ fromInt (b*h)/fromInt m
				      guard $ n > 1; Just (f,[n],const2 True)
 dissConstr b h (F "area" [m,n]) = do m <- parseNat m
                                      n <- parseNat n
                                      let f (_,_,b,h) = m <= bh && bh <= n
				                        where bh = b*h
				          bh = fromInt (b*h)
				          ns = [ceiling (bh/fromInt n)..
				                ceiling (bh/fromInt m)]
				      guard $ notnull ns
				      Just (f,ns,const2 True)
 dissConstr b h (F "brick" [])   = do let ns = [2..b*h] 
 				      guard $ notnull ns
 				      Just (const True,ns,f)
                                where f rs ((0,_,_,_):rs') = f rs rs'
				      f rs (rect@(x,y,_,h):rs')
				            = case search (c x y h) $ rs++rs' of
		                                   Just i -> False
						   _ -> f (rect:rs) rs'
	                              f rs _ = True
			              c x y h (x',y',_,h') =
				            x' == x && (y' == y+h || y == y'+h')
 dissConstr b h (F "eqarea" [n]) = do n <- parseNat n; guard $ n > 1
				      let f (_,_,b',h') = b'*h' == (b*h)`div`n
				      Just (f,[n],const2 True)
 dissConstr b h (F "factor" [p]) = do p <- parseNat p
                                      let ns = [2..b*h]
				          f (_,_,b,h) = p*b == h || p*h == b
                                      guard $ notnull ns
				      Just (f,ns,const2 True)
 dissConstr b h (F "hori" [])    = do let ns = [2..b*h]; f (_,_,b,h) = b >= h
 				      guard $ notnull ns
				      Just (f,ns,const2 True)
 dissConstr b h (F "sizes" [ns]) = do ns <- parseNats ns; guard $ all (> 1) ns
				      Just (const True,ns,const2 True)
 dissConstr b h (F "True" _)     = do let ns = [2..b*h] 
 				      guard $ notnull ns
				      Just (const True,ns,const2 True)
 dissConstr b h (F "vert" [])    = do let ns = [2..b*h]; f (_,_,b,h) = b <= h 
 				      guard $ notnull ns
				      Just (f,ns,const2 True)
 dissConstr _ _ _                = Nothing

-- mkPartitions c n computes all NESTED PARTITIONS of a list with n elements,
-- i.e. all trees with n leaves and outdegree =/= 1, that satisfy c.

 mkPartitions :: (Int -> [Term Int] -> Bool) -> Int -> TermS -> [TermS]
 mkPartitions c n = map (mapT show) . mkTrees c n . ht n
               where ht n (F "&" ts)             = minimum $ map (ht n) ts
 		     ht n (F "|" ts)             = maximum $ map (ht n) ts
		     ht n (F "bal" [])           = floor $ logBase 2 $ fromInt n
                     ht _ (F "hei" [m]) | just n = get n where n = parseNat m
		     ht n _	       	         = n-1

-- Given a list s with n elements, mkTrees c n h computes the nested partitions
-- ps of s such that ps satisfies the constraint c, the nesting degree of ps is
-- at most h and, at all nesting levels, each subpartition of ps has at least
-- two elements. mkTrees c n h represents the partitions as trees.

 mkTrees c n h = if c 1 ts then map (mkTree 1) $ foldl f [ts] [0..h-1] else []
   where mkTree _ [t] = t
 	 mkTree n ts  = F n ts
	 ts = replicate n $ F (h+1) []
	 f parts h = concatMap (successors 1 h) parts
	 -- parts s returns all list partitions of s.
	 parts :: [a] -> [[[a]]]
	 parts [a]   = [[[a]]]
	 parts (a:s) = concatMap glue $ parts s
	      	       where glue part@(s:rest) = [[a]:part,(a:s):rest]		     
         successors n h ts = filter (c n) $ newparts h ts
               where newparts _ []  = [[]]
                     newparts 0 [t] = [[t]]
                     newparts 0 ts  = map (map $ mkTree $ n+1) $ init $ parts ts
                     newparts h (F _ us:ts)
		                    = if null us then map (F k []:) ps
            			      else concatMap f $ successors k (h-1) us
 			              where k = n+1
				            ps = newparts h ts
				            f vs = map (mkTree k vs:) ps
               -- newparts h ts computes a list of lists of trees up to height h
	       -- from the list ts of trees up to height h-1.

-- partition constraints

 partConstr :: TermS -> Maybe (Int -> [Term Int] -> Bool)

 partConstr (F "|" ts)      = do fs <- mapM partConstr ts
                                 Just (foldl1 h fs)
				 where h f g n ts = f n ts || g n ts
 partConstr (F "&" ts)      = do fs <- mapM partConstr ts
                                 Just (foldl1 h fs)
				 where h f g n ts = f n ts && g n ts
 partConstr (F "alter" [])  = Just (\_ ts -> all isLeaf ts ||
                                             all isLeaf (evens ts) &&
                                             all isInner (odds ts))
 partConstr (F "bal" [])    = Just (\_ ts -> allEqual (map height ts))
 partConstr (F "eqout" [])  = Just (\_ ts -> allEqual (map (length . subterms)
 						      (innerNodes ts)))
 partConstr (F "hei" [m])   = do m <- parseNat m
                                 Just (\n _ -> n < m)
 partConstr (F "levmin" []) = Just (\n ts -> null ts || n <= length ts)
 partConstr (F "levmax" []) = Just (\n ts -> length ts <= max 2 n)
 partConstr (F "out" [m,n]) = do m <- parseNat m
 				 n <- parseNat n
                                 let f _ ts = all g (map (length . subterms)
 						         (innerNodes ts))
	                             g lg = m <= lg && lg <= n
	                         Just f
 partConstr (F "sym" [])    = Just (\_ ts -> pal (map (length . subterms) ts))
 partConstr (F "True" _)    = Just (const2 True)
 partConstr _               = Nothing

 innerNodes ts = filter isInner ts

 isInner (F _ (_:_)) = True
 isInner _           = False

 isLeaf = not . isInner
