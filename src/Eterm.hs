{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-|
Module      : Eterm
Description : Functions and parser for Term.
Copyright   : (c) Peter Padawitz, January 2021
                  Jos Kusiek, January 2021
License     : BSD3
Maintainer  : peter.padawitz@udo.edu
Stability   : experimental
Portability : portable

Eterm contains:

    * basic functions on lists and other types

    * a parser of symbols and numbers

    * a parser of terms and formulas

    * a compiler of Kripke models

    * the tree type 'Term'

    * an unparser of terms and formulas

    * functions for flowtree analysis (used by the simplifier)

    * operations on formulas

    * operations on trees, tree positions and term graphs

    * substitution, unification and matching functions

    * a compiler of trees into trees with coordinates

    * functions that enumerate terms (used by the enumerator template)
-}
module Eterm where

import Prelude ()
import qualified Base.Haskell as Haskell
import Base.System

import Data.Array

infixl 0 `onlyif`
infixl 6 `minus`, `minus1`

infixr 2 |||, `join`, `join1`
infixr 3 &&&, `meet`
infixr 4 ***, +++, -+-

infix 4 `subset`, `eqset`

infixl 9 &

(&) :: a -> (a -> b) -> b 
(&) = (Haskell.&)

just :: Maybe a -> Bool
just = Haskell.isJust

get :: Maybe a -> a
get = Haskell.fromJust

nothing :: Maybe a -> Bool
nothing = Haskell.isNothing

onlyif :: String -> Bool -> String
str `onlyif` b = if b then str else ""

ifnot :: String -> Bool -> String
str `ifnot` b  = if b then ""  else str

seed :: Int
seed = 17489   

nextRand :: Integral a => a -> a
nextRand n = if tmp<0 then m+tmp else tmp
           where tmp = a*(n `mod` q) - r*(n `div` q)
                 a = 16807        -- = 7^5
                 m = 2147483647   -- = maxBound = 2^31-1
                 q = 127773       -- = m `div` a
                 r = 2836         -- = m `mod` a

type BoolFun a = a -> a -> Bool

pr1 :: (a, b, c) -> a
pr1 (a,_,_) = a
pr2 :: (a, b, c) -> b
pr2 (_,b,_) = b
pr3 :: (a, b, c) -> c
pr3 (_,_,c) = c

const2 :: a -> b -> c -> a
const2 = const . const

const3 :: a -> b -> c -> d -> a
const3 = const . const2

upd :: Eq a => (a -> b) -> a -> b -> a -> b
upd f a b x = if x == a then b else f x

upd2 :: (Eq a,Eq b) => (a -> b -> c) -> a -> b -> c -> a -> b -> c
upd2 f a b = upd f a . upd (f a) b

incr,decr :: Eq a => (a -> Int) -> a -> a -> Int
incr f x y = if x == y then f x+1 else f y
decr f x y = if x == y then f x-1 else f y

neg2 :: (Num t, Num t1) => (t, t1) -> (t, t1)
neg2 (x,y) = (-x,-y)

div2 :: (Fractional t, Fractional t1) => (t, t1) -> (t, t1)
div2 (x,y) = (x/2,y/2)

add1 :: Num a => (a,a) -> a -> (a,a)
add1 (x,y) a = (a+x,y)

add2,sub2 :: Num a => (a,a) -> (a,a) -> (a,a)
add2 (x,y) (a,b) = (a+x,b+y)
sub2 (x,y) (a,b) = (a-x,b-y)

apply2 :: (t -> t1) -> (t, t) -> (t1, t1)
apply2 f (x,y) = (f x,f y)

fromInt :: Int -> Double
fromInt = fromIntegral

fromInt2 :: (Int, Int) -> (Double, Double)
fromInt2 (x,y) = (fromInt x,fromInt y)

fromDouble :: Fractional a => Double -> a
fromDouble = realToFrac

fromDouble2 :: (Fractional t, Fractional t1) => (Double, Double) -> (t, t1)
fromDouble2 (x,y) = (fromDouble x,fromDouble y)

round2 :: (RealFrac b, Integral d, RealFrac a, Integral c) => (a,b) -> (c,d)
round2 (x,y) = (round x,round y)

square :: Integral b => [a] -> b
square = round . sqrt . fromInt . length

minmax4 :: (Num a, Num a1, Num a2, Num a3, Ord a, Ord a1, Ord a2, Ord a3) =>
           (a, a1, a2, a3) -> (a, a1, a2, a3) -> (a, a1, a2, a3)
minmax4 p (0,0,0,0) = p
minmax4 (0,0,0,0) p = p
minmax4 (x1,y1,x2,y2) (x1',y1',x2',y2') = (min x1 x1',min y1 y1',
                                           max x2 x2',max y2 y2')

mkArray :: Ix a => (a,a) -> (a -> b) -> Array a b
mkArray bounds f = array bounds [(i,f i) | i <- range bounds]

-- * Coloring

isBW,deleted :: Color -> Bool
isBW c     = c == black || c == white
deleted c  = c == RGB 1 2 3

fillColor :: Color -> Int -> Color -> Color
fillColor c i bgc = if c == black || deleted c then bgc else mkLight i c

outColor :: Color -> Int -> Color -> Color
outColor c i bgc = if deleted c then bgc else mkLight i c

-- | @nextCol@ computes the successor of each color c c on a chromatic circle of 
-- 6*255 = 1530 equidistant pure (or hue) colors. A color c is pure if c is 
-- neither black nor white and at most one of the R-, G- and B-values of c is 
-- different from 0 and 255.
nextCol :: Color -> Color

nextCol (RGB 255 0 n) | n < 255 = RGB 255 0 (n+1)        -- n = 0   --> red
nextCol (RGB n 0 255) | n > 0   = RGB (n-1) 0 255        -- n = 255 --> magenta
nextCol (RGB 0 n 255) | n < 255 = RGB 0 (n+1) 255        -- n = 0   --> blue 
nextCol (RGB 0 255 n) | n > 0   = RGB 0 255 (n-1)        -- n = 255 --> cyan 
nextCol (RGB n 255 0) | n < 255 = RGB (n+1) 255 0        -- n = 0   --> green
nextCol (RGB 255 n 0) | n > 0   = RGB 255 (n-1) 0        -- n = 255 --> yellow
nextCol c | isBW c || deleted c = c 
          | otherwise           = nextCol $ getHue c

getHue,complColor :: Color -> Color
getHue (RGB r g b) = RGB (f 0) (f 1) (f 2) where s = [r,g,b]
                                                 low:mid:_ = qsort rel [0,1,2] 
                                                 rel i j = s!!i <= s!!j
                                                 f i | i == low  = 0 
                                                     | i == mid  = s!!i
                                                     | otherwise = 255

isHue :: Color -> Bool
isHue (RGB r g b) = all (`elem` [0..255]) [r,g,b] &&
                      [[0,255],[255,0]] `shares` [[r,g],[g,b],[b,r]]

complColor c = iterate nextCol c!!765
  
-- | @hue mode col n i@ computes the i-th successor of c in a chromatic circle
-- of n <= 1530 equidistant pure colors.
hue :: Int -- ^ mode 
    -> Color -- ^ col
    -> Int -- ^ n
    -> Int -- ^ i
    -> Color
hue 0 col n i = iterate nextCol col!!(i*1530`div`n)
                                  -- round (fromInt i*1530/fromInt n)
hue 1 col n i | i > 0 = if odd i then complColor $ hue 1 col n $ i-1
                                 else nextColor 0 (n`div`2) $ hue 1 col n $ i-2
hue 2 col n i = if odd i then complColor d else d where d = hue 0 col n i
hue 3 col n i = if odd i then complColor d else d where d = hue 0 col (2*n) i
hue _ col _ _ = col

nextColor :: Int -> Int -> Color -> Color
nextColor mode n col  = hue mode col n 1

{- |
    @nextLight n i c@ adds i/n units of white (if @i@ is positive) resp. black
    (if @i@ is negative) pigment to c. If @i = n@ resp. @i = -n@, then @c@ turns
    white resp. black.
-}
nextLight :: Int -- ^ n
    -> Int -- ^ i
    -> Color -- ^ c
    -> Color
nextLight n i (RGB x y z) = RGB (f x) (f y) (f z)
     where f x | i > 0     = x+i*(255-x)`div`n -- i=n  --> f x = 255 (white)
               | otherwise = x+i*x`div`n       -- i=-n --> f x = 0   (black)

mkLight :: Int -> Color -> Color
mkLight = nextLight 42

light, dark :: Color -> Color
light   = nextLight 3 2
dark    = nextLight 3 $ -1

whiteback, blueback, greenback, magback, redback, redpulseback :: Background
whiteback = Background "bg_white"
blueback  = Background "bg_blue"
greenback = Background "bg_green"
magback   = Background "bg_magenta"
redback   = Background "bg_red"
redpulseback = Background "bg_redpulse"

-- * String functions

leader :: String -> String -> Bool
leader "" _  = False
leader x str = head (words x) == str

removeCommentL :: String -> String
removeCommentL ('-':'-':_) = []
removeCommentL (x:str)     = x:removeCommentL str
removeCommentL _           = []

removeComment :: (Eq a, Num a) => a -> String -> String
removeComment 0 ('-':'-':str) = removeComment 1 str
removeComment 0 ('{':'-':str) = removeComment 2 str
removeComment 0 (x:str)       = x:removeComment 0 str
removeComment 1 ('\n':str)    = '\n':removeComment 0 str
removeComment 1 (_:str)       = removeComment 1 str
removeComment 2 ('-':'}':str) = removeComment 0 str
removeComment 2 (_:str)       = removeComment 2 str
removeComment _ _             = []

removeDot :: String -> String
removeDot ('\n':'\n':'.':str) = removeDot str
removeDot ('\n':'.':str)      = removeDot str
removeDot (x:str)             = x:removeDot str
removeDot _                   = []

showStr :: Show a => a -> String
showStr x = show x `minus1` '\"'

showStrList :: Show a => a -> String
showStrList xs = show xs `minus` "[]\""

splitSpec :: String -> (String, String, String, String, String)
splitSpec = searchSig []
  where searchSig sig []   = (sig,[],[],[],[])
        searchSig sig rest
                  | take 7 rest == "axioms:" = searchAxioms sig [] $ drop 7 rest
                  | take 9 rest == "theorems:" =
                    searchTheorems sig [] [] $ drop 9 rest
                  | take 9 rest == "conjects:" =
                    searchConjects sig [] [] [] $ drop 9 rest
                  | take 6 rest == "terms:" = (sig, [], [], [], drop 6 rest)
                  | otherwise = searchSig (sig ++ [head rest]) $ tail rest
        searchAxioms sig axs []   = (sig,axs,[],[],[])
        searchAxioms sig axs rest
                  | take 9 rest == "theorems:" =
                    searchTheorems sig axs [] $ drop 9 rest
                  | take 9 rest == "conjects:" =
                    searchConjects sig axs [] [] $ drop 9 rest
                  | take 6 rest == "terms:" = (sig, axs, [], [], drop 6 rest)
                  | otherwise = searchAxioms sig (axs ++ [head rest]) $ tail rest
        searchTheorems sig axs ths []   = (sig,axs,ths,[],[])
        searchTheorems sig axs ths rest
                  | take 9 rest == "conjects:" =
                    searchConjects sig axs ths [] $ drop 9 rest
                  | take 6 rest == "terms:" = (sig, axs, ths, [], drop 6 rest)
                  | otherwise =
                    searchTheorems sig axs (ths ++ [head rest]) $ tail rest
        searchConjects sig axs ths conjs []   = (sig,axs,ths,conjs,[])
        searchConjects sig axs ths conjs rest =
           if take 6 rest == "terms:" then (sig,axs,ths,conjs,drop 6 rest) 
           else searchConjects sig axs ths (conjs++[head rest]) $ tail rest

-- used by Ecom > addSpec

-- * List and set functions

notnull :: [a] -> Bool
notnull = not . null

nil2 :: ([a], [b])
nil2 = ([],[])

single :: t -> [t]
single x = [x]

emptyOrAll :: [[t]] -> [[t]]
emptyOrAll ss  = if null ss then [[]] else ss

emptyOrLast :: [[t]] -> [t]
emptyOrLast ss = if null ss then [] else last ss

(-+-) :: Eq a => [a] -> [a] -> [a]
s1@(_:_) -+- s2@(a:s) = if last s1 == a then init s1 -+- s else s1++s2
s1 -+- s2             = s1++s2

split :: (a -> Bool) -> [a] -> ([a],[a])
split f (x:s) = if f x then (x:s1,s2) else (s1,x:s2) where (s1,s2) = split f s
split _ _     = nil2

prod2 :: [t] -> [t1] -> [(t, t1)]
prod2 as bs = [(a,b) | a <- as, b <- bs]

domain :: (Eq a) => (t -> a) -> [t] -> [a] -> [t]
domain f s s' = [x | x <- s, f x `elem` s']

context :: Int -> [a] -> [a]
context i s = take i s++drop (i+1) s


indices_ :: [a] -> [Int]
indices_ s = [0..length s-1]

contextM :: [Int] -> [t] -> [t]
contextM is s = [s!!i | i <- indices_ s, i `notElem` is]

updMax :: (Eq a, Ord b) => (a -> b) -> a -> [b] -> a -> b
updMax f x = upd f x . maximum

updList :: [a] -> Int -> a -> [a]
updList s i x = take i s++x:drop (i+1) s

updListM :: [a] -> Int -> [a] -> [a]
updListM s i xs = take i s ++ xs ++ drop (i + 1) s

inverse :: Eq a => (a -> a) -> [a] -> a -> a
inverse f s = h s id where h (x:s) g = h s (upd g (f x) x)
                           h _ g     = g

-- | @getMax as pairs@ returns all maximal subsets bs of as such that for all
-- (a,b) in pairs, either a or b is in bs.

getMax :: Eq a => [a] -- ^ as
    -> [(a,a)] -- ^ pairs
    -> [[a]]
getMax as = maxima length . foldl f [as]
         where f ass (a,b) = concat [[minus1 as b,minus1 as a] | as <- ass]

lookupL :: (Eq a,Eq b) => a -> b -> [(a,b,c)] -> Maybe c
lookupL a b ((x,y,z):s) = if a == x && b == y then Just z else lookupL a b s
lookupL _ _ _           = Nothing

lookupL1 :: Eq a => a -> [(a,b,c)] -> [c]
lookupL1 a ((x,_,z):s) = if a == x then z:lookupL1 a s else lookupL1 a s
lookupL1 _ _           = []

lookupL2 :: Eq a => a -> [(a,b,c)] -> [(b,c)]
lookupL2 a ((x,y,z):s) = if a == x then (y,z):lookupL2 a s else lookupL2 a s
lookupL2 _ _           = []

-- @i in invertRel as bs iss !! k iff k in iss !! i@.
invertRel
    :: [a] -- ^ as
    -> [b] -- ^ bs
    -> [[Int]] -- ^ iss
    -> [[Int]]
invertRel as bs iss = map f $ indices_ bs where f i = searchAll (i `elem`) iss

{- general version:
invertRel :: (Eq a,Eq b) => [(a,[b])] -> [b] -> [(b,[a])]
invertRel s = map f where f b = (b,[a | (a,bs) <- s, b `elem` bs])
-}

-- | @invertRelII@ is used by 'actTable', 'Esolve.simplifyS', 'buildKripke', 
-- 'showEqsOrGraph', 'showMatrix' and 'Ecom.showRelation'.
-- @k in (invertRelL as bs cs isss !! i) !! j iff i in (isss !! k) !! j@. 
invertRelL
    :: [a] -- ^ as
    -> [b] -- ^ bs
    -> [c] -- ^ cs
    -> [[[Int]]] -- ^ isss
    -> [[[Int]]]
invertRelL as bs cs isss = map f $ indices_ cs
                            where f i = map g [0..length as-1]
                                        where g j = searchAll h isss where
                                                    h iss = i `elem` iss!!j

-- used by Esolve > actTable, simplifyS "out{L}" and
-- Ecom > buildKripke,showTransOrKripke,showMatrix,showRelation

{- general version:
invertRelL :: (Eq a,Eq b,Eq c) => [(a,b,[c])] -> [c] -> [b] -> [(c,b,[a])]
invertRelL s cs = map f . prod2 cs
             where f (c,b) = (c,b,[a | (a,b',cs) <- s, b == b' && c `elem` cs])
-}

prefixes p = [take n p | n <- [0..length p]]

-- | @subsets n@ returns all 'notnull' proper subsets of @[0..n-1]@.
subsets
    :: (Enum a, Num a, Ord a)
    => a -- ^ n
    -> [[a]]
subsets n = concatMap (subsetsN n) [1..n-1]

-- | @subsetsB n k@ returns all subsets of @[0..n-1]@ with at most @k@ elements.
subsetsB
    :: (Enum b, Enum a, Eq b, Num b, Num a, Ord a)
    => a -- ^ n
    -> b -- ^ k
    -> [[a]]
subsetsB n k = concatMap (subsetsN n) [0..k]

-- | @subsetsN n k@ returns all subsets of @[0..n-1]@ with exactly @k@ elements.
subsetsN
    :: (Enum a, Eq b, Num b, Num a, Ord a)
    => a
    -> b
    -> [[a]]
subsetsN _ 0 = [[]]
subsetsN n k = mkSet [insert (<) x xs | xs <- subsetsN n (k-1), 
                                        x <- [0..n-1]`minus`xs]

subset, supset, shares :: Eq a => [a] -> [a] -> Bool
s `subset` s' = all (`elem` s') s
supset         = flip subset
shares s       = any (`elem` s)

imgsSubset,imgsShares :: Eq a => [a] -> (a -> [a]) -> [a] -> [a]
imgsSubset xs f ys = filter (supset ys . f) xs
imgsShares xs f ys = filter (shares ys . f) xs

eqset :: Eq a => [a] -> [a] -> Bool
xs `eqset` ys = xs `subset` ys && ys `subset` xs

disjoint :: Eq a => [a] -> [a] -> Bool
disjoint xs = all (`notElem` xs)

meet :: Eq t => [t] -> [t] -> [t]
xs `meet` ys = [x | x <- xs, x `elem` ys]

-- | @related f xs ys =@ 'Prelude.any' (g ys) xs where g ys x =@ 'Prelude.any'
-- @(f x) ys@ 
minus1 :: Eq t => [t] -> t -> [t]
xs `minus1` y = [x | x <- xs, x /= y]

minus :: Eq t => [t] -> [t] -> [t]
xs `minus` ys = [x | x <- xs, x `notElem` ys]

powerset :: Eq a => [a] -> [[a]]
powerset (a:s) = if a `elem` s then ps else ps++map (a:) ps
                 where ps = powerset s
powerset _     = [[]]

join1 :: Eq a => [a] -> a -> [a]
join1 s@(x:s') y = if x == y then s else x:join1 s' y
join1 _ x        = [x]

join :: Eq a => [a] -> [a] -> [a]
join = foldl join1

mkSet :: Eq a => [a] -> [a]
mkSet = join []

insertR :: BoolFun a -> [a] -> a -> [a]
insertR r s@(x:s') y | r y x = s 
                     | r x y = insertR r s' y 
                     | True   = x:insertR r s' y
insertR _ _ x = [x]

joinR :: BoolFun a -> [a] -> [a] -> [a]
joinR r = foldl $ insertR r

joinMapR :: BoolFun a -> (a -> [a]) -> [a] -> [a]
joinMapR r f = foldl (joinR r) [] . map f


updL :: (Eq a,Eq b) => (a -> [b]) -> a -> b -> a -> [b]
updL f a = upd f a . join1 (f a)

upd2L :: (Eq a,Eq b,Eq c) => (a -> b -> [c]) -> a -> b -> c -> a -> b -> [c]
upd2L f a b = upd f a . upd (f a) b . join1 (f a b)

-- used by regToAuto,graphToRel2

updRel :: (Eq a,Eq b) => [(a,[b])] -> a -> [b] -> [(a,[b])]
updRel rel a bs = case searchGet ((== a) . fst) rel of
                       Just (i,(_,cs)) -> updList rel i (a,bs`join`cs)
                       _ -> (a,bs):rel

distinct :: Eq a => [a] -> Bool
distinct (x:xs) = x `notElem` xs && distinct xs
distinct _      = True

joinB1 :: Eq a => [[a]] -> [a] -> [[a]]
joinB1 ss@(s:ss') s' = if eqBag (==) s s' then ss else s:joinB1 ss' s'
joinB1 _ s              = [s]

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

joinBMap ::  Eq a => (a1 -> [[a]]) -> [a1] -> [[a]]
joinBMap f = joinBM . map f

splitAndMap2 :: (a -> (Bool, b)) -> [a] -> ([a], [b])
splitAndMap2 f (x:s) = if b then (x:s1,s2) else (s1,y:s2)
                    where (s1,s2) = splitAndMap2 f s; (b,y) = f x
splitAndMap2 _f _    = nil2

join6 :: (Eq a, Eq a1, Eq a2, Eq a3, Eq a4, Eq a5) =>
         ([a], [a1], [a2], [a3], [a4], [a5])
         -> ([a], [a1], [a2], [a3], [a4], [a5])
         -> ([a], [a1], [a2], [a3], [a4], [a5])
join6 (s1,s2,s3,s4,s5,s6) (t1,t2,t3,t4,t5,t6) =
      (join s1 t1,join s2 t2,join s3 t3,join s4 t4,join s5 t5,join s6 t6)

minus6 :: (Eq t, Eq t2, Eq t4, Eq t6, Eq t8, Eq t10) =>
          ([t], [t2], [t4], [t6], [t8], [t10])
          -> ([t], [t2], [t4], [t6], [t8], [t10])
          -> ([t], [t2], [t4], [t6], [t8], [t10])
minus6 (s1,s2,s3,s4,s5,s6) (t1,t2,t3,t4,t5,t6) =
      (minus s1 t1,minus s2 t2,minus s3 t3,minus s4 t4,minus s5 t5,minus s6 t6)

mkPartition :: Eq a => [a] -> [(a,a)] -> [[a]]
mkPartition = foldl f . map single where
              f part (a,b) = if cla `eqset` clb
                             then part else (cla++clb):minus part s
                             where s@[cla,clb] = map g [a,b]
                                   g a = head $ filter (elem a) part

-- fixpoint computations

fixpt :: BoolFun a -> (a -> a) -> a -> a
fixpt rel step a = if rel b a then a else fixpt rel step b where b = step a

fixptM :: BoolFun a -> (a -> Maybe a) -> a -> Maybe a
fixptM rel step a = do b <- step a
                       if rel b a then Just a else fixptM rel step b

-- | extensional equality
eqFun :: (a1 -> b -> Bool) -> (a -> a1) -> (a -> b) -> [a] -> Bool
eqFun eq f g s = length fs == length gs && and (zipWith eq fs gs)
                 where fs = map f s
                       gs = map g s

-- | generic set comparison
subSet :: (t -> a -> Bool) ->[t] -> [a] -> Bool
subSet le s s' = all (member s') s where member s x = any (le x) s

eqSet :: (t -> t -> Bool) -> [t] -> [t] -> Bool
eqSet eq s s' = subSet eq s s' && subSet eq s' s

-- | generic bag equality
eqBag :: (t -> t -> Bool) -> [t] -> [t] -> Bool
eqBag eq s s' = map f s == map g s && map f s' == map g s'
              where f = card eq s
                    g = card eq s'

card :: Num a => (t -> t1 -> Bool) -> [t] -> t1 -> a
card eq (x:s) y = if eq x y then card eq s y+1 else card eq s y
card _ _ _      = 0

allEqual :: Eq a => [a] -> Bool
allEqual (x:s) = all (\y -> x == y) s
allEqual _     = True

anyDiff :: Eq a => [a] -> Bool
anyDiff (x:s) = any (\y -> x /= y) s
anyDiff _     = False

forallThereis :: (a -> a1 -> Bool) -> [a] -> [a1] -> Bool
forallThereis rel xs ys = all (\x -> any (rel x) ys) xs

forsomeThereis :: (a -> a1 -> Bool) -> [a] -> [a1] -> Bool
forsomeThereis rel xs ys = any (\x -> any (rel x) ys) xs

thereisForall :: (a -> a1 -> Bool) -> [a] -> [a1] -> Bool
thereisForall rel xs ys = any (\x -> all (rel x) ys) xs

foldC :: (a -> b -> a) -> BoolFun a -> a -> [b] -> a
foldC f g a (b:bs) = if g a a' then a else foldC f g a' bs where a' = f a b
foldC _ _ a _      = a

fold2 :: (t -> t1 -> t2 -> t) -> t -> [t1] -> [t2] -> t
fold2 f a (x:xs) (y:ys) = fold2 f (f a x y) xs ys
fold2 _ a _ _           = a

fold3 :: (a -> b -> c -> d -> c) -> a -> [b] -> c -> [d] -> c
fold3 f a (x:xs) b (y:ys) = fold3 f a xs (f a x b y) ys
fold3 _ _ _ b _           = b

foldlM:: Monad m => (a -> b -> m a) -> a -> [b] -> m a
foldlM f a (b:bs) = do a <- f a b; foldlM f a bs
foldlM _ a _      = return a

zipL :: [(t, t1)] -> [t2] -> [(t, t1, t2)]
zipL ((a,b):ps) (c:cs) = (a,b,c):zipL ps cs
zipL _ _                = []

zipWith2 :: (t -> t1 -> t2 -> [a]) -> [t] -> [t1] -> [t2] -> [a]
zipWith2 f (x:xs) (y:ys) (z:zs) = f x y z++zipWith2 f xs ys zs
zipWith2 _ _ _ _                = []

zipWithM :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithM = Haskell.zipWithM

zipWithM_ :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m ()
zipWithM_ = Haskell.zipWithM_
 
pascal :: Int -> [Int]
pascal 0 = [1]
pascal n = zipWith (+) (s++[0]) (0:s) where s = pascal $ n-1

cantor :: Int -> Pos -> Pos
cantor n (x, y)
      | even x =
        if even y then
          if x > 0 then if y' < n then (x - 1, y') else (x', y) else
            if y' < n then (0, y') else (1, y)
          else if x' < n then (x', y - 1) else (x, y')
      | even y =
        if y > 0 then if x' < n then (x', y - 1) else (x, y') else
          if x' < n then (x', 0) else (x, 1)
      | y' < n = (x - 1, y')
      | otherwise = (x', y)
      where x' = x + 1
            y' = y + 1

cantorshelf :: Int -> [a] -> [a]
cantorshelf n s = foldl f s $ indices_ s
                   where f s' i = updList s' (x*n+y) $ s!!i 
                                  where (x,y) = iterate (cantor n) (0,0)!!i

snake :: Int -> [a] -> [a]
snake n s = [s!!(x i*n+z i) | i <- indices_ s]
             where z i
                      | even xi = yi
                      | xi == length s `div` n = length s `mod` n - 1 - yi
                      | otherwise = n - 1 - yi
                      where xi = x i
                            yi = y i
                   x i = i`div`n
                   y i = i`mod`n
 
transpose :: Int -> [a] -> [a]
transpose n s = [s!!(x i*n+y i) | i <- indices_ s] where x i = i`mod`n
                                                         y i = i`div`n
 
mirror :: Int -> [a] -> [a]
mirror n s = [s!!(x i*n+y i) | i <- indices_ s] where x i = n-1-i`div`n
                                                      y i = i`mod`n

-- | @shuffle ss@ zips the lists of @ss@ before concatenating them.
shuffle
    :: [[a]] -- ^ ss
    -> [a]
shuffle = concat . foldl f [[]] where f (s:ss) (x:s') = (s++[x]):f ss s'
                                      f _ (x:s)       = [x]:f [] s
                                      f ss _          = ss

revRows :: Int -> [a] -> [a]
revRows n s = if length s <= n then s else revRows n (drop n s)++take n s

pal :: Eq a => [a] -> Bool
pal (x:xs@(_:_)) = pal (init xs) && x == last xs
pal _            = True

evens :: [a] -> [a]
evens (x:xs) = x:odds xs
evens _      = []

odds :: [a] -> [a]
odds (_:xs) = evens xs
odds _      = []

-- | @search f s@ searches for the first element of @s@ satisfying @f@ and
-- returns its position within @s@.
search :: (a -> Bool) -> [a] -> Maybe Int
search f = g 0 where g i (a:s) = if f a then Just i else g (i+1) s
                     g _ _     = Nothing

getInd :: Eq a => a -> [a] -> Int
getInd a = get . search (== a)

getIndices :: (TermS -> Bool) -> [TermS] -> [Int]
getIndices f ts = [getInd t ts | t <- filter f ts]

searchGet,searchGetR :: (a -> Bool) -> [a] -> Maybe (Int,a)
searchGet f    = g 0 where g i (a:s) = if f a then Just (i,a) else g (i+1) s
                           g _ _     = Nothing
searchGetR f s = g $ length s-1 where
                    g (-1) = Nothing
                    g i    = if f a then Just (i,a) else g $ i-1 where a = s!!i

-- | @searchGet2 f g s@ searches for the first element @x@ of @s@ satisfying @f@
-- and then, in the rest of @s@, for the first element @y@ with @g x y@.
searchGet2 :: (a -> Bool) -> BoolFun a -> [a] -> Maybe (Int,a,a)
searchGet2 f g = h [] 0 where
                 h s i (x:s') = if f x then case searchGet (g x) $ s++s' of
                                                 Just (_,y) -> Just (i,x,y)
                                                 _ -> h (x:s) (i+1) s'
                                       else h (x:s) (i+1) s'
                 h _ _ _      = Nothing

searchArray :: (Num a, Ix a) => (b -> Bool) -> Array a b -> Maybe a
searchArray f ar = g 0 where g i = if f (ar!i) then Just i else g (i+1)
--                             g _ = Nothing

-- | @searchAll f s@ searches all elements of @s@ satisfying @f@ and returns
-- their positions within @s@.
searchAll :: (a -> Bool) -> [a] -> [Int]
searchAll f s = snd $ foldr g (length s-1,[]) s
                 where g a (i,is) = (i-1,if f a then i:is else is)

searchAll2 :: (a -> Bool) -> (a -> Bool) -> [a] -> ([Int],[Int])
searchAll2 f g s = (is,ks) where (_,is,ks) = foldr h (length s-1,[],[]) s
                                 h a (i,is,ks) = (i-1,if f a then i:is else is,
                                                      if g a then ks else i:ks)


searchGetM :: (a -> Maybe b) -> [a] -> Maybe b
searchGetM f = g 0 where g i (a:s) = if just b then b else g (i+1) s
                                      where b = f a
                         g _ _     = Nothing

search2 :: Num b => (a -> Bool) -> (a -> Bool) -> [a] -> Maybe (b, Bool)
search2 f g s = h s 0 where h (x : s) i
                                  | f x = Just (i, True)
                                  | g x = Just (i, False)
                                  | otherwise = h s $ i + 1
                            h _ _     = Nothing

search4 :: (Num b, Num c) =>
           (a -> Bool)
           -> (a -> Bool)
           -> (a -> Bool)
           -> (a -> Bool)
           -> [a]
           -> Maybe (b, c)
search4 f1 f2 f3 f4 s = g s 0 where g (x : s) i
                                      | f1 x = Just (i, 1)
                                      | f2 x = Just (i, 2)
                                      | f3 x = Just (i, 3)
                                      | f4 x = Just (i, 4)
                                      | otherwise = g s $ i + 1
                                    g _ _     = Nothing

-- | @searchback f s@ searches for the first element of reverse @s@ satisfying
-- @f@ and returns its position within @s@.
searchback
    :: (a -> Bool) -- ^ f
    -> [a] -- ^ s
    -> Maybe Int
searchback f s = g s $ length s-1
            where g s@(_:_) i = if f $ last s then Just i else g (init s) $ i-1
                  g _ _       = Nothing

-- | @shift n ns@ removes @n@ from @ns@ and decreases the elements @i > n@ of
-- @ns@ by 1.
shift
    :: (Num a, Ord a)
    => a -- ^ n
    -> [a] -- ^ ns
    -> [a]
shift n ns = [i | i <- ns, i < n] ++ [i-1 | i <- ns, i > n]

splitString :: Int -> Int -> Renaming
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

-- | @mkRanges ns n@ builds the syntactically smallest partition @p@ of
-- @n@:@ns@ such that all @ms@ in @p@ consist of successive integers.
mkRanges
    :: (Eq a, Num a, Show a)
    => [a] -- ^ ns
    -> a -- ^ n
    -> String
mkRanges ns n = f ns [] (n,n)
   where f (k:ns) part sect@(m,n) = if k == n' then f ns part (m,n')
                                               else f ns (part++[sect]) (k,k)
                                    where n' = n+1
         f _ part sect            = g (part++[sect])
         g ((m,n):sects) | m == n    = show m++rest
                         | otherwise = show m++".."++show n++rest
                                    where rest = if null sects then []
                                                               else ',':g sects
         g _ = ""

-- | @mkLists s ns@ computes the partition of @s@ whose i-th element has
-- @ns !! i@ elements.
mkLists
    :: (Eq b, Num b)
    => [a] -- ^ s
    -> [b] -- ^ ns
    -> [[a]]
mkLists s = f s [] where f s s' (0:ns)     = s':f s [] ns
                         f (x:s) s' (n:ns) = f s (s'++[x]) ((n-1):ns)
                         f _ _ _           = []

-- * Sets and relations translated into functions

setToFun :: Eq a => [a] -> a -> Bool
setToFun = foldl g (const False) where g f x = upd f x True

relToFun :: Eq a => [(a,[b])] -> a -> [b]
relToFun s a = case lookup a s of Just bs -> bs; _ -> []

relLToFun :: (Eq a,Eq b) => [(a,b,[c])] -> a -> b -> [c]
relLToFun s a b = case lookupL a b s of Just cs -> cs; _ -> []

-- traces

traces :: Eq a => (a -> [a]) -> a -> a -> [[a]]
traces f a = h [a] a where 
             h visited a c = if a == c then [[a]] 
                                       else do b <- f a`minus`visited
                                               trace <- h (b:visited) b c
                                               [a:trace]

tracesL :: Eq a => [lab] -> (a -> lab -> [a]) -> a -> a -> [[lab]]
tracesL labs f a = h [a] a where 
                   h visited a c = if a == c then [[]] 
                                   else do lab <- labs
                                           b <- f a lab`minus`visited
                                           trace <- h (b:visited) b c
                                           [lab:trace]

-- | minimal DNFs represented as subsets of {'0','1','#'}^n for some n > 0
minDNF :: [String] -> [String]
minDNF bins = f bins' $ length bins'
              where bins' = maxis leqBin bins
                    f bins n = if n' < n then f bins' n' else bins'
                               where bins' = maxis leqBin $ mkSups [] bins
                                     n' = length bins'

-- | @mkSups [] bins@ replaces elements of @bins@ by suprema of subsets of
-- @bins@.
mkSups
    :: [String] -- ^ []
    -> [String] -- ^ bins
    -> [String]
mkSups bins (bin:bins') = case search f $ indices_ bin of
                               Just i -> mkSups (updList bin i '#':bins) bins'
                               _ -> mkSups (bin:bins) bins'
               where f i = b /= '#' && ((cbin `elem`) ||| any (leqBin cbin) |||
                                        forallThereis leqBin (minterms cbin))
                                       (bins++bins') where
                           b = bin!!i
                           cbin = updList bin i $ if b == '0' then '1' else '0'
mkSups bins _ = bins

leqBin :: String -> String -> Bool
leqBin bin bin' = and $ zipWith leq bin bin'
                  where leq x y = x == y || y == '#'

minterms :: String -> [String]
minterms bin = if '#' `elem` bin then concatMap minterms [f '0',f '1']
                                 else [bin]
                where (bin1,bin2) = span (/= '#') bin
                      f x = bin1++x:tail bin2

-- | @funToBins (f,n)@ translates a function @f :: {'0','1','#'}^n ->@
-- 'Prelude.Bool' into a minimal DNF representing f.
funToBins :: (Eq a, Num a) => (String -> Bool, a) -> [String]
funToBins (f,n) = minDNF $ filter f $ binRange n
                  where binRange 0 = [""]
                        binRange n = map ('0':) s++map ('1':) s++map ('#':) s
                                      where s = binRange $ n-1

-- * Karnaugh diagrams

-- | @karnaugh n@ is the empty Karnaugh matrix that consists of all elements of
-- {'0','1'}^n.
karnaugh :: Int -> (Array (Int,Int) String,Int,Int)
karnaugh 1          = (array ((1,1),(1,2)) [((1,1),"0"),((1,2),"1")],1,2)
karnaugh n | even n = (mkArray ((1,1),(k,m)) f,k,m)
                       where (arr,mid,m) = karnaugh (n-1)
                             k = mid*2
                             f (i,j) | i <= mid  = '0':arr!(i,j)
                                     | otherwise = '1':arr!(2*mid-i+1,j)
karnaugh n          = (mkArray ((1,1),(k,m)) f,k,m)
                       where (arr,k,mid) = karnaugh (n-1)
                             m = mid*2
                             f (i,j) | j <= mid  = '0':arr!(i,j)
                                     | otherwise = '1':arr!(i,2*mid-j+1)

-- | @binsToBinMat bins n@ translates a DNF into an equivalent Karnaugh matrix.
binsToBinMat
    :: (Ix a, Ix b)
    => [String] -- ^ bins
    -> Array (a, b) String
    -> a
    -> b
    -> String
binsToBinMat bins arr i j = if any (e `leqBin`) bins then ("red_"++e) else e
                            where e = arr!(i,j)

-- * Sorting and permuting

sorted :: Ord a => [a] -> Bool
sorted (x:s@(y:_)) = x <= y && sorted s
sorted _             = True

-- sort removes duplicates if rel is irreflexive and total

sort,qsort :: BoolFun a -> [a] -> [a]
sort rel (x:s) = sort rel [z | z <- s, rel z x]++x:
                 sort rel [z | z <- s, rel x z]
sort _ s       = s         

qsort rel (x:s@(_:_)) = qsort rel s1++x:qsort rel s2
                        where (s1,s2) = split (`rel` x) s
qsort _ s             = s

-- sortR s s' sorts s such that x precedes y if f(x) < f(y) where f(x) is the
-- element of s' at the position of x in s.
sortR :: (Eq a,Ord b) => [a] -> [b] -> [a]
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
insert :: Eq a => BoolFun a -> a -> [a] -> [a]
insert r x s@(y:ys) | x == y = s
                    | r x y  = x:s
                    | True   = y:insert r x ys
insert _ x _                 = [x]

-- minis leq s computes the minima of s with respect to a partial order leq.

minis,maxis :: Eq a => BoolFun a -> [a] -> [a]
minis le = foldr f [] where f x (y:s) | le x y = f x s
                                      | le y x = f y s
                                      | True   = y:f x s
                            f x _              = [x]
maxis = minis . flip

-- maxima f s returns the subset of all x in s such that f(x) agrees with the
-- maximum of f(s).

maxima,minima :: Ord b => (a -> b) -> [a] -> [a]
maxima f s = [x | x <- s, f x == maximum (map f s)]
minima f s = [x | x <- s, f x == minimum (map f s)]

-- minmax ps computes minimal and maximal coordinates of the point list ps.

minmax :: (Ord a,Ord b,Num a,Num b) => [(a,b)] -> (a,b,a,b)
minmax ps@((x,y):_) = foldl f (x,y,x,y) ps
            where f (x1,y1,x2,y2) (x,y) = (min x x1,min y y1,max x x2,max y y2)

-- nextPerm s computes the successor of s with respect to the reverse
-- lexicographic ordering (see Paulson, ML for the Working Programmer, p. 95f.)

nextPerm :: Ord a => [a] -> [a]
nextPerm s@(x:xs) = if sorted s then reverse s else next [x] xs
   where next s@(x:_) (y:ys) = if x <= y then next (y:s) ys else swap s
            where swap [x]      = y:x:ys
                  swap (x:z:xs) = if z > y then x:swap (z:xs) else y:z:xs++x:ys
nextPerm _ = []

permute :: Ord a => ([a],[Int]) -> ([a],[Int])
permute (s,is) = ([s!!i | i <- is],nextPerm is)

intperms :: [Int] -> [[Int]]
intperms is = take (product [2..length is]) $ iterate nextPerm is

perms,subperms :: Ord a => [a] -> [[a]]
perms s    = map (map (s!!)) $ intperms $ indices_ s
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

-- monad handling

kfold :: (a -> state -> [state]) -> [state] -> [a] -> [state]
kfold f = foldl $ \sts a -> concatMap (f a) sts

liftM :: Monad m => (a -> b) -> m a -> m b
liftM = Haskell.liftM

liftM2  :: Monad m => (a -> b -> c) -> m a -> m b -> m c
liftM2 = Haskell.liftM2

(***) :: (a -> b) -> (a -> c) -> a -> (b,c)
(***) = liftM2 (,)

(&&&),(|||) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(&&&) = liftM2 (&&)
(|||) = liftM2 (||)

sat :: Parser b -> (b -> Bool) -> Parser b
sat m f = do a <- m; guard $ f a; return a

type MaybeT = Haskell.MaybeT

-- used by the widget interpreters of Epaint

maybeT :: Monad m => m (Maybe a) -> MaybeT m a
maybeT = Haskell.MaybeT
{-# INLINE maybeT #-}

runT :: MaybeT m a -> m (Maybe a)
runT = Haskell.runMaybeT

(+++) :: MonadPlus m => (a -> m b) -> (a -> m b) -> a -> m b
(+++) = liftM2 (++)

lift :: (Monad m, Haskell.MonadTrans t) => m a -> t m a
lift = Haskell.lift
{-# INLINE lift #-}

lift' :: Monad m => Maybe a -> MaybeT m a
lift' = maybeT . return

-- parser monad

newtype Parser a = P (Haskell.StateT String Maybe a)
   deriving (Functor, Applicative, Monad, Haskell.Alternative, MonadPlus)

applyPa :: Parser a -> String -> Maybe (a,String)
applyPa (P f) = Haskell.runStateT f

-- parse parser str applies parser to str and returns Nothing if str has no 
-- successful parses.

parse :: Parser a -> String -> Maybe a
parse parser str = do (x,"") <- applyPa parser str; Just x

data Parse a = Correct a | Partial a String | Wrong

-- parseE parser str returns an error message if str has no successful parses.

parseE :: Parser a -> String -> Parse a
parseE parser str = case applyPa parser str of Just (x,[]) -> Correct x
                                               Just (x,rest) -> Partial x rest
                                               _ -> Wrong

-- used by Ecom

-- ** Parser of symbols and numbers

haskell :: Read a => Parser a
haskell = P $ do
    str <- Haskell.get
    let (t, str'):_ = reads str
    Haskell.put str'
    return t

item :: Parser Char
item = P $ do
    (c:cs) <- Haskell.get
    Haskell.put cs
    return c

char :: Char -> Parser Char
char x        = sat item (== x)

nchar :: Char -> Parser Char
nchar x       = sat item (/= x)

string :: String -> Parser String
string        = mapM char

some :: Parser a -> Parser [a]
some p        = do x <- p; xs <- many p; return $ x:xs

many :: Parser a -> Parser [a]
many p        = some p ++ return []

space :: Parser String
space         = many $ sat item (`elem` " \t\n")

token :: Parser a -> Parser a
token p       = do space; x <- p; space; return x

tchar :: Char -> Parser Char
tchar         = token . char

symbol :: String -> Parser String
symbol        = token . string

oneOf :: [String] -> Parser String
oneOf         = concat . map symbol

enclosed p    = concat [do tchar '('; r <- p; tchar ')'; return r,
                        token p]

bool          = concat [symbol "True" >> return True,
                        symbol "False" >> return False]

data Strategy = DF | BF | PA deriving (Show,Eq)

strategy      = concat [symbol "DF" >> return DF,
                        symbol "BF" >> return BF,
                        symbol "PA" >> return PA]

stratWord strat = case strat of DF -> "depthfirst"
                                BF -> "breadthfirst"
                                _  -> "parallel"

digit :: Parser Int
digit         = do d <- sat item isDigit; return $ ord d-ord '0'

hexdigit :: Parser Int
hexdigit      = concat [do d <- sat item isAToF; return $ ord d-ord 'A'+10,
                        digit]
                where isAToF c = 'A' <= c && c <= 'F'

nat :: Parser Int
nat           = do ds <- some digit; return $ foldl1 f ds where f n d = 10*n+d

pnat :: Parser Int
pnat          = sat nat (> 0)

pnatSecs :: Parser Integer
pnatSecs      = do n <- pnat; char 's'; return $ toInteger n

charNat :: Char -> Parser Int
charNat x     = do char x; nat

strNat :: String -> Parser Int
strNat x      = do string x; nat

int :: Parser Int
int           = nat ++ do char '-'; n <- nat; return $ -n

intRange :: Parser [Int]
intRange      = do i <- int; string ".."; k <- int; return [i..k]

intRangeOrInt :: Parser [Int]
intRangeOrInt = intRange ++ do i <- int; return [i]

intRanges :: Parser [Int]
intRanges     = do is <- token intRangeOrInt
                   concat [do ks <- intRanges; return $ is++ks,
                           return is]

double :: Parser Double
double        = p ++ do char '-'; r <- p; return $ -r
                where p = do n <- nat; char '.'; ds <- some digit
                             let m = foldl1 (\n d -> 10*n+d) ds
                                 r = fromInt n+fromInt m*0.1^length ds
                             k <- expo; return $ r*10^k
                      expo = concat [do string "e+"; nat,
                                     do string "e-"; n <- nat; return $ -n,
                                     do string "e"; nat,
                                     return 0]


real :: Parser Double
real          = concat [do r <- double; return (realToFrac (fromDouble r::Float)),
                        int >>= return . fromInt]
-- OHaskell fix: Cast to Float and back to fix a precission problem.

realNeg :: Parser Double
realNeg       = sat real (< 0)

rgbcolor :: Parser Color
rgbcolor      = do symbol "RGB"; r <- token int; g <- token int; b <- token int
                   return $ RGB r g b

hexcolor :: Parser Color
hexcolor      = do char '#'
                   [d1,d2,d3,d4,d5,d6] <- Haskell.replicateM 6 hexdigit
                   return $ RGB (16*d1+d2) (16*d3+d4) $ 16*d5+d6

color :: Parser Color
color         = concat [symbol "dark" >> color >>= return . dark,
                        symbol "light" >> color >>= return . light,
                        symbol "black" >> return black,
                        symbol "grey" >> return grey,
                        symbol "white" >> return white,
                        symbol "red" >> return red,
                        symbol "magenta" >> return magenta,
                        symbol "blue" >> return blue,
                        symbol "cyan" >> return cyan,
                        symbol "green" >> return green,
                        symbol "yellow" >> return yellow,
                        symbol "orange" >> return orange,
                        rgbcolor,token hexcolor]

colPre :: Parser (Color, String)
colPre        = do col <- color; char '_'; x <- some item; return (col,x)

delCol :: String -> String
delCol a      = case parse colPre a of Just (_,a) -> a; _ -> a

delQuotes :: String -> String
delQuotes a = if just $ parse (quoted++infixWord) b then init $ tail b else b
              where b = delCol a

-- used by nodeLabels,mkSizes, Epaint > decXY,stringInTree,drawTreeNode,
-- drawWidg Text,halfmax, Esolve > simplifyOne and Ecom > drawNode

quoted :: Parser String
quoted      = do char '"'; x <- many $ sat item (/= '"'); char '"'; return x

noDelim :: Char -> Bool
noDelim c   = c `notElem` " \t\n()[]{},`$.;:+-*<=~>/\\^#&|!"

noBlanks :: Parser String
noBlanks    = token $ some $ sat item noDelim

infixChar c = c `elem` "$.;:+-*<=~>/\\^#&|!"

infixWord   = do char '`'; w <- some $ sat item (/= '`'); char '`'
                 return $ '`':w ++ "`"

digits      = some $ sat item isDigit

letters     = some $ sat item isAlpha

indEquiv    = do char '~'; concat [do n <- digits; return $ '~':n,
                                   do xs <- letters; char '~'; n <- digits
                                      return $ '~':xs++'~':n]

infixString = concat [do char '~'; concat [indEquiv,
                                           do xs <- letters; char '~'
                                              return $ '~':xs++"~"],
                      some $ sat item infixChar,
                      infixWord]

isInfix     = just . parse infixString

infixToken  = token infixString

infixFun    = sat infixToken . functional

infixRel    = sat infixToken . relational

functional :: Sig -> String -> Bool
functional sig    = (sig&isConstruct) ||| (sig&isDefunct)

relational :: Sig -> String -> Bool
relational sig x  = declaredRel sig x || isFixF x || x == "rel"

declared :: Sig -> String -> Bool
declared sig      = functional sig ||| relational sig ||| logical

declaredRel :: Sig -> String -> Bool
declaredRel sig x = (sig&isPred) x || (sig&isCopred) x || x `elem` words "= =/="

isConstr sig      = (sig&isConstruct) ||| collector

isValue sig       = andT $ isConstr sig

isNormal sig      = andT $ isConstr sig ||| isVar sig

list p            = concat [symbol "[]" >> return [],
                            do tchar '['; xs <- someC p; tchar ']'; return xs]

someC p           = do x <- p
                       concat [do tchar ','; xs <- someC p; return $ x:xs,
                               return [x]]

tuple p sig       = do tchar '('
                       concat [enclosedSect sig,
                               do ts <- p sig; tchar ')'; return $ mkTup ts]

enclosedSect sig  = concat [do x <- (infixRel +++ infixFun) sig
                               guard $ x /= "-"
                               concat [do tchar ')'; return $ leaf x,
                                       do t <- (term +++ atom) sig; tchar ')'
                                          return $ F "rsec" [leaf x,t]],
                            do t <- (term +++ atom) sig
                               concat [do tchar ')'; return t,
                                       do x <- (infixRel +++ infixFun) sig
                                          tchar ')'
                                          return $ F "lsec" [t,leaf x]]]

apply t u = applyL t [u]

applyL (F x []) ts = if just i && k < length ts then F x [mkTup ts]
                     else F x ts where i = parse (strNat "get") x; k = get i
applyL t ts        = F "$" [t,mkTup ts]

curryrest :: Sig -> Parser TermS -> TermS -> Parser TermS
curryrest sig p t = concat [do F "()" ts <- p; curryrest sig p $ applyL t ts,
                            do u <- p; curryrest sig p $ apply t u,
                            return t]

-- ** Parser of formulas

implication :: Sig -> Parser TermS
implication sig = do t <- disjunct sig
                     concat [symbol "==>" >> equation sig ["=="] 
                                          >>= return . mkImpl t,
                             do x <- oneOf $ words "<=> ==> <==> ===> <==="
                                u <- disjunct sig; return $ F x [t,u],
                             return t]

enclosedImpl :: Sig -> Parser TermS
enclosedImpl sig = do tchar '('; t <- implication sig; tchar ')'; return t

equation sig xs = do left <- term sig; x <- oneOf xs; right <- term sig
                     return $ F x [left,right]

disjunct :: Sig -> Parser TermS
disjunct sig = do t <- conjunct sig; ts <- many $ do tchar '|'; conjunct sig
                  return $ if null ts then t else F "|" $ t:ts

conjunct :: Sig -> Parser TermS
conjunct sig = do t <- factor sig; ts <- many $ do tchar '&'; factor sig
                  return $ if null ts then t else F "&" $ t:ts

conditional p sig = do symbol "ite"; tchar '('; t <- implication sig; tchar ','
                       u <- p sig; tchar ','; v <- p sig; tchar ')'
                       return $ F "ite" [t,u,v]

-- ** Parser of factors

factor :: Sig -> Parser TermS
factor sig = concat [equation sig ["==","="], atom sig, enclosedImpl sig,
                     symbol "True" >> return mkTrue,
                     symbol "False" >> return mkFalse,
                     do symbol "Not"; t <- factor sig; return $ F "Not" [t],
                     symbol "Any" >> closure "Any",
                     symbol "All" >> closure "All",
                     conditional implication sig,
                     do t <- term sig; x <- sat (infixRel sig) isOrd
                        u <- term sig; return $ F x [t,u]]
             where closure q = do xs@(_:_) <- boundVars sig; tchar ':'
                                  t <- factor sig; return $ mkBinder q xs t

boundVars :: Sig -> Parser [String]
boundVars sig = f [] where f xs = concat [do x <- sat noBlanks $ isVar sig
                                             f $ xs++[x],
                                          do guard $ distinct xs; return xs]

atom :: Sig -> Parser TermS
atom sig = concat [singleAtom sig >>= maybeComp sig,
                   singleRelterm sig >>= infixRelTerm sig]

relterm :: Sig -> Parser TermS
relterm sig = concat [singleRelterm sig >>= maybeComp sig,
                      singleRelterm sig >>= infixRelTerm sig]

singleAtom :: Sig -> Parser TermS
singleAtom sig = concat [infixRel sig >>= return . leaf,
                         prefixAtom sig,
                         enclosedAtom sig >>= curryrestR sig]

singleRelterm :: Sig -> Parser TermS
singleRelterm sig = concat [infixRel sig >>= return . leaf,
                            prefixAtom sig,
                            term sig,
                            enclosedRelterm sig >>= curryrestR sig]

infixRelTerm :: Sig -> TermS -> Parser TermS
infixRelTerm sig t = do x <- infixRel sig; relterm sig >>= application x t

application :: String -> TermS -> TermS -> Parser TermS
application "$" t u | null (subterms t) && z /= "_" && not (isPos z)
                    = return $ F z [u] where z = root t
application x t u   = return $ F x [t,u]

maybeComp :: Sig -> TermS -> Parser TermS
maybeComp sig t = concat [do tchar '.'; u <- singleTerm sig
                             maybeComp sig $ F "." [t,u],
                          infixRelTerm sig t,
                          return t]

enclosedAtom = tuple (someC . atom) +++ listterm atom

enclosedRelterm = tuple (someC . relterm) +++ listterm relterm +++ termlist

listterm p sig = do tchar '['; ts <- someC $ p sig; tchar ']'
                    return $ mkList ts

curryrestR :: Sig -> TermS -> Parser TermS
curryrestR sig = curryrest sig $ enclosedRelterm sig

prefixAtom :: Sig -> Parser TermS
prefixAtom sig = concat [sat noBlanks (declaredRel sig)
                                           >>= curryrestR sig . leaf,
                         do x <- symbol "rel"; tchar '('; ts <- p []; tchar ')'
                            curryrestR sig $ F x ts,
                         do x <- oneOf ["MU","NU"]
                            xs@(_:_) <- boundVars sig; tchar '.'
                            singleAtom sig >>= curryrestR sig . mkBinder x xs]
                 where p ts = do t <- term sig; tchar ','; u <- implication sig
                                 let us = ts++[t,u]
                                 (do tchar ','; p us) ++ return us

-- ** Parser of terms

term :: Sig -> Parser TermS
term sig = do t <- termbag sig; ts <- many $ do symbol "<+>"; termbag sig
              return $ if null ts then t else F "<+>" $ t:ts

termbag :: Sig -> Parser TermS
termbag sig = do t <- termsum sig; ts <- many $ do tchar '^'; termsum sig
                 return $ if null ts then t else F "^" $ t:ts

termsum :: Sig -> Parser TermS
termsum sig = termprod sig >>= maybeSum sig

maybeSum :: Sig -> TermS -> Parser TermS
maybeSum sig t = concat [do x <- oneOf ["+","-"]; u <- termprod sig
                            maybeSum sig $ F x [t,u],
                         do x <- infixFun sig; termbag sig >>= application x t,
                         return t]

termprod :: Sig -> Parser TermS
termprod sig = singleTerm sig >>= maybeProd sig

maybeProd :: Sig -> TermS -> Parser TermS
maybeProd sig t = concat [do symbol "||"; u <- implication sig
                             return $ F "||" [t,u],
                          do x <- oneOf $ words "** * /"; u <- singleTerm sig
                             maybeProd sig $ F x [t,u],
                          do x <- sat (infixFun sig) (`notElem` ["+","-"])
                             termbag sig >>= application x t,
                          return t]

termlist :: Sig -> Parser TermS
termlist sig = concat [symbol "[]" >> return mkNil,
                       do tchar '['
                          concat [do t <- term sig; symbol ".."; u <- term sig
                                     tchar ']'; return $ F "range" [t,u],
                                  do ts <- someC $ term sig; tchar ']'
                                     return $ mkList ts]]

termset :: Sig -> Parser TermS
termset sig = concat [symbol "{}" >> return (leaf "{}"),
                      do tchar '{'; ts <- someC $ term sig; tchar '}'
                         return $ F "{}" ts]

singleTerm :: Sig -> Parser TermS
singleTerm sig = concat [do x <- oneOf termBuilders
                            t <- concat [do tchar '$'; atom sig,
                                         enclosedAtom sig,
                                         enclosedImpl sig]
                            curryrestF sig $ F x [t],
                         sat noBlanks (functional sig)
                                                  >>= curryrestF sig . leaf,
                         sat noBlanks (sig&isFovar) >>= return . V,
                         constant sig,
                         symbol "pos " >> many (token nat) >>= return . mkPos,
                         do x <- oneOf ["-","~"]; t <- singleTerm sig
                            return $ F x [t],
                         symbol "()" >> return unit,
                         conditional term sig,
                         do x <- oneOf ["mu","nu"]
                            xs@(_:_) <- boundVars sig; tchar '.'
                            (enclosedTerm +++ singleTerm) sig
                                    >>= curryrestF sig . mkBinder x xs,
                         do enclosedTerm sig >>= curryrestF sig,
                         sat (token $ some $ sat item $ noDelim ||| (== ' '))
                             (not . declared sig)
                                    >>= curryrestF sig . leaf . unwords . words]

curryrestF :: Sig -> TermS -> Parser TermS
curryrestF sig = curryrest sig $ enclosedTerm sig

constant :: Sig -> Parser TermS
constant sig = concat [token double >>= return . mkConst,
                       token int >>= curryrestF sig . mkConst,
                       token quoted >>= return . mkConst,
                       token hexcolor >>= curryrestF sig . mkConst,
                       do RGB r g b <- rgbcolor
                          curryrestF sig $ leaf $ unwords
                                                $ "RGB":map show [r,g,b]]

enclosedTerm = tuple (someC . term) +++ termlist +++ termset

termBuilders :: [String]
termBuilders = words "bool evalG eval filter gaussI gauss postflow" ++
               words "stateflowT stateflow subsflow"

-- TRANSITION SYSTEMS and KRIPKE STRUCTURES

type Pairs a = [(a,[a])]

type Triples a b = [(a,a,[b])]
type TriplesL a  = Triples a ([a],[a])

mkPairs :: [a] -> [a] -> [[Int]] -> Pairs a
mkPairs dom ran = zipWith f [0..] where f i ks = (dom!!i,map (ran!!) ks)

mkTriples :: [a] -> [a] -> [a] -> [[[Int]]] -> Triples a a
mkTriples dom1 dom2 ran = concat . zipWith f [0..]
                     where f i = zipWith g [0..]
                                where g j ks = (dom1!!i,dom2!!j,map (ran!!) ks)


deAssoc0 :: [(a, [b])] -> [(a, b)]
deAssoc0 = concatMap f where f (x,ys) = map (\y -> (x,y)) ys

deAssoc1 :: [([a], b)] -> [(a, b)]
deAssoc1 = concatMap f where f (xs,y) = map (\x -> (x,y)) xs

deAssoc2 :: [([a], [b])] -> [(a, b)]
deAssoc2 = concatMap f where f (xs,ys) = concatMap g xs
                                      where g x = map (\y -> (x,y)) ys

deAssoc3 :: [([a], [b], c)] -> [(a, b, c)]
deAssoc3 = concatMap f where f (xs,ys,z) = concatMap g xs
                                        where g x = map (\y -> (x,y,z)) ys

infixl 7 <<=
infixl 8 >>>

-- generic set comparison

subGraph :: TermS -> TermS -> Bool
subGraph t u = subSet le (graphToRel t) (graphToRel u) -- && size t <= size u
                where le (a,as) (b,bs) = a == b && as `subset` bs

eqGraph :: TermS -> TermS -> Bool
eqGraph t = eqSet eq (graphToRel t) . graphToRel
             where eq (a,as) (b,bs) = a == b && as `eqset` bs
-- OBDDs

isObdd :: TermS -> Bool
isObdd        (F "0" [])  = True
isObdd        (F "1" [])  = True
isObdd        (F x [t,u]) = just (parse (charNat 'x') x) && isObdd t
                                                           && isObdd u
isObdd (V x)       = isPos x
isObdd _           = False

-- removeVar repeatedly applies the rule X(t,t)=t to an OBDD t.
removeVar :: TermS -> TermS
removeVar (F x [t,u]) = if eqTerm t' u' then t' else F x [t',u']
                        where t' = removeVar t; u' = removeVar u
removeVar t           = t

-- binsToObdd translates a subset of {'0','1','#'}^n into an equivalent minimal
-- OBDD.
binsToObdd :: [String] -> TermS
binsToObdd bins = binsToObddP (length bin-1) (indices_ bin) bins
                  where bin = head bins

binsToObddP :: Show a =>
               Int -> [a] -> [String] -> TermS
binsToObddP _ _ []    = mkZero
binsToObddP n ns bins = collapse True $ removeVar $ trans 0 $ setToFun bins
           where trans i f = F ('x':show (ns!!i)) $ if i < n then [g '0',g '1'] 
                                                             else [h "0",h "1"]
                             where g a = trans (i+1) $ f . (a:) ||| f . ('#':)
                                   h a = if f a || f "#" then mkOne else mkZero

-- obddToFun translates an OBDD t into the pair (f,n) consisting of the
-- characteristic function f :: {'0','1','#'}^n -> Bool of an equivalent DNF and
-- the number n of Boolean variables of t.
obddToFun :: TermS -> (String -> Bool, Int)
obddToFun t = (f t &&& g,dim)
     where f (F "0" [])        = const False
           f (F "1" [])        = const True
           f (F ('x':i) [t,u]) = f t &&& h '0' ||| f u &&& h '1'
                                        where h a bin = bin!!read i == a
           f (V x) | isPos x   = f $ getSubterm t $ getPos x
           f _                       = error "obddToFun"
           varInds (F ('x':i) [t,u]) = varInds t `join` varInds u `join1` read i
           varInds _                 = []
           dim = if null is then 0 else maximum is+1; is = varInds t
           g bin = all (== '#') $ map (bin!!) $ [0..dim-1] `minus` is


-- ** From GRAPHS to TRANSRULES

graphToTransRules :: TermS -> ([TermS],[TermS],[(TermS,[TermS],TermS)])
graphToTransRules = f [] where
                    f p (F x ts) = (joinM states `join1` st,
                                    joinM atoms `join1` at,trs) where
                       (states,atoms,transitions) = unzip3 $ zipWithSucs f p ts
                       st = mkConst p; at = leaf x
                       trs = (at,[],st):(st,[],mkSum $ map g $ indices_ ts):
                             concat transitions 
                       g i = mkConst $ if isPos x then getPos x else p++[i]
                             where x = root $ ts!!i
                    f p (V x) = if isPos x then ([],[],[])
                                           else ([mkConst p],[leaf x],[])


-- ** From REGULAR EXPRESSIONS to LABELLED TRANSITIONS and back

data RegExp = Mt | Eps | Const String | Sum_ RegExp RegExp | Int_ |
              Prod RegExp RegExp | Star RegExp | Var String deriving Eq

parseRE :: Sig -> TermS -> Maybe (RegExp,[String])
                                      -- list of acceptor labels
parseRE _ (F "mt" [])      = Just (Mt,[])
parseRE _ (F "eps" [])     = Just (Eps,["eps"])
parseRE _ (F "int" [])     = Just (Int_,["int"])
parseRE _ (F "+" [])       = Just (Mt,[])
parseRE sig (F "+" [t])    = parseRE sig t
parseRE sig (F "+" ts)     = do pairs <- mapM (parseRE sig) ts
                                let (e:es,ass) = unzip pairs
                                Just (foldl Sum_ e es,joinM ass)
parseRE _ (F "*" [])       = Just (Eps,["eps"])
parseRE sig (F "*" [t])    = parseRE sig t
parseRE sig (F "*" ts)     = do pairs <- mapM (parseRE sig) ts
                                let (e:es,ass) = unzip pairs
                                Just (foldl Prod e es,joinM ass)
parseRE sig (F a [])       = if (sig&isDefunct) a then Just (Var a,[a])
                                                else Just (Const a,[a])
parseRE sig (F "plus" [t]) = do (e,as) <- parseRE sig t
                                Just (Prod e $ Star e,as)
parseRE sig (F "star" [t]) = do (e,as) <- parseRE sig t
                                Just (Star e,as `join1` "eps")
parseRE sig (F "refl" [t]) = do (e,as) <- parseRE sig t
                                Just (Sum_ e Eps,as `join1` "eps")
parseRE _ (V x)            = Just (Var x,[x])
parseRE _ _                = Nothing

showRE :: RegExp -> TermS
showRE Mt           = leaf "mt"
showRE Eps          = leaf "eps"
showRE Int_         = leaf "int"
showRE (Const a)    = leaf a
showRE e@(Sum_ _ _) = case summands e of []  -> leaf "mt"
                                         [e] -> showRE e
                                         es  -> F "+" $ map showRE es
showRE e@(Prod _ _) = case factors e of []  -> leaf "eps"
                                        [e] -> showRE e
                                        es  -> F "*" $ map showRE es
showRE (Star e)     = F "star" [showRE e]
showRE (Var x)      = V x

-- The following binary RegExp-relations are subrelations of regular language
-- inclusion. In their defining equations, = means reverse implication.

instance Ord RegExp                                    -- used by summands
         where Eps <= Star _                   = True
               e <= Star e' | e <= e'          = True
               Prod e1 e2 <= Star e | e1 <= e && e2 <= Star e = True 
               Prod e1 e2 <= Star e | e1 <= Star e && e2 <= e = True 
               e <= Prod e' (Star _) | e == e' = True
               e <= Prod (Star _) e' | e == e' = True
               Prod e1 e2 <= Prod e3 e4        = e1 <= e3 && e2 <= e4
               e <= Sum_ e1 e2                 = e <= e1 || e <= e2
               e <= e'                         = e == e'

(<*) :: RegExp -> RegExp -> Bool                       -- used by factors
Sum_ Eps e <* Star e' | e == e' = True
e <* e' = False

(<+) :: RegExp -> RegExp -> Bool       -- Eps <+ e, e1*e2 <+ e3*e4 iff e1 <+ e3        
Eps <+ e                  = True       -- products are ordered by left factors 
Const a <+ Const b        = a <= b
e@(Const _) <+ Prod e1 e2 = e <+ e1
e@(Star _)  <+ Prod e1 e2 = e <+ e1
Prod e _ <+ e'@(Const _)  = e <+ e'
Prod e _ <+ e'@(Star _)   = e <+ e'
Prod e _ <+ Prod e' _     = e <+ e'
e <+ e'                   = e == e'

(+<) :: RegExp -> RegExp -> Bool       -- Eps +< e, e1*e2 <+ e3*e4 iff e2 <+ e4 
Eps +< e                  = True       -- products are ordered by right factors
Const a +< Const b        = a <= b
e@(Const _) +< Prod e1 e2 = e +< e2
e@(Star _)  +< Prod e1 e2 = e +< e2
Prod _ e +< e'@(Const _)  = e +< e'
Prod _ e +< e'@(Star _)   = e +< e'
Prod _ e +< Prod _ e'     = e +< e'
e +< e'                   = e == e'

-- flattening sums and products

summands,factors :: RegExp -> [RegExp]
summands (Sum_ e e') = joinMapR (<=) summands [e,e']   -- e <= e' ==> e+e' = e'
summands Mt          = []                              -- mt+e = e     
summands e           = [e]                             -- e+mt = e
factors (Prod e e')  = joinMapR (<*) factors [e,e']    -- e <* e' ==> e*e' = e'
factors Eps          = []                              -- eps*e = e
factors e            = [e]                             -- e*eps = e

-- sorting summands

sortRE :: (RegExp -> RegExp -> Bool) -> ([RegExp] -> RegExp) -> RegExp
                                                             -> RegExp
sortRE r prod e@(Sum_ _ _) = mkSumR $ map (sortRE r prod) $ qsort r
                                                          $ summands e
sortRE r prod e@(Prod _ _) = prod $ map (sortRE r prod) $ factors e
sortRE r prod (Star e)     = Star $ sortRE r prod e
sortRE _ _ e               = e

mkSumR,mkProdL,mkProdR :: [RegExp] -> RegExp
mkSumR []  = Mt
mkSumR es  = foldr1 Sum_ es
mkProdL [] = Eps
mkProdL es = foldl1 Prod es
mkProdR [] = Eps
mkProdR es = foldr1 Prod es

-- distributing products over sums

-- e*(eps+e') = e+e*e', e*(e1+e2) = e*e1+e*e2
-- (eps+e')*e = e+e'*e, (e1+e2)*e = e1*e+e2*e

distributeReg :: RegExp -> RegExp
distributeReg = fixpt (==) f
  where f e = case e of Sum_ _ _   -> mkSumR $ map f $ concatMap g $ summands e
                        Prod e1 e2 -> case g e of [e1,e2] -> Sum_ (f e1) $ f e2
                                                  _       -> Prod (f e1) $ f e2
                        Star e     -> Star $ distributeReg e
                        _          -> e
              where g (Prod e (Sum_ Eps e')) = [e,Prod e e']
                    g (Prod e (Sum_ e1 e2))  = [Prod e e1,Prod e e2]
                    g (Prod (Sum_ Eps e') e) = [e,Prod e' e]
                    g (Prod (Sum_ e1 e2) e)  = [Prod e1 e,Prod e2 e]
                    g e                      = [e]

-- reducing regular expressions iteratively.

reduceLeft,reduceRight,reduceRE :: RegExp -> RegExp
reduceLeft  = fixpt (==) (reduceRE . sortRE (+<) mkProdL)
reduceRight = fixpt (==) (reduceRE . sortRE (<+) mkProdR)
reduceRE e  = case e of Sum_ e1 e2 -> if sizeRE e' < sizeRE e then e'
                                      else Sum_ (reduceRE e1) $ reduceRE e2
                                      where es = summands e
                                            e' = mkSumR $ f es
                                            f (Eps:es) = reduceS True es
                                            f es       = reduceS False es
                        Prod _ _ -> if Mt `elem` es then Mt else mkProdR es
                                    where es = map reduceRE $ factors e
                        Star Mt           -> Eps
                        Star Eps          -> Eps
                        Star (Star e)     -> Star e
                        Star (Sum_ Eps e) -> Star e
                        Star (Sum_ e Eps) -> Star e
                        -- star(star(e)+e') = star(e+e')
                        Star (Sum_ (Star e) e') -> Star $ Sum_ e e'
                        -- star(star(e)+e') = star(e+e')
                        Star (Sum_ e (Star e')) -> Star $ Sum_ e e'
                        -- star(e*star(e)+e') = star(e+e')
                        Star (Sum_ (Prod e1 (Star e2)) e3) | e1 == e2
                                                -> Star $ Sum_ e1 e3
                        -- star(star(e)*e+e') = star(e+e')
                        Star (Sum_ (Prod (Star e1) e2) e3) | e1 == e2
                                                -> Star $ Sum_ e1 e3
                        -- star(e'+e*star(e)) = star(e+e')
                        Star (Sum_ e1 (Prod e2 (Star e3))) | e2 == e3
                                                -> Star $ Sum_ e1 e2
                        -- star(e'+star(e)*e) = star(e+e')
                        Star (Sum_ e1 (Prod (Star e2) e3)) | e2 == e3
                                                -> Star $ Sum_ e1 e2
                        Star e -> Star $ reduceRE e
                        _      -> e

sizeRE :: RegExp -> Int
sizeRE Eps         = 0
sizeRE (Sum_ e e') = sizeRE e+sizeRE e'
sizeRE (Prod e e') = sizeRE e+sizeRE e'+1
sizeRE (Star e)    = sizeRE e+1
sizeRE _           = 1

reduceS :: Bool -> [RegExp] -> [RegExp]

-- eps+e*star(e)   = star(e),   eps+star(e)*e   = star(e)       (1)
-- eps+e*e*star(e) = e+star(e), eps+star(e)*e*e = e+star(e)     (2)

reduceS True (Prod e (Star e'):es) | e == e' = reduceS False $ Star e:es
reduceS True (Prod (Star e) e':es) | e == e' = reduceS False $ Star e:es
reduceS True (Prod e (Prod e1 (Star e2)):es)
                        | e == e1 && e == e2 = reduceS False $ e:Star e:es
reduceS True (Prod (Prod e e1) (Star e2):es)
                        | e == e1 && e == e2 = reduceS False $ e:Star e:es
reduceS True (Prod (Star e1) (Prod e2 e):es)
                        | e == e1 && e == e2 = reduceS False $ e:Star e:es
reduceS True (Prod (Prod (Star e1) e2) e:es)
                        | e == e1 && e == e2 = reduceS False $ e:Star e:es

-- e+e*e'    = e*(eps+e'), e+e'*e    = (eps+e')*e        prepares (1) and (2)
-- e*e1+e*e2 = e*(e1+e2),  e1*e+e2*e = (e1+e2)*e

reduceS b (e:Prod e1 e2:es) | e == e1  = reduceS b $ Prod e (Sum_ Eps e2):es
reduceS b (Prod e1 e2:e:es) | e == e2  = reduceS b $ Prod (Sum_ Eps e1) e:es
reduceS b (Prod e1 e2:Prod e3 e4:es) 
                            | e1 == e3 = reduceS b $ Prod e1 (Sum_ e2 e4):es
reduceS b (Prod e1 e2:Prod e3 e4:es) 
                            | e2 == e4 = reduceS b $ Prod (Sum_ e1 e3) e2:es

reduceS b (e:es) = e:reduceS b es
reduceS True _   = [Eps]
reduceS _ _      = []

-- regToAuto e builds a nondeterministic acceptor with epsilon-transitions of 
-- the language of e.

type NDA = Int -> String -> [Int]

regToAuto :: RegExp -> ([Int],NDA)
regToAuto e = ([0..nextq-1],delta)
      where (delta,nextq) = eval e 0 1 (const2 []) 2
            eval :: RegExp -> Int -> Int -> NDA -> Int -> (NDA,Int)
            eval Mt _ _ delta nextq             = (delta,nextq)
            eval Eps q q' delta nextq           = (upd2L delta q "eps" q',nextq)
            eval (Const a) q q' delta nextq     = (upd2L delta q a q',nextq)
            eval (Var x) q q' delta nextq       = (upd2L delta q x q',nextq)
            eval (Sum_ e e') q q' delta nextq   = eval e' q q' delta' nextq'
                          where (delta',nextq') = eval e q q' delta nextq
            eval (Prod e e') q q' delta nextq   = eval e' nextq q' delta' nextq'
                          where (delta',nextq') = eval e q nextq delta $ nextq+1
            eval (Star e) q q' delta nextq      = (delta2,nextq')
                   where q1 = nextq+1
                         (delta1,nextq') = eval e nextq q1 delta $ q1+1
                         delta2 = fold2 f delta1 [q,q1,q1,q] [nextq,nextq,q',q']
                         f delta q = upd2L delta q "eps"

-- used by Esolve > simplifyT . F "auto" and Ecom > buildKripke 5

type PDA = [Int] -> String -> [Int]

-- powerAuto nda labs builds the (deterministic) power automaton induced by nda 
-- with label set labs.

powerAuto :: NDA -> [String] -> ([[Int]],PDA)
powerAuto nda labs = (reachables,deltaH)
     where reachables = fixpt subset deltaM [epsHull [0]]
           deltaM qss = qss `join` [deltaH qs a | qs <- qss, a <- labs]
           deltaH qs  = epsHull . delta qs
           delta qs a = joinMap (flip nda a) qs
           epsHull :: [Int] -> [Int]
           epsHull qs = if qs' `subset` qs then qs else epsHull $ qs `join` qs'
                        where qs' = delta qs "eps"

-- used by Esolve > simplifyT . F "pauto" and Ecom > buildKripke 5

-- autoToReg sig start builds a regular expression with the same language as the
-- automaton contained in sig if started in start. 

autoToReg :: Sig -> TermS -> RegExp                     -- Kleene's algorithm
autoToReg sig start = if null finals then Const "no final states"
                                     else foldl1 Sum_ $ map (f lg i) finals
         where finals = (sig&value)!!0
               lg = length (sig&states)-1
               Just i = search (== start) (sig&states)
               f (-1) i j = if i == j then Sum_ (delta i i) Eps else delta i j
               f k i j    = Sum_ (f' i j) $
                                 Prod (f' i k) $ Prod (Star $ f' k k) $ f' k j
                            where f' = f $ k-1
               delta :: Int -> Int -> RegExp
               delta i j = if null labs then Mt else foldl1 Sum_ labs
                           where labs = [Const $ showTerm0 $ (sig&labels)!!k |
                                                     k <- indices_ (sig&labels),
                                                     (sig&transL)!!i!!k == [j]]

-- used by Ecom > buildRegExp

-- Brzozowski acceptor of regular and context-free languages

deltaBro :: (String -> Maybe RegExp) -> RegExp -> String -> Maybe RegExp
deltaBro getRHS e x = f e where
                      f Mt          = Just Mt
                      f Eps         = Just Mt
                      f Int_        = Just $ if just $ parse int x then Eps
                                                                   else Mt
                      f (Const a)   = Just $ if a == x then Eps else Mt
                      f (Sum_ e e') = do e <- f e; e' <- f e'; Just $ Sum_ e e'
                      f (Prod e e') = do e1 <- f e
                                         b <- betaBro getRHS e
                                         let p = Prod e1 e'
                                         if b == 0 then Just p
                                                   else do e' <- f e'
                                                           Just $ Sum_ p e'
                      f e'@(Star e) = do e <- f e; Just $ Prod e e'
                      f (Var x)     = do e <- getRHS x; f e

betaBro :: (String -> Maybe RegExp) -> RegExp -> Maybe Int
betaBro getRHS = f where f Eps         = Just 1
                         f Mt          = Just 0
                         f Int_        = Just 0
                         f (Const a)   = Just 0
                         f (Sum_ e e') = do b <- f e; c <- f e'; Just $ max b c
                         f (Prod e e') = do b <- f e; if b == 0 then Just 0
                                                                else f e'
                         f (Star e)    = Just 1
                         f (Var x)     = do e <- getRHS x; f e

unfoldBro :: (String -> Maybe RegExp) -> RegExp -> [String] -> Maybe Int
unfoldBro getRHS e w = do e <- foldlM (deltaBro getRHS) e w; betaBro getRHS e

-- * Minimization with the Paull-Unger algorithm

bisim :: Sig -> [(Int,Int)]
bisim = map (\(i,j,_) -> (i,j)) . fixpt supset bisimStep . bisim0

bisim0 :: Sig -> TriplesL Int
bisim0 sig = [(i,j,f i j) | i <- is, j <- is, i < j, 
                            out sig!!i `eqset` out sig!!j,
                            and $ zipWith eqset (outL sig!!i) $ outL sig!!j]
           where is = indices_ (sig&states)
                 ks = indices_ (sig&labels)
                 b = null (sig&trans)
                 f i j = if b then s
                         else s `join1` ((sig&trans)!!i,(sig&trans)!!j)
                         where s = mkSet $ map h ks
                               h k = ((sig&transL)!!i!!k,(sig&transL)!!j!!k)

bisimStep :: Eq a => TriplesL a -> TriplesL a
bisimStep trips = [trip | trip@(_,_,bs) <- trips, all r bs] where
        r (is,js) = forallThereis r' is js && forallThereis r' js is
        r' i j = i == j || just (lookupL i j trips)
                        || just (lookupL j i trips)
                                                                            
mkQuotient :: Sig -> ([TermS],[[Int]],[[[Int]]],[[Int]],[[[Int]]])
mkQuotient sig = (states',tr,trL,va,vaL)
         where part = mkPartition (indices_ (sig&states)) $ bisim sig 
               states' = map (((sig&states)!!) . minimum) part
               oldPos i = get $ search (== (states'!!i)) (sig&states)
               newPos i = get $ search (elem i) part
               h = mkSet . map newPos
               [is,js,ks] = map indices_ [states',(sig&labels),(sig&atoms)]
               tr  = if null (sig&trans) then []
                     else map f is where f i = h $ (sig&trans)!!oldPos i
               trL = if null (sig&transL) then []
                     else map f is 
                     where f i = map (g i) js
                           g i j = h $ (sig&transL)!!oldPos i!!j
               va  = if null (sig&value) then []
                     else map f ks where f i = h $ (sig&value)!!i
               vaL = if null (sig&valueL) then []
                     else map f ks where f i = map (g i) js
                                         g i j = h $ (sig&valueL)!!i!!j

-- * LR parsing

data ActLR  = Rule String [String] Int | Read | Error deriving (Show,Eq,Ord)

data LoopLR = More [Int] [TermS] [Int] | Success TermS | NoParse

nextLR :: Sig -> Array (Int,Int) ActLR -> [Int] -> [TermS] -> [Int] -> LoopLR
nextLR sig acttab sts@(i:_) ts input@(k:rest) = 
    case acttab!(i,k) of Read | notnull succs -> More (head succs:sts) ts rest
                                              where succs = transL sig!!i!!k
                         Rule left right lg | left == "S" && length ts == lg 
                           -> Success $ F rule ts 
                                            | lgr < length sts && notnull succs
                           -> More (head succs:is) (us++[F rule vs]) input
                              where rule = unwords $ left:"_":right
                                    lgr = length right
                                    is@(i:_) = drop lgr sts
                                    labs = map root (labels sig) 
                                    succs = transL sig!!i!!getInd left labs
                                    (us,vs) = splitAt (length ts-lg) ts
                         _ -> NoParse
nextLR _ _ _ _ _ = NoParse

actTable :: Sig -> (Int,Int) -> ActLR
actTable sig (i,k) = if k `elem` nonterminals || length acts /= 1 then Error
                     else case words $ root $ atoms sig!!head acts of 
                          ["shift"] -> Read
                          ["error"] -> Error
                          left:right 
                            -> Rule left right $ length $ meet right $
                                    map (root . (labels sig!!)) nonterminals
                 where acts = outL!!i!!k
                       outL = invertRelL (sig&labels) (sig&atoms) (sig&states)
                              (sig&valueL)
                       is = indices_ (states sig)
                       ks = indices_ (labels sig)
                       nonterminals = [k | k <- ks, all (null . h k) is]
                       h k i = outL!!i!!k

-- linear equations (polynomials)

type LinEq = ([(Double,String)],Double)   -- a1*x1+...+an*xn+a*x = b

combLins :: (Double -> Double -> Double) -> Double -> LinEq -> LinEq -> LinEq
combLins f c (ps,a) (qs,b) = (comb ps qs,f a b)
           where comb ps@(p@(a,x):ps') qs@((b,y):qs')
                       | x == y               = if fab == 0 then comb ps' qs'
                                                      else (fab,x):comb ps' qs'
                      | y `elem` map snd ps' = p:comb ps' qs
                      | x `elem` map snd qs' = (b*c,y):comb ps qs'
                      | otherwise            = p:(b*c,y):comb ps' qs'
                                                      where fab = f a b
                 comb [] ps                  = map h ps where h (a,x) = (a*c,x)
                 comb ps _                   = ps

addLin, subLin :: LinEq -> LinEq -> LinEq
addLin = combLins (+) 1
subLin = combLins (-) $ -1

mulLin :: (Double -> Double) -> LinEq -> LinEq
mulLin f (ps,b) = (map h ps,f b) where h (a,x) = (f a,x)

-- gauss solves linear equations.

gauss :: [LinEq] -> Maybe [LinEq]
gauss eqs = case gauss1 eqs of 
                  Just eqs -> gauss $ gauss3 eqs
                  _ -> case gauss2 eqs of Just eqs -> gauss $ gauss3 eqs
                                          _ -> Just eqs

-- a1*x1+...+an*xn+a*x = b ----> a1/a*x1+...+an/a*xn+x = b/a
                  
gauss1 :: [LinEq] -> Maybe [LinEq]
gauss1 eqs = do (i,a) <- searchGet (/= 1) $ map (fst . last . fst) eqs
                Just $ updList eqs i $ mulLin (/a) $ eqs!!i

-- p+x = b & q+x = c ----> p-q = b-c & q+x = c

gauss2 :: [LinEq] -> Maybe [LinEq]
gauss2 eqs = do (i,eq,eq') <- searchGet2 f g eqs
                Just $ updList eqs i $ subLin eq eq'
             where f (ps,_)        = fst (last ps) == 1
                   g (ps,_) (qs,_) = last ps == last qs

-- x = b & eqs ----> x = b & eqs[(ps = c-a*b)/(a*x+ps = c)]

gauss3 :: [LinEq] -> [LinEq]
gauss3 = f []
 where f eqs (eq@([(1,x)],b):eqs') = f (map g eqs++[eq]) (map g eqs')
                  where g eq@(ps,c) = case searchGet ((== x) . snd) ps of
                                       Just (i,(a,_)) -> (context i ps,c-a*b) 
                                       _ -> eq
       f eqs (eq:eqs')             = f (eqs++[eq]) eqs'
       f eqs _                            = eqs
                     

-- * Terms, formulas and reducts

data Term a = V a | F a [Term a] | Hidden Special deriving (Show,Eq,Ord)

data Special = Dissect [(Int,Int,Int,Int)] | 
               BoolMat [String] [String] [(String,String)] |
               ListMat [String] [String] (Triples String String) | 
               ListMatL [String] (TriplesL String) | 
               LRarr (Array (Int,Int) ActLR) | Nil deriving (Show,Eq,Ord)

type TermS = Term String

class Root a where undef :: a

instance Root Color                         where undef = white
instance Root Int                           where undef = 0
instance Root Double                         where undef = 0.0
instance Root [a]                           where undef = []
instance (Root a,Root b) => Root (a,b) where undef = (undef,undef)
instance (Root a,Root b,Root c) => Root (a,b,c) 
                                        where undef = (undef,undef,undef)

isV :: Term t -> Bool
isV (V _) = True
isV _     = False

isF :: Term t -> Bool
isF (F _ _) = True
isF _       = False

isHidden :: Term t -> Bool
isHidden (Hidden _) = True
isHidden _          = False

root :: Root a => Term a -> a
root (V x)   = x
root (F x _) = x
root _       = undef

subterms :: Term t -> [Term t]
subterms (F _ ts) = ts
subterms _        = []

outdegree (F _ ts) = length ts
outdegree _        = 0

isLeaf :: Term t -> Bool
isLeaf = null . subterms

height :: (Num a, Ord a) => Term t -> a
height (F _ ts) = foldl max 0 (map height ts)+1
height _        = 1

sizeAll :: Num a => Term t -> a
sizeAll (F _ ts) = sum (map sizeAll ts)+1
sizeAll _        = 1
 
--- instance Eq a => Ord (Term a) where t <= u = sizeAll t <= sizeAll u
size :: Num a => TermS -> a
size (V x)    = if isPos x then 0 else 1
size (F _ ts) = sum (map size ts)+1
size _        = 1

takeT :: (Eq r, Num r) => r -> Term a -> Term a
takeT 1 (F x _)  = F x []
takeT n (F x ts) = F x $ map (takeT $ n-1) ts
takeT _ t        = t

isin :: Eq a => a -> Term a -> Bool
x `isin` V y    = x == y
x `isin` F y ts = x == y || any (isin x) ts
x `isin` _      = False

notIn :: Eq a => a -> Term a -> Bool
notIn x = not . isin x

mapT :: (a -> b) -> Term a -> Term b
mapT f (V a)      = V $ f a
mapT f (F a ts)   = F (f a) $ map (mapT f) ts
mapT _ (Hidden t) = Hidden t

mapTP :: ([Int] -> a -> b) -> [Int] -> Term a -> Term b
mapTP f p (V a)      = V $ f p a
mapTP f p (F a ts)   = F (f p a) $ zipWithSucs (mapTP f) p ts
mapTP f _ (Hidden t) = Hidden t

mapT2 :: (b -> c) -> Term (a,b) -> Term (a,c)
mapT2 f (V (a,p))    = V (a,f p)
mapT2 f (F (a,p) ts) = F (a,f p) $ map (mapT2 f) ts
mapT2 _ (Hidden t)   = Hidden t

foldT :: Root a => (a -> [b] -> b) -> Term a -> b
foldT f (V a)    = f a []
foldT f (F a ts) = f a $ map (foldT f) ts
foldT f _        = f undef []

andT,orT :: Root a => (a -> Bool) -> Term a -> Bool
andT f = foldT g where g x bs = f x && and bs
orT f  = foldT g where g x bs = f x || or bs

foldTP :: Root a => ([Int] -> a -> [b] -> b) -> Term a -> b
foldTP f = g [] where g p (V a)    = f p a []
                      g p (F a ts) = f p a $ zipWithSucs g p ts
                      g p _        = f p undef []

isSubterm :: Eq a => Term a -> Term a -> Bool
isSubterm t u | t == u = True
isSubterm t (F _ ts)   = any (isSubterm t) ts
isSubterm _ _          = False

nodeLabels :: TermS -> [String]
nodeLabels = foldT f where f ('@':_) _ = ["@"]
                           f x xss     = delQuotes x:concat xss

-- used by Ecom > drawThis

transTree1 :: Num a => a -> Term (b,(a,a)) -> Term (b,(a,a))
transTree1 = mapT2 . flip add1

transTree2 :: Num a => (a,a) -> Term (b,(a,a)) -> Term (b,(a,a))
transTree2 = mapT2 . add2

mapT3 :: (b -> c) -> Term (a,b,d) -> Term (a,c,d)
mapT3 f (V (a,p,d))    = V (a,f p,d)
mapT3 f (F (a,p,d) ts) = F (a,f p,d) $ map (mapT3 f) ts
mapT3 _ (Hidden t)     = Hidden t

bothHidden :: Term a -> Term b -> Bool
bothHidden (Hidden _) (Hidden _) = True
bothHidden _ _                   = False

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

-- POINTERS

getPos :: String -> [Int]
getPos = map read . tail . words

isPos :: String -> Bool
isPos x  = leader x "pos"

mkPos0 :: [Int] -> String
mkPos0 p = "pos " ++ unwords (map show p)

mkPos :: [Int] -> TermS
mkPos = V . mkPos0

hasPos :: TermS -> Bool
hasPos (V x)    = isPos x
hasPos (F x ts) = any hasPos ts
hasPos _        = False

-- getSubterm t p returns the subterm at position p of t.

getSubterm :: Term a -> [Int] -> Term a
getSubterm t [] = t
getSubterm (F _ ts) (n:p) | n < length ts = getSubterm (ts!!n) p
getSubterm t _  = Hidden Nil

getSubterm1,removeAllCopies :: TermS -> [Int] -> TermS

-- getSubterm1 t p returns the subterm u at position p of t and replaces each
-- pointer p++q in u by q.

getSubterm1 t p = dropFromPoss p $ getSubterm t p

removeAllCopies t p = f [] t where u = getSubterm t p
                                   f q t | p == q = t
                                         | t == u = mkPos p
                                   f p (F x ts) = F x $ zipWithSucs f p ts
                                   f _ t        = t

-- used by Ecom > removeCopies

-- label t p returns the root of the subterm at position p of t.

label :: Root a => Term a -> [Int] -> a
label t [] = root t
label (F _ ts) (n:p) | n < length ts = label (ts!!n) p
label _ _  = undef

allPoss :: Root a => Term a -> [[Int]]
allPoss (F _ ts) = []:liftPoss allPoss ts
allPoss _        = [[]]

labPositions :: (String -> Bool) -> TermS -> [[Int]]
labPositions f t = filter (f . label t) $ allPoss t

refPositions = labPositions isPos

-- used by Esolve > bodyAndSub

noRefPositions = labPositions $ not . isPos

-- used by removeNonRoot,reduceExas,unify,
-- Esolve > parseFlow,applyToHeadOrBody and Ecom > narrowPar,rewritePar

-- sources p t returns all (non-pointer) sources in t of pointer q.

sources q t = labPositions f t where f x = isPos x && getPos x == q
           -- [p | p <- allPoss t `minus` targets t, getPos (trace t p) == q]

-- used by Esolve > simplifyOne

targets :: TermS -> [[Int]]

targets = foldT f where f x pss = if isPos x then [getPos x] else joinM pss

-- used by addTargets and Esolve > bodyAndSub

markPoss :: Char -> TermS -> [[Int]]
markPoss c = foldT f
             where f x pss = if leader x $ c:"pos" then getPos z:ps else ps
                             where (z,_) = break (== '@') x
                                   ps = concat pss

-- used by Esolve > simplifyOne

reference :: TermS -> [Int] -> [[Int]] -> TermS
reference t p ps = foldl g (f [] t) ps
                   where f q (F x ts) = if q `elem` ps then mkPos p
                                        else F x $ zipWithSucs f q ts
                         f q t        = if q `elem` ps then mkPos p else t
                         g t q = changePoss q p t

-- used by Ecom > refNodes

dereference :: TermS -> [[Int]] -> TermS
dereference = foldl f where f t p = moveAndReplace t (getPos $ label t p) t p
                                                            -- trace

-- used by Esolve > simplifyOne,expandFix,bodyAndSub and Ecom > derefNodes

-- trace t p returns the position of the first non-pointer that is reachable
-- from p.

trace :: TermS -> [Int] -> String
trace t p = if isPos x then trace t $ getPos x else mkPos0 p
            where x = label t p

-- used by dereference,setPointers,collapseCycles,composePtrs

mkHidden :: TermS -> TermS
mkHidden (F x ts)   = F x $ map mkHidden ts
mkHidden (Hidden _) = leaf "hidden"
mkHidden t          = t

-- used by Epaint > widgConst and Ecom > drawThis

constrPositions sig    = labPositions (sig&isConstruct)

fixPositions           = labPositions $ isFixF . take 2

varPositions sig       = labPositions $ isVar sig

changeable t p         = label (t>>>(const $ leaf "FREEPOS")) p == "FREEPOS"

freePositions sig t    = filter (changeable t) $ varPositions sig t

freeXPositions sig t x = filter (changeable t &&& f) $ varPositions sig t
                         where f p = label t p == x

-- used by Ecom > applySubstTo'

boolPositions sig t@(F _ ts) = if isFormula sig t then []:ps else ps
                               where ps = liftPoss (boolPositions sig) ts
boolPositions _ _            = []

-- used by Ecom > setNarrow,narrowOrRewritePar

-- valPositions t returns the value positions of flowtree nodes of t.

valPositions (F x ts) | isFlowNode x = [last $ indices_ ts]:f (init ts)
                      | True         = f ts where f = liftPoss valPositions
valPositions _ = []

isFlowNode x = x `elem` words "assign ite fork not \\/ /\\ <> # MU NU"

(m:p) << (n:q) = m == n && p << q
_     << p     = notnull p

p <<= q = p << q || p == q

orthos ps = and [not $ p << q | p <- ps, q <- ps]

-- liftPoss lifts the term positions computed by f to term list positions.

liftPoss :: Root a => (Term a -> [[Int]]) -> [Term a] -> [[Int]]
liftPoss f ts = concatMap g $ indices_ ts where g i = map (i:) $ f $ ts!!i

-- addToPoss p t adds the prefix p to all pointers of t that point to subterms
-- of t. dropFromPoss p t removes the prefix p from each pointer of t below p.

addToPoss,dropFromPoss :: [Int] -> TermS -> TermS

addToPoss [] = id
addToPoss p  = mapT f where f x = if isPos x then mkPos0 $ p++getPos x else x

dropFromPoss [] = id
dropFromPoss p  = mapT f where
                  n = length p
                  f x = if isPos x && p <<= q then mkPos0 $ drop n q else x
                        where q = getPos x

dropFromPossC :: Char -> [Int] -> TermS -> TermS
dropFromPossC _ [] = id
dropFromPossC c p  = mapT f where
                     n = length p
                     f x = if isPos x then if p <<= q then mkPos0 $ drop n q
                                                      else c:x
                           else x where q = getPos x

-- used by addTargets,match

add1ToPoss = addToPoss [1]

addNatsToPoss = zipWith (addToPoss . single) [0..]

drop0FromPoss = dropFromPoss [0]

dropnFromPoss :: Int -> TermS -> TermS
dropnFromPoss n = mapT f where
                  f x = if isPos x then mkPos0 $ drop n $ getPos x else x

-- changePoss p q t replaces all pointers p++r of t by q++r.

changePoss :: [Int] -> [Int] -> TermS -> TermS
changePoss p q = mapT f where f x = if isPos x && p <<= r
                                    then mkPos0 $ q++drop (length p) r else x
                                    where r = getPos x

-- used by moveAndReplace,expand and Esolve > simplifyGraph.

-- changeLPoss p q ts applies changePoss p(i) q(i) to ts!!i.

changeLPoss :: (Int -> [Int]) -> (Int -> [Int]) -> [TermS] -> [TermS]
changeLPoss p q ts = zipWith g ts $ indices_ ts
                     where f t = foldl g t $ indices_ ts
                           g t i = changePoss (p i) (q i) t

-- used by Esolve > simplifyF mapG/cantor../t:ts

-- movePoss t p q dereferences a pointer pos of u = getSubterm t p and expands
-- the target of pos if pos points to a node r below q, but not below p.
-- On other nodes of u, movePoss t p q works the same as changePoss p q u does.

movePoss :: TermS -> [Int] -> [Int] -> TermS
movePoss t p q = f $ getSubterm t p
           where n = length p
                 f (F x ts)          = F x $ map f ts
                 f u@(V x) | isPos x = if p <<= r then mkPos $ q++drop n r
                                       else if q <<= r then expand 0 t r else u
                                       where r = getPos x
                 f t = t

-- used by replace,moveAndReplace,expand{One,Into}

-- Before simplifying a redex t, addTargets t p redex saves the target positions
-- of every pointer of t into redex by prefixing the label of its target node q
-- with tpos(q) if q belongs to redex. Pointers of redex that point to the
-- context of redex are prefixed with 'e'.

addTargets :: TermS -> [Int] -> TermS
addTargets t p = addChar 't' u $ targets u where u = dropFromPossC 'e' p t

-- used by Esolve > simplifyOne,expandFix

addChar :: Char -> TermS -> [[Int]] -> TermS
addChar c t srcs = mapTP f [] t
                   where f p x = if p `elem` srcs then c:mkPos0 p++'@':x else x

-- used by addTargets and Esolve > simplifyOne,bodyAndSub

-- For all nodes p of t with label prefix tpos(q) such that p =/= q,
-- chgTargets t turns all pointers of t to q into pointers to p. Then the
-- prefixes are deleted.

chgTargets :: TermS -> TermS
chgTargets t = mapT (delMark 't') $ mapT f t where
               f x = if isPos x then case lookup (getPos x) pairs of
                                          Just target -> mkPos0 target
                                          _ -> x
                                else x
               pairs = foldTP mkPairs t
               mkPairs target x pss = if leader x "tpos" && p /= target
                                      then (p,target):pairs else pairs
                                      where p = getPos $ fst $ break (== '@') x
                                            pairs = concat pss

-- used by Esolve > simplifyOne

delMark c x = if leader x $ c:"pos" then z else x
              where (_,_:z) = break (== '@') x

-- used by chgTargets and Esolve > bodyAndSub

delExt x = if leader x "epos" then tail x else x

-- used by chgTargets

delHid x = if leader x "hpos" then tail x else x

-- used by instantiate

-- connected t p q checks whether t contains a path from p to q.

connected :: TermS -> [Int] -> [Int] -> Bool
connected t p q = f t [] p
             where f t ps p = p `notElem` ps && g ps p (getSubterm t p)
                   g ps p (F x ts) = p == q || or (zipWithSucs (g $ p:ps) p ts)
                   g ps p (V x)    = p == q || isPos x && f t ps (getPos x)
                   g _ p _         = p == q

-- used by cycleTargets,removeCyclePtrs,expand

cycleTargets :: TermS -> [[Int]]
cycleTargets t = f [] t
            where f p (F _ ts) = joinM $ zipWithSucs f p ts
                  f p (V x)    = if isPos x && connected t q p then [q] else []
                                 where q = getPos x
                  f _ _        = []

-- used by Ecom > showCycleTargets

removeCyclePtrs :: TermS -> TermS
removeCyclePtrs t = case f [] t of Just p -> removeCyclePtrs $ lshiftPos t [p]
                                   _ -> t
             where f p (F _ ts) = do guard $ any just ps; head $ filter just ps
                                  where ps = zipWithSucs f p ts
                   f p (V x)    = do guard $ isPos x && connected t q p; Just p
                                  where q = getPos x
                   f _ _        = Nothing

-- used by Ecom > removeEdges

-- succs p computes a list of successor positions of p.

succs :: [Int] -> [Int] -> [[Int]]
succs p = map $ \i -> p++[i]

succsInd :: [Int] -> [a] -> [[Int]]
succsInd p = succs p . indices_

-- zipWithSucs f p s applies a binary function after zipping the list of
-- direct successor positions of p with s.

zipWithSucs :: ([Int] -> a -> b) -> [Int] -> [a] -> [b]
zipWithSucs f p = zipWith f $ succs p [0..]

zipWithSucsM :: Monad m => ([Int] -> a -> m b) -> [Int] -> [a] -> m [b]
zipWithSucsM f p = zipWithM f $ succs p [0..]

-- zipWithSucs2 f p as bs applies a ternary function after zipping the list of
-- direct successor positions of p with as and bs.

zipWithSucs2 :: ([Int] -> a -> b -> c) -> [Int] -> [a] -> [b] -> [c]
zipWithSucs2 f p = zipWith3 f $ succs p [0..]

-- possOf t x returns the first position of t labelled with x.

possOf :: TermS -> String -> Maybe [Int]
possOf t x = do p:_ <- Just $ f t; Just p
             where f (F y ts)       = if x == y then [[]] else liftPoss f ts
                   f (V y) | x == y = [[]]
                   f _              = []

-- closedSub t p turns the subtree of t at position p into a closed subgraph.

closedSub :: TermS -> [Int] -> TermS
closedSub t p = dropFromPoss p $ if foldT f u then u else expand 0 t p
                where u = getSubterm t p
                      f x bs = not (isPos x) || p <<= getPos x && and bs

-- used by Ecom > showSubtreePicts

-- colorWith2 c d ps t colors t at all positions of ps with c and at all other
-- positions with d.

colorWith2 c d ps = mapTP f [] where
                    f p x = if isPos x then x 
                            else if p `elem` ps then c++'_':x else d++'_':x

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

-- used by Ecom > showChanged

-- glbPos ps returns the greatest lower bound of ps with respect to <<=.

glbPos :: [[Int]] -> [Int]
glbPos ps = foldl1 f ps where f (m:p) (n:q) = if m == n then m:f p q else []
                              f _ _         = []

-- used by Ecom > applyDisCon,showGlb

-- Any r: restPos p q = r  <==>  p <<= q

restPos (m:p) (n:q) = if m == n then restPos p q else []
restPos _ q         = q

-- used by Ecom > applyDisCon   

-- nodePreds t p returns the predecessor positions of position p of t.

nodePreds t p = if null p then ps else init p:ps
                where ps = concatMap (nodePreds t) $ labPositions f t
                      f x = x == mkPos0 p

-- used by Ecom > showPreds

-- nodeSucs t p returns the first non-pointer successor positions of position p
-- of t.

nodeSucs t p = case getSubterm t p of F x ts -> zipWithSucs getNode p ts
                                      V x | isPos x -> nodeSucs t $ getPos x
                                          | True    -> []
               where getNode _ (V x) | isPos x = getNode p $ getSubterm t p
                                                 where p = getPos x
                     getNode p _               = p

-- used by Ecom > showSucs

-- posTree [] t replaces the node entries of t by the respective node positions.
-- Pointer positions are labelled with the respective target node positions.

posTree :: [Int] -> TermS -> Term [Int]
posTree p t | isHidden t  = F p []
posTree p (F _ ts)        = F p $ zipWithSucs posTree p ts
posTree p (V x) | isPos x = V $ getPos x
                | True    = V p

-- replace0 t p u replaces the subterm of t at position p by u.

replace0 :: Term a -> [Int] -> Term a -> Term a
replace0 t p u = f t p where f _ []         = u
                             f (F x ts) p   = F x $ g ts p
                             g (t:ts) (0:p) = f t p:ts
                             g (t:ts) (n:p) = t:g ts (n-1:p)
                             g _ _          = []

-- used by cutTree,dereference,derefFst,separateTerms,removeNonRoot,exchange,
-- expand and Ecom > catchTree,copySubtrees,expandTree',reduceRegExp,
-- releaseNode,releaseTree,replaceNodes',subsumeSubtrees

replace,replace1 :: TermS -> [Int] -> TermS -> TermS

-- For all pointers p->q of t such that p does not belong to the subterm t|p0 of
-- t at position p0, but q >> p0, replace t p0 u dereferences t at p. Further
-- pointers with target q are redirected to the root of t|p. Then t|p0 is
-- replaced by u.

replace t p0 u = f [] t
         where f p _ | p == p0     = u
               f p (F x ts)        = F x $ zipWithSucs f p ts
               f p (V x) | h x p q = if p == r then movePoss t q p else mkPos r
                                     where q = getPos x
                                           Just r = lookup q $ foldTP g t
               f _ t               = t
               g p x pss | p == p0 = []
                         | h x p q = [(q,p)]
                         | True    = concat pss where q = getPos x
               h x p q = isPos x && p0 << q && not (p0 <<= p)

-- used by collapseCycles,cutTree,expandOne,replace1,moveAndReplace,unify,
-- Esolve > applyAx,applyLoop{Random},applyMany,applyPar,applySingle,mkEqs and
-- Ecom > applyInd,applySubst{To'},createInvariant,expandTree',generalizeEnd,
-- narrowPar,narrowSubtree,releaseNode,releaseTree,renameVar',replaceVar,
-- rewriteVar,stretch,subsumeSubtrees

replace1 t p u = replace t p $ mapT delExt $ addToPoss p u

-- used by changeTerm, Esolve > shiftSubformulas and Ecom > applyTransitivity,
-- collapseStep,composePointers,decomposeAtom,evaluateTrees,releaseTree,
-- replaceOther,replaceSubtrees',shiftPattern,shiftQuants,showEqsOrGraph,
-- showNumbers,showRelation,showTransOrKripke,simplifySubtree,storeGraph,
-- subsumeSubtrees,unifySubtrees

-- moveAndReplace t src u tgt copies the subterm at position src of t to
-- position tgt of u and replaces each pointer src++r in the modified term by
-- tgt++r.

moveAndReplace :: TermS -> [Int] -> TermS -> [Int] -> TermS
moveAndReplace t src u tgt = replace u tgt $ changePoss src tgt
                                           $ f [] $ getSubterm t src
                       where f p (F x ts) = F x $ zipWithSucs f p ts
                             f p (V x) | isPos x && not (src <<= q) && tgt << q
                                          = movePoss t q p where q = getPos x
                             f _ t = t

-- used by dereference,changeTerm and Ecom > releaseSubtree

-- removeTreePath p t removes the path p in the Hackendot game.

removeTreePath :: [Int] -> TermS -> TermS
removeTreePath p t = F "" $ map (getSubterm t) $ filter f $ allPoss t
                     where f q = not (q <<= p) && (null q' || q' <<= p)
                                 where q' = init q

-- TERM EQUALITY and more

collector x = x `elem` words "^ {} []"

collectors x y = collector x && collector y

isNEq x = x `elem` words "== = =/="

isOrd x = x `elem` words "< > = <= >=" 

permutative x = isNEq x || idempotent x || x `elem` words "^ + * ;"

idempotent x = x `elem` words "| & \\/ /\\ <+> {}"

isEmpty :: TermS -> Bool
isEmpty (F x []) | collector x = True
isEmpty _ = False

eqTerm :: TermS -> TermS -> Bool
eqTerm t u | t == u                  = True
eqTerm (F "<" [t,u]) (F ">" [v,w])   = eqTerm t w && eqTerm u v
eqTerm (F ">" [t,u]) (F "<" [v,w])   = eqTerm t w && eqTerm u v
eqTerm (F "<=" [t,u]) (F ">=" [v,w]) = eqTerm t w && eqTerm u v
eqTerm (F ">=" [t,u]) (F "<=" [v,w]) = eqTerm t w && eqTerm u v
eqTerm (F x [t]) (F y [u])
               | binder x && binder y && opx == opy && length xs == length ys =
                          eqTerm (renameFree emptySig (fold2 upd id xs ys) t) u
                          where opx:xs = words x
                                opy:ys = words y
eqTerm (F x ts) (F y us)
               | x == y = if idempotent x then eqSet eqTerm ts us
                          else if permutative x then eqBag eqTerm ts us
                               else eqTerms (renameVars emptySig x ts us) us
eqTerm t u = bothHidden t u

eqTerms :: [TermS] -> [TermS] -> Bool
eqTerms ts us = length ts == length us && and (zipWith eqTerm ts us)

renameVars :: Sig -> String -> [TermS] -> [TermS] -> [TermS]
renameVars sig x ts us = if lambda x then f ts us else ts
                    where f (t:t':ts) (u:_:us) = mapT chg t:mapT chg t':f ts us
                                  where xs = allVars sig t
                                        ys = allVars sig u
                                        chg x = case search (== x) xs of 
                                                 Just i | i < length ys -> ys!!i
                                                 _ -> x
                          f _ _ = []

-- used by eqTerm,splitEq

neqTerm :: TermS -> TermS -> Bool
neqTerm t = not . eqTerm t

inTerm :: TermS -> [TermS] -> Bool
inTerm    = any . eqTerm

notInTerm :: TermS -> [TermS] -> Bool
notInTerm = all . neqTerm

subsetTerm :: [TermS] -> [TermS] -> Bool
subsetTerm ts us = all (`inTerm` us) ts

prefix :: [TermS] -> [TermS] -> Bool
prefix (t:ts) (u:us) = eqTerm t u && prefix ts us
prefix ts _          = null ts

suffix :: [TermS] -> [TermS] -> Bool
suffix ts@(_:_) us@(_:_) = eqTerm (last ts) (last us) && 
                            suffix (init ts) (init us)
suffix ts _              = null ts

sharesTerm :: [TermS] -> [TermS] -> Bool
sharesTerm = any . flip inTerm

disjointTerm :: [TermS] -> [TermS] -> Bool
disjointTerm = all . flip notInTerm

distinctTerms :: [[TermS]] -> Bool
distinctTerms (ts:tss) = all (null . meetTerm ts) tss && distinctTerms tss
distinctTerms _        = True

meetTerm :: [TermS] -> [TermS] -> [TermS]
meetTerm ts us = [t | t <- ts, inTerm t us]

joinTerm :: [TermS] -> TermS -> [TermS]
joinTerm ts@(t:us) u = if eqTerm t u then ts else t:joinTerm us u
joinTerm _         t = [t]

joinTerms :: [TermS] -> [TermS] -> [TermS]
joinTerms = foldl joinTerm

mkSetTerm = F "{}" . joinTerms []

joinTermsM :: [[TermS]] -> [TermS]
joinTermsM = foldl joinTerms []

joinTermMap :: (TermS -> [TermS]) -> [TermS] -> [TermS]
joinTermMap f = joinTermsM . map f

removeTerm :: [TermS] -> TermS -> [TermS]
removeTerm (t:ts) u = if eqTerm t u then removeTerm ts u else t:removeTerm ts u
removeTerm _ _      = []

removeTerms :: [TermS] -> [TermS] -> [TermS]
removeTerms = foldl removeTerm

-- sucTerms t ps returns the proper subterms of t that include a position of ps.
sucTerms :: Term t -> [[Int]] -> [Term t]
sucTerms t = concatMap (f . tail)
    where f p@(_:_) = getSubterm t p:f (init p)
          f _       = []

-- used by Ecom > applyDisCon

-- * Variables

vars :: TermS -> [String]
vars (F _ ts) = joinMap vars ts
vars (V x)    = if isPos x then [] else [x]
vars _        = []

isVar :: Sig -> String -> Bool
isVar sig = isFovar sig ||| isHovar sig

isVarRoot :: Sig -> TermS -> Bool
isVarRoot sig = isV ||| isHovar sig . getOp ||| isHidden

newVar :: Int -> TermS
newVar n = V $ 'z':show n

mkVar :: Sig -> String -> TermS 
mkVar sig x = if (sig&isFovar) x then V x else F x []

allSyms :: (String -> Bool) -> TermS -> [String]
allSyms b (F x [t]) | binder x = allSyms b t `join` filter b (tail $ words x)
allSyms b (F x ts)  | b x      = us `join1` x
                    | True     = us where us = joinMap (allSyms b) ts
allSyms b (V x) = if null x || isPos x || not (b x) then [] else [x]
allSyms _ _     = []

sigVars,allVars,bounded,frees :: Sig -> TermS -> [String]
sigVars = allSyms . isVar

allVars sig t = vars t `join` sigVars sig t

bounded sig (F x [t]) | binder x = tail (words x)
bounded sig (F x ts)  | lambda x = joinMap (sigVars sig) $ evens ts
                      | True     = joinMap (bounded sig) ts
bounded sig (V x)                = []

frees sig t = sigVars sig t `minus` bounded sig t

allFrees :: TermS -> [String]
allFrees (F x [t]) | binder x = allFrees t `minus` tail (words x)
allFrees (F x ts)  | lambda x = concat $ zipWith f (evens ts) $ odds ts
                   | True     = joinMap allFrees ts `join1` x
                                where f par t = allFrees t `minus` allFrees par
allFrees (V x)                = if null x || isPos x then [] else [x]
allFrees _                    = []

-- used by renameAwayFrom

anys :: TermS -> [String]
anys (F ('A':'n':'y':x) _) = words x
anys _                     = []

alls :: TermS -> [String]
alls (F ('A':'l':'l':x) _) = words x
alls _                     = []

removeAny :: String -> TermS -> TermS
removeAny x (F ('A':'n':'y':z) [t]) = mkAny (words z `minus1` x) t
removeAny _ t                       = t

removeAll :: String -> TermS -> TermS
removeAll x (F ('A':'l':'l':z) [t]) = mkAll (words z `minus1` x) t
removeAll _ t                       = t

isAnyQ :: TermS -> Bool
isAnyQ (F ('A':'n':'y':_) _) = True
isAnyQ _                     = False

isAllQ :: TermS -> Bool
isAllQ (F ('A':'l':'l':_) _) = True
isAllQ _                     = False

-- isAny/isAll t x p checks whether an occurrence of x at position p of t is
-- existentially/universally quantified and, if so, returns the quantifier 
-- position.
isAny,isAll :: TermS -> String -> [Int] -> Maybe [Int]
isAny t x = f where f p = case getSubterm t p of
                          F ('A':'n':'y':z) _ | x `elem` words z -> Just p
                          F ('A':'l':'l':z) _ | x `elem` words z -> Nothing
                          _ -> do guard $ notnull p; f $ init p

isAll t x = f where f p = case getSubterm t p of
                          F ('A':'l':'l':z) _ | x `elem` words z -> Just p
                          F ('A':'n':'y':z) _ | x `elem` words z -> Nothing
                          _ -> do guard $ notnull p; f $ init p

-- isFree t x p checks whether an occurrence of x at position p of t is free.

isFree :: TermS -> String -> [Int] -> Bool
isFree t x = f where f p = case getSubterm t p of
                                F ('A':'l':'l':z) _ | x `elem` words z -> False
                                F ('A':'n':'y':z) _ | x `elem` words z -> False
                                _ -> null p || f (init p)

isAnyOrFree t x = just . isAny t x ||| isFree t x

isAllOrFree t x = just . isAll t x ||| isFree t x

-- universal sig t p u checks whether all occurrences of free variables of u
-- below position p of t are (implicitly) universally quantified at position p.

universal :: Sig -> TermS -> [Int] -> TermS -> Bool
universal sig t p u = polarity True t p && all f (frees sig u) where
                      f x = case isAny t x p of
                                 Just q  -> cond False q
                                 _ -> case isAll t x p of Just q -> cond True q
                                                          _ -> True
                          where cond b q = polarity b t q &&
                                           (all (p <<) $ filter (q <<)
                                                       $ labPositions (== x) t)

-- used by Ecom > applyCoinduction,applyInduction,createInvariant

-- quantPoss t xs computes, for every quantified variable x in xs, the root 
-- position of the scope of x.

quantPoss :: TermS -> [String] -> ([String],[[Int]])
quantPoss t xs = unzip $ do p <- labPositions (`elem` xs) t
                            let x = label t p
                                anyPos = isAny t x p; allPos = isAll t x p
                                q = get anyPos; r = get allPos
                            if just anyPos && polarity True t q
                               then [(x,q++[0])]
                               else if just allPos && polarity False t r
                                       then [(x,r++[0])] else []

-- used by Ecom > unifySubtrees

-- * Unparser
-- ** Term unparser

blanks :: Int -> String -> String
blanks n    = (replicate n ' ' ++)

newBlanks :: Int -> String -> String
newBlanks n = ('\n':) . blanks n

enclose :: (String -> String) -> String -> String
enclose f   = ('(':) . f . (')':)

showTree :: Bool -> TermS -> String
showTree False t = fst (showImpl t 0) ""
showTree _ t     = foldT f t
                   where f "range" [str1,str2] = '[':str1++".."++str2++"]"
                         f "lsec" [str,x]      = '(':str++x++")"
                         f "rsec" [x,str]      = '(':x++str++")"
                         f x []                = x
                         f "()" strs           = '(':g "," strs++")"
                         f "[]" strs           = '[':g "," strs++"]"
                         f "{}" strs           = '{':g "," strs++"}"
                         f "~" [str]           = '~':str
                         f x [str@(_:_:_)] | head str == '(' && last str == ')'
                                               = x++str
                         f x strs | isInfix x  = '(':g x strs++")"
                                  | isQuant x  = x++':':'(':g "," strs++")"
                                  | isFix x    = x++'.':'(':g "," strs++")"
                                  | True       = x++'(':g "," strs++")"
                         g _ [str]      = str
                         g x (str:strs) = str++x++g x strs

-- show+ t n = (u,k) iff the string u that represents t starts at position n of
-- a line and the last line of u consists of k characters.
showImpl :: TermS -> Int -> (String -> String, Int)
showImpl (F x ds@[_,_]) | implicational x = showVer x showDisjunct ds
showImpl d                                    = showDisjunct d

showDisjunct :: TermS -> Int -> (String -> String, Int)
showDisjunct (F "|" cs) = showVer "|" showConjunct cs
showDisjunct c          = showConjunct c

showConjunct :: TermS -> Int -> (String -> String, Int)
showConjunct (F "&" fs) = showVer "&" showFactor fs
showConjunct f          = showFactor f

showFactor (F "Not" [impl]) n     = (("Not(" ++) . si . (')':),k+5)
                                    where (si,k) = showImpl impl $ n+4
showFactor t@(F x _) n
      | propositional x           = (enclose si,k+2)
                                    where (si,k) = showImpl t $ n+1
showFactor (F "==" ts) n          = showVer "==" showTerm ts n
showFactor t n                    = showTerm t n

showTerm0 :: TermS -> String
showTerm0 t = fst (showTerm t 0) ""

showTerm :: TermS -> Int -> (String -> String, Int)
showTerm (V x) _                  = ((x++),length x)
showTerm (F x []) _               = if just $ parse realNeg x
                                     then ((' ':) . (x++),lg+1) else ((x++),lg)
                                    where lg = length x
showTerm (F x [t]) n
      | x `elem` "~":termBuilders = ((x++) . enclose st,lg+2+k)
                                     where lg = length x
                                           (st,k) = showImpl t $ n+lg+1
showTerm (F "$" [t,u]) n          = (st . argEnclose u su,k+m+2)
                                    where (st,k) = showTerm t n
                                          (su,m) = showTerm u $ n+k+1
showTerm (F x ts) n
      | just $ parse indEquiv x   = showVer ('~':x) showFactor ts n
showTerm (F x ts) n | isInfix x   = showVer x showFactor ts n
showTerm (F "ite" [t,u,v]) n      = (("ite("++) . st . (',':) . su . (',':) .
                                     sv . (')':),k+l+m+7)
                                    where (st,k) = showImpl t $ n+4
                                          (su,l) = showTerm u $ n+k+1
                                          (sv,m) = showTerm v $ n+k+l+1
showTerm (F "||" [t,u]) n         = (st . ("||"++) . su,k+m+2)
                                    where (st,k) = showTerm t n
                                          (su,m) = showTerm u $ n+k+2
showTerm (F "range" [t,u]) n      = (('[':) . st . (".."++) . su . (']':),
                                     k+m+4) where (st,k) = showTerm t $ n+1
                                                  (su,m) = showTerm u $ n+k+3
showTerm (F "lsec" [t,F x []]) n  = (enclose $ st . (x++),k+length x)
                                    where (st,k) = showTerm t (n+1)
showTerm (F "rsec" [F x [],t]) n  = (enclose $ (x++) . st,k+lg)
                                    where (st,k) = showTerm t $ n+lg-1
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
                                          (st,k) = infixEnclosed t $ n+lg
                                          (su,m) = infixEnclosed t $ n+1
showTerm (F x ts) n               = ((x++) . sts,lg+k) 
                                     where lg = length x
                                           (sts,k) = showEnclosed ts $ n+lg
showTerm (Hidden _) _             = (("hidden"++),6)

showTerms :: [TermS] -> Int -> (String -> String, Int)
showTerms = showVer "," showFactor

showVer x single ts n = f ts
    where (lgx,g) = if x `elem` words ". ^ ^^ , : ++ + - * ** / # <> /\\ \\/"
                    then (lg,(x++)) else (lg+2,((' ':x++" ")++))
                    where lg = length x
          f ts = if length ts < 2 then showHor ts n
                                  else if just pair then fst $ get pair
                                       else (sts . g . newBlanks n . sus,k')
                 where pair = fits ts []
                       fits ts us = do guard $ n+k < 80 && all (/= '\n') (g "")
                                       Just (stsk,us)
                                    where stsk@(g,k) = showHor ts n
                       ((sts,_),us) = h (init ts) [last ts]
                       (sus,k') = f us
                       h ts us = if length ts < 2 then (showHor ts n,us)
                                 else if just pair then get pair
                                      else h (init ts) $ last ts:us
                                 where pair = fits ts us
          showHor (t:ts) n = if null ts then stk else (st . g . sts,k'+m)
                   where stk@(st,k) = if propositional x || isNEq x || x == ","
                                      then single t n else infixEnclosed t n
                         (sts,m) = showHor ts $ n+k'
                         k' = k+lgx
          showHor _ _ = (id,0)

infixEnclosed t = if isInfix $ root t then showEnclosed [t] else showImpl t

showEnclosed [t] n | root t `elem` words "[] {} lsec rsec" = showTerm t n
showEnclosed ts n = (enclose sts,k+2) where (sts,k) = showTerms ts $ n+1

argEnclose t st = if root t `elem` words "() {} [] range lsec rsec"
                  then st else enclose st

-- special unparsers

showSummands cs = fst (showVer0 "| " showConjunct cs 0 True) ""

showFactors fs  = fst (showVer0 "& " showFactor fs 0 True) ""

showSum ts      = fst (showVer0 "<+> " showTerm ts 0 True) ""

showVer0 x single (t:ts) n b = if b then (blanks lg . st . sts,m)
                               else if null ts then (h,lg+k) else (h . sts,m)
                               where lg = length x
                                     (st,k) = single t (n+lg)
                                     (sts,m) = showVer0 x single ts n False
                                     h = newBlanks n . (x++) . st
showVer0 _ _ _ _ _           = (id,0)

-- * Term parser into Haskell types

parseBins :: TermS -> Maybe [String]
parseBins t = do s <- parseList (parse quoted . root) t
                 guard $ notnull s && allEqual (map length s) && 
                         all (all (`elem` "01#")) s        
                 Just s

parseBool :: TermS -> Maybe Bool
parseBool (F "0" []) = Just False
parseBool t               = do F "1" [] <- Just t; Just True

parseChar :: TermS -> Maybe Char
parseChar t          = do F [c] [] <- Just t; Just c

parseConst :: Term a -> Maybe a
parseConst t         = do F a [] <- Just t; Just a

parseConsts :: TermS -> Maybe [String]
parseConsts          = parseList' parseConst

parseConstTerms :: TermS -> Maybe (String, [String])
parseConstTerms t    = do F "()" [c,ts] <- Just t
                          c <- parseConst c; Just (c,show ts)
                       where show (F x ts) | collector x = map showTerm0 ts
                             show t                      = [showTerm0 t]


parseConsts2 :: TermS -> Maybe ([String], [String])
parseConsts2 t       = do F "()" [cs,ds] <- Just t; cs <- parseConsts cs
                          ds <- parseConsts ds; Just (cs,ds)

parseConsts3 :: TermS -> Maybe ([String], [String], [String])
parseConsts3 t       = do F "()" [cs,ds,es] <- Just t; cs <- parseConsts cs
                          ds <- parseConsts ds; es <- parseConsts es
                          Just (cs,ds,es)

parseConsts2Term :: TermS -> Maybe ([String], [String], TermS)
parseConsts2Term t   = do F "()" [cs,ds,t] <- Just t; cs <- parseConsts cs
                          ds <- parseConsts ds; Just (cs,ds,t)

parseConsts2Terms :: TermS -> Maybe ([String], [String], [TermS])
parseConsts2Terms t  = do F "()" [cs,ds,ts] <- Just t; cs <- parseConsts cs
                          ds <- parseConsts ds; Just (cs,ds,get ts)
                       where get (F x ts) | collector x = ts
                             get t                      = [t]


type Termparser a = TermS -> Maybe a

parseList,parseList' :: Termparser a -> Termparser [a]
parseList f t  = do F "[]" ts <- Just t; mapM f ts
parseList' f t = parseList f t ++ do a <- f t; Just [a]

type TermparserT m a = TermS -> MaybeT m a

parseListT,parseListT' :: Monad m =>  TermparserT m a ->  TermparserT m [a]
parseListT f t  = case t of F "[]" ts -> mapM f ts; _ -> zero
parseListT' f t = parseListT f t ++ do a <- f t; return [a]

parseColl :: (TermS -> Maybe b) -> TermS -> Maybe [b]
parseColl parser t  = do F x ts <- Just t; guard $ collector x; mapM parser ts

parseWords :: TermS -> Maybe [String]
parseWords cw              = do cw <- parseConst cw; Just $ words cw

parseNat :: TermS -> Maybe Int
parseNat t                 = do a <- parseConst t; parse nat a

parsePnat :: TermS -> Maybe Int
parsePnat t                = do a <- parseConst t; parse pnat a

parseInt :: TermS -> Maybe Int
parseInt t                 = do a <- parseConst t; parse int a

parseReal :: TermS -> Maybe Double
parseReal t                = do a <- parseConst t; parse real a

parseReals :: TermS -> TermS -> Maybe (Double,Double)
parseReals t u             = do a <- parseReal t; b <- parseReal u; Just (a,b)

parseDouble :: TermS -> Maybe Double
parseDouble t              = do a <- parseConst t; parse double a

parseNats :: TermS -> Maybe [Int]
parseNats                  = parseList parseNat

parseIntQuad :: TermS -> Maybe (Int, Int, Int, Int)
parseIntQuad t      = do F "()" [i,j,b,h] <- Just t; i <- parseInt i
                         j <- parseInt j; b <- parseInt b; h <- parseInt h
                         Just (i,j,b,h)

parseRealReal :: TermS -> Maybe (Double, Double)
parseRealReal t = do F "()" [r,s] <- Just t; r <- parseReal r; s <- parseReal s
                     Just (r,s)

parseRealPair :: TermS -> Maybe ((Double, Double), Double)
parseRealPair t     = do F "()" [p,r] <- Just t; p <- parseRealReal p
                         r <- parseReal r; Just (p,r)

parseColor :: TermS -> Maybe Color
parseColor      = parse color . root

parseRenaming :: [TermS] -> Maybe (String -> String)
parseRenaming r = do r <- mapM f r; Just $ fold2 upd id (map fst r) $ map snd r
                  where f t = do F "=" [V x,V y] <- Just t; Just (x,y)

-- parseLinEqs recognizes conjunctions of linear equations. 

parseLinEqs :: TermS -> Maybe [LinEq]
parseLinEqs (F "&" ts) = mapM parseLinEq ts                                    
parseLinEqs t          = do eq <- parseLinEq t; Just [eq]       

parseLinEq :: TermS -> Maybe LinEq
parseLinEq t = do F "=" [t,u] <- Just t; ps <- parseProds t; b <- parseReal u
                  Just (ps,b)

parseLin :: TermS -> Maybe LinEq
parseLin (F "lin" [F "+" [t,u]]) | just b = do ps <- parseProds t
                                               Just (ps,get b)
                                            where b = parseReal u
parseLin (F "lin" [F "-" [t,u]]) | just b = do ps <- parseProds t
                                               Just (ps,-get b)
                                            where b = parseReal u
parseLin t = do F "lin" [t] <- Just t; ps <- parseProds t; Just (ps,0)

parseProds :: TermS -> Maybe [(Double, String)]
parseProds (F "+" [ts,t]) = do ps <- parseProds ts; p <- parseProd t
                               Just $ ps++[p]
parseProds (F "-" [ts,t]) = do ps <- parseProds ts; (a,x) <- parseProd t
                               Just $ ps++[(-a,x)]
parseProds t              = do p <- parseProd t; Just [p]

parseProd :: TermS -> Maybe (Double, String)
parseProd (F "*" [t,V x]) = do a <- parseReal t; guard $ a /= 0; Just (a,x)
parseProd (F "-" [V x])   = Just (-1,x)
parseProd t               = do V x <- Just t; Just (1,x)

parseRel :: [TermS]
            -> TermS -> Maybe [(TermS, TermS)]
parseRel sts t = do F "rel" [t] <- Just t
                    rels <- parseList f t; Just $ concat rels
                 where f (F "()" [t,F "[]" ts]) | (t:ts) `subset` sts  
                           = Just $ map (\u -> (t,u)) ts
                       f t = do F "()" [t,u] <- Just t
                                guard $ t `elem` sts && u `elem` sts
                                Just [(t,u)]

-- * Signatures, Horn and Co-Horn clauses
iniSymbols :: ([String], [String], [String], [String], [a], [b])
iniSymbols = (iniPreds,[],iniConstructs,iniDefuncts,[],[])

iniConstructs :: [String]
iniConstructs = words "() [] : 0 suc lin"

iniDefuncts = words "_ $ . ; + ++ - * ** / !! atoms auto bag branch color" ++
              words "concat curry dnf filter flip foldl1 foldl foldr1 foldr" ++
              words "height id index indices insert `join` labels length" ++
              words "list lsec mapG map `meet` min minimize `mod` obdd" ++
              words "prodE prodL product procs range reverse rsec set" ++
              words "shuffle states sum tup uncurry upd zip zipWith"

iniPreds = words "_ $ . () [] : ++ <= >= < > >> true false not /\\ \\/" ++
           words "`then` EX AX # <> nxt all any allany disjoint" ++
           words "filterL filter flip foldl1 foldl foldr1 foldr `in`" ++
           words "`NOTin` Int `IN` `NOTIN` INV Nat List lsec mapG map null" ++
           words "NOTnull prodL Real `shares` `NOTshares` single `subset`" ++
           words "`NOTsubset` rsec Value zipWith"

data Sig = Sig {
              isPred,isCopred,isConstruct,isDefunct,isFovar,isHovar,blocked
                                  :: String -> Bool,
              hovarRel            :: BoolFun String,
              simpls,transitions  :: [(TermS,[TermS],TermS)],
              states,atoms,labels :: [TermS],     -- components
              trans,value         :: [[Int]],     -- of a
              transL,valueL       :: [[[Int]]],   -- Kripke model
              notSafe             :: Bool
              }

out,parents :: Sig -> [[Int]]
out sig     = invertRel (sig&atoms) (sig&states) (sig&value)
parents sig = invertRel (sig&states) (sig&states) (sig&trans)

outL,parentsL :: Sig -> [[[Int]]] 
outL sig     = invertRelL (sig&labels) (sig&atoms) (sig&states) (sig&valueL)
parentsL sig = invertRelL (sig&labels) (sig&states) (sig&states) (sig&transL)

predSig :: [String] -> Sig
predSig preds = Sig { isPred = (`elem` preds)
                    , isCopred = const False
                    , isConstruct = const False
                    , isDefunct = const False
                    , isFovar = const False
                    , isHovar = const False
                    , blocked = const False
                    , hovarRel = \_ _ -> False
                    , simpls = []
                    , transitions = []
                    , states = []
                    , atoms = []
                    , labels = []
                    , trans = []
                    , transL = []
                    , value = [], valueL = [], notSafe = False
                    }

emptySig :: Sig
emptySig = predSig []

chgRedPos :: Sig -> [Int] -> Sig
chgRedPos sig pos = Sig {  isPred = (sig&isPred), isCopred = (sig&isCopred),
                           isConstruct = (sig&isConstruct),
                           isDefunct = (sig&isDefunct), isFovar = (sig&isFovar),
                           isHovar = (sig&isHovar), blocked = (sig&blocked),
                           hovarRel = (sig&hovarRel), simpls = (sig&simpls),
                           transitions = (sig&transitions),states = (sig&states),
                           atoms = (sig&atoms), labels = (sig&labels),
                           trans = (sig&trans), transL = (sig&transL),
                           value = (sig&value), valueL = (sig&valueL),
                           notSafe = (sig&notSafe)
                        }


applySignatureMap sig sig' f t@(V x) | f x /= x         = Just $ V $ f x
                                     | (sig'&isFovar) x = Just t
                                     | True             = Nothing
applySignatureMap sig sig' f (F x ts) =
        do ts <- mapM (applySignatureMap sig sig' f) ts
           if f x /= x then Just $ F (f x) ts
                       else do guard $ logical x ||
                                       functional sig x && functional sig' x ||
                                       relational sig x && relational sig' x ||
                                       (sig&isHovar) x && (sig'&isHovar) x
                               Just $ F x ts

defuncts sig (F x ts) = if (sig&isDefunct) x then x:fs else fs
                        where fs = concatMap (defuncts sig) ts
defuncts _ _          = []

isSum :: TermS -> Bool
isSum (F "<+>" _)  = True
isSum _            = False

projection :: String -> Bool
projection          = just . parse (strNat "get")

logical :: String -> Bool
logical x         = propositional x || x `elem` words "True False Not" ||
                    isQuant x || isFixF x

propositional x   = implicational x || x == "|" || x == "&"

implicational :: String -> Bool
implicational x   = x `elem` words "==> <==> ===> <==="

lambda :: String -> Bool
lambda x            = x `elem` words "fun rel"

binder :: String -> Bool
binder              = isQuant ||| isFix

isQuant :: String -> Bool
isQuant x           = leader x "All" || leader x "Any"

isFix :: String -> Bool
isFix               = isFixT ||| isFixF

isFixT :: String -> Bool
isFixT x            = leader x "mu" || leader x "nu"

isFixF :: String -> Bool
isFixF x            = leader x "MU" || leader x "NU"

mkBinder :: String -> [String] -> TermS -> TermS
mkBinder op xs t  = F (op ++ ' ':unwords (mkSet xs)) [t]

isFormula :: Sig -> TermS -> Bool
isFormula sig t@(F x _) = logical x || isAtom sig t
isFormula _ _           = False

isTerm :: Sig -> TermS -> Bool
isTerm sig = not . isFormula sig

isAtom :: Sig -> TermS -> Bool
isAtom sig = relational sig . getOp

isOnlyAtom sig = isAtom sig &&& not . functional sig . getOp

getOp :: TermS -> String
getOp (F "$" [t,_]) = getOp t
getOp t             = root t

getOpArgs :: TermS -> (String, [TermS])
getOpArgs t = (getOp t,getArgs t)

getArgs :: TermS -> [TermS]
getArgs (F "$" [_,t]) = case t of F "()" ts -> ts; _ -> [t]
getArgs (F _ ts)      = ts
getArgs _               = []

updArgs :: TermS -> [TermS] -> TermS
updArgs (F "$" [t,_]) us = applyL t us
updArgs (F x _) us       = F x us
updArgs t _              = t

-- unCurry (f(t1)...(tn)) returns (f,[t1,...,tn]).
unCurry :: TermS -> (String, [[TermS]])
unCurry (F "$" [t,u]) = (x,tss++[ts]) where (x,tss) = unCurry t
                                            ts = case u of F "()" us -> us
                                                           _ -> [u]
unCurry (F x ts)      = (x,[ts])
unCurry t             = (root t,[[]])

-- used by turnIntoUndef and Esolve > simplifyT,flatCands,preStretch,
-- stretchConc,stretchPrem

getOpSyms :: TermS -> [String]
getOpSyms (F "$" [t,_]) = foldT f t where f x xss = x:concat xss
getOpSyms _             = []

getHead :: TermS -> TermS
getHead (F "<===" [t,_]) = t
getHead (F "===>" [t,_]) = t
getHead t                = t

getBody :: TermS -> TermS
getBody (F "<===" [_,t]) = t
getBody (F "===>" [_,t]) = t
getBody t                = t

quantConst :: String -> TermS -> Bool
quantConst x (F y [])                       = x == y
quantConst x (F ('A':'n':'y':_) [t]) = quantConst x t
quantConst x (F ('A':'l':'l':_) [t]) = quantConst x t
quantConst _ _                       = False

isTup :: TermS -> Bool
isTup (F "()" _) = True
isTup _          = False

isList :: TermS -> Bool
isList (F "[]" _) = True
isList _          = False

isTrue (F "True" [])  = True
isTrue _              = False

isFalse (F "False" []) = True
isFalse _              = False

isImpl :: TermS -> Bool
isImpl (F "==>" _) = True
isImpl _             = False

isQDisjunct :: TermS -> Bool
isQDisjunct (F ('A':'l':'l':_) [t]) = isDisjunct t
isQDisjunct t                              = isDisjunct t

isDisjunct :: TermS -> Bool
isDisjunct (F "|" _) = True
isDisjunct _               = False

isQConjunct :: TermS -> Bool
isQConjunct (F ('A':'n':'y':_) [t]) = isConjunct t
isQConjunct t                              = isConjunct t

isConjunct :: TermS -> Bool
isConjunct (F "&" _) = True
isConjunct _         = False

isProp :: Sig -> TermS -> Bool
isProp sig = isAtom sig ||| isDisjunct ||| isConjunct

isSimpl :: TermS -> Bool
isSimpl (F "==>" [_,F "==" _])   = True
isSimpl (F "==>" [_,F "<==>" _]) = True
isSimpl (F "==" _)               = True
isSimpl (F "<==>" _)             = True
isSimpl _                        = False

isTrans :: TermS -> Bool
isTrans (F "==>" [_,F "->" _]) = True
isTrans (F "->" _)             = True
isTrans _                      = False

isHorn :: Sig -> TermS -> Bool
isHorn sig (F "<===" [t,_]) = isHorn sig t
isHorn sig (F "=" [t,_])    = isDefunct sig $ getOp t
isHorn sig t                      = isPred sig $ getOp t
--isHorn _ _                         = False

isCoHorn :: Sig -> TermS -> Bool
isCoHorn sig (F "===>" [t,_]) = isCopred sig $ getOp t
isCoHorn _ _                   = False

isAxiom :: Sig -> TermS -> Bool
isAxiom sig = isTrans ||| isHorn sig ||| isCoHorn sig

isHornT :: TermS -> Bool
isHornT (F "<===" [t,_]) = noQuantsOrConsts t
isHornT (F "===>" _)     = False
isHornT t                = noQuantsOrConsts t

isCoHornT :: TermS -> Bool
isCoHornT (F "===>" [t,_]) = noQuantsOrConsts t
isCoHornT _                = False

noQuantsOrConsts :: TermS -> Bool
noQuantsOrConsts (F "True" _)          = False
noQuantsOrConsts (F "False" _)         = False
noQuantsOrConsts (F ('A':'n':'y':_) _) = False
noQuantsOrConsts (F ('A':'l':'l':_) _) = False
noQuantsOrConsts (F _ ts)              = all noQuantsOrConsts ts
noQuantsOrConsts _                     = True

isTheorem :: TermS -> Bool
isTheorem = isHornT ||| isCoHornT ||| noQuantsOrConsts

unconditional :: TermS -> Bool
unconditional (F "<===" _) = False
unconditional (F "===>" _) = False
unconditional _            = True

isTaut :: TermS -> Bool
isTaut (F "<===" [F "False" _,_]) = True
isTaut (F "===>" [F "True"  _,_]) = True
isTaut _                          = False

isDisCon :: TermS -> Bool
isDisCon (F "<===" [F "|" _,_]) = True
isDisCon (F "<===" [F "&" _,_]) = True
isDisCon (F "===>" [F "|" _,_]) = True
isDisCon (F "===>" [F "&" _,_]) = True
isDisCon (F "|" _)              = True
isDisCon (F "&" _)              = True
isDisCon _                      = False

noOfComps (F "<===" [t,_]) = outdegree t
noOfComps (F "===>" [t,_]) = outdegree t
noOfComps t                = outdegree t

-- used by Ecom > applyTheorem

copyRedex :: TermS -> TermS
copyRedex (F "==>" [guard,u]) = mkImpl guard $ copyRedex u
copyRedex (F "===>" [t,u])    = mkCoHorn t $ mkConjunct [t,u]
copyRedex (F "<===" [t,u])    = mkHorn t $ mkDisjunct [t,u]
copyRedex t                        = mkHorn t t

-- used by Ecom > applyTheorem

mergeWithGuard (F "==>" [t,F "<===" [u,v]]) = mkHorn u $ mkConjunct [t,v]
mergeWithGuard (F "==>" [t,F "===>" [u,v]]) = mkCoHorn u $ mkImpl t v
mergeWithGuard t                            = t

-- used by Ecom > applyInd

makeLambda :: Sig -> TermS -> [Int] -> Maybe TermS
makeLambda sig cl p = 
  case (cl,p) of (F "==>" [F "&" cs,F x [l,r]],[0,i,1])
                       -> do guard $ i < length cs && rel x && xs `disjoint` zs
                             Just $ mkImpl (mkConjunct ds) (F x [l,app r arg])
                      where arg = getSubterm cl [0,i,0]
                            ds = context i cs
                            zs = joinMap (frees sig) $ arg:ds
                 (F "==>" [_, F x [l,r]],[0,1])
                       -> do guard $ rel x && xs `disjoint` frees sig arg
                             Just $ F x [l,app r arg]
                      where arg = getSubterm cl [0,0]
                 (F "==>" [c,F x [l,r]],[1,0])
                       -> do guard $ rel x; Just $ mkImpl c $ at x l pars r
                      where (_, pars) = getOpArgs l 
                 (F x [l,r],[0])
                       -> do guard $ rel x; Just $ at x l pars r
                      where (_, pars) = getOpArgs l 
                 _ -> Nothing
      where rel x = x `elem` words "= == ->"
            par = getSubterm cl p
            xs = frees sig par             
            app r = apply $ F "fun" [par,r]
            removePars (F "$" [t,_]) = t
            removePars (F op _)      = F op []
            removePars t             = t
            at x l pars r = F x [removePars l,F "fun" [mkTup pars,r]]

axiomsFor :: [String] -> [TermS] -> [TermS]
axiomsFor xs = filter f where f (F "==>" [_,cl])  = f cl
                              f (F "===>" [at,_]) = f at
                              f (F "<===" [at,_]) = f at
                              f (F "<==>" [at,_]) = f at
                              f (F "==" [t,_])    = any (`isin` t) xs
                              f (F "=" [t,_])     = any (`isin` t) xs
                              f at                = any (`isin` at) xs

noSimplsFor :: [String] -> [TermS] -> [TermS]
noSimplsFor xs = filter f where f (F "==>" [_,cl])  = f cl
                                f (F "===>" [at,_]) = f at
                                f (F "<===" [at,_]) = f at
                                f (F "<==>" _)      = False
                                f (F "==" _)        = False
                                f (F "=" [t,_])     = any (`isin` t) xs
                                f at                = any (`isin` at) xs

-- filterClauses sig redex filters the axioms/theorems that may be applicable to
-- redex.

filterClauses sig redex = filter f where
                         f ax = (isAxiom sig ||| isTheorem) ax &&
                                any (flip any (anchors ax) . g) (anchors redex)
                         g x = (x ==) ||| h x ||| flip h x
                         h x y = (sig&isFovar) x || (sig&hovarRel) x y
                         anchors (F "==>" [_,cl]) = anchors cl
                         anchors (F x [t,_]) | x `elem` words "===> <=== = ->"
                                            = anchors t
                         anchors (F "^" ts) = concatMap anchors ts
                         anchors t          = [getOp t]

-- used by Esolve > applyLoop/Random and Ecom > narrowPar,rewritePar

-- turnIntoUndef recognizes a non-rewritable/narrowable first order term/atom u. 

turnIntoUndef :: Sig -> TermS -> [Int] -> TermS -> Maybe TermS
turnIntoUndef sig t p redex =
   do guard $ isF redex && and (map (all $ isNormal sig) tss)
      if x `notElem` iniPreds && (sig&isPred) x then Just mkFalse
      else if (sig&isCopred) x then Just mkTrue
           else do guard $ notnull p && root (getSubterm t $ init p) == "->" ||
                           x `notElem` iniDefuncts && (sig&isDefunct) x
                   Just unit
   where (x,tss) = unCurry redex

-- used by Esolve > applyLoop

-- * Generators
-- ** Term generation

leaf :: a -> Term a
leaf a = F a []

mkZero, mkOne, unit :: TermS
mkZero = leaf "0"
mkOne  = leaf "1"
unit   = leaf "()"

mkList = F "[]"

jList :: [TermS] -> Maybe TermS
jList = Just . mkList

mkNil = mkList []

mkList' [a] = a
mkList' as  = mkList as

leaves :: [String] -> TermS
leaves = mkList' . map leaf

mkConst :: Show a => a -> TermS
mkConst = leaf . show

mkBool :: TermS -> TermS
mkBool t =  F "bool" [t]

jConst :: Show a => a -> Maybe TermS
jConst  = Just . mkConst

mkConsts :: Show a => [a] -> TermS
mkConsts = mkList . map mkConst

jConsts :: Show a => [a] -> Maybe TermS
jConsts = Just . mkConsts

mkSuc t = F "suc" [t]

mkPair t u = F "()" [t,u]

mkTup [t] = t
mkTup ts  = F "()" ts

mkConstPair :: (Show a, Show b) => (a, b) -> TermS
mkConstPair (a,b) = mkPair (mkConst a) $ mkConst b

mkStrPair :: (String,String) -> TermS
mkStrPair (a,b) = mkTup $ map leaf [a,b]

mkStrLPair :: ([String],[String]) -> TermS
mkStrLPair (as,bs) = mkTup $ map leaves [as,bs]

mkGets :: [a] -> TermS -> [TermS]
mkGets xs t = case xs of [_] -> [t]; _ -> map f $ indices_ xs
              where f i = F ("get"++show i) [t]

mkLin :: LinEq -> TermS
mkLin (ps,b) = F "lin" [if b < 0 then F "-" [mkProds ps,mkConst $ -b]
                                  else if b == 0 then mkProds ps
                                       else F "+" [mkProds ps,mkConst b]]

mkLinEqs :: [LinEq] -> TermS
mkLinEqs eqs = F "&" $ map mkLinEq eqs
                where mkLinEq (ps,b) = F "=" [mkProds ps,mkConst b]

mkProds :: [(Double,String)] -> TermS
mkProds [p]            = mkProd p
mkProds ps | a < 0     = F "-" [mkProds qs,mkProd (-a,x)]
           | otherwise = F "+" [mkProds qs,mkProd p]
                      where (qs,p@(a,x)) = (init ps,last ps)

mkProd :: (Double,String) -> TermS
mkProd (a,x) | a == 1    = V x
             | a == -1   = F "-" [V x]
             | otherwise = F "*" [mkConst a,V x]

mkRel :: Ord a => String -> [a] -> TermS
mkRel "="   [a,b] = mkConst $ a==b
mkRel "=/=" [a,b] = mkConst $ a/=b
mkRel "<="  [a,b] = mkConst $ a<=b
mkRel ">="  [a,b] = mkConst $ a>=b
mkRel "<"   [a,b] = mkConst $ a<b
mkRel ">"   [a,b] = mkConst $ a>b

-- mkRelConsts rel returns the representation of a binary relation rel as a 
-- list of type [TermS].

mkRelConsts :: Pairs String -> [TermS]
mkRelConsts = map g where g (a,[b]) = mkTup [leaf a,leaf b]
                          g (a,bs)  = mkPair (leaf a) $ leaves bs

-- used by Ecom > showRelation

mkRelConstsI :: [String] -> [String] -> [[Int]] -> [TermS]
mkRelConstsI as bs = zipWith f [0..]
                     where f i [k] = mkPair (g i) $ leaf $ bs!!k
                           f i ks  = mkPair (g i) $ leaves $ map (bs!!) ks
                           g i = leaf $ as!!i

-- mkRel2Consts f dom returns the representation of a ternary relation as a 
-- list of type [TermS]. 

mkRel2Consts :: [(String,String,[String])] -> [TermS]
mkRel2Consts = map g where g (a,b,[c]) = mkTup $ map leaf [a,b,c]
                           g (a,b,cs)  = mkTup [leaf a,leaf b,leaves cs]

-- used by Ecom > showRelation

mkRel2ConstsI :: [String] -> [String] -> [String] -> [[[Int]]] -> [TermS]
mkRel2ConstsI as bs cs = concat . zipWith f [0..]
           where f i = zipWith g [0..]
                       where g j [k] = mkTup [h1 i,h2 j,leaf $ cs!!k]
                             g j ks  = mkTup [h1 i,h2 j,leaves $ map (cs!!) ks]
                             h1 i = leaf $ as!!i
                             h2 i = leaf $ bs!!i

-- used by Ecom > showRelation

evenNodes :: TermS -> [String]
evenNodes (F x ts) = x:concatMap oddNodes ts
evenNodes (V x)    = if isPos x then [] else [x]
evenNodes _        = []

oddNodes :: TermS -> [String]
oddNodes (F _ ts) = concatMap evenNodes ts
oddNodes _        = []

mkSum :: [TermS] -> TermS
mkSum []  = unit
mkSum [t] = t
mkSum ts  = case mkTerms (F "<+>" ts) of [] -> unit; [t] -> t
                                         ts  -> F "<+>" ts

mkTerms :: TermS -> [TermS]
mkTerms (F "<+>" ts) = joinTermMap mkTerms $ removeUndef ts
mkTerms t            = removeUndef [t]

removeUndef :: [TermS] -> [TermS]
removeUndef = filter $ not . quantConst "()"

mkBag :: [TermS] -> TermS
mkBag []  = mkNil
mkBag [t] = t
mkBag ts  = case mkElems (F "^" ts) of [t] -> t; ts  -> F "^" ts

mkElems :: TermS -> [TermS]
mkElems (F "^" ts) = concatMap mkElems ts
mkElems t          = [t]

mkApplys :: (String, [[TermS]]) -> TermS
mkApplys (x,[])   = V x
mkApplys (x,[ts]) = F x ts
mkApplys (x,tss)  = applyL (mkApplys (x,init tss)) $ last tss

-- ** Generators of formulas

mkComplSymbol :: String -> String
mkComplSymbol "="                 = "=/="
mkComplSymbol "->"                = "-/->"
mkComplSymbol "-/->"              = "->"
mkComplSymbol "=/="               = "="
mkComplSymbol "<="                = ">"
mkComplSymbol ">="                = "<"
mkComplSymbol "<"                 = ">="
mkComplSymbol ">"                 = "<="
mkComplSymbol ('`':'n':'o':'t':x) = '`':x
mkComplSymbol ('`':'N':'O':'T':x) = '`':x
mkComplSymbol ('`':x@(c:_))       = if isLower c then "`NOT"++x else "`not"++x
mkComplSymbol ('n':'o':'t':x)     = x
mkComplSymbol ('N':'O':'T':x)     = x
mkComplSymbol x@(c:_)             = if isLower c then "NOT"++x else "not"++x
mkComplSymbol x                   = x

complOccurs :: [TermS] -> Bool
complOccurs ts = forsomeThereis (eqTerm . F "Not" . single) ts ts

mkTrue, mkFalse :: TermS
mkTrue  = F "True" []
mkFalse = F "False" []

mkNot :: Sig -> TermS -> TermS
mkNot _ t | quantConst "True" t   = mkFalse
mkNot _ t | quantConst "False" t  = mkTrue
mkNot _ (F "Not" [t])                   = t
mkNot sig (F "==>" [t,u])           = mkConjunct [t,mkNot sig u]
mkNot sig (F "|" ts)                   = mkConjunct $ map (mkNot sig) ts
mkNot sig (F "&" ts)                   = mkDisjunct $ map (mkNot sig) ts
mkNot sig (F ('A':'n':'y':x) [t]) = mkAll (words x) $ mkNot sig t
mkNot sig (F ('A':'l':'l':x) [t]) = mkAny (words x) $ mkNot sig t
-- mkNot sig (F "$" [t,u])           = F "$" [mkNot sig t,u]
mkNot sig (F x ts) | declaredRel sig z && not (isHovar sig x)
                                   = F z ts where z = mkComplSymbol x
mkNot _ t                                = F "Not" [t]

mkImpl :: TermS -> TermS -> TermS
mkImpl t u | quantConst "True" t  = u
           | quantConst "False" t = mkTrue
           | quantConst "True" u  = mkTrue
           | eqTerm t u           = mkTrue
           | otherwise            = F "==>" [t, u]

premise :: TermS -> TermS
premise (F ('A':'l':'l':_) [t]) = premise t
premise (F "==>" [t,_])          = t
premise t                          = t

conclusion :: TermS -> TermS
conclusion (F ('A':'l':'l':_) [t]) = conclusion t
conclusion (F "==>" [_,t])             = t
conclusion t                             = t

mkEq, mkNeq, mkGr, mkTrans :: TermS -> TermS -> TermS
mkEq t u    = F "=" [t,u]
mkNeq t u   = F "=/=" [t,u] 
mkGr t u    = F ">" [t,u]
mkTrans t u = F "->" [t,u]

mkEqsConjunct :: [String] -> [TermS] -> TermS
mkEqsConjunct [x] [t] = mkEq (V x) $ add1ToPoss t
mkEqsConjunct xs ts   = f $ F "&" $ zipWith (mkEq . V) xs ts
                   where f (F x ts)        = F x $ map f ts
                         f (V x) | isPos x = mkPos $ i:1:s where i:s = getPos x
                         f t               = t

-- used by connectEqs

separateTerms :: TermS -> [Int] -> TermS
separateTerms t is = if isConjunct t then moreTree $ foldl f t is else t
                      where f u i = replace0 u p $ expandOne 0 t p
                                   where p = [i,1]

-- used by eqsToGraph(s)

mkAny,mkAll,addAnys,addAlls :: [String] -> TermS -> TermS

mkAny xs (F ('A':'n':'y':x) [t]) = mkAny (xs `join` words x) t
mkAny xs (F "==>" [t,u])           = F "==>" [mkAll xs t,mkAny xs u]
mkAny xs (F "|" ts)                   = F "|" $ map (mkAny xs) ts
mkAny [] t                           = t
mkAny xs t                           = mkBinder "Any" xs t

mkAll xs (F ('A':'l':'l':x) [t]) = mkAll (xs `join` words x) t
mkAll xs (F "&" ts)                   = F "&" $ map (mkAll xs) ts
mkAll [] t                           = t
mkAll xs t                           = mkBinder "All" xs t

addAnys xs t = mkAny (filter (`isin` t) xs) t
addAlls xs t = mkAll (filter (`isin` t) xs) t

moveQdown :: Sig -> TermS -> TermS
moveQdown sig = f where
 f (F ('A':'n':'y':x) [F "|" ts]) = F "|" $ map (mkAny (words x) . f) ts
 f (F ('A':'l':'l':x) [F "&" ts]) = F "&" $ map (mkAll (words x) . f) ts
 f (F ('A':'n':'y':x) [F "==>" [t,u]])
                                  = F "==>" [mkAll xs $ f t,mkAny xs $ f u]
                                    where xs = words x
 f (F ('A':'n':'y':x) [F "&" ts]) | notnull inds
                                  = F "&"  $ updList ts i $ mkAny xs $ ts!!i
                                    where xs = words x
                                          inds = disjointVars sig xs ts
                                          i:_ = inds
 f (F ('A':'l':'l':x) [F "|" ts]) | notnull inds
                                  = F "|"  $ updList ts i $ mkAll xs $ ts!!i
                                    where xs = words x
                                          inds = disjointVars sig xs ts
                                          i:_ = inds
 f (F ('A':'l':'l':x) [F "==>" ts@[t,u]]) | notnull inds
                                  = F "==>" $ if i == 0 then [mkAny xs $ f t,u]
                                                        else [t,mkAll xs $ f u]
                                    where xs = words x
                                          inds = disjointVars sig xs ts
                                          i:_ = inds
 f t = t

disjointVars :: Sig -> [String] -> [TermS] -> [Int]
disjointVars sig xs ts = [i | i <- indices_ ts, xs `shares` frees sig (ts!!i),
                              xs `disjoint` joinMap (frees sig) (context i ts)]


mkDisjunct,mkConjunct :: [TermS] -> TermS

mkDisjunct []  = mkFalse
mkDisjunct [t] = t
mkDisjunct ts  = case mkSummands (F "|" ts) of [] -> mkFalse; [t] -> t
                                               ts  -> F "|" ts

mkConjunct []  = mkTrue
mkConjunct [t] = t
mkConjunct ts  = case mkFactors (F "&" ts) of [] -> mkTrue; [t] -> t
                                              ts  -> F "&" ts

mkSummands,mkFactors :: TermS -> [TermS]

mkSummands (F "|" ts) = if any isTrue ts || complOccurs ts then [mkTrue]
                        else joinTermMap mkSummands $ removeFalse ts
mkSummands t          = removeFalse [t]

mkFactors (F "&" ts) = if any isFalse ts || complOccurs ts then [mkFalse] 
                       else joinTermMap mkFactors $ removeTrue ts
mkFactors t               = removeTrue [t]

removeFalse,removeTrue :: [TermS] -> [TermS]
removeFalse = filter $ not . quantConst "False"
removeTrue  = filter $ not . quantConst "True"

joinTrees :: String -> [TermS] -> TermS
joinTrees _ [t]       = t
joinTrees treeMode ts = case treeMode of "summand" -> F "|" $ addNatsToPoss ts
                                         "factor" -> F "&" $ addNatsToPoss ts
                                         _ -> F "<+>" $ addNatsToPoss ts

insertFormula "&" factor (F "|" ts)  = mkDisjunct $ map f ts
                                       where f t = mkConjunct [factor,t]
insertFormula "|" summand (F "&" ts) = mkConjunct $ map f ts
                                       where f t = mkDisjunct [summand,t]
insertFormula "==>" prem (F "&" ts)  = mkConjunct $ map f ts
                                       where f t = mkImpl prem t
insertFormula "==>" conc (F "|" ts)  = mkConjunct $ map f ts
                                       where f t = mkImpl t conc

-- used by Ecom > distribute

mkHorn :: TermS -> TermS -> TermS
mkHorn conc prem                 = F "<===" [conc,prem]

mkHornG :: TermS -> TermS -> TermS -> TermS
mkHornG guard conc prem   = F "==>" [guard,F "<===" [conc,prem]]

mkCoHorn :: TermS -> TermS -> TermS
mkCoHorn prem conc        = F "===>" [prem,conc]

mkCoHornG :: TermS
             -> TermS -> TermS -> TermS
mkCoHornG guard prem conc = F "==>" [guard,F "===>" [prem,conc]]

invertClause :: TermS -> TermS
invertClause (F "<===" [F x [t,u],v]) | permutative x = mkHorn (F x [u,t]) v
invertClause (F "<===" [t,u])                         = mkCoHorn u t
invertClause (F "===>" [t,u])                         = mkHorn u t
invertClause (F x [t,u]) | permutative x              = F x [u,t]
invertClause t                                        = t

-- mkIndHyps t desc constructs the induction hypothesis from a conjecture t and
-- a descent condition.

mkIndHyps :: TermS -> TermS -> [TermS]
mkIndHyps t desc = case t of F "==>" [u,v] -> [mkHorn v $ F "&" [u,desc],
                                               mkCoHorn u $ F "==>" [desc,v]]
                             _             -> [mkHorn t desc]

-- used by Ecom > createIndHyp

congAxs :: String -> [String] -> [TermS]
congAxs equiv pars = map f pars where
                     t ~~ u  = F equiv [t,u]
                     f "refl" = x ~~ x
                     f "symm" = mkHorn (x ~~ y) $ y ~~ x
                     f "tran" = mkHorn (x ~~ z) $ F "&" [x ~~ y,y ~~ z]
                     f par    = mkHorn (t 'x' ~~ t 'y') $ F "&" $ map h [1..n]
                                where c = init par
                                      n = get $ parse digit [last par]
                                      t x = F c $ map (g x) [1..n]
                     [x,y,z] = map V $ words "x y z"
                     g x i   = V $ x:show i
                     h i     = g 'x' i ~~ g 'y' i

-- used by Ecom > addCongAxioms

-- derivedFun sig f xs axs returns Just (loop,inits[xs/ys],ax) if 
-- ax is f(ys)=loop(take i ys++inits) and ax is the only axiom for f. 

derivedFun :: t
              -> String
              -> [TermS]
              -> Int
              -> Int
              -> [TermS]
              -> Maybe (String, [TermS], TermS)
derivedFun _ f xs i lg axs =
     case axiomsFor [f] axs of
          [ax@(F "=" [F _ zs,F loop inits])] | lg == length zs && all isV zs && 
                                               distinct zs &&
                                               drop (lg-i) zs == take i inits
            -> Just (loop,map (>>>(forL xs $ map root zs)) $ drop i inits,ax)
          _ -> Nothing

-- used by Ecom > createInvariant

-- mkInvs True/False constructs the conditions on a Hoare/subgoal invariant INV.

mkInvs :: Bool
          -> String
          -> [TermS]
          -> [TermS]
          -> [TermS]
          -> [TermS]
          -> TermS
          -> TermS
          -> TermS
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

-- used by Ecom > createInvariant

trips :: [String] -> [TermS] -> [(TermS, [TermS], TermS)]
trips xs = foldr f []
           where f (F x [t,u]) trips | x `elem` xs  = (t,[],u):trips
                 f (F "==>" [c,F x [t,u]]) trips | x `elem` xs
                                                    = (t,mkFactors c,u):trips
                 f _ trips = trips


-- transClosure ts applies rules to ts that employ the transitivity of the
-- relation between the elements of ts. 
transClosure :: [TermS] -> Maybe TermS
transClosure [t@(F _ [_,_])] = Just t
transClosure (t:ts)          = do u <- transClosure ts
                                  (F x [l,r],F y [l',r']) <- Just (t,u)
                                  guard $ isOrd x && x == y && eqTerm r l'
                                  Just $ F x [l,r']
transClosure _               = Nothing

-- splitEq True t u decomposes t=u. splitEq False t u decomposes t=/=u.

splitEq :: Sig -> Bool -> TermS -> TermS -> TermS
splitEq sig b = f where
       f t@(F x ts) u@(F y us) | x == y && length ts == length us
                                  = mk1 $ zipWith f (renameVars sig x ts us) us
       f t@(V x) u@(V y) | x == y = mk3
       f t u                      = mk2 t u
       (mk1,mk2,mk3) = if b then (mkConjunct,mkEq,mkTrue)
                            else (mkDisjunct,mkNeq,mkFalse)

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
polarity pol (F _ ts) (n:p)         = polarity pol (ts!!n) p
polarity pol _ _                           = pol

correctPolarity :: Term [Char] -> TermS -> [Int] -> Bool
correctPolarity th t p = isHornT th && b || isCoHornT th && not b
                         where b = polarity True t p

monotone :: Sig -> [String] -> TermS -> Bool
monotone _ xs = f True
   where f pol (F "`then`" [t,u]) = f (not pol) t && f pol u
         f pol (F "not" [t])      = f (not pol) t
         f pol (F x ts)           = if x `elem` xs then pol else all (f pol) ts
         f _ _                    = True

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
polTree pol p (F _ ts)         = if pol then p:concat pss else concat pss
                                 where pss = zipWithSucs (polTree pol) p ts
polTree pol p _                      = [p | pol]

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
-- nodes of t in accordance with the color function hue 0 col n where n is the
-- maximum of positions of t and col is the start color.
levelTerm,preordTerm,heapTerm,hillTerm ::
                         Color -> (Color -> Int -> b) -> Term a -> (Term b,Int)

levelTerm col lab t = un where un@(_,n) = f 0 t
                               f i (F _ ts@(_:_)) = (F (label i) us,maximum ks)
                                        where (us,ks) = unzip $ map (f $ i+1) ts
                               f i _= (F (label i) [],i+1)
                               label i = lab (hue 0 col n i) i

preordTerm col lab t = un where un@(_,n) = f 0 t
                                f i (F _ ts) = (F (label i) us,n)
                                               where (us,n) = g (i+1) ts
                                f i _        = (F (label i) [],i+1)
                                g i (t:ts) = (u:us,n) where (u,m) = f i t
                                                            (us,n) = g m ts
                                g i _      = ([],i)
                                label i = lab (hue 0 col n i) i

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
           label i = lab (hue 0 col n i) i
              
hillTerm col lab t = un where un@(_,n) = f 0 t
                              f i (F _ ts) = (F (label i) us,maximum $ n:ns)
                                  where (us,ns) = unzip $ zipWith f ks ts
                                        lg = length ts; k = lg `div` 2
                                        n = if even lg then k else k+1
                                        is = [0..k-1]; js = [k-1,k-2..0]
                                        ks = is++(if even lg then js else k:js)
                              f i _ = (F (label i) [],i)
                              label i = lab (hue 0 col n i) i

-- cutTree max t ps col qs hides each subtree of t whose root position is in qs 
-- or greater than max (wrt the heap order). Each subtrees of t whose root 
-- position is in ps is colored with col.
cutTree :: Int -> TermS -> [[Int]] -> String -> [[Int]] -> TermS
cutTree max t ps col qs = mapTP c [] $
       fold2 replace0 (head $ cutTreeL [t] 0) qs $ map (hide . getSubterm t) qs
   where c p x = if p `elem` ps then col++'_':delCol x else x
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
         hide t@(F ('@':_) _) = t
         hide (F x ts)        = F ('@':x) ts   
         hide t@(V ('@':_))   = t
         hide (V x)           = V ('@':x)
         hide t               = t

-- used by Ecom > drawThis

-- moreTree t turns all non-tree downward edges of t into tree edges.

moreTree :: TermS -> TermS
moreTree t = case f [] t of
                  Just (p,q) -> moreTree $ composePtrs $ exchange t p q
                  _ -> t
             where f p (F _ ts) = concat $ zipWithSucs f p ts
                   f p t        = do V x <- return t; let q = getPos x
                                     guard $ isPos x && length p < length q 
                                     Just (p,q)

-- used by separateTerms and Ecom > expandTree',removeEdges.

-- removeNonRoot t p removes the node at position p of t. removeNonRoot is used 

removeNonRoot :: TermS -> [Int] -> TermS
removeNonRoot t p = removeX $ chgPoss $ replace0 t q 
                            $ if isV u then u 
                                       else F x $ take n us++vs++drop (n+1) us
  where (q,n) = (init p,last p)
        snp = length p; np = snp-1
        u = getSubterm t q
        vs = subterms $ getSubterm t p
        incr = length vs-1
        midPoss = [r | r <- noRefPositions t, p << r]
        rightPoss = [r | r <- noRefPositions t, q << r, n < r!!np]
        newM r = take np r++r!!snp+n:drop (snp+1) r
        newR r = take np r++r!!np+incr:drop snp r
        (x,us) = (root u,subterms u)
        chgPoss (F x ts) = F x $ map chgPoss ts
        chgPoss (V x) | r == p = V "XXX"
                      | isPos x && r `elem` midPoss   = mkPos $ newM r
                      | isPos x && r `elem` rightPoss = mkPos $ newR r
                                                        where r = getPos x
        chgPoss t = t
        removeX t = lshiftPos t [p | p <- noRefPositions t, label t p == "XXX"]

-- used by Ecom > removeNode

data ChangedTerm = Wellformed TermS | Bad String

-- changeTerm t u ps@(p:qs) replaces the subterm of t at position p by u and 
-- then replaces the leaves of u with label "_" by the subterms vs of t at 
-- positions qs. 
-- If u does not have leaves with label "_", then all v in vs are replaced by u.
-- If u has a single leaf with label "_" and ps is a list of pairwise orthogonal
-- positions or if qs is empty, then for all v in vs, v is replaced by u[v/_]. 

changeTerm t u ps =
    case n of 0 -> Wellformed $ fold2 replace1 t ps $ replicate m u
              1 | orthos ps -> Wellformed $ f t ps t1 $ map g ps
              _ -> if m == 1
                   then Wellformed $ f t (replicate n p) t2 rs
                   else if all (p <<) qs
                        then let k = m-n-1
                             in case signum k of
                                0 -> Wellformed $ f t qs t2 rs
                                1 -> Bad $ "Add " ++ unstr k
                                _ -> Bad $ "Remove " ++ unstr (n-m+1)
                        else Bad "Select further subtrees below the first one!"
    where m = length ps; p:qs = ps
          t1 = foldl f t ps where f t p = replace1 t p u
          t2 = replace1 t p u; rs = map (p++) underlines
          g p = p++head underlines
          underlines = labPositions (== "_") u
          n = length underlines
          unstr 1 = "an underline!"
          unstr k = show k ++ " underlines!"
          f = fold3 moveAndReplace

-- used by Ecom > replaceText'

-- exchange t p q exchanges the subterms of t at position p resp. q.

exchange :: TermS -> [Int] -> [Int] -> TermS
exchange t p q = exchangePos p q $ replace0 (replace0 t p v) q u
                  where u = getSubterm t p; v = getSubterm t q

-- used by Ecom > reverseSubtrees

exchangePos :: [Int] -> [Int] -> TermS -> TermS
exchangePos p q = mapT f where f x | isPos x = 
                                     if p <<= r then g q p
                                       else if q <<= r then g p q else x
                                    where r = getPos x
                                          g p q = mkPos0 $ p++drop (length q) r
                               f x = x

incrPos :: Num r => [r] -> Int -> [r]
incrPos p n = updList p n $ p!!n+1

decrPos :: Num r => [r] -> Int -> [r]
decrPos p n = updList p n $ p!!n-1

-- lshiftPos t ps removes map (getSubterm t) ps from t and changes the pointers
-- of t accordingly.

lshiftPos :: TermS -> [[Int]] -> TermS
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

-- used by removeCyclePtrs, removeNonRoot (see above) and Ecom > removeSubtrees

-- removeSubterm t p removes the subterm at position p of t.
removeSubterm :: [Int] -> Term a -> Term a
removeSubterm p = head . f []
               where f q t = if p == q then [] 
                             else case t of 
                                  F x ts -> [F x $ concat $ zipWithSucs f q ts]
                                  _ -> [t]

-- rshiftPos p t adapts the pointer values of t to a copy of getSubterm t p.

rshiftPos :: [Int] -> TermS -> TermS
rshiftPos p = mapT f where f x = if isPos x 
                                  then mkPos0 $ rshiftPos0 p $ getPos x else x

rshiftPos0 :: (Num a, Ord a) => [a] -> [a] -> [a]
rshiftPos0 p q = if init p << q && last p <= q!!n then incrPos q n else q
                 where n = length p-1

-- used by Ecom > copySubtrees

-- atomPosition sig t p returns the position of the atom that encloses the
-- subterm of t at position p.

atomPosition :: Sig -> TermS -> [Int] -> Maybe ([Int],TermS,[Int])

atomPosition sig t [] = guard (isAtom sig t) >> Just ([],t,[])
atomPosition sig t p  = goUp t (init p) [last p]
     where goUp t p q = if null p then guard (isAtom sig t) >> Just ([],t,q)
                        else if isOnlyAtom sig u then Just (p,u,q)
                             else goUp t (init p) $ last p:q
                        where u = getSubterm t p

-- used by Esolve > applyToHeadOrBody,applyLoop/Random,applySingle and
-- Ecom > narrowPar

-- orPosition t p returns the position of the smallest disjunction v that
-- encloses the subterm of t at position p provided that there are only
-- existential quantifiers on the path from the root of v to p. 

orPosition :: TermS -> [Int] -> Maybe ([Int], [Int])
orPosition t p = goUp t (init p) [last p]
      where goUp t p q = if isDisjunct u then Just (p,q)
                         else guard (isConjunct u || take 4 (root u) == "Any ")
                              >> goUp t (init p) (last p:q)
                         where u = getSubterm t p

-- used by Ecom > applyDisCon

-- andPosition t p returns the position of the smallest conjunction v that
-- encloses the subterm of t at position p provided that there are only
-- universal quantifiers on the path from the root of v to p. 

andPosition :: TermS -> [Int] -> Maybe ([Int], [Int])
andPosition t p = goUp t (init p) [last p]
      where goUp t p q = if isConjunct u then Just (p,q)
                         else guard (isDisjunct u || take 4 (root u) == "All ")
                              >> goUp t (init p) (last p:q)
                         where u = getSubterm t p

-- used by Ecom > applyDisCon

-- outGraph{L} ... out {outL} t adds out!!x to each state node x of t and 
-- outL!!x!!y to each label node y of t with state predecessor x. 

outGraph :: [String] -> [String] -> [[Int]] -> TermS -> TermS
outGraph sts ats out = mapT $ extendNode sts ats out

outGraphL :: [String] -> [String] -> [String] -> [[Int]] -> [[[Int]]] -> TermS
                                                                      -> TermS
outGraphL sts labs ats out outL = f where
      f (F x ts) | x == "<+>" = F x $ map f ts
      f (F x ts) = F (extendNode sts ats out x) $ map g ts ++ map h labs' where
            xoutL = outL!!getInd x sts
            labs' = [lab | lab <- labs, all ((/= lab) . root) ts,
                                        notnull $ xoutL!!getInd lab labs]
            g (F lab ts) = F (extendNodeL lab) $ map f ts
            g t = t                 
            h = leaf . extendNodeL
            extendNodeL lab = enterAtoms lab $ map (ats!!) 
                                             $ xoutL!!getInd lab labs
      f t = t

-- used by Ecom > showTransOrKripke

extendNode :: [String] -> [String] -> [[Int]] -> Renaming
extendNode _ _ [] x      = x
extendNode sts ats out x = if isPos x || x == "<+>" then x
                           else enterAtoms (filter (/= '\"') x)
                                           $ map (ats!!) $ out!!getInd x sts


enterAtoms :: String -> [String] -> String
enterAtoms x []       = x
enterAtoms x [at]     = x++" : "++at
enterAtoms x (at:ats) = x++" : "++at++concatMap (',':) ats

-- colorClasses{L} colors equivalent states of a transition graph with the same
-- color and equivalent states with different colors unless they belong to 
-- singleton equivalence classes. Such states are blackened.
colorClasses,colorClassesL :: Sig -> TermS -> TermS
colorClasses sig = mapT $ setColor sts part n where
              sts = map showTerm0 (sig&states)
              part = [s | s@(_:_:_) <- mkPartition (indices_ sts) $ bisim sig]
              n = length part 
colorClassesL sig = g where
              g (F x ts) = F (setColor sts part n x) $ map h ts
              g t        = t
              h (F lab ts) = F lab $ map g ts
              h t          = t
              sts = map showTerm0 (sig&states)
              part = [s | s@(_:_:_) <- mkPartition (indices_ sts) $ bisim sig]
              n = length part
                          
setColor :: [String] -> [[Int]] -> Int -> Renaming
setColor sts part n x = if x `notElem` sts then x
                        else case searchGet (elem $ getInd x sts) part of
                          Just (k,_) -> show (hue 0 red n k) ++ '_':x
                          _          -> x

-- concept ts posExas negExas computes the minimal concept wrt the feature trees
-- ts that satisfy the positive/negative examples posExas/negExas.
concept :: [TermS] -> [[String]] -> [[String]] -> [[String]]
concept ts posExas negExas = 
     if all (== length ts) $ map length $ posExas ++ negExas
     then map f $ minis r $ g (possOfTup posExas) `minus` g (possOfTup negExas)
     else [["Some example is not covered by the tuple of feature trees."]]
     where f = map root . zipWith getSubterm ts
           r ps = and . zipWith (<<=) ps 
           g = concatMap $ mapM prefixes
           possOfTup = map (zipWith h ts) . reduceExas ts
           h t = get . possOf t

-- reduceExas ts exas combines subsets of exas covering a subconcept to single 
-- examples.
reduceExas :: [TermS] -> [[String]] -> [[String]]
reduceExas ts exas = 
           if all (== length ts) $ map length exas
          then iterate (flip (foldl f) $ indices_ ts) exas
          else [["Some example is not covered by the tuple of feature trees."]]
     where iterate h exas = if exas == exas' then exas else iterate h exas'
                                  where exas' = h exas
           f exas i = foldl g exas $ tail $ noRefPositions t
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

graphToRel :: TermS -> Pairs String
graphToRel t = case t of F "<+>" ts -> concatMap f ts; _ -> f t
               where dom x xss = joinM xss `join1` x
                     f t@(F x ts) = foldl g [] $ foldT dom t
                                  where g s a = if null bs then s else (a,bs):s
                                         where bs = foldl (h x) (const []) ts a
                     f _ = []
                     h x f (F z ts) = foldl (h z) (updL f x z) ts
                     h x f (V z)    = updL f x $ if isPos z then root u else z
                                      where u = getSubterm t $ getPos z
                     h _ f _        = f

-- used by collapseCycles,eqsToGraph,showMatrix and Ecom > showRelation

graphToRel2 :: [String] -> TermS -> Triples String String
graphToRel2 xs t = case t of F "<+>" ts -> concatMap f ts; _ -> f t
        where dom x xss = joinM xss `join1` x
              (domx,domy) = split (`elem` xs) $ foldT dom t
              f (F x ts) = foldl g [] $ prod2 domx domy
                            where g s (a,b) = if null cs then s else (a,b,cs):s
                                      where cs = foldl (h x) (const2 []) ts a b
              f _ = []
              h x f (F y ts) = foldl (h' x y) f ts
              h _ f _        = f
              h' x y f (F z ts) = foldl (h z) (upd2L f x y z) ts
              h' x y f (V z)    = upd2L f x y $ if isPos z then root u else z
                                  where u = getSubterm t $ getPos z
              h' _ _ f _        = f

-- used by Ecom > showMatrix,showRelation.

-- * ITERATIVE EQUATIONS and INEQUATIONS

data IterEq = Equal String TermS | Diff String TermS deriving (Eq,Ord)

getVar :: IterEq -> String
getVar (Equal x _) = x
getVar (Diff x _)  = x

getTerm :: IterEq -> TermS
getTerm (Equal _ t) = t
getTerm (Diff _ t)  = t

updTerm :: (TermS -> TermS) -> IterEq -> IterEq
updTerm f (Equal x t) = Equal x (f t)
updTerm f (Diff x t)  = Diff x (f t)

eqPairs :: [IterEq] -> [(String,TermS)]
eqPairs = map (getVar *** getTerm)

unzipEqs :: [IterEq] -> ([String], [TermS])
unzipEqs = unzip . eqPairs

mkSubst :: [IterEq] -> SubstS
mkSubst eqs = forL ts xs where (xs,ts) = unzipEqs eqs

-- used by Esolve > rewrite,applyAx,rewriteTerm

solAtom :: Sig -> TermS -> Maybe IterEq
solAtom sig t | just eq = eq where eq = solEq sig t
solAtom sig t           = solIneq sig t

solEq :: Sig -> TermS -> Maybe IterEq
solEq sig t = do (l,r) <- getEqSides t
                 let x = root l; y = root r
                 if isV l && x `notElem` xs && isNormal sig r 
                    then Just $ Equal x r
                    else do guard $ isV r && y `notElem` xs && isNormal sig l
                            Just $ Equal y l
                    where xs = anys t

solIneq :: Sig -> TermS -> Maybe IterEq
solIneq sig t = do (l,r) <- getIneqSides t
                   let x = root l; y = root r
                   if isV l && x `notElem` xs && isNormal sig r
                      then Just $ Diff x r
                      else do guard $ isV r && y `notElem` xs && isNormal sig l
                              Just $ Diff y l
                      where xs = alls t

getEqSides (F ('A':'n':'y':_) [F "=" [l,r]]) = Just (l,r)
getEqSides (F "=" [l,r])                     = Just (l,r)
getEqSides _                                 = Nothing

getIneqSides :: TermS -> Maybe (TermS, TermS)
getIneqSides (F ('A':'l':'l':_) [F "=/=" [l,r]]) = Just (l,r)
getIneqSides (F "=/=" [l,r])                     = Just (l,r)
getIneqSides _                                   = Nothing

autoEqsToRegEqs :: Sig -> [IterEq] -> [IterEq]
autoEqsToRegEqs sig = map f
    where f (Equal x t) = case parseRE sig $ g t of
                               Just (e,_) -> Equal x $ showRE $ distributeReg e
                               _ -> Equal x $ leaf "OOPS"
          g (F q ts)    = F "+" $ if n >= 0 && drop n q == "final"
                                  then leaf "eps":map h ts else map h ts
                          where n = length q-5
          g t           = t
          h (F lab [t]) = F "*" [F lab [],g t]
          h t           = t

-- used by Ecom > showEqsOrGraph

substituteVars :: TermS -> [IterEq] -> [[Int]] -> Maybe TermS
substituteVars t eqs ps = do guard $ all isV ts
                             Just $ fold2 replace1 t ps $ map (subst . root) ts
                          where ts = map (getSubterm1 t) ps
                                subst x = if nothing t || x `isin` u
                                          then V x else u
                                          where t = lookup x $ eqPairs eqs
                                                u = get t

-- solveRegEq turns a regular equation x = t1*x+...+tn*x+t into its least 
-- solution star(t1+...+t2)*t, which is unique if eps =/= ti for all 1≤i≤n.

solveRegEq :: Sig -> IterEq -> Maybe TermS
solveRegEq sig (Equal x t) = do (e,_) <- parseRE sig $ f $ case t of
                                                                F "+" ts -> ts
                                                                _ -> [t]
                                Just $ mkEq (V x) $ showRE e
          where f ts = case us of []  -> leaf "mt"
                                  [u] -> F "*" [star,u]
                                  _   -> F "*" [star,F "+" us]
                       where us = ts `minus` recs                              
                             recs = [t | t@(F "*" us) <- ts, last us == V x]
                             star = case recs of 
                                         []    -> leaf "eps"
                                         [rec] -> F "star" [g rec]
                                         _     -> F "star" [F "+" $ map g recs]
                g (F "*" [t,_]) = t
                g (F "*" ts)    = F "*" $ init ts
                g _             = leaf "OOPS" 

parseSol :: (TermS -> Maybe IterEq) -> TermS -> Maybe [IterEq]
parseSol f t = case t of F "True" [] -> Just []
                         F "&" ts -> do eqs <- mapM f ts
                                        let (xs,us) = unzipEqs eqs
                                        guard $ distinct xs && all (g xs) us
                                        Just $ map (updTerm $ mapT h) eqs
                         _ -> do eq <- f t; guard $ g [getVar eq] $ getTerm eq
                                 Just [updTerm (dropnFromPoss 1) eq]
               where g xs t = root t `notElem` xs
                     h x = if isPos x then mkPos0 $ tail $ tail $ getPos x 
                                      else x

-- used by parseEqs,isSol, Epaint > solPict and Esolve > solveGuard

isSol :: Sig -> TermS -> Bool
isSol sig = just . parseSol (solAtom sig) ||| isFalse

-- used by Ecom > makeTrees,narrowLoop,splitTree

solPoss :: Sig -> [TermS] -> [Int]
solPoss sig ts = filter (isSol sig . (ts!!)) $ indices_ ts

-- used by Ecom > makeTrees,narrowLoop,showSolutions

-- parseEqs is used by simplifyS postflow/stateflow/subsflow, simplReducts 
-- (see Esolve) and

parseEqs :: TermS -> Maybe [IterEq]
parseEqs t = parseSol parseIterEq t ++
           do F x ts <- Just t; guard $ isFixT x
              let _:zs = words x
              case ts of [t] -> Just $ case zs of [z] -> [Equal z t]
                                                  _ -> zipWith (f x t) [0..] zs
                         _ -> do guard $ length zs == length ts
                                 Just $ zipWith Equal zs ts
           where parseIterEq (F x [t,u])
                  | b x && null (subterms t) && isF u = Just $ Equal (root t) u
                  | b x && null (subterms u) && isF t = Just $ Equal (root u) t
                 parseIterEq _ = Nothing
                 b x = x == "=" || x == "<=>"
                 f x u i z = Equal z $ F ("get"++show i) [u]

-- used by parseEqs, Esolve > simplifyS postflow/subsflow and 
-- Ecom > modifyEqs,showEqsOrGraph,showMatrix,showRelation

parseIterEq :: TermS -> Maybe IterEq
parseIterEq (F "=" [V x,t]) | isF t = Just $ Equal x t
parseIterEq _ = Nothing

-- used by parseEqs and Ecom > modifyEqs

eqsTerm :: [IterEq] -> TermS
eqsTerm eqs = case eqs' of [eq] -> f eq
                           _ -> F "&" $ addNatsToPoss $ map f eqs'
              where eqs' = mkSet eqs
                    f (Equal x t) = mkEq (V x) t
                    f (Diff x t)  = mkNeq (V x) t

-- used by Ecom > modifyEqs,transformGraph

-- graphToEqs n t transforms a graph into an equivalent set of iterative 
-- equations.

graphToEqs :: Int -> TermS -> [Int] -> ([IterEq],Int)
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

-- used by Ecom > showEqsOrGraph

-- relToEqs n rel transforms a binary relation into an equivalent set of 
-- iterative equations.

relToEqs :: Int -> Pairs String -> ([IterEq],Int)
relToEqs n rel = (map g $ indices_ ps,n+length ps)
                 where ps = foldr f [] rel
                       f (a,bs) rel = if null bs then rel else updRel rel a bs
                       g i = Equal ('z':show (n+i)) $ F a $ map h bs
                             where p@(a,bs) = ps!!i
                                   h b = case search ((== b) . fst) ps of
                                              Just i -> V $ 'z':show (n+i)
                                              _ -> leaf b

-- used by Ecom > showEqsOrGraph

-- relLToEqs n rel transforms a ternary relation into an equivalent set of 
-- iterative equations.

relLToEqs :: Int -> Triples String String -> ([IterEq],Int)
relLToEqs n rel = (map g $ indices_ ts,n+length ts)
         where ts = foldr f [] rel
               f (a,b,cs) rel = if null cs then rel
                                else case lookup a rel of
                                     Just bcs -> updRel rel a $ updRel bcs b cs
                                     _ -> (a,[(b,cs)]):rel
               g i = Equal ('z':show (n+i)) $ F a $ map f bcs
                     where (a,bcs) = ts!!i
                           f (b,cs) = F b $ map h cs
                           h c = case search ((== c) . fst) ts of
                                      Just i -> V $ 'z':show (n+i)
                                      _ -> F c []

-- used by Esolve > simplifyT "auto" and Ecom > showTransOrKripke,transformGraph

mkArc :: String -> [Int] -> TermS -> TermS
mkArc x p = f where f (F z ts) = if x == z then if null ts then mkPos p
                                                     else applyL (mkPos p) ts
                                            else F z $ map f ts
                    f t@(V z)  = if x == z then mkPos p else t
                    f t        = t



-- eqsToGraph is eqs selects the maximal elements of the separated right-hand 
-- sides of eqs. 

eqsToGraph :: [Int] -> [IterEq] -> TermS
eqsToGraph [] []  = emptyGraph
eqsToGraph [] eqs = collapse True $ eqsToGraph (indices_ eqs) eqs
eqsToGraph is eqs = case maxis subGraph us of [t] -> t
                                              ts -> F "<+>" $ addNatsToPoss ts
                     where t = connectEqs eqs
                           ts = subterms $ separateTerms t is
                           us = case t of 
                             F "&" _ -> map (dropnFromPoss 2 . rhs . (ts!!)) is
                             _ -> [dropnFromPoss 1 $ rhs t]
                           rhs t = getSubterm t [1]

-- used by eqsToGraphx, Epaint > graphToTree, Esolve > mkCycles,simplifyS and
-- Ecom > showMatrix 6,showRelation 6,showTransOrKripke,transformGraph 2

-- eqsToGraphs t transforms the equations of t into connected components.

eqsToGraphs :: TermS -> TermS
eqsToGraphs (t@(F "&" eqs)) = F "&" $ addNatsToPoss us
                              where is = indices_ eqs
                                    g i = getSubterm (separateTerms t is) [i]
                                    ts = map g is
                                    us = map (dropnFromPoss 1 . (ts!!)) is
eqsToGraphs t = t

-- used by Ecom > modifyEqs 0

emptyGraph = leaf "This graph is empty."

connectEqs :: [IterEq] -> TermS
connectEqs eqs = mkEqsConjunct xs $ f xs ts where
                  (xs,ts) = unzipEqs eqs
               -- f xs ts replaces each occurrence in ts of a variable xs!!i by 
               -- a pointer to ts!!i. 
                  f [x] [t] = [mkArc x [] t]
                  f xs ts   = g 0 xs $ addNatsToPoss ts where
                              g n (x:xs) ts = g (n+1) xs $ map (mkArc x [n]) ts
                              g _ _ ts      = ts

-- used by eqsToGraph and Ecom > modifyEqs 0

eqsToGraphx :: String -> [IterEq] -> TermS
eqsToGraphx x eqs = eqsToGraph is eqs where
                    is = case search ((== x) . root) $ snd $ unzipEqs eqs of 
                         Just i -> [i]
                         _ -> []

-- used by Ecom > transformGraph 2

-- COLLAPSING and EXPANDING

-- collapse b t recognizes the common subterms of t and builds a collapsed
-- tree without common subtrees (see Huth, Ryan, Logic in Computer Science,
-- p. 361 f.). collapse builds up a node partition (h,dom), starting out from
-- (id,[]) and proceeding bottom-up through the levels of t. dom is the domain
-- of h that consists of all nodes with h p =/= p. 
-- b = True  --> arrows point to the right.
-- b = False --> arrows point to the left.
collapse :: Bool -> TermS -> TermS
collapse b t = fst $ foldC (collapseLoop b) g (u,(id,[])) [0..height u-1]
               where u = collapseCycles t
                     g (t,_) (u,_) = t == u

type Node      = ([Int],String,[[Int]])
type Partition = ([Int] -> [Int],[[Int]])

collapseLoop :: Bool -> (TermS, Partition) -> Int -> (TermS, Partition)
collapseLoop b (t,part) i = (setPointers t part',part')
                  where part' = chgPart part $ if b then f i else reverse $ f i
                        nodes = mkNodes t
                        f 0 = filter (null . pr3) nodes
                        f i = filter (p . pr3) nodes
                              where p = supset $ map pr1 $ f $ i-1

-- setPointers t (h,dom) replaces each subterm of t whose position p is in dom
-- by trace t $ h p.

setPointers :: TermS -> Partition -> TermS
setPointers t (h,dom) = f [] t
                    where f p (F x ts) = g p $ F x $ zipWithSucs f p ts
                          f p t        = g p t
                          g p u = if p `elem` dom then V $ trace t $ h p else u

-- | @chgPart part nodes@ adds each node @n@ of @nodes@ to part by setting @n@
-- and all equivalent nodes to the same h-value.
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

-- | @mkNodes t@ translates @t@ into a list of all triples consisting of the
-- position, the label and the positions of the direct successors of each node
-- of @t@.
mkNodes
    :: TermS -- ^ t
    -> [Node]
mkNodes (V x)    = [([],x,[])]
mkNodes (F x ts) = ([],x,map (:[]) is):concatMap h is
                   where is = indices_ ts
                         h i = map g $ mkNodes $ ts!!i
                               where g (p,x,ps) = (i:p,x,map (i:) ps)
mkNodes _        = [([],"hidden",[])]

-- collapseCycles t removes all duplicates of cycles of t.

collapseCycles :: TermS -> TermS
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
            getRoot u = head . labPositions (== (root u))
            cyclePoss p (F _ ts) = concat $ zipWithSucs cyclePoss p ts
            cyclePoss p (V x)    = [q | isPos x && q <<= p]
                                    where q = getPos x
            cyclePoss _ _        = []

composePtrs :: TermS -> TermS
composePtrs t = mapT f t where f x = if isPos x && isPos y 
                                      then trace t $ getPos y else x
                                     where y = label t $ getPos x

-- used by moreTree and Ecom > composePointers

-- collapseSubs pred t sets collapses all equal subterms u of t such that
-- pred(p)(x) holds true for the root position p and root label x of u.

collapseSubs :: ([Int] -> String -> Bool) -> TermS -> TermS
collapseSubs pred t = setPointers t $ chgPart (id,[]) $ filter f nodes
                      where nodes = mkNodes t
                            f (q,_,_) = any g nodes
                                        where g (p,x,_) = p <<= q && pred p x

collapseVars :: Sig -> [String] -> TermS -> TermS
collapseVars sig xs t = collapseSubs pred t where
                        pred p x = x `elem` xs && p `elem` freePositions sig t

-- used by Esolve > bodyAndSub,expandFix,simplifyS"subst" and
-- Ecom > collapseVarsCom

-- expand{One} n t p expands u = getSubterm t p by dereferencing all pointers
-- resp. a pointer to the same subterm. Each circle of u is unfolded n times.

expand,expandOne :: Int -> TermS -> [Int] -> TermS

expand n t p = f n t p $ getSubterm t p
  where f n t p (F x ts)          = F x $ zipWithSucs (f n t) p ts
        f n t p u@(V x) | isPos x = if connected t q p
                                    then if n == 0 then u else g $ n-1 else g n
                                    where q = getPos x
                                          v = movePoss t q p
                                          g n = f n (replace0 t p v) p v
        f _ _ _ u = u

-- used by closedSub,dereference,expand0 and Ecom > "expand"

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

-- used by separateTerms and the Ecom > "expand one"

expand0 :: TermS -> [Int] -> TermS
expand0 t p = dropFromPoss p $ expand 0 t p

-- used by Esolve > simplifyOne and Ecom > refNodes

-- expandInto t r expands t at all pointers into the subterm of t at position r.

expandInto t r = f [] t where f p (F x ts) = F x $ zipWithSucs f p ts
                              f p (V x) | isPos x && r <<= q
                                           = movePoss t q p where q = getPos x
                              f _ t        = t

-- used by Ecom > removeSubtrees

-- * Substitutions and unifiers

type Subst a = a -> Term a
type SubstS  = Subst String

domSub :: (Eq a,Root a) => [a] -> Subst a -> [a]
domSub as f = [a | a <- as, let t = f a, a /= root t || notnull (subterms t)]

for :: Eq a => Term a -> a -> Subst a
t `for` a = upd V a t

forL :: Eq a => [Term a] -> [a] -> Subst a
ts `forL` as = fold2 upd V as ts

restrict :: Eq a => [a] -> Subst a -> Subst a
restrict as f = map f as `forL` as

eqSub :: [String] -> SubstS -> SubstS -> Bool
eqSub xs f g = eqFun eqTerm f g xs

subSubs :: [String] -> [SubstS] -> [SubstS] -> Bool
subSubs xs fs gs = all (\f -> any (eqSub xs f) gs) fs

meetSubs,joinSubs :: [String] -> [SubstS] -> [SubstS] -> [SubstS]
meetSubs xs fs gs = [f | f <- fs, any (eqSub xs f) gs]
joinSubs xs fs gs = h $ fs++gs where h (f:s) = f:[g | g <- h s,
                                                      not $ eqSub xs g f,
                                                      not $ eqSub xs g V]
                                     h _     = []

andThen :: SubstS -> SubstS -> SubstS
andThen f g x = f x>>>g

(>>>) :: TermS -> SubstS -> TermS
t>>>f = instantiate addToPoss t f []

instantiate :: ([Int] -> TermS -> TermS) -> TermS -> SubstS -> [Int] -> TermS
instantiate chg t sub = mapT delHid . h t where
          rename c = renameAwayFrom chg c sub
          f x = if leader x "tpos" && t /= V z then addChar 't' t [] else sub x
                where t = sub z
                      (_,_:z) = break (== '@') x
          h c@(V x) p    = if isPos x then c else chg p $ f x
          h c@(F x [t]) p
              | binder x = mkBinder op zs $ g $ p++[0]
                           where (zs,_,g) = rename c xs t
                                 op:xs = words x
          h c@(F x ts) p
              | lambda x = F x $ concat $ zipWithSucs2 g p (evens ts) $ odds ts
                           where g p par t = [g1 par,g2 p]
                                             where (_,g1,g2) = rename c xs t
                                                   xs = foldT v par
                                 v x xss = if x == root (f x) then xs else x:xs
                                           where xs = concat xss
          h (F x []) p   = case f x of V z -> F z [] -- z is higher-order
                                       t -> chg p t
          h (F x ts) p   = case f x of V z -> F z $ g2 g0
                                       F z [] -> F z $ g2 g0
                                       t -> F "$" [chg (p++[0]) t,u]
                           where g0 t n = h t $ p++[n]
                                 g1 t n = h t $ p++[1,n]
                                 g2 g = zipWith g ts $ indices_ ts
                                 u = case ts of [t] -> g0 t 1
                                                _ -> mkTup $ g2 g1
          h t _ = t

-- used by instantiate,renameAwayFrom and Esolve > expandFix

renameAwayFrom :: ([Int] -> TermS -> TermS) -> TermS -> SubstS -> [String]
                  -> TermS -> ([String], TermS -> TermS, [Int] -> TermS)
renameAwayFrom chg c f xs t =
                     (zs,g',instantiate chg (g' t) $ fold2 upd f zs $ map V zs)
                     where g  = getSubAwayFrom c xs ys
                           zs = map g xs
                           g' = renameAll g
                           ys = joinMap (allFrees . f) $ domSub (allFrees t) f

-- used by instantiate

-- translations between formulas and substitutions

substToEqs f = map g where g x = F "=" [V x,add1ToPoss $ f x]

substToIneqs f = map g where g x = F "=/=" [V x,add1ToPoss $ f x]

eqsToSubst :: [TermS] -> Maybe (String -> TermS, [String])
eqsToSubst []                  = Just (V,[])
eqsToSubst (F "=" [V x,t]:eqs) = do (f,xs) <- eqsToSubst eqs
                                    Just (for t x `andThen` f,x:xs)
eqsToSubst (F "=" [t,V x]:eqs) = do (f,xs) <- eqsToSubst eqs
                                    Just (for t x `andThen` f,x:xs)
eqsToSubst _                   = Nothing

-- used by Ecom > addSubst

-- * Renaming

type Renaming   = String -> String
type VarCounter = String -> Int

-- | @splitVar x@ splits @x@ into its non-numerical prefix and its numerical
-- suffix.
splitVar :: String -> (String,String,Bool)
splitVar x = (base,ds,b)
      where b = just $ parse infixWord x
            (base,ds) = span (not . isDigit) $ if b then init $ tail x else f x
            f ('!':x) = x; f x = x

                      
-- getSubAwayFrom t xs ys renames the variables of xs `meet` ys away from the
-- symbols of t.

getSubAwayFrom :: TermS -> [String] -> [String] -> Renaming
getSubAwayFrom t xs ys = fst $ renaming (iniVC $ allSyms b t) toBeRenamed
                         where toBeRenamed = xs `meet` ys
                               b x = any eqBase toBeRenamed
                                     where eqBase y = base x == base y
                               base = pr1 . splitVar

-- used by renameAwayFrom and Ecom > simplifyF,bodyAndSub

-- iniVC syms initializes the index counter vc of the maximal non-numerical 
-- prefixes of all strings of xs. If there is no n such that xn is in syms, 
-- then vc x is set to 0. If n is maximal such that xn is in syms, then vc x is 
-- set to n+1.

iniVC :: [String] -> VarCounter
iniVC = foldl f $ const 0
        where f vc x = upd vc base $ max (vc base) $ if null ds then 0
                                                                else read ds+1
                       where (base,ds,_) = splitVar x

-- used by (>>>),renameAwayFrom,iniVarCounter and Ecom > initialize,parseSig

-- decrVC vc xs decreases the counter vc of the maximal non-numerical prefixes 
-- of all strings of xs. 

decrVC :: VarCounter -> [String] -> VarCounter
decrVC = foldl f where f vc x = upd vc z $ vc z-1 where z = pr1 $ splitVar x

-- used by Ecom > applyInd

-- renaming vc xs renames xn in xs to x(vc(x)). The values of vc are increased 
-- accordingly.

renaming :: VarCounter -> [String] -> (Renaming,VarCounter)
renaming vc = foldl f (id,vc) where f (g,vc) x = (upd g x y,incr vc base)
                                      where (base,_,b) = splitVar x
                                            str = base++show (vc base)
                                            y = if b then '`':str++"`" else str

-- used by (>>>),getSubAwayFrom,renameApply, Esolve > moveUp and Ecom > applyInd

-- renameApply sig t vc cls computes a renaming f of the variables of t and
-- applies f to cls.

renameApply :: Sig -> TermS -> VarCounter -> [TermS] -> ([TermS],VarCounter)
renameApply sig t vc cls = (map (renameAll f) cls,vc')
                where (f,vc') = renaming vc [x | x <- sigVars sig t, noExcl x,
                                                    any (isin x) cls]

-- used by Esolve > applyLoop{Random},applyToHeadOrBody and Ecom > applyTheorem,
-- narrowPar,rewritePar

noExcl :: String -> Bool
noExcl ('!':_:_) = False
noExcl _         = True

-- renameAll f t renames by f all symbol occurrences in t.
renameAll :: Renaming -> TermS -> TermS
renameAll f (F x [t]) | binder x = mkBinder op (map f xs) $ renameAll f t
                                   where op:xs = words x
renameAll f (F x ts)             = F (f x) $ map (renameAll f) ts
renameAll f (V x)                = V $ f x
renameAll _ t                    = t

-- used by (>>>),renameApply, Esolve > simplifyF/A and Ecom > renameVar'

-- renameFree sig f t renames by f all free symbol occurrences in t.

renameFree :: Sig -> Renaming -> TermS -> TermS
renameFree sig = rename where
  rename f (F x [t]) | binder x = mkBinder op xs $ rename (block f xs) t
                                  where op:xs = words x
  rename f (F x ts)  | lambda x = F x $ concat $ zipWith g (evens ts) $ odds ts
                                  where g pat t = [pat,rename (block f xs) t]
                                                  where xs = allVars sig pat
  rename f (F x ts) = F (f x) $ map (rename f) ts
  rename f (V x)    = V $ f x
  rename _ t        = t
  block f xs = fold2 upd f xs xs

-- used by eqTerm,match and Esolve > moveUp,subsumes

-- renameBound sig f t renames by f all bound symbol occurrences in t.

renameBound :: Sig -> Renaming -> TermS -> TermS
renameBound sig f = rename where
    rename (F x [t]) | binder x = mkBinder op (map f xs) $ g t
                                  where op:xs = words x
    rename (F x ts)  | lambda x = F x $ concat $ zipWith h (evens ts) $ odds ts
                                  where h pat t = [g pat,g t]
    rename (F x ts) = F x $ map rename ts
    rename t      = t
    g = rename . mapT f

-- used by Esolve > bodyAndSub

getPrevious :: Renaming
getPrevious x = if b then '`':str++"`" else str
                where (base,ds,b) = splitVar x; n = read ds
                      str = if n == 0 then base else base++show (n-1)

-- used by Ecom > applyCoinduction,applyInd,applyInduction

-- * Unification of terms and formulas

-- | Result returns unifiers or error messages.
data Result a = Def a | BadOrder | Circle [Int] [Int] | NoPos [Int] | NoUni | 
                OcFailed String | ParUni SubstS [String] | TotUni SubstS

instance Functor Result where
   fmap = liftM

instance Applicative Result where
   pure = Def
   (<*>)  = Haskell.ap

instance Monad Result where
   Def a >>= h       = h a
   BadOrder >>= _    = BadOrder
   Circle p q >>= _  = Circle p q
   NoPos p >>= _     = NoPos p
   NoUni >>= _       = NoUni
   OcFailed x >>= _  = OcFailed x
   ParUni a xs >>= _ = ParUni a xs
   TotUni a >>= _    = TotUni a
   return = Def

unify0 sig xs u redex t p = case unify sig xs V u redex u t [] p of
                                 Def (f,True)                  -> TotUni f
                                 Def (f,_) | all (isV . f) dom -> NoUni
                                           | True              -> ParUni f dom
                                             where dom = domSub xs f
                                 result -> result

-- used by Esolve > applyAx,partialUnify,totalUnify,applySingle

-- unify sig xs f u u' t t' p q computes the extension of f by a unifier of the
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

unify sig xs f = h f where

 h f t@(V x) u@(V y) _ _ _ _
  | x == y                   = Def (f,True)
  | not (isPos x || isPos y) = Def (andThen f g,True)
                             where g = if x `elem` xs then for t y else for u x
 h f (V x) u t t' p q
  | isPos x   = if r == q then Def (f,True)
                else if r << p then Circle r q
                     else if r `elem` noRefPositions t
                          then h f v u (replace t p v) t' p q else NoPos r
  | True      = if isin x u then OcFailed x else Def (andThen f $ for u x,True)
                where r = getPos x
                      v = getSubterm t r
 h f u (V x) t t' p q = h f (V x) u t' t q p
 h f (F x [V z]) (F y us) t t' p q
  | not (collector x) && x == y && length us > 1
              = h f (V z) (mkTup us) t t' (p++[0]) q
 h f (F x ts) (F y [V z]) t t' p q
  | not (collector y) && x == y && length ts > 1
              = h f (mkTup ts) (V z) t t' p $ q++[0]
 h f (F x ts) (F y us) t t' p q = case unifyFuns f x ts y us t t' p q of
                                  BadOrder -> unifyFuns f y us x ts t' t q p
                                  result -> result
 h f t u _ _ _ _ = if bothHidden t u then Def (f,True) else NoUni

 unifyFuns f x ts y us t t' p q
  | x == y           = if b then unifyM ts us t t' ps qs else NoUni
  | (sig&isHovar) x && (sig&isHovar) y && b
                     = if x `elem` xs then g x y else g y x
  | (sig&hovarRel) x y = if b then g y x
                       else if null ts then Def (sub2 x y,True) else NoUni
                     where b = length ts == length us
                           unifyM = if permutative x then unifyBag
                                                     else unifyList sig xs f
                           dom = indices_ ts
                           ps = succs p dom
                           qs = succs q dom
                           g x y = unifyList sig xs (sub1 x y) ts us t t' ps qs
                           sub1 x y = andThen f $ for (F x []) y
                           sub2 x y = andThen f $ for (F y us) x
 unifyFuns _ x _ "suc" [u] t t' p q
  | just n           = h f (mkConst $ get n-1) u t t' [] $ q++[0]
                       where n = parse pnat x
 unifyFuns _ "[]" (u:us) ":" [v,v'] t t' p q
                     = unifyList sig xs f [u,mkList us] [v,v'] t t' (g p) $ g q
                       where g p = [p++[0],p++[1]]
 unifyFuns _ x _ y _ _ _ _ _ = if (sig&isDefunct) x && not ((sig&isHovar) y)
                               then Def (f,False) else BadOrder

 unifyBag [] _ _ _ _ _  = Def (f,True)
 unifyBag (t:ts) us v v' (p:ps) qs
                        = do (f,b,us) <- try t us v v' p qs
                             (f,c) <- unifyBag (map (>>>f) ts) us v v' ps qs
                             Def (f,b&&c)
 unifyBag _ _ _ _ _ _   = NoUni

 try t (u:us) v v' p (q:qs) = case h f (t>>>f) (u>>>f) v v' p q of
                                   Def (f,b) -> Def (f,b,map (>>>f) us)
                                   _ -> do (f,b,us) <- try t us v v' p qs
                                           Def (f,b,u>>>f:us)
 try _ _ _ _ _ _            = NoUni

-- used by unify0,unifyList,unifyAC and Ecom > unifyAct

unifyList _ _ f [] [] _ _ _ _ = Def (f,True)
unifyList sig xs f (t:ts) (u:us) v v' (p:ps) (q:qs)
                      = do (f,b) <- unify sig xs f (t>>>f) (u>>>f) v v' p q
                           let h = map (>>>f)
                           (f,c) <- unifyList sig xs f (h ts) (h us) v v' ps qs
                           Def (f,b&&c)
unifyList _ _ _ _ _ _ _ _ _   = NoUni

-- used by unify and Esolve > searchReds,applyMany

-- unifyAC ts reds checks whether for all terms t in ts some term red in reds
-- unifies with t. If the check succeeds, then unifyAC returns the most general
-- unifier f and all terms of reds that were not unified with terms of ts.

unifyAC sig xs f (t:ts) reds = do (f,rest) <- g reds (length reds-1)
                                  let h = map (>>>f)
                                  unifyAC sig xs f (h ts) $ h rest
               where g reds i = do guard $ i >= 0
                                   case unify sig xs f t red t red [] [] of
                                        Def (f,True) -> Just (f,context i reds)
                                        _ -> g reds (i-1)
                                where red = reds!!i
unifyAC _ _ f _ reds = Just (f,reds)

-- used by Esolve > applySingle

-- unifyS sig xs t t' substitutes only variables of xs and neither dereferences
-- pointers nor finds partial unifiers (see above).

unifyS sig xs = h where

 h (V x) (V y) | x == y                 = Just V
 h (V x) t | x `elem` xs && x `notIn` t = Just $ t `for` x
 h t (V x) | x `elem` xs && x `notIn` t = Just $ t `for` x
 h (F x ts) (F y us) = unifyFuns x ts y us ++ unifyFuns y us x ts
 h t u               = do guard $ bothHidden t u; Just V

 unifyFuns x ts y us
  | (sig&hovarRel) x y && x `elem` xs
                = if b then do g <- unifyList (map (>>>f) ts) $ map (>>>f) us
                               Just $ f `andThen` g
                          else do
                               guard $ null ts
                               Just $ F y us `for` x
  | x == y && b = unifyM ts us
                  where b = length ts == length us
                        f = F y [] `for` x
                        unifyM = if permutative x then unifyBag else unifyList
 unifyFuns x _ "suc" [t] | just n = h (mkConst $ get n-1) t
                                    where n = parse pnat x
 unifyFuns "[]" (t:ts) ":" [u,v]  = unifyList [t,mkList ts] [u,v]
 unifyFuns _ _ _ _                = Nothing

 unifyList (t:ts) (u:us) = do f <- h t u
                              g <- unifyList (map (>>>f) ts) $ map (>>>f) us
                              Just $ f `andThen` g
 unifyList _ _ = Just V

 unifyBag (t:ts) us = do (f,us) <- try t us
                         g <- unifyBag (map (>>>f) ts) us; Just $ f `andThen` g
 unifyBag _ _ = Just V

 try t us = do u:us <- Just us
               case h t u of Just f -> Just (f,map (>>>f) us)
                             _ -> do (f,us) <- try t us; Just (f,u>>>f:us)

-- used by Esolve > removeEq and Ecom > unifySubtrees

-- MATCHING of terms and formulas

-- match sig xs t u computes a substitution f that extends u to t (t matches u).
-- Only the variables of xs are substituted. For all x in xs, the pointers of
-- f(x) are decreased by the position of x in u.

match :: Sig -> [String] -> TermS -> TermS -> Maybe SubstS
match sig xs = h []
  where h _ (V x) (V y) | x == y  = Just V
        h p t (V y) | y `elem` xs = Just $ dropFromPossC 'h' p t `for` y
        h p t@(F x ts) (F y us)
          | (sig&hovarRel) y x && y `elem` xs =
                    if b then do g <- match' ps (map (>>>f) ts) $ map (>>>f) us
                                 Just $ f `andThen` g
                            else do
                                 guard $ null us
                                 Just $ dropFromPossC 'h' p t `for` y
          | x == y && b = if permutative x then matchBag ps ts us
                                           else match' ps ts us
                          where b = length ts == length us
                                f = F x [] `for` y
                                ps = succsInd p ts
        h p (F x [t]) (F y [u])
          | binder x && binder y && opx == opy && length xs == length ys =
                           h (p++[0]) (renameFree sig (fold2 upd id xs ys) t) u
                           where opx:xs = words x; opy:ys = words y
        h p t (F "suc" [u]) | just n = h (p++[0]) (mkConst $ get n-1) u
                                       where n = parsePnat t
        h p (F "suc" [t]) u | just n = h (p++[0]) t $ mkConst $ get n-1
                                       where n = parsePnat u
        h p (F "[]" (t:ts)) (F ":" [u,v]) = match' [p++[0],p++[1]]
                                                   [t,mkList ts] [u,v]
        h p (F ":" [u,v]) (F "[]" (t:ts)) = match' [p++[0],p++[1]] [u,v]
                                                   [t,mkList ts]
        h _ t u                           = do guard $ bothHidden t u; Just V
        match' (p:ps) (t:ts) (u:us) = do f <- h p t u
                                         g <- match' ps ts us
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

-- used by matchSubs and Esolve > subsumes,simplifyA

onlyRenamed sig t u = just (match sig (frees sig u) t u) &&
                      just (match sig (frees sig t) u t)

-- used by joinTerm

-- matchSubs sig xs t u computes a substitution f that extends u to the subbag 
-- t' of t that matches u. It is assumed that t' is unique. The other values of
-- matchSubs are the list of all (bag) elements of t, the list of positions of 
-- the bag elements of t' within t and a bit denoting whether or not the redex t
-- has been treated as a bag. 

matchSubs
    :: Sig -- ^ sig
    -> [String] -- ^ xs
    -> TermS -- ^ t
    -> TermS -- ^ u
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
                             h ts i  = match sig xs (ts!!i)

-- used by Esolve > simplReducts

-- * Trees with node coordinates

type Sizes = (Int, String -> Int)

sizes0 :: Sizes
sizes0 = (6,const 0)

-- mkSizes font xs takes a font and a list xs of strings and returns the actual
-- font size and a function that maps each string of xs to its width. 

mkSizes :: Canvas -> FontDescription -> [String] -> Request Sizes
mkSizes canv font xs = do
    widths <- mapM (getTextWidth canv font . delQuotes) xs
    let f x = case lookup x $ zip xs widths of
                   Just w -> w
                   _ -> 1
        g x = if x `elem` xs then f x
                             else maximum $ 1:[f y | y <- xs, lg x == lg y]
    size <- Haskell.fromMaybe 0 <$> fontDescriptionGetSize font
    return (h size, truncate . g)
                  where lg = length . delQuotes
                        h n | n < 7     = 6
                            | n < 8     = 7
                            | n < 10    = 8
                            | n < 13    = 10
                            | n < 16    = 13
                            | otherwise = 16

-- used by Epaint and Ecom

nodeWidth :: (String -> Int) -> String -> Int
nodeWidth w a = if isPos a then 4 else w a`div`2

-- coordTree w (hor,ver) p t adds coordinates to the nodes of t such that p is
-- the leftmost-uppermost corner of the smallest rectangle enclosing t.
-- w is the actual node width function, hor is the horizontal space between
-- adjacent subtrees. ver is the vertical space between adjacent tree levels.
-- coordTree cuts off all subtrees whose root labels start with @.

type TermSP = Term (String,Pos)

coordTree :: (String -> Int) -> Pos -> Pos -> TermS -> TermSP
coordTree w (hor,ver) p = alignLeaves . f p
   where alignLeaves (F a ts) = F a $ equalGaps w hor $ map alignLeaves ts
         alignLeaves t        = t
      -- alignLeaves t replaces the leaves of t such that all horizontal gaps
      -- between neighbours become equal.
         f (x,y) (V ('@':_))   = V ("@",(x+nodeWidth w "@",y))
         f (x,y) (V a)         = V (a,(x+nodeWidth w a,y))
         f (x,y) (F ('@':_) _) = F ("@",(x+nodeWidth w "@",y)) []
         f (x,y) (F a [])      = F (a,(x+nodeWidth w a,y)) []
         f (x,y) (F a ts) = if diff <= 0 then ct'
                                         else transTree1 (diff`div`2) ct'
                 where diff = nodeWidth w a-foldT h ct+x
                       ct:cts = map (f (x,y+ver)) ts
                       cts' = transTrees w hor ct cts
                       ct' = F (a,((g (head cts')+g (last cts'))`div`2,y)) cts'
                       g = fst . snd . root
                       h (a,(x,_)) xs = maximum $ x+nodeWidth w a:xs

-- transTrees w hor ct cts orders the trees of ct:cts with a horizontal space of
-- hor units between adjacent trees. transTrees takes into account different 
-- heights of adjacent trees by shifting them to the left or to the right such 
-- that nodes on low levels of a tree may occur below a neighbour with fewer 
-- levels.
transTrees :: (String -> Int) -> Int -> TermSP -> [TermSP] -> [TermSP]
transTrees w hor ct = f [ct]
      where f us (t:ts) = if d < 0 then f (map (transTree1 $ -d) us++[t]) ts
                          else f (us++[transTree1 d t]) $ map (transTree1 d) ts
                       -- f (us++[if d < 0 then t else transTree1 d t]) ts
                          where d = maximum (map h us)+hor 
                                h u = f (+) maximum u-f (-) minimum t
                                     where f = g $ min (height t) $ height u
            f us _      = us
            g _ op _ (V (a,(x,_)))    = h op x a
            g 1 op _ (F (a,(x,_)) _)  = h op x a
            g n op m (F (a,(x,_)) ts) = m $ h op x a:map (g (n-1) op m) ts
            h op x = op x . nodeWidth w

equalGaps :: (String -> Int) -> Int -> [TermSP] -> [TermSP]
equalGaps w hor ts = if length ts > 2 then us++vs else ts
                     where (us,vs) = foldl f ([],[head ts]) $ tail ts
                           f (us,vs) v = if pred v then (us,vs++[v])
                                         else (us++transLeaves w hor vs v,[v])
                           pred (F _ [V (x,_)]) = isPos x
                           pred t               = isLeaf t

transLeaves :: (String -> Int) -> Int -> [TermSP] -> TermSP -> [TermSP]
transLeaves w hor ts t = loop hor
         where loop hor = if x1+w1+hor >= x2-w2 then us else loop $ hor+1 
                    where us = transTrees w hor (head ts) $ tail ts
                          [x1,x2] = map (fst . snd . root) [last us,t]
                          [w1,w2] = map (nodeWidth w . fst . root) [last us,t]

{-|
    @shrinkTree y ver t@ shrinks @t@ vertically such that ver becomes the
    distance between a node and its direct sucessors (0,upb). @y@ is the
    y-coordinate of the root.
-}
shrinkTree
    :: Num a
    => a -- ^ y
    -> a -- ^ ver
    -> Term (b, (c, d)) -- ^ t
    -> Term (b, (c, a))
shrinkTree y _ver (V (a,(x,_)))    = V (a,(x,y))
shrinkTree y ver (F (a,(x,_)) cts) = F (a,(x,y)) $
                                       map (shrinkTree (y+ver) ver) cts

-- | @cTree t ct@ replaces the node entries of @t@ by the coordinates of @ct@.
cTree
    :: Show c
    => Term a -- ^ t
    -> Term (b, c) -- ^ ct
    -> TermS
cTree (F _ ts) (F (_,p) cts) = F (show p) $ zipWith cTree ts cts
cTree (V _) (V (_,p))        = V $ show p
cTree _     (F (_,p) _)      = mkConst p

{-|
    @getSubtree ct x y@ returns the pair @(ct',p)@ consisting of the subtree
    @ct'@ of @ct@ close to position @(x,y)@ and the tree position @p@ of @ct'@
    within @ct@. @getSubtree@ performs breadthfirst search and binary search at
    each tree level.
-}
getSubtree
    :: TermSP -- ^ ct
    -> Int -- ^ x
    -> Int -- ^ y
    -> Maybe ([Int], TermSP) -- ^ (ct', p)
getSubtree ct = getSubtrees [([],ct)]

getSubtrees
    :: [([Int], TermSP)]
    -> Int
    -> Int
    -> Maybe ([Int], TermSP)
getSubtrees pcts@((_,ct):_) x y = if abs (y-y') < 10 then getSubtreeX pcts x
                                  else let f (p,ct) = zipWithSucs (,) p $
                                                                    subterms ct
                                       in getSubtrees (concatMap f pcts) x y
                                  where (_,(_,y')) = root ct
getSubtrees _ _ _               = Nothing

getSubtreeX :: [(a, TermSP)] -> Int -> Maybe (a, TermSP)
getSubtreeX [] _   = Nothing
getSubtreeX pcts x 
    | abs (x - x') < 10 = Just pct
    | x < x' = getSubtreeX (take middle pcts) x
    | otherwise = getSubtreeX (drop (middle + 1) pcts) x
     where middle = length pcts`div`2
           pct@(_,ct) = pcts!!middle
           (_,(x',_)) = root ct

-- * Enumerators

data Align_ a = Compl a a (Align_ a) | Equal_ [a] (Align_ a) | 
                 Ins [a] (Align_ a) | Del [a] (Align_ a) | End [a] 
                deriving (Show,Eq)

parseAlignment :: TermS -> Maybe (Align_ String)
parseAlignment (F "compl" [u,t,v]) = do t <- parseAlignment t
                                        Just $ Compl (showTerm0 u) 
                                                      (showTerm0 v) t
parseAlignment (F "equal" (t:ts))  = do t <- parseAlignment t
                                        Just $ Equal_ (map showTerm0 ts) t
parseAlignment (F "insert" (t:ts)) = do t <- parseAlignment t
                                        Just $ Ins (map showTerm0 ts) t
parseAlignment (F "delete" (t:ts)) = do t <- parseAlignment t
                                        Just $ Del (map showTerm0 ts) t
parseAlignment t                   = do F "end" ts <- Just t
                                        Just $ End $ map showTerm0 ts

-- | @mkAlign global xs ys@ generates __alignments__ of @xs@ and @ys@ by
-- recursive tabulation and optimization.
mkAlign :: Eq a => Bool -> [a] -> [a] -> BoolFun a -> [Align_ a]
mkAlign global xs ys compl = (if global then id else maxima maxmatch)
                              $ align!(0,0)
 where lg1 = length xs; lg2 = length ys
       align = mkArray ((0,0),(lg1,lg2)) $ maxima matchcount . f
         where f (i,j)
                | i == lg1 = if j == lg2 then [End []] else insert
                | j == lg2 = delete
                | x == y = equal ++ append
                | compl x y || compl y x = match ++ append
                | otherwise = append
                         where x = xs!!i; y = ys!!j; ts = align!(i+1,j+1)
                               equal  = map (Equal_ [x]) ts
                               match  = map (Compl x y) ts
                               insert = map (Ins [y]) $ align!(i,j+1)
                               delete = map (Del [x]) $ align!(i+1,j)
                               append = insert++delete

-- | @mkPali xs@ recognizes locally separated __palindromes__ within @xs@ by
-- recursive tabulation and optimization.
mkPali :: Eq a => [a] -> BoolFun a -> [Align_ a]
mkPali xs compl = align!(0,lg)
 where lg = length xs
       align = mkArray ((0,0),(lg,lg)) $ maxima matchcount . f
         where f (i,j)
                | i == j = [End []]
                | i + 1 == j = [End [x]]
                | x == y = equal ++ append
                | compl x y || compl y x = match ++ append
                | otherwise = append
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
                       Del xs t                -> Del xs $ compress t
                       Compl x y t           -> Compl x y $ compress t
                       End _                  -> t

-- | @matchcount t@ computes the number of matches of @t@ of length 1.
matchcount
    :: Align_ a -- ^ t
    -> Int
matchcount t = case t of Compl _ _ t -> matchcount t+1
                         Equal_ _ t -> matchcount t+1
                         Ins _ t -> matchcount t
                         Del _ t -> matchcount t
                         _ -> 0

-- | @maxmatch t@ returns the length of the maximal match of @t@.
maxmatch
    :: Align_ a -- ^ t
    -> Int
maxmatch = f False 0 0 where f False _ n (Compl _ _ t) = f True 1 n t
                             f _ m n (Compl _ _ t)     = f True (m+1) n t
                             f False _ n (Equal_ _ t)  = f True 1 n t
                             f _ m n (Equal_ _ t)      = f True (m+1) n t
                             f _ m n (Ins _ t)         = f False 0 (max m n) t
                             f _ m n (Del _ t)         = f False 0 (max m n) t
                             f _ m n _                        = max m n

{- |
@mkDissects c c' ns b h@ computes all __dissections__ @d@ of @a@ rectangle with
breadth @b@, height @h@ and the cardinality among @ns@ such that all elements of
@d@
satisfy @c@ and @d@ satisfies @c'@.
-}
mkDissects
    :: ((Int,Int,Int,Int) -> Bool) -- ^ c
    -> BoolFun [(Int,Int,Int,Int)] -- ^ c'
    -> [Int] -- ^ n
    -> Int -- ^ b
    -> Int -- ^ h
    -> [TermS] -- ^ d

mkDissects c c' ns b h = map (Hidden . Dissect) $ joinBMap f ns
  where f n = joinBMap (flip (disSucs m) ([(0,0,b,h)],[],[]))
                                         [max 0 (n+1-b-h)..m-1] where m = n-1
        disSucs 0 0 (top,left,inner) =
            [topleft ++ inner | all c topleft && c' inner topleft]
                                       where topleft = top++left
        disSucs n k trip | n == 0    = ds1 -- n = number of splits
                         | k == 0    = ds2 -- k = number of joins
                         | otherwise = ds1 `join` ds2
             where ds1 = maybe [] (disSucs n (k-1)) trip'
                         where trip' = joinHV c c' trip
                   ds2 = joinBMap (disSucs (n-1) k) $ splitV trip++splitH trip

splitV ((0,0,b,h):top,left,inner) = if b < 2 then [] else map f [1..b-1]
                             where f i = ((0,0,i,h):(i,0,b-i,h):top,left,inner)

splitV :: (Enum a, Eq b, Num b, Num a, Ord a) =>
          ([(a, b, a, c)], d, e) -> [([(a, b, a, c)], d, e)]
splitH :: (Enum d, Eq a, Eq b, Num a, Num b, Num e, Num d, Ord d) =>
          ([(a, b, c, d)], [(e, d, c, d)], f)
          -> [([(a, b, c, d)], [(e, d, c, d)], f)]
splitH ((0,0,b,h):top,left,inner) = if h < 2 then [] else map f [1..h-1]
                             where f i = ((0,0,b,i):top,(0,i,b,h-i):left,inner)

joinHV :: (Eq c, Eq d, Num b, Num a, Num c, Num d, Ord b, Ord a) =>
          ((a, b, a, b) -> Bool)
          -> ([(a, b, a, b)] -> [(a, b, a, b)] -> Bool)
          -> ([(a, c, a, b)], [(d, b, a, b)], [(a, b, a, b)])
          -> Maybe ([(a, c, a, b)], [(d, b, a, b)], [(a, b, a, b)])
joinHV c c' ((0,0,b,h):(i,0,b',h'):top,left,inner)
         | h' > h && c r && c' inner [r] = Just ((0,0,b+b',h):top,left,r:inner)
                                           where r = (i,h,b',h'-h)
joinHV c c' ((0,0,b,h):top,(0,i,b',h'):left,inner)
         | b' > b && c r && c' inner [r] = Just ((0,0,b,h+h'):top,left,r:inner)
                                           where r = (b,i,b'-b,h')
joinHV _ _ _                             = Nothing

-- | dissection constraints
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
                                                  Just _ -> False
                                                  _ -> f (rect:rs) rs'
                                     f _rs _ = True
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
dissConstr _ _ (F "sizes" [ns]) = do ns <- parseNats ns; guard $ all (> 1) ns
                                     Just (const True,ns,const2 True)
dissConstr b h (F "True" _)     = do let ns = [2..b*h] 
                                     guard $ notnull ns
                                     Just (const True,ns,const2 True)
dissConstr b h (F "vert" [])    = do let ns = [2..b*h]; f (_,_,b,h) = b <= h 
                                     guard $ notnull ns
                                     Just (f,ns,const2 True)
dissConstr _ _ _                = Nothing

{- |
    @mkPartitions c n@ computes all __nested partitions__ of a list with @n@
    elements, i.e. all trees with @n@ leaves and @outdegree =/= 1@,
    that satisfy @c@.
-}
mkPartitions
    :: (Int -> [Term Int] -> Bool) -- ^ c
    -> Int -- ^ n
    -> TermS
    -> [TermS]
mkPartitions c n = map (mapT show) . mkTrees c n . ht n
          where ht n (F "&" ts)             = minimum $ map (ht n) ts
                ht n (F "|" ts)             = maximum $ map (ht n) ts
                ht n (F "bal" [])           = floor $ logBase 2 $ fromInt n
                ht _ (F "hei" [m]) | just n = get n where n = parseNat m
                ht n _                                = n-1

{- |
    Given a list @s@ with @n@ elements, @mkTrees c n h@ computes the nested
    partitions @ps@ of @s@ such that @ps@ satisfies the constraint @c@, the 
    nesting degree of @ps@ is at most @h@ and, at all nesting levels, each
    subpartition of @ps@ has at least two elements. @mkTrees c n h@ represents
    the partitions as trees.
-}
mkTrees :: (Enum a, Eq a, Num a) =>
           (a -> [Term a] -> Bool) -- ^ c
           -> Int -- ^ n
           -> a -- ^ h
           -> [Term a]
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

-- | partition constraints
partConstr :: TermS -> Maybe (Int -> [Term Int] -> Bool)
partConstr (F "|" ts)      = do fs <- mapM partConstr ts
                                Just (foldl1 h fs)
                                where h f g n ts = f n ts || g n ts
partConstr (F "&" ts)      = do fs <- mapM partConstr ts
                                Just (foldl1 h fs)
                                where h f g n ts = f n ts && g n ts
partConstr (F "alter" [])  = Just (\_ ts -> all (not . isInner) ts ||
                                            all (not . isInner) (evens ts) &&
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

innerNodes :: [Term t] -> [Term t]
innerNodes = filter isInner

isInner :: Term a -> Bool
isInner (F _ (_:_)) = True
isInner _           = False

