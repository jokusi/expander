{-|
Module      : Esolve
Description : TODO
Copyright   : (c) Peter Padawitz, November 2018
                  Jos Kusiek, November 2018
License     : BSD3
Maintainer  : (padawitz peter)@(edu udo)
Stability   : experimental
Portability : portable

Esolve contains:

* a parser and an unparser of signatures
* an unparser for proofs
* the simplifier
* algorithms for performing rewriting, narrowing, induction, coinduction and
* the application of theorems
-}
module Esolve where

import Prelude ()
import qualified Base.Haskell as Haskell
import Base.Gui
import Eterm
import Epaint (hilbshelf,reducePath)

import Data.Array

-- * __String parser__ into signatures and signature maps

signature :: ([String],
              [String],
              [String],
              [String],
              [String],
              [String],
              [(String, [String])])
             -> Parser
                  ([String],
                   [String],
                   [String],
                   [String],
                   [String],
                   [String],
                   [(String, [String])])
signature syms = concat [do key <- oneOf keywords; sigrest key syms,
                         return syms]

sigrest :: String
           -> ([String],
               [String],
               [String],
               [String],
               [String],
               [String],
               [(String, [String])])
           -> Parser
                ([String],
                 [String],
                 [String],
                 [String],
                 [String],
                 [String],
                 [(String, [String])])
sigrest key syms =
    concat
        [do key <- oneOf keywords; sigrest key syms,
         do x <- sigWord
            let [ps',cps',cs',ds',fs'] = map (`minus1` x) [ps,cps,cs,ds,fs]
                f s = s `join1` x
            case key of
                "specs:"      -> sigrest key (f specs,ps,cps,cs,ds,fs,hs)    
                "preds:"      -> sigrest key (specs,f ps,cps',cs',ds',fs',hs)
                "copreds:"    -> sigrest key (specs,ps',f cps,cs',ds',fs',hs)
                "constructs:" -> sigrest key (specs,ps',cps',f cs,ds',fs',hs)
                "defuncts:"   -> sigrest key (specs,ps',cps',cs',f ds,fs',hs)
                "fovars:"     -> sigrest key (specs,ps',cps',cs',ds',f fs,hs)
                "hovars:"     -> do es <- instances syms
                                    sigrest key (specs,ps,cps,cs,ds,fs,
                                                 updAssoc hs x es),
             return syms]
     where (specs,ps,cps,cs,ds,fs,hs) = syms

instances :: (t, [String], [String], [String], [String], t1, t2)
          -> Parser [String]
instances syms = concat [do symbol "{"; es <- p; symbol "}"; return es,
                            return []]
                 where (_,ps,cps,cs,ds,_,_) = syms
                       p = do e <- oneOf $ ps++cps++cs++ds
                              concat [do symbol ","; es <- p; return $ e:es,
                                      return [e]]

sigWord :: Parser String
sigWord = token $ some (sat item (`notElem` "{\t\n ")) ++ infixWord

keywords :: [String]
keywords = words "specs: preds: copreds: constructs: defuncts: fovars: hovars:"

sigMap :: (String -> String, [String])
       -> Sig -> Sig -> Parser (String -> String, [String])
sigMap p@(f,xs) sig sig' = concat [act relational, act functional,
                                   act isFovar, act isHovar, return p]
                        where act g = do (x,y) <- assignment (g sig) $ g sig'
                                         sigMap (upd f x y,xs`join1`x) sig sig'

assignment :: (String -> Bool) -> (String -> Bool) -> Parser (String, String)
assignment c d = do x <- sat sigWord c; symbol "->"
                    y <- sat sigWord d; return (x,y)

-- * __Signature__ and __signature map parser__ into strings

showSignature :: ([String],[String],[String],[String],[String],Pairs String)
                 -> String -> String
showSignature (ps,cps,cs,ds,fs,hs) = showSymbols "preds:      " ps .
                                       showSymbols "copreds:    " cps .
                                     showSymbols "constructs: " cs .
                                     showSymbols "defuncts:   " ds .
                                     showSymbols "fovars:     " fs .
                                     showHovars hs

showSymbols :: String -> [String] -> String -> String
showSymbols _ []   = id 
showSymbols init s = ((splitStrings 12 85 init s ++ "\n") ++) 

showHovars :: Show t => [(String, [t])] -> String -> String
showHovars []          = id
showHovars [(x,[])]    = ("hovars:     " ++) . (x ++) . (' ':)
showHovars [(x,es)]    = ("hovars:     " ++) . (x ++) . showInstances es 
showHovars ((x,[]):hs) = showHovars hs . (x ++) . (' ':)
showHovars ((x,es):hs) = showHovars hs . (x ++) . showInstances es

showInstances :: Show a => a -> String -> String
showInstances es = ('{':) . (init (tail (filter (/= '\"') (show es))) ++) .
                   ("} " ++)

showSignatureMap :: (String -> String, [String]) -> String -> String
showSignatureMap (f,[x]) str  = x++" -> "++f x++str
showSignatureMap (f,x:xs) str = x++" -> "++f x++"\n"++
                                 showSignatureMap (f,xs) str
showSignatureMap _ str        = str

-- * __Evaluation__

-- * signature for arithmetic expressions

data Arith a = Arith
    { parseA :: TermS -> Maybe a
    , aZero, one :: a
    , inv :: a -> a
    , aPlus, aMinus, aTimes, aDiv, aMin, aMax :: a -> a -> a
    }

-- * The Arith-algebras of integer numbers, real numbers, linear functions and 
-- binary relations

intAlg :: Arith Int
intAlg = Arith
    { parseA = parseInt
    , aZero = 0
    , one = 1
    , inv = \i -> -i
    , aPlus = (+)
    , aMinus = (-)
    , aTimes = (*)
    , aDiv = div
    , aMin = min
    , aMax = max
    }

realAlg :: Arith Double
realAlg = Arith
    { parseA = parseReal
    , aZero = 0
    , one = 1
    , inv = \r -> -r
    , aPlus = (+)
    , aMinus = (-)
    , aTimes = (*)
    , aDiv = (/)
    , aMin = min
    , aMax = max
    }

linAlg :: Arith LinEq
linAlg = Arith
    { parseA = parseLin
    , aZero = ([],0)
    , one = ([],1)
    , inv = mulLin ((-1)*)
    , aPlus = addLin
    , aMinus = subLin
    , aTimes = \f (_,a) -> mulLin (*a) f
    , aDiv = \f (_,a) -> mulLin (/a) f
    , aMin = \_ _ -> ([],0)
    , aMax = \_ _ -> ([],1)
    }

relAlg :: Sig -> Arith [(TermS,TermS)]
relAlg sig = Arith
    { parseA = parseRel $ states sig
    , aZero = []
    , one = [(x,x) | x <- states sig]
    , inv = minus pairs
    , aPlus = join
    , aMinus = minus
    , aTimes = \ps qs -> [p | p@(x,y) <- pairs, any ((== x) . fst) ps,
                                              any ((== y) . snd) qs]
    , aDiv = meet
    , aMin = min
    , aMax = max
    }
             where pairs = prod2 (states sig) (states sig)
                   
-- * generic Arith-interpreter

foldArith :: Eq a => Arith a -> TermS -> Maybe a
foldArith alg = f
 where f (F "-" [t])      = do a <- f t; Just $ inv alg a
       f (F "+" [t,u])    = do a <- f t; b <- f u; Just $ aPlus alg a b
       f (F "sum" [F x ts]) | collector x = do as <- mapM f ts; Just $ sum_ as
       f (F "-" [t,u])    = do a <- f t; b <- f u; Just $ aMinus alg a b
       f (F "*" [t,u])    = do a <- f t; b <- f u; Just $ aTimes alg a b
       f (F "product" [F x ts]) | collector x
                          = do as <- mapM f ts; Just $ prod as
       f (F "**" [t,u])   = do a <- f t; n <- parseNat u
                               Just $ prod $ replicate n a
       f (F "/" [t,u])    = do a <- f t; b <- f u; guard $ b /= aZero alg
                               Just $ aDiv alg a b
       f (F "min" [t,u])  = do a <- f t; b <- f u; Just $ aMin alg a b
       f (F "max" [t,u])  = do a <- f t; b <- f u; Just $ aMax alg a b
       f (F "min" [F x ts]) | collector x
                          = do as@(_:_)<- mapM f ts; Just $ foldl1 (aMin alg) as
       f (F "max" [F x ts]) | collector x
                          = do as@(_:_)<- mapM f ts; Just $ foldl1 (aMax alg) as
       f t                    = parseA alg t
       sum_ = foldl (aPlus alg) (aZero alg)
       prod = foldl (aTimes alg) (one alg)

-- * a signature for state formulas

data Modal a label = Modal
    { true, false :: a
    , modalNeg :: a -> a
    , modalOr, modalAnd :: a -> a -> a
    , ex,ax,xe,xa :: a -> a
    , dia,box,aid,xob :: label -> a -> a
    }

-- * the Modal-algebra of state sets

ctlAlg :: Sig -> Modal [Int] Int
ctlAlg sig = Modal
  { true  = sts
  , false = []
  , modalNeg   = minus sts 
  , modalOr    = join
  , modalAnd   = meet
  , ex    = imgsShares sts $ f (sig&trans) (sig&transL)
  , ax    = imgsSubset sts $ f (sig&trans) (sig&transL)
  , xe    = imgsShares sts $ f (parents sig) (parentsL sig)
  , xa    = imgsSubset sts $ f (parents sig) (parentsL sig)
  , dia   = imgsShares sts . flip (g (sig&transL))
  , box   = imgsSubset sts . flip (g (sig&transL))
  , aid   = imgsShares sts . flip (g $ parentsL sig)
  , xob   = imgsSubset sts . flip (g $ parentsL sig)
  }
              where sts = indices_ (sig&states)
                    f trans transL i = join (trans!!i) $ joinMap (g transL i) 
                                                       $ indices_ (sig&labels)
                    g transL i k = transL!!i!!k

-- | the interpreter of state formulas in ctlAlg
type States = Maybe [Int]

foldModal :: Sig -> TermS -> States
foldModal sig = f $ const Nothing where
           alg = ctlAlg sig
           f :: (String -> States) -> TermS -> States
           f g (F x []) | just a       = a where a = g x
           f _ (F "true" [])           = Just (alg&true)
           f _ (F "false" [])          = Just (alg&false)
           f g (F "not" [t])           = do a <- f g t; Just $ (alg&modalNeg) a
           f g (F "\\/" [t,u])         = do a <- f g t; b <- f g u
                                            Just $ (alg&modalOr) a b
           f g (F "/\\" [t,u])         = do a <- f g t; b <- f g u
                                            Just $ (alg&modalAnd) a b
           f g (F "`then`" [t,u])      = do a <- f g t; b <- f g u
                                            Just $ (alg&modalOr) ((alg&modalNeg) a) b
           f g (F "EX" [t])            = do a <- f g t; Just $ (alg&ex) a
           f g (F "AX" [t])            = do a <- f g t; Just $ (alg&ax) a
           f g (F "XE" [t])            = do a <- f g t; Just $ (alg&xe) a
           f g (F "XA" [t])            = do a <- f g t; Just $ (alg&xa) a
           f g (F "<>" [lab,t])        = do a <- f g t; k <- searchL lab
                                            Just $ (alg&dia) k a
           f g (F "#" [lab,t])         = do a <- f g t; k <- searchL lab
                                            Just $ (alg&box) k a
           f g (F "><" [lab,t])        = do a <- f g t; k <- searchL lab
                                            Just $ (alg&aid) k a
           f g (F "##" [lab,t])        = do a <- f g t; k <- searchL lab
                                            Just $ (alg&xob) k a
           f g (F ('M':'U':' ':x) [t]) = fixptM subset (step g x t) (alg&false)
           f g (F ('N':'U':' ':x) [t]) = fixptM supset (step g x t) (alg&true)
           f _ (F "$" [at,lab])        = do i <- searchA at; k <- searchL lab
                                            Just $ (sig&valueL)!!i!!k
           f _ at                      = do
                                          i <- searchA at; Just $ (sig&value)!!i

           searchA,searchL :: Term String -> Maybe Int
           searchA at  = search (== at) (sig&atoms)
           searchL lab = search (== lab) (sig&labels)

           step :: (String -> States) -> String -> TermS -> [Int] -> States
           step g x t a = f (upd g x $ Just a) t

{-h :: (TermS -> TermS) -> [Int]
  h app = getIndices (isTrue . simplifyIter sig . app) (sig&states)-}

-- | partial evaluation
evaluate :: Sig -> TermS -> TermS
evaluate sig = eval
   where eval (F "==>" [t,u])              = mkImpl (eval t) $ eval u
         eval (F "<==>" [t,u])             = F "<==>" [eval t,eval u]
         eval (F "===>" [t,u])             = mkImpl (eval t) $ eval u
         eval (F "<===" [t,u])             = mkImpl (eval u) $ eval t
         eval (F "&" ts)                          = mkConjunct $ map eval ts
         eval (F "|" ts)                   = mkDisjunct $ map eval ts
         eval (F ('A':'n':'y':x) [t])      = mkAny (words x`meet`frees sig u) u
                                             where u = eval t
         eval (F ('A':'l':'l':x) [t])      = mkAll (words x`meet`frees sig u) u
                                             where u = eval t
         eval (F "Not" [t])                = mkNot sig $ eval t
         eval (F "id" [t])                  = eval t
         eval (F "ite" [t,u,v]) | isTrue t = eval u
                                | isFalse t = eval v
         eval (F x p@[_,_]) | arithmetical x && just ip = mkRel $ get ip
                            | arithmetical x && just rp = mkRel $ get rp
                            | arithmetical x && just fp = mkRel $ get fp
                            | arithmetical x && just sp = mkRel $ get sp
            where ip = mapM (parseA intAlg) p; rp = mapM (parseA realAlg) p
                  fp = mapM (parseA linAlg) p; sp = mapM (parseA $ relAlg sig) p
                  mkRel [a,b] = mkConst $ case x of "="  -> a==b; "=/=" -> a/=b
                                                    "<=" -> a<=b; ">="  -> a>=b
                                                    "<"  -> a<b;  ">"   -> a>b
         eval (F "=" [t,u])   = evalEq t u
         eval (F "=/=" [t,u]) = evalNeq t u
         eval (F "<+>" ts)    = mkSum $ map eval ts
         eval (F x [F "()" ts]) | not $ collector x || binder x || projection x
                         || x `elem` words "~ List Value sat string true false"
                              = eval $ F x ts
         eval (F "length" [F x ts]) | collector x 
                              = mkConst $ length ts
         eval (F "size" [F "{}" ts])
                              = mkConst $ length $ mkSet ts
         eval (F "$" [t,u])   = apply (eval t) $ eval u
         eval t | just i      = mkConst $ get i
                | just r      = mkConst $ get r
                | just f      = mkLin $ get f
                | just s      = mkList $ map pair $ sort (<) $ get s
                                where i = foldArith intAlg t
                                      r = foldArith realAlg t
                                      f = foldArith linAlg t
                                      s = foldArith (relAlg sig) t
                                      pair (x,y) = F "()" [x,y]
         eval (F x ts)        = F x $ map eval ts
         eval t               = t
         
         evalEq t u | eqTerm t u = mkTrue
         evalEq (F "{}" ts) (F "{}" us)
                    | just qs && just rs
                        = mkConst $ eqSet (==) (get qs) $ get rs
                                           where qs = mapM parseReal ts
                                                 rs = mapM parseReal us
         evalEq t (F "suc" [u]) | just n = evalEq (mkConst $ get n-1) u
                                             where n = parsePnat t
         evalEq (F "suc" [u]) t | just n = evalEq u (mkConst $ get n-1)
                                             where n = parsePnat t
         evalEq (F "[]" (t:ts)) (F ":" [u,v]) = mkConjunct 
                                               [evalEq t u,evalEq (mkList ts) v]
         evalEq (F ":" [u,v]) (F "[]" (t:ts)) = mkConjunct 
                                               [evalEq u t,evalEq v $ mkList ts]
         evalEq (F x ts) (F y us) | all (isConstruct sig) [x,y] =
                                       if x == y && length ts == length us 
                                       then mkConjunct $ zipWith evalEq ts us
                                       else mkFalse
         evalEq t u = mkEq (eval t) $ eval u
                                   
         evalNeq t u | eqTerm t u = mkFalse
         evalNeq (F "{}" ts) (F "{}" us)
            | just qs && just rs
                    = mkConst $ not $ eqSet (==) (get qs) $ get rs
                                   where qs = mapM parseReal ts
                                         rs = mapM parseReal us
         evalNeq t (F "suc" [u]) | just n = evalNeq (mkConst $ get n-1) u
                                              where n = parsePnat t
         evalNeq (F "suc" [u]) t | just n = evalNeq u (mkConst $ get n-1)
                                              where n = parsePnat t
         evalNeq (F "[]" (t:ts)) (F ":" [u,v]) = 
                                  mkDisjunct [evalNeq t u,evalNeq (mkList ts) v]
         evalNeq (F ":" [u,v]) (F "[]" (t:ts)) = 
                                  mkDisjunct [evalNeq u t,evalNeq v $ mkList ts]
         evalNeq (F x ts) (F y us) | all (isConstruct sig) [x,y] =
                                      if x == y && length ts == length us 
                                      then mkDisjunct $ zipWith evalNeq ts us
                                      else mkTrue
         evalNeq t u = mkNeq (eval t) $ eval u

-- * __Subsumption__

-- | subsumes is used by simplifyF, implToConc (see below) and subsumeSubtrees
-- (see Ecom).
subsumes :: Sig -> TermS -> TermS -> Bool
subsumes sig = h
  where h t u             | eqTerm t u        = True
        h (F "Not" [t]) (F "Not" [u])         = h u t
        h (F "==>" [t,u]) (F "==>" [v,w])     = h v t && h u w
        h t (F "|" us)    | any (h t) us      = True
        h (F "|" ts) u    | all (flip h u) ts = True 
        h t (F "&" us)    | all (h t) us      = True
        h (F "&" ts) u    | any (flip h u) ts = True 
        h (F ('A':'n':'y':x) [t]) (F ('A':'n':'y':y) [u]) 
                   | perm (words x) ys ys t u = True where ys = words y
        h (F ('A':'l':'l':x) [t]) (F ('A':'l':'l':y) [u]) 
                   | perm (words x) ys ys t u = True where ys = words y
        h (F ('A':'n':'y':x) [t]) u | noFrees (words x) u && h t u = True
        h t (F ('A':'l':'l':x) [u]) | noFrees (words x) t && h t u = True
        h t (F ('A':'n':'y':x) [u]) | g x u t = True
        h (F ('A':'l':'l':x) [t]) u | g x t u = True
        h (F "&" ts) (F ('A':'n':'y':x) [u])  | any (g x u) $ sub mkConjunct ts  
                                               = True
        h (F ('A':'l':'l':x) [t]) (F "|" us)  = any (g x t) $ sub mkDisjunct us
        h _ _                                 = False
        g x t u                               = just $ match sig (words x) u t
        perm xs ys zs t u = h (renameFree (fold2 upd id xs zs) t) u ||
                            ys /= zs' && perm xs ys zs' t u
                            where zs' = nextPerm zs
        sub f ts = [f $ map (ts!!) ns | ns <- subsets $ length ts]
        noFrees xs = disjoint xs . frees sig
        
-- * __Simplification__

simplifyIter :: Sig -> TermS -> TermS
simplifyIter sig = pr1 . simplifyLoop sig BFP 100

sapply :: Sig -> TermS -> TermS -> TermS
sapply sig t  = simplifyIter sig . apply t

sapplyL :: Sig -> TermS -> [TermS] -> TermS
sapplyL sig t = simplifyIter sig . applyL t

reduceString :: Sig -> String -> Maybe String
reduceString sig t = do t <- parse (term sig) t
                        Just $ showTerm0 $ simplifyIter sig t

-- applyDrawFun is used by showSubtreePicts, showTreePicts and showTransOrKripke
-- (see Ecom).

applyDrawFun :: Sig -> String -> String -> [TermS] -> [TermS]
applyDrawFun _ "" _       = id
applyDrawFun _ "text" ""  = id
applyDrawFun _ "text" str = map $ add . addToPoss [0]
                            where add t = mkSum [t,F "widg" [F "red" [F "frame"
                                           [F "black" [F "text" [leaf str]]]]]]
applyDrawFun sig draw _   = map $ wtree . pr1 . simplifyLoop sig BFP 11
                                        . F draw . single . addToPoss [0]
     where wtree (F "$" [F "wtree" [f],t]) = g t
             where g (F x ts) | just u  = F "widg" $ vs++[sapply sig f $ get u]
                              | True    = F x vs where vs = map g ts
                                                       u = parse (term sig) x
                   g t@(V x)  | isPos x = mkPos $ tail $ getPos x
                              | True    = F "widg" [sapply sig f t]
                   g t = t
           wtree (F "$" [F "wtree" [m,f],t]) | just m' = g t pt
               where m' = parsePnat m
                     order = case get m' of 1 -> levelTerm; 2 -> preordTerm
                                            3 -> heapTerm;  _ -> hillTerm
                     (pt,n) = order black (const id) t
                     h t k = sapplyL sig f [t,mkConst k,mkConst n]
                     g (F x ts) (F k us) | just u = F "widg" $ vs++[h (get u) k] 
                                         | True   = F x vs
                                                   where vs = zipWith g ts us
                                                         u = parse (term sig) x
                     g t@(V x) (F k _) | isPos x = mkPos $ tail $ getPos x
                                       | True    = F "widg" [h t k]
                     g t _ = t
           wtree t = simplifyIter sig t

-- wtree(f)(t) replaces each subgraph x(t1,..,tm) of t by the subgraph 
-- widg(t1,...,tm,f(x)).

-- wtree(i,f)(t) replaces each subtree x(t1,...,tm) of t by the subtree 
-- widg(t1,...,tm,f(x,k,n)) where k is the position of x within t with respect
-- to level order (i=1), prefix order (i=2), heap order (i=3) or hill order 
-- (i>3) and n is the maximum of positions of t.

-- If the interpreter widgetTree is applied to the resulting term, node x is 
-- replaced by the widget f(x) resp. f(x,k,n).

data Strategy = DF | BF | BFP deriving Show

-- simplifyLoop sig depthfirst m t applies simplification rules at most m times
-- to the maximal subtrees of t and returns the simplified tree together with 
-- the number of actually applied steps. 
-- simplifyLoop is used by applyDrawFun, simplifyIter, simplifyA lambda 
-- (see here), simplify' and simplifySubtree (see Ecom).
simplifyLoop :: Sig -> Strategy -> Int -> TermS -> (TermS,Int,Bool)
simplifyLoop sig strat m t = loop 0 m [t] where
  loop k m ts = if m == 0 then (t,k,False)
                else case f (simplifyOne sig) t of
                          Just t -> loop' t
                          _ -> case f (expandFix sig) t of Just t -> loop' t
                                                           _ -> (t,k,False)
                where t = head ts
                      loop' t = if just $ search (eqTerm t) ts then (t,k,True)
                                else loop (k+1) (m-1) $ t:ts

  f :: (TermS -> [Int] -> Maybe TermS) -> TermS -> Maybe TermS
  f g t = case strat of DF -> modifyDF [] t                     -- depthfirst
                        BF -> modifyBF [[]] [t]                 -- breadthfirst
                        _  -> do let u = modifyBFP t [] t       -- parallel
                                 guard $ t /= u; Just u
         where modifyDF p u = concat $ g t p:zipWithSucs modifyDF p (subterms u)
               modifyBF [] _  = Nothing
               modifyBF ps us = concat (map (g t) ps) ++ modifyBF qs vs
                   where (qs,vs) = unzip $ concat $ zipWith (zipWithSucs (,)) ps
                                                  $ map subterms us
               modifyBFP t p u = case g t p of
                                      Just t -> t
                                      _ -> fold2 modifyBFP t (succsInd p ts) ts
                                           where ts = subterms u

-- simplifyOne sig t p applies the first applicable simplification rule to the
-- subterm of t at position p.
-- expandFix sig t p expands a fixpoint abstraction at position p of t if there
-- is any.
-- simplifyOne and expandFix are used by simplifyLoop (see above).
-- simplifyOne is also used by simplifyPar (see Ecom).

simplifyOne,expandFix :: Sig -> TermS -> [Int] -> Maybe TermS
simplifyOne sig t p = do guard $ isF redex1
                         if reduct /= redex1 
                         then Just $ replace1 t p $ mapT g reduct
                         else concat [do reduct <- simplifyGraph sig redex1
                                         Just $ replace1 t p $ mapT g reduct,
                                      do reduct <- simplifyUser sig redex1
                                         Just $ replace1 t p $ mapT g reduct,
                                      do guard $ polarity True t p 
                                         reduct <- simplCoInd sig redex2
                                         Just $ replace1 t p $ mapT g reduct,
                                      do reduct <- simplifyF sig redex2
                                         Just $ replace1 t p $ mapT g reduct]
                      where redex1 = mapT block $ getSubterm1 t p
                            reduct = evaluate sig redex1
                            redex2 = mapT block $ expand0 t p
                            block x = if blocked sig x then "BLOCK"++x else x
                            g ('B':'L':'O':'C':'K':x) = x
                            g x                            = x

expandFix sig t p = do guard $ not $ (sig&blocked) "fixes"
                       F x [u] <- Just redex; guard $ isFix x
                       let _:xs = words x
                           f i = F ("get"++show i) [redex]
                           sub = case xs of [x] -> redex `for` x
                                            _ -> map f (indices_ xs)`forL` xs
                       Just $ replace1 t p $ u>>>sub
                    where redex = expand0 t p

simplifyGraph,simplifyUser :: Sig -> TermS -> Maybe TermS

simplifyGraph _ (F "$" [F "mapG" [f@(F _ ts)],F x us]) | collector x =
                               Just $ F x $ if null ts then map (apply f) us
                                                       else map g $ indices_ us
                               where g 0 = apply f $ vs!!0
                                     g i = apply (mkPos [0,0]) $ vs!!i
                                     vs = changeLPoss p q us
                                     p i = [1,i]; q i = [i,1]

simplifyGraph _ (F "$" [F "replicate" [t],u]) | just n =
            jList $ changePoss [1] [0] u:replicate (get n-1) (mkPos [0])
                   where n = parsePnat t

simplifyGraph _ (F "concat" [F "[]" ts]) | all isList ts =
                          jList $ concatMap (subterms . f) ts
                              where subs i = subterms $ ts!!i
                                    f t = foldl g t $ indices_ ts
                                    g t i = foldl (h i) t $ indices_ $ subs i
                                    h i t k = changePoss [0,i,k] [lg (i-1)+k] t
                                    lg (-1) = 0
                                    lg i    = lg (i-1) + length (subs i)

simplifyGraph sig (F "$" [F "concRepl" [t],u@(F "[]" us)]) | just n =
                   simplifyGraph sig $ F "concat" [addToPoss [0] $ mkList vs]
                   where n = parsePnat t
                         vs = changePoss [1] [0] u:replicate (get n-1)
                                                 (mkList $ map f $ indices_ us)
                         f i = mkPos [0,i]

simplifyGraph _ (F "$" [F "**" [f@(F _ ts),t],u]) | just n =
                 Just $ if null ts then iterate (apply f) v!!m
                        else apply first $ iterate (apply $ mkPos [0]) v!!(m-1)
                 where n = parsePnat t
                       m = get n
                       first = changePoss [0,0] [0] f
                       v = changePoss [1] (replicate m 1) u

simplifyGraph sig (F "++" ts) = simplifyGraph sig $ F "concat" [mkList ts]

simplifyGraph _ (F ":" [t,F "[]" ts]) = jList $ t:changeLPoss p q ts
                                        where p i = [1,i]; q i = [i+1]

simplifyGraph _ (F "$" [F x [n],F "[]" ts])
           | x `elem` words "cantor hilbert mirror snake transpose" && just k
                         = jList $ f (get k) $ changeLPoss p single ts
                           where k = parsePnat n
                                 f = case head x of 'c' -> cantorshelf
                                                    'h' -> hilbshelf
                                                    'm' -> mirror
                                                    's' -> snake
                                                    _ -> transpose
                                 p i = [1,i]

simplifyGraph _ (F x [F "bool" [t],F "bool" [u]]) | isEq x
                         = Just $ if x == "=/=" then F "Not" [v] else v
                           where v = F "<==>" [changePoss [0,0] [0] t,
                                               changePoss [1,0] [1] u]

simplifyGraph _ (F "permute" (t:ts)) | isObdd t =
                if n == 0 then Just t
                else if null ts
                     then perm [t,changePoss [0] [1] t,mkConsts [0..n-1]]
                     else do [u,ns] <- Just ts; ns <- parseNats ns
                             let permute s = map (s!!) ns
                                 v = addToPoss [1] $ binsToObddP (n-1) ns
                                                   $ map permute $ funToBins fn
                             perm [t,if size v < size u then v else u,
                                   mkConsts $ nextPerm ns]
                where fn@(_,n) = obddToFun $ drop0FromPoss t
                      perm = Just . F "permute"

simplifyGraph _ _ = Nothing

-- | apply user-defined simplification rules
simplifyUser sig t | notnull ts = Just $ mkSum ts
                                  where ts = simplReducts sig False t

simplifyUser sig (F x ts@(_:_)) | notnull us =
                               Just $ applyL (mkSum us) $ map (mapT f) ts
                               where us = simplReducts sig False $ F x []
                                     f x = if isPos x && notnull p 
                                           then mkPos0 $ head p+1:tail p else x
                                           where p = getPos x

simplifyUser sig (F "$" [t,u]) | notnull ts = Just $ apply (mkSum ts) u
                                            where ts = simplReducts sig False t

simplifyUser _ _ = Nothing

simplCoInd,simplifyF,simplifyA,simplifyS :: Sig -> TermS -> Maybe TermS

-- remove in/equational summands or factors

simplCoInd sig t | not (sig&safeEqs) && just u = u where u = removeEq sig True t

-- apply fixpoint induction to an inequation or an implication

simplCoInd _ (F "<=" [F x [t],u])
    | leader x "mu" = Just $ F "<=" [t>>>forL us xs,u]
                           where _:xs = words x; us = mkGets xs u

simplCoInd _ (F "<=" [F "$" [F x [t],arg],u])
    | leader x "mu" && null (subterms arg) =
                             Just $ mkAll [root arg] 
                                  $ F "<=" [apply (t>>>forL us xs) arg,u]
                            where _:xs = words x
                                  us = mkGets xs $ F "fun" [arg,u]

simplCoInd sig (F "`then`" [F x [t],u])
    | leader x "MU" && monotone sig xs t =
                               Just $ F "`then`" [t>>>forL us xs,u]
                            where _:xs = words x; us = mkGets xs u

simplCoInd sig (F "==>" [F "$" [F x [t],arg],u])
    | leader x "MU" && null (subterms arg) && monotone sig xs t =
                             Just $ mkAll [root arg] 
                                 $ mkImpl (apply (t>>>forL us xs) arg) u
                            where _:xs = words x
                                  us = mkGets xs $ F "rel" [arg,u]

-- apply coinduction to an inequation or an implication

simplCoInd _ (F "<=" [u,F x [t]])
    | leader x "nu" = Just $ F "<=" [t>>>forL us xs,u]
                           where _:xs = words x; us = mkGets xs u

simplCoInd _ (F "<=" [u,F "$" [F x [t],arg]])
    | leader x "nu" && null (subterms arg) =
                             Just $ mkAll [root arg] 
                                  $ F "<=" [u,apply (t>>>forL us xs) arg]
                            where _:xs = words x
                                  us = mkGets xs $ F "fun" [arg,u]

simplCoInd sig (F "`then`" [u,F x [t]])
    | leader x "NU" && monotone sig xs t =
                                 Just $ F "`then`" [u,t>>>forL us xs]
                            where _:xs = words x; us = mkGets xs u

simplCoInd sig (F "==>" [u,F "$" [F x [t],arg]])
    | leader x "NU" && null (subterms arg) && monotone sig xs t = 
                             Just $ mkAll [root arg] 
                                 $ mkImpl u $ apply (t>>>forL us xs) arg
                            where _:xs = words x
                                  us = mkGets xs $ F "rel" [arg,u]

simplCoInd _ _ = Nothing

simplifyF sig (F "tree" [F x []]) = parse (term sig) x

simplifyF sig (F "subst" [t,u,v]) | isVar sig x = Just $ v>>>for t x
                                                   where x = root u
                           
simplifyF sig (F "mergeV" [t]) = Just $ collapseVars sig t

-- reduce equivalences

simplifyF sig (F "<==>" [t,u]) | isTrue t         = Just u
                               | isTrue u         = Just t
                               | isFalse t        = Just $ mkNot sig u
                               | isFalse u        = Just $ mkNot sig t
                               | subsumes sig t u = Just $ mkImpl u t
                               | subsumes sig u t = Just $ mkImpl t u

-- try subsumption and replace non-constructor-headed subterms by in/equivalent
-- constructor-headed ones

simplifyF _ (F "==>" [t])     = Just t
simplifyF sig (F "==>" [t,u])
           | subsumes sig t u = Just mkTrue
           | just pair1     = Just $ mkImpl (mkConjunct ts1) $ mkDisjunct us1
           | just pair2     = Just $ mkImpl (mkConjunct ts2) $ mkDisjunct us2
                                where (ts,us) = (mkFactors t,mkSummands u)
                                      pair1 = replaceTerms sig "=" ts us
                                      pair2 = replaceTerms sig "=/=" us ts
                                      (ts1,us1) = get pair1
                                      (us2,ts2) = get pair2

-- move quantifiers out of an implication

simplifyF sig c@(F "==>" [t,u]) | b = Just result
           where (result,b) = moveAny [] t u False
                 moveAny zs (F ('A':'n':'y':x) [t]) u _ = 
                         moveAll (zs++map f xs) (renameAll f t) u True
                         where xs = words x
                               ys = sigVars sig u
                               f = getSubAwayFrom xs ys c
                 moveAny zs t u b = moveAll zs t u b
                 moveAll zs t (F ('A':'l':'l':x) [u]) _ = 
                         (mkAll (zs++map f xs) $ mkImpl t $ renameAll f u,True)
                         where xs = words x
                               ys = sigVars sig t
                               f = getSubAwayFrom xs ys c
                 moveAll zs t u b = (mkAll zs $ mkImpl t u,b)

-- move universal quantifiers out of a disjunction

simplifyF sig c@(F "|" ts) | b = Just result
         where (result,b) = move [] ts [] False
               move zs (F ('A':'l':'l':x) [t]:ts) us _ = 
                       move (zs++map f xs) ts (renameAll f t:us) True
                       where xs = words x
                             ys = joinMap (sigVars sig) $ ts++us
                             f = getSubAwayFrom xs ys c
               move zs (t:ts) us b = move zs ts (t:us) b
               move zs _ us b      = (mkAll zs $ mkDisjunct us,b)

-- restrict a disjunction to its maximal summands with respect to subsumption 
-- and replace non-constructor-headed subterms by inequivalent 
-- constructor-headed ones

simplifyF sig (F "|" ts) | just t = t
                             | just p = Just $ mkDisjunct $ fst $ get p
                                    where t = subsumeDisj sig ts []
                                          p = replaceTerms sig "=/=" ts []

simplifyF _ (F "$" [F "any" [p],F x ts]) | collector x =
                                            Just $ mkDisjunct $ map (apply p) ts

-- modus ponens

simplifyF _ (F "&" ts) | notnull is = Just $ mkConjunct $ map f $ indices_ ts
                                where is = [i | i <- searchAll isImpl ts, 
                                                let F _ [prem,_] = ts!!i,
                                                      prem `elem` context i ts]
                                      f i = if i `elem` is then conc else ts!!i
                                            where F _ [_,conc] = ts!!i
                                 
-- move existential quantifiers out of a conjunction

simplifyF sig c@(F "&" ts) | b = Just result
         where (result,b) = move [] ts [] False
               move zs (F ('A':'n':'y':x) [t]:ts) us _ =
                           move (zs++map f xs) ts (renameAll f t:us) True
                       where xs = words x
                             ys = joinMap (sigVars sig) $ ts++us
                             f = getSubAwayFrom xs ys c
               move zs (t:ts) us b = move zs ts (t:us) b
               move zs _ us b      = (mkAny zs $ mkConjunct us,b)

-- restrict a conjunction to its minimal factors with respect to subsumption and
-- replace non-constructor-headed subterms by equivalent constructor-headed 
-- ones

simplifyF sig (F "&" ts) | just t = t
                            | just p = Just $ mkConjunct $ fst $ get p
                                      where t = subsumeConj sig ts []
                                            p = replaceTerms sig "=" ts []
                                                   
simplifyF _ (F "$" [F "all" [p],F x ts]) | collector x =
                                        Just $ mkConjunct $ map (apply p) ts
                                           
simplifyF _ (F "$" [F "allany" [r],F "()" [F x ts,F y us]])
                    | collector x && collector y = Just $ mkConjunct $ map q ts
                                          where q t = mkDisjunct $ map (f t) us
                                                f t u = applyL r [t,u]


simplifyF _ (F "$" [F "prodE" ts,u])  = Just $ mkTup $ map (flip apply u) ts

simplifyF _ (F "$" [F "/\\" [t,u],v]) = Just $ F "&" [apply t v,apply u v]

simplifyF _ (F "$" [F "\\/" [t,u],v]) = Just $ F "|" [apply t v,apply u v]

{-
simplifyF _ (F "$" [F "&" (t:ts),u])  = Just $ F "&" $ apply t u:ts

simplifyF _ (F "$" [F "|" ts,t])      = Just $ F "|" $ map (flip apply t) ts

simplifyF (F x ts) _ | x `elem` words "\\/ /\\" && notnull is =
                          Just $ F x $ foldl f [] $ indices_ ts
                         where is = searchAll ((x==) . root) ts
                               f us i = if i `elem` is 
                                        then subterms (ts!!i)++us else ts!!i:us
                          
simplifyF _ (F "$" [F "\\/" ts,u]) = Just $ mkDisjunct $ map (flip apply u) ts

simplifyF _ (F "$" [F "/\\" ts,u]) = Just $ mkConjunct $ map (flip apply u) ts
-}                           

-- remove in/equational summands or factors with a quantified variable on one 
-- side.

simplifyF sig t | just u = u where u = removeEq sig False t

-- uncurrying: shift the premise of an implication from the conclusion to the
-- premise of an outer implication

simplifyF _ (F "==>" [t,u])
 | getOp t `notElem` words "F FS `U` EF AF `EU` `AU`" && just i 
         = Just $ mkImpl (mkConjunct [t,prem]) $ mkDisjunct $ conc:context k ts
           where ts = mkSummands u; i = search isImpl ts
                 k = get i; F _ [prem,conc] = ts!!k

-- distribute ==> over the factors of the conclusion of an implication

simplifyF _ (F "==>" [t,c@(F "&" ts)])
 | getOp t `notElem` words "F FS `U` EF AF `EU` `AU`"
                                   = Just $ mkConjunct $ map (mkImpl t) ts

-- distribute ==> over the summands the premise of an implication

simplifyF _ (F "==>" [d@(F "|" ts),t])
 | getOp t `notElem` words "G GS `W` `R` -> EF AF `EW` `AW` `ER` `AR`"
                                    = Just $ mkConjunct $ map (flip mkImpl t) ts

simplifyF sig t = simplifyA sig t

removeEq :: Sig -> Bool -> Term [Char] -> Maybe TermS
removeEq sig unsafe t =
      case t of F ('A':'l':'l':x) [F "==>" [F "&" ts,u]] | just pair 
                  -> Just $ mkAll xs $ mkImpl (mkConjunct reds) $ u>>>g
                             where xs = words x
                                   pair = f "=" xs ts; (reds,g) = get pair
                F ('A':'l':'l':x) [F "==>" [t,u]] | just pair 
                  -> Just $ mkAll xs $ u>>>snd (get pair)
                             where xs = words x
                                   pair = f "=" xs [t]
                F ('A':'l':'l':x) [F "==>" [t,F "|" us]] | just pair 
                  -> Just $ mkAll xs $ mkImpl (t>>>g) $ mkDisjunct reds
                             where xs = words x
                                   pair = f "=/=" xs us
                                   (reds,g) = get pair
                F ('A':'l':'l':x) [F "==>" [t,u]] | just pair 
                  -> Just $ mkAll xs $ mkNot sig $ t>>>snd (get pair)
                             where xs = words x
                                   pair = f "=/=" xs [u]
                F ('A':'l':'l':x) [F "|" ts] | just pair 
                  -> Just $ mkAll xs $ mkDisjunct $ fst $ get pair
                            where xs = words x
                                  pair = f "=/=" xs ts
                F ('A':'l':'l':x) ts | just $ f "=/=" (words x) ts
                  -> Just mkFalse
                F ('A':'n':'y':x) [F "&" ts] | just pair 
                  -> Just $ mkAny xs $ mkConjunct $ fst $ get pair
                            where xs = words x
                                  pair = f "=" xs ts
                F ('A':'n':'y':x) ts
                    | just $ f "=" (words x) ts -> Just mkTrue
                _ -> Nothing
      where f rel xs = g [] 
              where g rest (t@(F z us@[l,r]):ts) 
                             | z == rel && (unsafe || xs  `shares` map root us)
                                        = case unifyS sig xs l r of
                                    Just h -> Just (map (>>>h) $ ts++rest,h)
                                    _ -> g (rest++[t]) ts
                    g rest (t:ts) = g (rest++[t]) ts
                    g _ _         = Nothing

-- replaceTerms sig rel ts vs replaces l in vs by r if ts contains the
-- atom (l rel r) or (r rel l). At first, atoms (t rel t) are removed.
replaceTerms :: Sig -> String -> [TermS] -> [TermS] -> Maybe ([TermS],[TermS])
replaceTerms sig rel ts vs = f [] ts
   where f us ts = do t:ts <- Just ts
                      let vs = us++ts
                          rest = f (t:us) ts
                      case t of
                        F x [l,r] | x == rel ->
                            if l == r then f us ts 
                            else h l r vs ++ h r l vs ++ rest
                        _ -> rest
         h l r ts = do guard $ not (isc l || isSubterm l r) && 
                               isc r && (or bs || or cs)
                       Just (F rel [l,r]:ts',vs')
                    where (ts',bs) = unmap g ts
                          (vs',cs) = unmap g vs
                          g t | t == l = (r,True)
                          g (F x ts)   = (F x us,or bs)
                                         where (us,bs) = unmap g ts
                          g t          = (t,False) 
         isc = isConstruct sig . root
         unmap g = unzip . map g

-- | subsume a summand or distribute the factors of a conjunctive summand if
-- this leads to a smaller formula
subsumeDisj :: Sig -> [TermS] -> [TermS] -> Maybe TermS
subsumeDisj sig (t:ts) rest = if subsumes sig t u then Just u
                               else case t of 
                                   F "&" us | size v < size t+size u -> Just v
                                              where v = mkConjunct $ map f us
                                   _ -> subsumeDisj sig ts $ rest++[t]
                              where u = mkDisjunct $ ts++rest
                                    f v = mkDisjunct [v,u]
subsumeDisj _ _ _           = Nothing

-- | subsume a factor or distribute the summands of a disjunctive factor
subsumeConj :: Sig -> [TermS] -> [TermS] -> Maybe TermS
subsumeConj sig (t:ts) rest = if subsumes sig u t then Just u 
                               else case t of
                                   F "|" us -> Just $ mkDisjunct $ map f us
                                   _ -> subsumeConj sig ts $ rest++[t]
                              where u = mkConjunct $ ts++rest
                                    f v = mkConjunct [v,u]
subsumeConj _ _ _           = Nothing

-- LAMBDA APPLICATIONS
-- see: https://fldit-www.cs.uni-dortmund.de/~peter/CTL.pdf, page 102 ff.

simplifyA sig (F "$" [F x [p,t],u])
  | lambda x && just sub = Just $ renameAll f t>>>get sub
                           where ys = frees sig p
                                 sub = match sig ys u p
                                 zs = sigVars sig u
                                 f = getSubAwayFrom (frees sig u) zs t

simplifyA sig (F "$" [F x [F "~" [p],t],u])
  | lambda x = Just $ renameAll f t>>>sub'
               where ys = frees sig p
                     sub = match sig ys u p
                     zs = sigVars sig u
                     f = getSubAwayFrom (frees sig u) zs t
                     g y = apply (F x [p,mkVar sig y]) u
                     sub' = if just sub then get sub else forL (map g ys) ys

simplifyA sig (F "$" [F x ts,u])
  | lambda x && lg > 2 && even lg = Just $ F "CASE" cases where
                   lg = length ts
                   cases = [get t | t <- zipWith f (evens ts) $ odds ts, just t]
                   f p t =   do let xs = sigVars sig u
                                    g = getSubAwayFrom (frees sig u) xs t
                                    v = renameAll g t
                                concat [do F "||" [p,b] <- Just p
                                           sub <- match sig (frees sig p) u p
                                           Just $ F "->" [b>>>sub,v>>>sub],
                                        do sub <- match sig (frees sig p) u p
                                           Just $ F "->" [mkTrue,v>>>sub]]

-- distribute a relation over a sum

simplifyA sig t | relational sig x && just n = Just $ mkDisjunct $ map g
                                                     $ mkTerms $ ts!!i
             where (x,ts) = getOpArgs t
                   n = search isSum ts; i = get n
                   g u = updArgs t $ updList ts i u

simplifyA _ (F "`IN`" [t,F x ts])    | collector x = jConst $ inTerm t ts

simplifyA _ (F "`NOTIN`" [t,F x ts]) | collector x = jConst $ notInTerm t ts

simplifyA sig (F "`in`" [t,F x ts])
   | collector x = do guard $ f t && all f ts; jConst $ inTerm t ts
                   where f = isValue sig

simplifyA sig (F "`NOTin`" [t,F x ts])
   | collector x = do guard $ f t && all f ts; jConst $ notInTerm t ts
                   where f = isValue sig

simplifyA sig (F "`shares`" [F x ts,F y us])
   | collectors x y = do guard $ all f ts && all f us; jConst $ sharesTerm ts us
                      where f = isValue sig

simplifyA sig (F "`NOTshares`" [F x ts,F y us])
   | collectors x y = do guard $ all f ts && all f us
                         jConst $ disjointTerm ts us
                      where f = isValue sig

simplifyA sig (F "disjoint" [F x ts])
   | all collector (x:map root ts) = do guard $ all f tss 
                                        jConst $ distinctTerms tss
                                     where f = all $ isValue sig
                                           tss = map subterms ts

simplifyA sig (F "`subset`" [F x ts,F y us])
   | collectors x y = do guard $ all f ts && all f us; jConst $ subsetTerm ts us
                      where f = isValue sig

simplifyA sig (F "`NOTsubset`" [F x ts,F y us])
   | collectors x y = do guard $ all f ts && all f us
                         jConst $ not $ subsetTerm ts us
                      where f = isValue sig

-- simplifyA _ (F "Nat" [t]) | just $ parseNat t = jConst True

simplifyA _ (F "Int" [t])     = jConst $ just $ parseInt t

simplifyA _ (F "Real" [t])    = jConst $ just $ parseDouble t

simplifyA _ (F "List" [t])    = jConst $ isList t

simplifyA sig (F "Value" [t]) = jConst $ isValue sig t

simplifyA sig t = simplifyS sig t

mkStates :: Sig -> [Int] -> TermS
mkStates sig = mkList . map (states sig!!)

mkLabels :: Sig -> [Int] -> TermS
mkLabels sig = mkList . map ((sig&labels)!!)

mkAtoms :: Sig -> [Int] -> TermS
mkAtoms sig = mkList . map ((sig&atoms)!!)

-- distribute a function over a sum

simplifyS sig t | functional sig x && just n = Just $ mkSum $ map g $ mkTerms
                                                                     $ ts!!i
     where (x,ts) = getOpArgs t
           n = search isSum ts; i = get n
           g u = updArgs t $ updList ts i u

simplifyS sig (F "`meet`" [F x ts,F y us])
  | collectors x y = do guard $ all f ts && all f us
                        jList $ meetTerm ts us
                     where f = isValue sig

simplifyS sig (F "`join`" [F x ts,F y us])
  | collectors x y = do guard $ all f ts && all f us
                        jList $ joinTerms ts us
                     where f = isValue sig

simplifyS sig (F "-" [F x ts,F y us])
  | collectors x y = do guard $ all f ts && all f us
                        jList $ removeTerms ts us
                     where f = isValue sig
                                             
simplifyS sig (F "-" [F x ts,u])
  | collector x = do guard $ all f ts && f u; jList $ removeTerm ts u
                  where f = isValue sig

simplifyS _ (F "$" [F "filter" _,F "[]" []]) = Just mkNil

simplifyS sig (F "$" [F "filter" [p],F x ts])
 | collector x && just us = Just $ F x $ fst $ get us
                            where us = split2 (isTrue . f) (isFalse . f) ts
                                  f = sapply sig p

simplifyS sig (F "$" [F "$" [F "sfold" [f],a],F x []]) | collector x = Just a

simplifyS sig (F "$" [F "$" [F "sfold" [f],a],F x (t:ts)]) | collector x =
       Just $ apply (apply (F "sfold" [f]) $ simplifyIter sig $ applyL f [a,t])
            $ F x ts


-- LR parsing

simplifyS sig (F "parseLR" [str]) =
             do input <- parseWords str
                guard $ ("end":input) `subset` map root (labels sig) &&
                        all (\i -> all (det i) [0..m]) [0..n]
                Just $ F "parseLR" [Hidden $ LRarr acttab,mkStates sig [0],
                                     mkNil,mkList $ map leaf input]
             where upb@(n,m) = (length (states sig)-1,length (labels sig)-1)
                   bds = ((0,0),upb)
                   acttab = array bds [(ik,actTable sig ik) | ik <- range bds]
                   det i k = length (transL sig !!i!!k) <= 1
                             
simplifyS sig (F "parseLR" [Hidden (LRarr acttab),F "[]" sts,F "[]" trees,
                            F "[]" input])  =
            Just $ case nextLR sig acttab (getIndices (`elem` sts) (sig&states))
                               trees $ getIndices (`elem` input) (sig&labels) of
                        Success t -> t
                        More is trees input
                          -> F "parseLR" [Hidden $ LRarr acttab,
                                          mkStates sig is,mkList trees,f input]
                        _ -> leaf "no parse"
            where f [] = mkList [leaf "end"] 
                  f ks = mkList $ map (labels sig !!) ks

-- functions of a Kripke model generated by transition rules

simplifyS sig (F "trans" state) = do i <- searchTup state (sig&states)
                                     Just $ mkStates sig $ (sig&trans)!!i

simplifyS sig (F "$" [F "transL" state,lab])
                                = do i <- searchTup state (sig&states)
                                     k <- search (== lab) (sig&labels)
                                     Just $ mkStates sig $ (sig&transL)!!i!!k

simplifyS sig (F "succs" state) = do i <- searchTup state (sig&states)
                                     Just $ mkStates sig $ fixpt subset f [i]
                                  where f is = is `join` joinMap g is
                                        ks = indices_ (sig&labels)
                                        g i = sig&trans!!i `join`
                                              joinMap ((sig&transL!!i)!!) ks

simplifyS sig (F "parents" state) = do i <- searchTup state (sig&states)
                                       Just $ mkStates sig $ parents sig!!i

simplifyS sig (F "$" [F "parentsL" state,lab])
                                  = do i <- searchTup state (sig&states)
                                       k <- search (== lab) (sig&labels)
                                       Just $ mkStates sig $ parentsL sig!!i!!k

simplifyS sig (F "preds" state)   = do i <- searchTup state (sig&states)
                                       Just $ mkStates sig $ fixpt subset f [i]
                                    where f is = is `join` joinMap g is
                                          ks = indices_ (sig&labels)
                                          g i = parents sig !!i `join`
                                               joinMap ((parentsL sig!!i)!!) ks

simplifyS sig (F "$" [F "traces" state1,state2])
                         = do i <- searchTup state1 (sig&states)
                              j <- search (== state2) (sig&states)
                              jList $ map (mkStates sig) $ traces f i j
                           where ks = indices_ (sig&labels)
                                 f i = (sig&trans)!!i `join`
                                       joinMap (((sig&transL)!!i)!!) ks

simplifyS sig (F "$" [F "tracesL" state1,state2])
                         = do i <- searchTup state1 (sig&states)
                              j <- search (== state2) (sig&states)
                              jList $ map (mkLabels sig)
                                            $ tracesL ks f i j
                           where ks = indices_ (sig&labels)
                                 f i k = ((sig&transL)!!i)!!k

simplifyS sig (F "out" state) = do i <- searchTup state (sig&states)
                                   Just $ mkAtoms sig $ out sig!!i

simplifyS sig (F "$" [F "outL" state,lab])
                              = do i <- searchTup state (sig&states)
                                   k <- search (== lab) (sig&labels)
                                   Just $ mkAtoms sig $ outL sig!!i!!k

-- state equivalence

simplifyS sig (F "~" [t,u]) | notnull (sig&states)
                              = do i <- search (== t) (sig&states)
                                   j <- search (== u) (sig&states)
                                   let cli = search (elem i) part
                                       clj = search (elem j) part
                                   Just $ mkConst $ cli == clj
                  where part = mkPartition (indices_ (sig&states)) $ bisim sig 

simplifyS sig (F x@"equivStep" [])
                            | notnull (sig&states) = Just $ F x [Hidden mat] 
                     where sts = map showTerm0 (sig&states)
                           mat = ListMatL sts [(f i,f j,map (apply2 $ map f) ps) 
                                                | (i,j,ps) <- bisim0 sig]
                           f = showTerm0 . ((sig&states)!!)

simplifyS _ (F x@"equivStep" [Hidden mat]) =
                                    do ListMatL sts s <- Just mat
                                       let new = bisimStep s
                                       guard $ s /= new 
                                       Just $ F x [Hidden $ ListMatL sts new]

-- global model checking

simplifyS sig (F "eval" [phi])  = do sts <- foldModal sig phi
                                     Just $ mkStates sig sts

simplifyS sig (F "evalG" [phi]) = do sts <- foldModal sig phi
                                     let f st = if st `elem` map (strs!!) sts 
                                                then "sat$"++st else st
                                     Just $ mapT f $ eqsToGraph [] eqs
    where [strs,labs] = map (map showTerm0)[(sig&states),(sig&labels)]
          (eqs,_) = if null labs then relToEqs 0 $ mkPairs strs strs (sig&trans)
                    else relLToEqs 0 $ mkTriples strs labs strs (sig&transL)
         
-- flow graph initialization

simplifyS sig (F "stateflow" [t]) | just eqs =
                                 initStates True sig $ eqsToGraph [0] $ get eqs
                                 where eqs = parseEqs t

simplifyS sig (F "stateflowT" [t]) | just eqs =
                                initStates False sig $ eqsToGraph [0] $ get eqs
                                where eqs = parseEqs t

simplifyS sig (F "stateflow" [t]) | isFixF $ root t =
                                    initStates True sig $ eqsToGraph [0] eqs
                                    where (_,eqs,_) = fixToEqs t 0

simplifyS sig (F "stateflowT" [t]) | isFixF $ root t =
                                     initStates False sig $ eqsToGraph [0] eqs
                                     where (_,eqs,_) = fixToEqs t 0

simplifyS _ (F "postflow" [t]) = do eqs <- parseEqs t
                                    Just $ initPost $ eqsToGraph [0] eqs

simplifyS _ (F "subsflow" [t]) = do eqs <- parseEqs t
                                    Just $ initSubs $ eqsToGraph [0] eqs

-- flowgraph transformation

simplifyS sig t | just flow = do guard changed; Just $ mkFlow True sig ft id
                   where flow = parseFlow True sig t $ parseVal sig
                         (ft,changed) = evalStates sig t $ get flow

simplifyS sig t | just flow = do guard changed; Just $ mkFlow False sig ft id
                   where flow = parseFlow False sig t $ parseVal sig
                         (ft,changed) = evalStates sig t $ get flow

simplifyS sig t | just flow = do guard changed
                                 Just $ mkFlow True sig ft $ F "bool" . single
                   where flow = parseFlow True sig t mkVal
                         (ft,changed) = evalPost (simplifyIter sig) $ get flow
                         mkVal t = do F "bool" [t] <- Just t; Just t

simplifyS sig t | just flow = do guard changed
                                 Just $ mkFlow True sig ft
                                      $ mkList . concatMap mkSub
                   where flow = parseFlow True sig t parseSubs
                         flow' = get flow
                         xs = vars flow'
                         vars (In g _)         = vars g
                         vars (Assign x _ g _) = vars g `join1` x
                         vars (Ite _ g1 g2 _)  = vars g1 `join` vars g2
                         vars (Fork gs _)      = joinMap vars gs
                         vars flow             = []
                         (ft,changed) = evalSubs (simplifyIter sig) flow' xs
                         parseSubs t = do F "[]" ts <- Just t; mapM parseSub ts
                         parseSub t = do s <- parseList parseEq t
                                         let (xs,ts) = unzip s
                                         Just $ forL ts xs
                         parseEq t = do F "=" [V x,t] <- Just t; Just (x,t)
                         mkSub f = if null ys then [] else [mkList $ map g ys]
                             where ys = domSub xs f
                                   g x = mkEq (V x) $ f x

-- regular expressions and acceptors

simplifyS sig (F "flatten" [t]) | just e = Just $ showRE $ fst $ get e
                                           where e = parseRE sig t
                       
simplifyS sig (F "deltaBro" [t,F x []])
                                | just e && just e' = Just $ showRE $ get e'
                               where e = parseRE sig t
                                     e' = deltaBro (getRHS sig) (fst $ get e) x
                                               
simplifyS sig (F "betaBro" [t]) | just e && just b = Just $ mkConst $ get b
                                   where e = parseRE sig t
                                         b = betaBro (getRHS sig) $ fst $ get e

simplifyS sig (F "$" [F "unfoldBro" [t],F "[]" xs])
                                | just e && just b = Just $ mkConst $ get b
                   where e = parseRE sig t
                         b = unfoldBro (getRHS sig) (fst $ get e) $ map root xs

simplifyS sig (F "auto" [t]) | just e = Just $ eqsToGraph [] $ fst
                                             $ relLToEqs 0 trips
           where e = parseRE sig t
                 (e',labs) = get e
                 (sts,nda) = regToAuto e'
                 trips = [(show q,a,map show $ nda q a) | q <- sts, a <- labs]

simplifyS sig (F "pauto" [t]) | just e = Just $ eqsToGraph [] $ fst
                                              $ relLToEqs 0 trips
           where e = parseRE sig t
                 (e',labs) = get e
                 (_,nda) = regToAuto e'
                 labs' = labs `minus1` "eps"
                 (sts,delta) = powerAuto nda labs' 
                 trips = [(show q,a,[show $ delta q a]) | q <- sts, a <- labs']

simplifyS _ t = simplifyT t

getRHS :: Sig -> String -> Maybe RegExp
getRHS sig x = do [rhs] <- Just $ simplReducts sig False $ F "step" [leaf x]
                  (e,_) <- parseRE sig rhs; Just e

-- * __Signature-independent simplification__

-- simplifyT1 removed in Haskell since it is only needed for O'Haskells limited
-- number of pattern.

simplifyT :: TermS -> Maybe TermS

simplifyT (F x [F "skip" []])             = Just $ F "skip" []

simplifyT (F "$" [F "lsec" [t,F x []],u]) = Just $ F x [t,u]

simplifyT (F "$" [F "rsec" [F x [],t],u]) = Just $ F x [u,t]
 
simplifyT (F "CASE" (F "->" [F "True" [],t]:_))   = Just t
simplifyT (F "CASE" (F "->" [F "False" [],_]:ts)) = Just $ F "CASE" ts
simplifyT (F "CASE" [])                            = Just $ F "undefined" []

simplifyT (F "string" [t])       = Just $ leaf $ showTree False t

simplifyT (F "stringNB" [t])     = Just $ leaf $ showTree False t `minus` "()"

simplifyT (F "noBrackets" [t])   = Just $ leaf $ minus (showTree False t) "()"

simplifyT (F "getCols" [F x ts]) = Just $ if null z then F x $ map f ts
                                          else F col [F (tail z) $ map f ts]
                                 where (col,z) = span (/= '_') x
                                       f t = F "erect" [t]

-- projection

simplifyT (F "$" [F "get" [n],t])
    | just i = Just $ F ("get"++show (get i)) [t]
                                              where i = parseNat n

simplifyT (F x [F "()" ts]) | just i && k < length ts = Just $ ts!!k
                                              where i = parse (strNat "get") x
                                                    k = get i
                                             
simplifyT (F "height" [t])        = jConst $ height t

simplifyT (F "$" [F "." [g,f],t]) = Just $ apply g $ apply f t 

simplifyT (F "$" [F "$" [F "flip" [f],t],u]) = Just $ apply (apply f u) t

simplifyT (F "suc" [t])        | just i = jConst $ get i+1 where i = parseInt t

simplifyT (F "range" [t,u])    | just i && just k = 
         jList $ map mkConst [get i..get k]
         where i = parseInt t; k = parseInt u

simplifyT (F "list" [F x ts])  | collector x = Just $ drop0FromPoss $ mkList ts

simplifyT (F "set" [F x ts])   | collector x = Just $ F "{}" $ joinTerms [] ts

simplifyT (F "bag" [F x ts])   | collector x = Just $ drop0FromPoss $ mkBag ts

simplifyT (F "tup" [F x ts])   | collector x = Just $ drop0FromPoss $ mkTup ts

simplifyT (F "branch" [F x ts]) | collector x = Just $ drop0FromPoss $ mkSum ts

simplifyT (F "null" [F x ts])      | collector x = jConst $ null ts

simplifyT (F "NOTnull" [F x ts])   | collector x = jConst $ not $ null ts

simplifyT (F "single" [F x ts])    | collector x = jConst $ length ts == 1

simplifyT (F "!!" [F x ts,n])      | just i && collector x && k < length ts = 
                                                Just $ ts!!k
                                            where i = parseNat n; k = get i
simplifyT (F "!!" [F ":" [t,u],n]) | just i = Just $ if k == 0 then t
                                              else F "!!" [u,mkConst $ k-1]
                                           where i = parseNat n; k = get i

simplifyT (F "$" [F "map" [f@(F _ ts)],F x us]) | collector x 
                                             = Just $ F x $ map (apply f) us

simplifyT (F "$" [F "map" [f],F ":" [t,ts]]) = Just $ F ":" [apply f t,
                                                        F "$" [F "map" [f],ts]]

simplifyT (F "$" [F "map" _,F "[]" _]) = Just mkNil

simplifyT (F "$" [F "$" [F "upd" [F x ts],n],u]) 
        | just i && collector x && k < length ts = Just $ F x $ updList ts k u 
                                          where i = parseNat n; k = get i
                                    
simplifyT (F "$" [F "$" [F "upd" [F ":" [t,v]],n],u]) | just i =
              Just $ if k == 0 then F ":" [u,v] 
                      else F ":" [t,F "$" [F "$" [F "upd" [v],mkConst $ k-1],u]]
                                          where i = parseNat n; k = get i

simplifyT (F "$" [F "insert" [t],F x ts]) 
        | collector x && just rs = jConsts $ insert (<) q qs
                                              where rs = mapM parseInt $ t:ts
                                                    q:qs = get rs

simplifyT (F "$" [F "$" [F "insertL" [t],F "[]" ts],F "[]" all]) 
        | (t:ts) `subset` all = jList $ insert less t ts
                                 where t `less` u = getInd t all < getInd u all

simplifyT (F "prodL" [F x ts]) | all collector (x:map root ts) = 
                                jList $ map mkTup $ mapM subterms ts

simplifyT t | f == "curry" && notnull tss && length us == 1 =
                              Just $ applyL (head us) $ concat uss
                              where (f,tss) = unCurry t; us:uss = tss

simplifyT (F "$" [F "uncurry" [f],F "()" (t:ts@(_:_))]) =
                              Just $ F "$" [F "uncurry" [apply f t],F "()" ts]

simplifyT (F "$" [F "uncurry" [f],F "()" [t]]) = Just $ apply f t

simplifyT (F "$" [F "$" [F "foldl" [f],a],F x ts]) | collector x = 
                              Just $ foldl g a ts where g a t = applyL f [a,t]

simplifyT (F "$" [F "foldl1" [f],F x ts]) | collector x =
                              Just $ foldl1 g ts where g a t = applyL f [a,t]

simplifyT (F "$" [F "$" [F "foldr" [f],a],F x ts]) | collector x = 
                              Just $ foldr g a ts where g t a = applyL f [t,a]

simplifyT (F "$" [F "foldr1" [f],F x ts]) | collector x = 
                              Just $ foldr1 g ts where g t u = applyL f [t,u]
                                      
simplifyT (F "$" [F "zip" [F x ts],F y us]) | collectors x y = 
            jList $ map g $ zip ts us where g (t,u) = mkPair t u

simplifyT (F "$" [F "$" [F "zipWith" _,F "[]" _],F ":" _]) = Just mkNil

simplifyT (F "$" [F "$" [F "zipWith" _,F ":" _],F "[]" _]) = Just mkNil

simplifyT (F "$" [F "$" [F "zipWith" [f],F ":" [t,ts]],F ":" [u,us]]) =
            Just $ F ":" [applyL f [t,u],apply (apply (F "zipWith" [f]) ts) us]

simplifyT (F "$" [F "$" [F "zipWith" [f],F x ts],F y us]) | collectors x y =
            jList $ zipWith g ts us where g t u = applyL f [t,u]

simplifyT (F "index" [t,F x ts])
                         | collector x = do i <- search (eqTerm t) ts; jConst i

simplifyT (F "singles" [F x ts])
                         | collector x = jList $ map (mkList . single) ts

simplifyT (F "subsets" [F x ts]) | collector x = jList $ map (F x) subs
                       where subs = [map (ts!!) ns | ns <- subsetsB lg lg]
                             lg = length ts

simplifyT (F "subsetsB" [F x ts,t]) | collector x && just i = 
                        jList $ map (F x) subs
                   where lg = length ts; i = parseInt t
                         subs = [map (ts!!) ns | ns <- subsetsB lg $ get i]

simplifyT (F "perms" [F "[]" ts])   = jList $ map mkList $ perms ts

simplifyT (F "reverse" [F "[]" ts]) = jList $ reverse ts

simplifyT (F "shuffle" [F x ts])
           | all ((== "[]") . root) ts  = jList $ shuffle $ map subterms ts

simplifyT (F "sort" [F "[]" ts])
           | all just is = jConsts $ qsort (<=) $ map get is
           | all just rs = jConsts $ qsort (<=) $ map get rs
           | True        = jList $ sort (<) ts
                           where is = map (foldArith intAlg) ts
                                 rs = map (foldArith realAlg) ts

-- begin functions with pattern match checker problems
simplifyT (F "subperms" [F "[]" ts]) = jList $ map mkList $ subperms ts

simplifyT (F "=" [F "^" ts@(t:ts'),F "^" us@(u:us')]) = 
                  case search (eqTerm t) us of
                       Just n -> Just $ mkEq (mkBag ts') $ mkBag $ context n us
                       _ -> do n <- search (eqTerm u) ts
                               Just $ mkEq (mkBag $ context n ts) $ mkBag us'
-- end functions with pattern match checker problems

simplifyT (F "`mod`" [t,u]) | just i && just j && k /= 0 = 
                                      Just $ mkConst $ mod (get i) k
                            where i = parseInt t; j = parseInt u; k = get j
                                                
simplifyT (F x [F "+" [t,u],n])
    | arithmetical x && just i && just j =
        Just $ F x [u,mkConst $ get i-get j] 
    | arithmetical x && just i && just k =
        Just $ F x [u,mkConst $ get i-get k] 
    where i = parseInt n; j = parseInt t; k = parseInt u
                                                
simplifyT (F x [n,F "+" [t,u]])
    | arithmetical x && just i && just j =
        Just $ F x [mkConst $ get i-get j,u] 
    | arithmetical x && just i && just k =
        Just $ F x [mkConst $ get i-get k,t] 
    where i = parseInt n; j = parseInt t; k = parseInt u
                                                
simplifyT (F "+" [n,F "+" [t,u]])
    | just i && just j =
        Just $ F "+" [mkConst $ get i+get j,u] 
    | just i && just k =
        Just $ F "+" [mkConst $ get i+get k,t] 
    where i = parseInt n; j = parseInt t; k = parseInt u
                                                
simplifyT (F "+" [F "+" [t,u],n])
    | just i && just j =
        Just $ F "+" [mkConst $ get i+get j,u] 
    | just i && just k =
        Just $ F "+" [mkConst $ get i+get k,t] 
    where i = parseInt n; j = parseInt t; k = parseInt u
                                                           
simplifyT (F ">" [F "()" (t:ts),F "()" (u:us)]) =
             Just $ F "|" [mkGr t u,F "&" [mkEq t u,mkGr (mkTup ts) $ mkTup us]]
                              
simplifyT (F "color" [i,n]) = do i <- parseNat i; n <- parseNat n
                                 jConst $ hue 0 red n i

simplifyT (F "dnf" [t]) | isObdd t = jConsts $ funToBins $ obddToFun 
                                               $ drop0FromPoss t

simplifyT (F "minimize" [t]) | just bins = jConsts $ minDNF $ get bins
                                            where bins = parseBins t

simplifyT (F "minimize" [t]) | isObdd t = Just $ drop0FromPoss $ collapse True
                                                 $ removeVar t

simplifyT (F "gauss" [t]) | just eqs =
                              Just $ F "bool" [mkLinEqs $ get $ gauss $ get eqs]
                              where eqs = parseLinEqs t

simplifyT (F x@"gaussI" [t]) | just eqs =
                               case gauss1 $ get eqs of
                                    Just eqs -> f eqs
                                    _ -> do eqs <- gauss2 $ get eqs; f eqs
                               where eqs = parseLinEqs t
                                     f eqs = Just $ F x [mkLinEqs $ gauss3 eqs]

simplifyT (F "obdd" [t])   = do bins <- parseBins t; Just $ binsToObdd bins

simplifyT (F "pascal" [t]) = do n <- parseNat t; jConsts $ pascal n

simplifyT (F "concept" [F "[]" ts,F "[]" us,F "[]" vs]) | f us && f vs =
                               Just $ h $ concept ts (g us) $ g vs
                               where f = all $ (== "()") . root
                                     g = map $ map root . subterms
                                     h = mkSum . map (mkTup . map leaf)

simplifyT (F x ts) | (x == "[]" || x == "{}") && length us < length ts = 
                  Just $ F x us where us = if head x == '[' then mergeActs ts
                                                            else joinTerms [] ts
                                                             
-- change the variable ordering of a DNF or an OBDD

simplifyT (F "nextperm" [F x ns]) | collector x 
                                    = do ns <- mapM parseInt ns
                                         Just $ F x $ map mkConst $ nextPerm ns

simplifyT (F "permute" (t:ts)) | just bins =
                     if null s then Just t
                     else if null ts then perm [t,t,mkConsts first]
                          else do [_,ns] <- Just ts; ns <- parseNats ns
                                  let permute s = map (s!!) ns
                                  perm [t,mkConsts $ map permute s,
                                            mkConsts $ nextPerm ns]
                     where bins = parseBins t; s = get bins
                           first = indices_ $ head s; perm = Just . F "permute"

simplifyT (F "light" [i,n,c]) = do i <- parseNat i; n <- parseNat n
                                   c <- parseColor c
                                   jConst $ nextLight n (-n`div`3+i) c

simplifyT (F x@('p':'a':'t':'h':_) [F "[]" ts])
                               | all just ps && length qs < length ps =
                                 Just $ F x $ map mkConstPair qs
                                 where ps = map parseRealReal ts
                                       qs = reducePath $ map get ps

simplifyT (F "reduce" [F "[]" ts,F "[]" us]) 
             | all isTup us = Just $ g $ reduceExas ts $ f us
                      where f = map $ map root . subterms
                            g = mkSum . map (mkTup . map leaf)

simplifyT _ = Nothing

mergeActs :: [TermS] -> [TermS]
mergeActs (F x [t]:F y [u]:ts) 
                   | x == y && x `elem` words "J M T" && just r && just s
                         = F x [mkConst (get r+get s)]:ts 
                         where r = parseReal t
                               s = parseReal u
mergeActs (F "L" []:F "R" []:ts) = ts
mergeActs (F "R" []:F "L" []:ts) = ts
mergeActs (t:u:ts)                   = t:mergeActs (u:ts)
mergeActs ts                         = ts

-- * __Aciom-base simplification__

-- simplReducts sig True t returns the reducts of all axioms of sig.transitions
-- that are applicable to t and is used by rewriteSig/States (see below).

-- simplReducts sig False t returns the reduct of the first axiom of sig.simpls 
-- that is applicable to t and is used by simplifyUser (see above).
simplReducts :: Sig -> Bool -> TermS -> [TermS]
simplReducts sig isTrans t = if isTrans then concatMap f (sig&transitions)
                             else if null reds then [] else [head reds]
 where reds = concatMap f (simpls sig)
       f (u,cs,v) = case matchSubs sig xs t u of
                         Just (sub,ts,is,bag) | just sub'
                           -> map (mkBag . h is ts . toElems)
                                  $ mkTerms $ reduce $ v>>>get sub'
                              where sub' = g sub cs xs
                                    toElems = if bag then mkElems else single
                         _ -> []
                     where xs = frees sig u
                           h is ts vs = g 0 0 ts 
                                where g i k (u:us) = if i `elem` is
                                                     then vs!!k:g (i+1) (k+1) us
                                                     else ts!!i:g (i+1) k us
                                      g _ _ _ = []
                           reduce = if isTrans then simplifyIter sig else id
       g sub (c:cs) xs | isTrue $ simplifyIter sig $ c>>>sub = g sub cs xs
       g sub (F "=" [t,u]:cs) xs | frees sig t `subset` xs &&
                                       xs `disjoint` zs && just h
                        = g (sub `andThen` get h) cs $ xs++zs
                          where zs = frees sig u
                                h = match sig zs (simplifyIter sig $ t>>>sub) u
       g sub [] _ = Just sub
       g _ _ _    = Nothing

-- | rewriteSig sig ts constructs the (labelled) relations generated by ts and
-- the
-- simplification and transition axioms of sig.
-- rewriteSig is used by 'Ecom.buildKripke'.
rewriteSig :: Sig -> [TermS] -> (Pairs TermS,Triples TermS TermS)
rewriteSig sig ts = (zip ts $ reduce ts,
                     zipL pairs $ reduce [mkPair t lab | (t,lab) <- pairs])
                  where reduce = map $ simplReducts sig True
                        pairs = prod2 ts (sig&labels)

-- | rewriteStates sig mode constructs the transition system generated by
-- sig.states and the simplification and transition axioms of sig.
-- rewriteStates is used by 'Ecom.buildKripke'.
rewriteStates :: Sig -> Int -> ([TermS],Pairs TermS,Triples TermS TermS)
rewriteStates sig mode = h (sig&states) (sig&states) [] [] where
                    h sts ts ps psL = if null new then (sts,rs,rsL) 
                                      else h (sts `join` new) new rs rsL
                      where new = reds `minus` sts
                            reds = joinM redss `join` joinM redssL
                            redss = reduce ts
                            redssL = reduce [mkPair t lab | (t,lab) <- pairs]
                            reduce = map $ simplReducts sig True
                            pairs = prod2 ts (sig&labels)
                            qs = zip ts redss
                            qsL = zipL pairs redssL
                            (rs,rsL) = case mode of 
                                       0 -> (mkAcyclic ps qs,mkAcyclicL psL qsL)
                                       1 -> (ps++map f qs,psL++map fL qsL)
                                       _ -> (ps++qs,psL++qsL)
                            f (t,ts)    = (t,onlyNew ts)
                            fL (t,u,ts) = (t,u,onlyNew ts)
                            onlyNew ts = minus ts $ meet reds sts
                           
pairsToInts :: [TermS] -> Pairs TermS -> [TermS] -> [[Int]]
pairsToInts us ps = map f where
  f t = searchAll (`elem` (get $ lookup t ps)) us

tripsToInts :: [TermS] -> [TermS] -> Triples TermS TermS -> [TermS] 
            -> [[[Int]]]
tripsToInts us vs ps = map f
                where f t = map (flip (g t) us) vs
                      g t u = searchAll (`elem` (get $ lookupL t u ps))

-- * __Rewriting and narrowing__

data Reducts = Sum [TermS] (String -> Int) | Backward [TermS] (String -> Int) |
                Forward [TermS] (String -> Int) | MatchFailure String | Stop
               -- MatchFailure is only generated by genMatchFailure.

-- | solveGuard guard axs applies axs by narrowing at most 100 times to guard. 
-- axs are also the axioms applied to the guards of axs. Reducts are simplified,
-- but irreducible subtrees are not removed.
-- solveGuard is used by applyAx, rewrite and rewriteTerm (see below).
solveGuard :: Sig -> TermS -> [TermS] -> (String -> Int) -> Maybe [[IterEq]]
solveGuard sig cond axs vc = do guard $ notnull sols; Just sols
                  where sols = Haskell.mapMaybe f (mkSummands $ pr1 t)
                        f = parseSol $ solEq sig
                        t = applyLoop cond 100 vc axs axs sig True 2 True False

-- | applyLoop t 0 m ... axs preAxs sig nar match simplify refute applies axioms
-- at most m times to the maximal subtrees of t and returns the modified tree 
-- together with the number of actually applied steps. 
-- preAxs are applied to the guards of axs. 
-- nar = True            --> narrowing          
-- nar = False     --> rewriting
-- match = 0            --> match t against axs
-- match = 1            --> match t against the first applicable axiom of axs
-- match = 2            --> unify t against axs
-- match = 3       --> unify t against the first applicable axiom of axs
-- simplify = True --> simplifyIter
-- refute = True   --> turnIntoUndef
-- applyLoop is used by solveGuard (see above) and narrowStep (see Ecom).
applyLoop :: TermS -> Int -> (String -> Int) -> [TermS] -> [TermS] -> Sig 
                    -> Bool -> Int -> Bool -> Bool -> (TermS,Int,String -> Int)
applyLoop t m vc axs preAxs sig nar match simplify refute =
          f t 0 m vc
 where f t k 0 vc = (t,k,vc)
       f t k m vc = case modify t vc [] of Just (t,vc) -> f t (k+1) (m-1) vc 
                                           _ -> (t,k,vc)
       uni = match > 1
       simpl = if simplify then simplifyIter sig else id
       remove p = if refute then turnIntoUndef sig t p else const Nothing
       modify t vc p = case f redex t p vc' of 
                            Just (t',vc) -> Just (simpl t',vc)
                            _ -> case remove p redex of 
                                 Just u -> Just (simpl $ replace t p u,vc')
                                 _ -> concat $ map (modify t vc) 
                                               $ succsInd p $ subterms redex
                   where redex = getSubterm t p
                         filtered = filterClauses sig redex axs
                         rules
                            | isVarRoot sig redex = []
                            | nar = filtered
                            | otherwise = filter unconditional filtered
                         (axs',vc') = renameApply rules sig t vc
                         f = if nar then modifyForm $ applyAxs axs' axs' preAxs
                             else modifyTerm $ applyAxsToTerm axs' axs' preAxs
       modifyForm f redex t p vc 
        | isDefunct sig sym = do (q,at,r) <- atomPosition sig t p
                                 Backward reds vc <- g at r
                                 Just (replace t q $ mkDisjunct reds,vc)
        | notnull p && isTerm sig redex =
                              do (at@(F "->" [_,_]),0) <- Just (getSubterm t q,
                                                                       last p)
                                 Backward reds vc <- g at [0]
                                 Just (replace t q $ mkDisjunct reds,vc)
        | isPred sig sym    = do Backward reds vc <- g redex []
                                 Just (replace t p $ mkDisjunct reds,vc)
        | True              = do guard $ isCopred sig sym
                                 Forward reds vc <- g redex []
                                 Just (replace t p $ mkConjunct reds,vc)
                            where sym = getOp redex; q = init p
                                  g at r = Just $ fst $ f redex at r sig vc uni
       modifyTerm f redex t p vc
                            = do Sum reds vc <- Just $ fst $ f redex sig vc
                                 Just (replace t p $ mkSum reds,vc)
                       
-- | applyLoopRandom is used by 'Ecom.narrowStep'.
applyLoopRandom :: Int -> TermS -> Int -> (String -> Int) -> [TermS] -> [TermS]
                        -> Sig -> Bool -> Int -> Bool 
                       -> (TermS,Int,String -> Int,Int)
applyLoopRandom rand t m vc axs preAxs sig nar match simplify = f t 0 m vc rand
 where f t k 0 vc rand = (t,k,vc,rand)
       f t k m vc rand = case modify t [] vc rand of 
                         Just (t,vc,rand) -> f t (k+1) (m-1) vc $ nextRand rand
                         _ -> (t,k,vc,rand)
       uni = match > 1
       simpl = if simplify then simplifyIter sig else id
       modify t p vc rand = 
             case f redex t p vc' of 
                  Just (t,vc,rand) -> Just (simpl t,vc,rand)  
                  _ -> modifyL $ succsInd p $ subterms redex
         where redex = getSubterm t p
               filtered = filterClauses sig redex axs
               rules
                    | isVarRoot sig redex = []
                    | nar = filtered
                    | otherwise = filter unconditional filtered
               (axs',vc') = renameApply rules sig t vc
               f = if nar then modifyForm $ applyAxsR axs' axs' preAxs rand
                   else modifyTerm $ applyAxsToTermR axs' axs' preAxs rand
               modifyL ps@(_:_) = modify t (ps!!i) vc (nextRand rand) ++ 
                                     modifyL (context i ps)
                                  where i = mod rand $ length ps
               modifyL _        = Nothing
       modifyTerm f redex t p vc =
                  do (Sum reds vc,rand) <- Just $ (pr1***pr3) $ f redex sig vc
                     Just (replace t p $ mkSum reds,vc,rand)
       modifyForm f redex t p vc 
        | isDefunct sig sym = do (q,at,r) <- atomPosition sig t p
                                 (Backward reds vc,rand) <- g at r
                                 Just (replace t q $ mkDisjunct reds,vc,rand)
        | notnull p && isTerm sig redex =
                              do (at@(F "->" [_,_]),0) <- Just (getSubterm t q,
                                                                       last p)
                                 (Backward reds vc,rand) <- g at [0]
                                 Just (replace t q $ mkDisjunct reds,vc,rand)
        | isPred sig sym    = do (Backward reds vc,rand) <- g redex []
                                 Just (replace t p $ mkDisjunct reds,vc,rand)
        | True                = do guard $ isCopred sig sym
                                   (Forward reds vc,rand) <- g redex []
                                   Just (replace t p $ mkConjunct reds,vc,rand)
                    where sym = getOp redex; q = init p
                          g at r = Just $ (pr1***pr3) $ f redex at r sig vc uni

-- | applyAxs cls axs preAxs redex u r computes all narrowing/rewriting reducts 
-- of the redex at position r of u that result from unifying/matching redex 
-- against axs. The guards of axs are narrowed by preAxs. cls is the original, 
-- non-extended and non-renamed version of axs. 
-- uni = True  --> The redex is unified against axs.
-- uni = False --> The redex is matched against axs.
-- applyAxs is used by applyLoop (see above), applyPar (see below) and narrowPar
-- (see Ecom). 
applyAxs :: [a]
            -> [TermS]
            -> [TermS]
            -> TermS
            -> TermS
            -> [Int]
            -> Sig
            -> (String -> Int)
            -> Bool
            -> (Reducts, [a])
applyAxs (cl:cls) (ax:axs) preAxs redex at p sig vc uni =
  case applyAx ax preAxs redex at p sig vc uni of
       reduct@(Backward reds vc) 
         -> case applyAxs cls axs preAxs redex at p sig vc uni of
                 (Backward reds' vc,cls) -> (Backward (reds++reds') vc,cl:cls)
                 mf@(MatchFailure _,_) -> mf
                 _ -> (reduct,[cl])
       reduct@(Forward reds vc) 
         -> case applyAxs cls axs preAxs redex at p sig vc uni of
                 (Forward reds' vc,cls) -> (Forward (reds++reds') vc,cl:cls)
                 mf@(MatchFailure _,_) -> mf
                 _ -> (reduct,[cl])
       mf@(MatchFailure _) -> (mf,[])
       _ -> applyAxs cls axs preAxs redex at p sig vc uni
applyAxs _ _ _ _ _ _ _ _ _ = (Stop,[])

-- | applyAxsR axs preAxs rand redex t p computes the narrowing/rewriting 
-- reducts of the redex at position p of t that result from unifying/matching 
-- redex against a random element of axs. The guards of axs are narrowed by 
-- preAxs. 
-- applyAxsR is used by applyLoopRandom (see above) and narrowPar (see Ecom).
applyAxsR :: [TermS]
             -> [TermS]
             -> [TermS]
             -> Int
             -> TermS
             -> TermS
             -> [Int]
             -> Sig
             -> (String -> Int)
             -> Bool
             -> (Reducts, [TermS], Int)
applyAxsR _ [] _ rand _ _ _ _ _ _                  = (Stop,[],rand)
applyAxsR cls axs preAxs rand redex at p sig vc uni =
  case applyAx ax preAxs redex at p sig vc uni of
       Stop -> applyAxsR cls' axs' preAxs (nextRand rand) redex at p sig vc uni
       reduct -> (reduct,[cl],rand)
  where n = rand `mod` length axs
        cl = cls!!n; cls' = removeTerm cls cl
        ax = axs!!n; axs' = removeTerm axs ax

-- | applyAxsToTerm is used by 'applyLoop', 'getRel', 'getRel2', 'getFun'
-- and 'Ecom.rewritePar'.
applyAxsToTerm :: [a]
                  -> [TermS]
                  -> [TermS]
                  -> TermS
                  -> Sig
                  -> (String -> Int)
                  -> (Reducts, [a])
applyAxsToTerm (cl:cls) (ax:axs) preAxs redex sig vc =
  case applyAxToTerm ax preAxs redex sig vc of
  reduct@(Sum reds vc) -> case applyAxsToTerm cls axs preAxs redex sig vc of
                          (Sum reds' vc,cls) -> (Sum (reds++reds') vc,cl:cls)
                          _ -> (reduct,[cl])
  _ -> applyAxsToTerm cls axs preAxs redex sig vc
applyAxsToTerm _ _ _ _ _ _ = (Stop,[])

-- | applyAxsToTermR is used by applyLoopRandom (see above) and rewritePar (see 
-- Ecom).
applyAxsToTermR :: [TermS]
                   -> [TermS]
                   -> [TermS]
                   -> Int
                   -> TermS
                   -> Sig
                   -> (String -> Int)
                   -> (Reducts, [TermS], Int)
applyAxsToTermR _ [] _ rand _ _ _                = (Stop,[],rand)
applyAxsToTermR cls axs preAxs rand redex sig vc =
  case applyAxToTerm ax preAxs redex sig vc of
       Stop -> applyAxsToTermR cls' axs' preAxs (nextRand rand) redex sig vc
       reduct -> (reduct,[cl],rand)
  where n = rand `mod` length axs
        cl = cls!!n; cls' = removeTerm cls cl
        ax = axs!!n; axs' = removeTerm axs ax

-- * __Narrowing of formulas__

-- | quantify sig add ts t quantifies the free variables xs of ts that and 
-- quantifies t with xs.
quantify :: Sig -> ([String] -> TermS -> TermS) -> [TermS] -> TermS -> TermS
quantify sig add ts reduct = add (filter (noExcl &&& (`elem` ys)) xs) reduct
                                 where xs = freesL sig ts
                                       ys = sigVars sig reduct

-- | addTo is used by searchReds, applyAx, applyAxToTerm and applySingle.
addTo :: Bool -> [TermS] -> TermS -> TermS
addTo _ [] t                  = t 
addTo True rest (F "=" [t,u]) = mkEq (mkBag $ t:rest) u
addTo True _ t                = t
addTo _ rest t                = mkBag $ t:rest

-- | searchReds .. ts reds .. pars tries to unify ts with a subset of reds such
-- that the instance of a given guard by the unifier is solvable by applying 
-- given axioms. The guard and the axioms are part of pars. 
-- searchReds is used by applyAx and applyAxToTerm (see below).
searchReds :: ((String -> TermS) -> Sig -> [String] -> t -> t1 -> Reducts)
              -> (TermS
                  -> (String -> TermS)
                  -> Sig
                  -> [String]
                  -> t
                  -> t1
                  -> Reducts)
              -> t
              -> [TermS]
              -> [TermS]
              -> Bool
              -> TermS
              -> Sig
              -> [String]
              -> t1
              -> Maybe Reducts
searchReds check rewrite vc ts reds b t sig xs pars = sr Stop ts [] reds [] 
  where lg = length ts
        sr _ (t:ts) us reds vs =
                          do (reduct,red,rest) <- h us' reds vs $ length reds-1
                             sr reduct ts us' rest $ red:vs
                          where us' = t:us
        sr reduct _ _ _ _ = Just reduct
        h ts reds vs i =
           do guard $ i >= 0
              case unify' ts (red:vs) (V"") (V"") ps ps V sig xs of
                   Def (f,True) -> case checkOrRewrite f sig xs vc pars of
                                        Stop -> h ts reds vs (i-1)
                                        reduct -> Just (reduct,red,rest)
                   _ -> h ts reds vs (i-1)
           where red = reds!!i; rest = context i reds
                 ps = replicate lg' []; lg' = length ts
                 checkOrRewrite = if lg == lg' then rewrite $ addTo b rest t
                                               else check

addAnys :: [String] -> TermS -> TermS
addAnys xs reduct = mkAny (filter (`isin` reduct) xs) reduct

addAlls :: [String] -> TermS -> TermS
addAlls xs reduct = mkAll (filter (`isin` reduct) xs) reduct

genMatchFailure :: Sig -> Bool -> [String] -> TermS -> Reducts -> Reducts
genMatchFailure sig uni dom t reduct
    | uni || null dom = reduct
    | any (isHovar sig) dom = Stop
    | True = MatchFailure $ "Some redex does not match " ++ showTree False t

partialUnify :: TermS
                -> [TermS]
                -> TermS
                -> TermS
                -> TermS
                -> TermS
                -> TermS
                -> [Int]
                -> Sig
                -> (String -> Int)
                -> Bool
                -> TermS
                -> Reducts
partialUnify guard axs left right prem at at' p sig vc uni redex =
       case unify0 left redex at p sig xs of
            TotUni f -> rewrite at' f sig xs vc (guard,axs,left,right,prem,uni)
            ParUni f dom -> genMatchFailure sig uni dom left $ Backward [t] vc
                            where reduct = mkConjunct $ at>>>f:substToEqs f dom
                                  t = quantify sig addAnys [left] reduct
            _ -> Stop
       where xs = frees sig redex

rewrite :: TermS
           -> (String -> TermS)
           -> Sig
           -> [String]
           -> (String -> Int)
           -> (TermS, [TermS], TermS, TermS, TermS, Bool)
           -> Reducts
rewrite at f sig xs vc (guard,axs,left,right,prem,uni) =
       genMatchFailure sig uni (domSub xs f) left $
                       case t of F "True" _ -> Backward [mkRed []] vc
                                 F "False" _ -> Stop
                                 _ -> case solveGuard sig t axs vc of
                                      Just sols -> Backward (map mkRed sols) vc
                                      _ -> Stop
       where t = simplifyIter sig $ guard>>>f
             mkRed sol = quantify sig addAnys [left,right,prem] reduct
                         where reduct = mkConjunct $ at>>>g:prem>>>g:
                                                    substToEqs g (domSub xs g)
                               g = f `andThen` mkSubst sol

checkGuard :: (String -> TermS)
              -> Sig
              -> [String]
              -> (String -> Int)
              -> (TermS, t, TermS, t1, t2, Bool)
              -> Reducts
checkGuard f sig xs vc (guard,_,left,_,_,uni) =
   genMatchFailure sig uni (domSub xs f) left $
        if isFalse $ simplifyIter sig $ guard>>>f then Stop else Backward [] vc

-- | applyAx ax axs redex at p sig vc applies the axiom ax to the redex at
-- position p of at. vc is the variable counter that is needed for renaming the
-- variables of ax that are introduced into t.
applyAx :: TermS
           -> [TermS]
           -> TermS
           -> TermS
           -> [Int]
           -> Sig
           -> (String -> Int)
           -> Bool
           -> Reducts
applyAx (F "==>" [guard,F "<===" [F "->" [left,right],prem]]) axs redex 
        at@(F "->" [_,r]) p sig vc uni | notnull p =
     case redex of 
     F "^" reds 
       -> case left of 
          F "^" ts 
            -> try (reds,[0..lg-1]) 100
               where lg = length reds 
                     b = product [2..lg] > 100
                     xs = frees sig redex
                     pars = (guard,axs,left,right,prem,uni)
                     try (reds,s) 0 = 
                           if b then Backward [F "^" $ fst $ permute reds s] vc 
                                else Stop
                     try (reds,s) n = case searchReds checkGuard rewrite vc ts 
                                                    reds True eq sig xs pars of
                                           Just reduct -> reduct
                                           _ -> try (permute reds s) $ n-1
          _ -> foldl (applyTo reds) Stop $ indices_ reds
     _ -> applyTo [redex] Stop 0
     where eq = mkEq right r
           applyTo reds reduct i =               
               case partialUnify guard axs left right prem at eq p sig vc uni $
                                 reds!!i of
               (Backward ts vc) 
                 -> case reduct of
                         Backward reducts vc -> Backward (reducts++reducts') vc
                         _ -> Backward reducts' vc 
                    where reducts' = map (addTo True $ context i reds) ts
               _ -> reduct
       
applyAx (F "==>" [guard,F "<===" [F x [left,right],prem]]) axs redex at p sig
     vc uni | x `elem` words "= == <==>" = 
               partialUnify guard axs left right prem at (replace at p right) p
                            sig vc uni redex

applyAx (F "==>" [guard,F "<===" [at,prem]]) axs redex _ _ sig vc uni =
     case unify0 at redex redex [] sig xs of          
     TotUni f 
       -> genMatchFailure sig uni dom at $
                  case u of F "True" _ -> Backward [mkRed []] vc
                            F "False" _ -> Stop
                            _ -> case solveGuard sig u axs vc of
                                      Just sols -> Backward (map mkRed sols) vc
                                      _ -> Stop
          where dom = domSub xs f
                u = simplifyIter sig $ guard>>>f
                mkRed sol = quantify sig addAnys [at,prem] $ mkConjunct reduct
                            where g = f `andThen` mkSubst sol
                                  reduct = prem>>>g:substToEqs g (domSub xs g)
     _ -> Stop
     where xs = frees sig redex
                               
applyAx (F "==>" [guard,F "===>" [at,conc]]) axs redex _ _ sig vc uni =
     case unify0 at redex redex [] sig xs of
     TotUni f 
       -> genMatchFailure sig uni dom at $
                  case u of F "True" _ -> Forward [mkRed []] vc
                            F "False" _ -> Stop
                            _ -> case solveGuard sig u axs vc of
                                      Just sols -> Forward (map mkRed sols) vc
                                      _ -> Stop
          where dom = domSub xs f
                u = simplifyIter sig $ guard>>>f
                mkRed sol = quantify sig addAlls [at,conc] $ mkDisjunct reduct
                          where g = f `andThen` mkSubst sol
                                reduct = conc>>>g:substToIneqs g (domSub xs g)
     _ -> Stop
     where xs = frees sig redex

applyAx (F "==>" [guard,cl]) axs redex at p sig vc uni =
     applyAx (mkHornG guard cl mkTrue) axs redex at p sig vc uni

applyAx (F "===>" [prem,conc]) axs redex at p sig vc uni =
     applyAx (mkCoHornG mkTrue prem conc) axs redex at p sig vc uni

applyAx (F "<===" [conc,prem]) axs redex at p sig vc uni =
     applyAx (mkHornG mkTrue conc prem) axs redex at p sig vc uni

applyAx at axs redex t p sig vc uni =
     applyAx (mkHorn at mkTrue) axs redex t p sig vc uni

-- * __Rewriting of terms__
                                           
-- * auxiliary functions for applyAxToTerm (see below):
totalUnify :: TermS
              -> [TermS]
              -> TermS
              -> TermS
              -> Sig
              -> (String -> Int)
              -> TermS
              -> Reducts
totalUnify guard axs left right sig vc redex =
     case unify0 left redex redex [] sig xs of
          TotUni f -> rewriteTerm right f sig xs vc (guard,axs,left)
          _ -> Stop
     where xs = frees sig redex

rewriteTerm :: TermS
               -> (String -> TermS)
               -> Sig
               -> [String]
               -> (String -> Int)
               -> (TermS, [TermS], t)
               -> Reducts
rewriteTerm right f sig xs vc (guard,axs,_) =
     if notnull dom then Stop
     else case u of F "True" _ -> Sum [mkRed []] vc
                    F "False" _ -> Stop
                    _ -> case solveGuard sig u axs vc of
                              Just sols -> Sum (map mkRed sols) vc
                              _ -> Stop
     where dom = domSub xs f
           u = simplifyIter sig $ guard>>>f
           mkRed sol = right>>>(f `andThen` mkSubst sol)

checkGuardT :: (String -> TermS)
               -> Sig
               -> [String]
               -> (String -> Int)
               -> (TermS, t, t1)
               -> Reducts
checkGuardT f sig xs vc (guard, _, _)
    | notnull $ domSub xs f = Stop
    | isFalse $ simplifyIter sig $ guard >>> f = Stop
    | otherwise = Sum [] vc

-- | applyAxToTerm ax is applied only within a TERM. Hence ax must be a
-- (guarded or unguarded) equation without a premise.
applyAxToTerm :: TermS
                 -> [TermS] -> TermS -> Sig -> (String -> Int) -> Reducts
applyAxToTerm (F "==>" [guard,F "->" [left,right]]) axs redex sig vc =
     case redex of 
     F "^" reds 
       -> case left of 
          F "^" ts 
            -> try (reds,[0..lg-1]) 100
               where lg = length reds 
                     b = product [2..lg] > 100
                     xs = frees sig redex
                     pars = (guard,axs,left)
                     try (reds,s) 0 = 
                      if b then Sum [F "^" $ fst $ permute reds s] vc else Stop
                     try (reds,s) n = 
                       case searchReds checkGuardT rewriteTerm vc ts reds False
                                       right sig xs pars of 
                            Just reduct -> reduct
                            _ -> try (permute reds s) $ n-1
          _ -> foldl (applyTo reds) Stop $ indices_ reds
     _ -> applyTo [redex] Stop 0
     where applyTo reds reduct i =
               case totalUnify guard axs left right sig vc $ reds!!i of
                    (Sum ts vc)
                      -> case reduct of 
                              Sum reducts vc -> Sum (reducts++reducts') vc
                              _ -> Sum reducts' vc
                         where reducts' = map (addTo False $ context i reds) ts
                    _ -> reduct
            
applyAxToTerm (F "==>" [guard,F x [left,right]]) axs redex sig vc 
    | x `elem` words "= == <==>" = totalUnify guard axs left right sig vc redex

applyAxToTerm t@(F _ [_,_]) axs redex sig vc =
    applyAxToTerm (F "==>" [mkTrue,t]) axs redex sig vc

applyAxToTerm _ _ _ _ _ = Stop

-- * __Application of theorems__

-- | applySingle and applyMany work similarly to applyAxs, but apply only single
-- non-guarded clauses. In the case of applyMany, the redex splits into several
-- factors or summands of a conjunction resp. disjunction. applySingle and 
-- applyMany are used by applyTheorem and finishDisCon, respectively (see Ecom).
applySingle :: TermS
               -> TermS
               -> TermS
               -> [Int]
               -> Sig
               -> t
               -> Maybe (TermS, t)
applySingle (F "<===" [F "False" _,prem]) redex t p sig vc =
       Just (replace t p $ mkImpl (mkNot sig redex) conc, vc)
       where conc = mkAny (frees sig prem) prem

applySingle (F "===>" [F "True" _,conc]) redex t p sig vc =
       Just (replace t p $ mkImpl prem redex, vc)
        where prem = mkAll (frees sig conc) conc

applySingle (F "<===" [F "->" [left,right],prem]) redex t p sig vc
       | notnull p && isTerm sig redex =
                 do (F "->" [_,r],0) <- Just (getSubterm t q,last p)
                    (f,rest) <- unify left
                    let eq = addTo True rest $ mkEq right r
                        eqs = substToEqs f $ domSub xs f
                        reduct = mkConjunct $ eq>>>f:prem>>>f:eqs
                        reduct' = quantify sig addAnys [left,right,prem] reduct
                    Just (replace t q reduct',vc)
                 where xs = frees sig redex; reds = mkElems redex; q = init p
                       unify (F "^" ts) = unifyAC ts reds V sig xs
                       unify t          = unifyAC [t] reds V sig xs

applySingle th@(F "<===" [at,prem]) redex t p sig vc =
    case unify0 at redex t p sig xs of
         TotUni f -> Just (replace t p reduct',vc)
                     where dom = domSub xs f
                           reduct = mkConjunct $ prem>>>f:substToEqs f dom
                           reduct' = quantify sig addAnys [at,prem] reduct
         _ -> do F _ [F "=" [left,right], F "True" _] <- Just th
                 TotUni f <- Just $ unify0 left redex t p sig xs
                 let dom = domSub xs f
                     ts = prem>>>f:substToEqs f dom
                     bind = quantify sig addAnys [left,right,prem] . mkConjunct
                 do (q,at,r) <- atomPosition sig t p
                    Just (replace t q $ bind $ replace at r right>>>f:ts,vc)
    where xs = frees sig redex

applySingle (F "===>" [at,conc]) redex t p sig vc =
      do TotUni f <- Just $ unify0 at redex t p sig xs
         let dom = domSub xs f
             reduct = mkDisjunct $ conc>>>f:substToIneqs f dom
             reduct' = quantify sig addAlls [at,conc] reduct
         Just (replace t p reduct',vc)
      where xs = frees sig redex

applySingle at redex t p sig vc = 
      applySingle (mkHorn at mkTrue) redex t p sig vc

applyMany :: Bool
             -> Bool
             -> [TermS]
             -> TermS
             -> [TermS]
             -> TermS
             -> [[Int]]
             -> [Int]
             -> [[Int]]
             -> Sig
             -> t
             -> Maybe (TermS, t)
applyMany forward different left right redices t ps pred qs sig vc =
      do Def (f,True) <- Just $ unify' left redices (V"") t 
                                       (replicate (length left) []) ps V sig xs
         let dom = domSub xs f
             (mk1,mk2,addQuants,subst)
                 = if forward then (mkDisjunct,mkConjunct,addAlls,substToIneqs)
                              else (mkConjunct,mkDisjunct,addAnys,substToEqs)
             reduct1 = mk1 $ right>>>f:subst f dom
             reduct2 = quantify sig addQuants (right:left) reduct1
             newIndices = map head qs
             ts = subterms $ getSubterm t pred
             us = zipWith f newIndices $ map tail qs
                  where f i p = replace (ts!!i) p reduct2
             vs = [ts!!i | i <- indices_ ts, i `notElem` newIndices]
             reduct3 = if different then mk2 $ mk1 us:vs else mk1 $ us++vs
         Just (replace t pred reduct3,vc)
      where xs = freesL sig redices

-- | applyToHeadOrBody is used by 'Ecom.applyInd'.
applyToHeadOrBody :: Sig
                     -> (TermS -> [Int] -> Bool)
                     -> Bool
                     -> [TermS]
                     -> [TermS]
                     -> VarCounter
                     -> ([TermS], VarCounter)
applyToHeadOrBody sig g head axs = f
 where f (t:cls) vc = 
         case t of F x [h,b] | x `elem` words "<=== ===>" 
                     -> if head then (F x [redh,b]:clsh,vch)
                                       else (F x [h,redb]:clsb,vcb)
                        where (redh,clsh,vch) = redvc h
                              (redb,clsb,vcb) = redvc b
                   _ -> (redt:clst,vct) where (redt,clst,vct) = redvc t
         where redvc t = (reduct,cls',vc3)
                  where (axs',vc1) = renameApply axs sig t vc
                        (reduct,vc2) = applyPar axs' ps t vc1
                        (cls',vc3) = f cls vc2
                        ps = filter (g t) $ positions t
               -- applyPar axs t ps sig applies axs in parallel at all 
               -- positions of t that are in ps.
               applyPar axs (p : ps) t vc
                    | p `notElem` positions t || isVarRoot sig redex = proceed0
                    | isDefunct sig sym =
                      case atomPosition sig t p of
                          Just (_, at, r) ->
                            case apply at r of
                                 Backward reds vc -> proceed mkDisjunct reds vc
                                 _ -> proceed0
                          _ -> proceed0
                    | isPred sig sym =
                      case apply redex [] of
                          Backward reds vc -> proceed mkDisjunct reds vc
                          _ -> proceed0
                    | isCopred sig sym =
                      case apply redex [] of
                          Forward reds vc -> proceed mkConjunct reds vc
                          _ -> proceed0
                    | otherwise = proceed0
                  where redex = getSubterm t p
                        sym = getOp redex
                        cls = filterClauses sig redex axs
                        apply at r = fst $ applyAxs cls cls [] redex at r sig
                                                     vc True
                        proceed0 = applyPar axs ps t vc
                        proceed mk = applyPar axs ps . replace t p . mk
               applyPar _ _ t vc = (t,vc)
       f _ vc = ([],vc)

-- | mkComplAxiom sig ax transforms an axiom ax for p into an axiom for NOTp and
-- is used by negateAxioms (see Ecom).
mkComplAxiom :: Sig -> TermS -> TermS
mkComplAxiom sig t =
        case t of F "==>" [guard,t]        -> mkImpl guard $ mkComplAxiom sig t
                  F "===>" [t,F "False" _] -> t
                  F "===>" [t,u]           -> mkHorn (neg t) $ f $ neg u
                  F "<===" [t,u]           -> mkCoHorn (neg t) $ f $ neg u
                  t                        -> mkCoHorn t mkFalse
        where neg = mkNot sig
              f = simplifyIter sig

-- | flatten k xs cl turns cl into an equivalent clause cl' such that all
-- equations t=u of cl' are flat wrt xs, (e i). either root(t) is in xs and all
-- other symbols of t or u are not in xs or u=t is flat wrt xs.
flatten :: (Num t, Show t) =>
           t -> [String] -> TermS -> (TermS, t)
flatten k [] cl                     = (cl,k)
flatten k xs (F "==>" [guard,cl])   = (F "==>" [guard,cl'],n)
                                      where (cl',n) = flatten k xs cl
flatten k xs (F "<===" [conc,prem]) = mkFlatEqs k xs conc prem
flatten k xs at                     = mkFlatEqs' k xs at

mkFlatEqs :: (Num a, Show a) =>
             a -> [String] -> TermS -> TermS -> (TermS, a)
mkFlatEqs k xs conc prem = 
                      if null tps && null ups then (mkHorn conc prem,k)
                      else mkFlatEqs n xs conc' (mkConjunct (prem':eqs1++eqs2))
                      where tps = flatCands xs [] conc
                            ups = flatCands xs [] prem
                            (conc',eqs1,m) = mkEqs tps conc [] k
                            (prem',eqs2,n) = mkEqs ups prem [] m

mkFlatEqs' :: (Num a, Show a) =>
              a -> [String] -> TermS -> (TermS, a)
mkFlatEqs' k xs at = if null tps then (at,k) 
                                  else mkFlatEqs n xs at' (mkConjunct eqs)
                     where tps = flatCands xs [] at
                           (at',eqs,n) = mkEqs tps at [] k

-- | mkEqs tps t [] k creates for each (u,p) in tps an equation u=zn with n>=k
-- and replaces u in t by zn.
mkEqs :: (Num a, Show a) =>
         [(TermS, [Int])]
         -> TermS
         -> [TermS]
         -> a
         -> (TermS, [TermS], a)
mkEqs ((u,p):tps) t eqs k = mkEqs tps (replace t p new) (eqs++[mkEq u new]) 
                                                        (k+1)
                             where new = newVar k
mkEqs _ t eqs k           = (t,eqs,k)

{-
    | flatCands xs [] t returns the list of pairs (u,p) such that u is the
    subterm
    of t at position p and the root of u is in xs, but u is not the left- or
    right-hand side of a flat equation.
-}
flatCands :: [String] -> [Int] -> TermS -> [(TermS, [Int])]
flatCands xs p (F "=" [l,r])
    | x `elem` xs = concat (zipWith (flatCands xs) ps (concat tss))
                ++ flatCands xs p1 r
    | y `elem` xs = flatCands xs p0 l ++
                concat (zipWith (flatCands xs) qs (concat uss))
                                where (x,tss) = unCurry l
                                      (y,uss) = unCurry r
                                      p0 = p++[0]
                                      p1 = p++[1]
                                      ps = curryPositions p0 tss
                                      qs = curryPositions p1 uss
flatCands xs p t | getOp t `elem` xs = [(t,p)]
flatCands xs p (F _ ts) = concat $ zipWithSucs (flatCands xs) p ts
flatCands _ _ _         = []

-- | curryPositions [] [t1,...,tn] = ps1++...++psn implies that for all 1<=i<=n,
-- psi are the root positions of ti within f(t1)...(tn).
curryPositions :: [Int] -> [[a]] -> [[Int]]
curryPositions _ []   = []
curryPositions p [ts] = succsInd p ts
curryPositions p tss  = map (0:) (curryPositions p $ init tss) ++
                         succsInd p (last tss)

-- | preStretch prem f t checks whether the premises (prem = True) or
-- conclusions
-- (prem = False) of t can be stretched. If so, then preStretch returns their 
-- leading function/relation x and the positions varps of all subterms to be 
-- replaced by variables. f is a condition on x.

preStretch :: Bool -> (String -> Bool) -> TermS -> Maybe (String,[Int])
preStretch prem f t = 
   case t of F "&" ts -> do s <- mapM g ts
                            let (xs,tss@(ts:uss)) = unzip s
                                varps = joinMap toBeReplaced tss `join`
                                        [i | i <- indices_ ts,
                                             any (neqTerm (ts!!i) . (!!i)) uss]
                            guard $ allEqual xs && allEqual (map length tss)
                            Just (head xs,varps)
             F "==>" [F "=" [u,_],v] -> do (x,ts) <- g $ if prem then u else v
                                           Just (x,toBeReplaced ts)
             F "==>" [u,v] -> do (x,ts) <- g $ if prem then u else v
                                 Just (x,toBeReplaced ts)
             F "=" [u,_] -> do (x,ts) <- g $ if prem then u else t
                               Just (x,toBeReplaced ts)
             _ -> do guard $ not prem; (x,ts) <- g t; Just (x,toBeReplaced ts)
   where g t = do guard $ f x; Just (x,concat tss) where (x,tss) = unCurry t
         toBeReplaced ts = [i | i <- indices_ ts, let t = ts!!i; x = root t,
                                  isF t || not (noExcl x) ||
                                any (x `isin`) (context i ts) ]

-- | stretchConc k ns t replaces the subterms of t at positions ns by variables
-- zk,z(k+1),... and turns t into a Horn axiom to be used by a proof by 
-- coinduction.
stretchConc,stretchPrem :: Int -> [Int] -> TermS -> (TermS,Int)

stretchConc k ns (F "&" (cl:cls)) = (mkHorn conc $ mkDisjunct $ prem:map g cls,
                                      n)
        where (F "<===" [conc,prem],n) = f cl
              f (F "==>" [prem,t]) = (mkHorn conc $ mkConjunct $ prem:eqs,n)
                         where (x,tss) = unCurry t
                               (us,eqs,n) = addEqs (concat tss) [] [] k ns 0
                               conc = mkApplys (x,mkLists us $ map length tss)
              f t = f $ F "==>" [mkTrue,t]
              g (F "==>" [prem,t]) = mkConjunct $ prem:eqs
                                     where (_,tss) = unCurry t
                                           eqs = addEqs0 (concat tss) [] k ns 0
              g t = g $ F "==>" [mkTrue,t]
stretchConc k ns cl = stretchConc k ns $ F "&" [cl]

-- | stretchPrem k ns t replaces the subterms of t at positions ns by variables
-- zk,z(k+1),... and turns t into a co-Horn axiom to be used by a proof by
-- fixpoint induction.

stretchPrem k ns (F "&" (cl:cls)) = (mkCoHorn prem $ mkConjunct $ conc:cls',
                                     maximum $ n:ks)
 where (F "===>" [prem,conc],n) = f cl
       f (F "==>" [F "=" [t,r],conc]) = (mkCoHorn prem $ mkImpl prem' conc,m)
                   where (x,tss) = unCurry t
                         (us,eqs,n) = addEqs (concat tss) [] [] k ns 0
                         u = mkApplys (x,mkLists us (map length tss))
                         (r',eqs',m) = if isV r && root r `notElem` map root us
                                       then (r,eqs,n)
                                       else (new,mkEq new r:eqs,n+1)
                         prem = mkEq u r'; prem' = mkConjunct eqs'
                         new = newVar n
       f (F "==>" [t,conc]) = (mkCoHorn prem $ mkImpl prem' conc,n)
                         where (x,tss) = unCurry t
                               (us,eqs,n) = addEqs (concat tss) [] [] k ns 0
                               prem = mkApplys (x,mkLists us (map length tss))
                               prem' = mkConjunct eqs
       f (F "=" [t,r]) = (mkCoHorn prem $ mkImpl prem' $ mkEq new r,n+1)
                         where (x,tss) = unCurry t
                               (us,eqs,n) = addEqs (concat tss) [] [] k ns 0
                               u = mkApplys (x,mkLists us $ map length tss)
                               new = newVar n
                               prem = mkEq u new
                               prem' = mkConjunct eqs
       (cls',ks) = unzip $ map g cls
       g (F "==>" [F "=" [t,r],conc]) = (mkImpl (mkConjunct eqs') conc,m)
                      where (_,tss) = unCurry t
                            (us,eqs,n) = addEqs (concat tss) [] [] k ns 0
                            (eqs',m) = if isV r && root r `notElem` map root us
                                       then (eqs,n)
                                       else (mkEq (newVar n) r:eqs,n+1)
       g (F "==>" [t,conc]) = (mkImpl (mkConjunct eqs) conc,n)
                              where (_,tss) = unCurry t
                                    eqs = addEqs0 (concat tss) [] k ns 0
       g (F "=" [t,r]) = (mkImpl (mkConjunct eqs) $ mkEq (newVar n) r,n+1)
                         where (_,tss) = unCurry t
                               eqs = addEqs0 (concat tss) [] k ns 0
stretchPrem k ns cl = stretchPrem k ns $ F "&" [cl]

-- | For each term t of ts at a position in ns, addEqs ts [] [] k ns 0 replaces
-- t by a new variable zn for some n >= k and creates the equation zn=t.
addEqs :: [TermS] -> [TermS] -> [TermS] -> Int -> [Int] -> Int 
                  -> ([TermS],[TermS],Int)
addEqs [] us eqs k _ _  = (us,eqs,k)
addEqs ts us eqs k [] _ = (us++ts,eqs,k)
addEqs (t:ts) us eqs k ns n =
          if n `elem` ns then addEqs ts (us++[u]) (eqs++[mkEq u t]) (k+1) ms n'
                         else addEqs ts (us++[t]) eqs k ms n'
          where u = newVar k; ms = ns`minus1`n; n' = n+1
            
addEqs0 :: [TermS] -> [TermS] -> Int -> [Int] -> Int -> [TermS]
addEqs0 [] eqs _ _ _      = eqs
addEqs0 _ eqs _ [] _      = eqs
addEqs0 (t:ts) eqs k ns n = addEqs0 ts eqs' k' (ns`minus1`n) (n+1)
           where (eqs',k') = if n `elem` ns then (eqs++[mkEq (newVar k) t],k+1)
                                            else (eqs,k)

-- | replaceByApprox and updArgsA are used by mk(Co)HornLoop (see below).
replaceByApprox :: TermS -> String -> TermS -> TermS
replaceByApprox i x = f 
                   where f (F "$" [t,u]) = if x == getOp t 
                                           then applyL (F "$" [addLoop t,i]) ts
                                           else applyL t ts
                                     where ts = case u of F "()" us -> map f us
                                                          _ -> [f u]
                         f (F y ts)      = if x == y 
                                           then F (x++"Loop") $ i:map f ts
                                           else F x $ map f ts
                         f t             = t

updArgsA :: TermS -> TermS -> [TermS] -> TermS
updArgsA (F "$" [t,_]) i ts = applyL (F "$" [addLoop t,i]) ts
updArgsA (F x _) i ts       = F (x++"Loop") $ i:ts
updArgsA t _ _              = t

addLoop :: TermS -> TermS
addLoop (F "$" [t,u]) = F "$" [addLoop t,u]
addLoop (F x ts)      = F (x++"Loop") ts
addLoop t             = t

-- | mkEqsWithArgs is used by mk(Co)HornLoop and compressAll (see below).
mkEqsWithArgs :: t -> [TermS] -> [Int] -> TermS -> [TermS]
mkEqsWithArgs _ zs is = zipWith mkEq zs . contextM is . getArgs

-- | mkHornLoop sig x transforms the co-Horn axioms for x into an equivalent set
-- of three Horn axioms and is used by kleeneAxioms (see Ecom).
mkHornLoop :: Sig
              -> t -> [TermS] -> TermS -> Int -> ([TermS], Int)
mkHornLoop sig _ axs i k = f axs
  where f axs = ([mkHorn (updArgs t zs) $ mkAll [root i] $ updArgsA t i zs,
                  updArgsA t mkZero zs,
                  mkHorn (updArgsA t (mkSuc i) zs) $ mkConjunct 
                                                      $ map mkPrem axs],
                 k')
          where t = g (head axs)
                (x,ts) = getOpArgs t
                k' = k+length ts
                zs = map (V . ('z':) . show) [k..k'-1]
                mkPrem (F "==>" [guard,F "===>" [t,u]]) = 
                                            mkPrem $ mkCoHorn t $ mkImpl guard u
                mkPrem cl@(F "===>" [t,u]) = simplifyIter sig conc
                              where conc = mkAll xs $ mkImpl (mkConjunct eqs) v
                                    xs = frees sig cl `minus` getOpSyms t
                                    eqs = mkEqsWithArgs sig zs [] t
                                    v = replaceByApprox i x u
                mkPrem t = t
        g (F "==>" [_,cl])  = g cl
        g (F "===>" [at,_]) = at
        g t                     = t

-- | mkCoHornLoop sig x transforms the Horn axioms for x into an equivalent set
-- of three co-Horn axioms and is used by kleeneAxioms (see Ecom).
mkCoHornLoop :: Sig
                -> t -> [TermS] -> TermS -> Int -> ([TermS], Int)
mkCoHornLoop sig _ axs i k = f axs
  where f axs = ([mkCoHorn (updArgs t zs) $ mkAny [root i] $ updArgsA t i zs,
                  mkCoHorn (updArgsA t mkZero zs) mkFalse,
                  mkCoHorn (updArgsA t (mkSuc i) zs) $ mkDisjunct
                                                         $ map mkConc axs],
                 k')
          where t = g (head axs)
                (x,ts) = getOpArgs t
                k' = k+length ts
                zs = map (V . ('z':) . show) [k..k'-1]
                eqs = mkEqsWithArgs sig zs []
                mkConc (F "==>" [guard,F "<===" [t,u]]) =
                                        mkConc $ mkHorn t $ mkConjunct [guard,u]
                mkConc cl@(F "<===" [t,u]) = simplifyIter sig prem
                                   where prem = mkAny xs $ mkConjunct $ v:eqs t
                                         xs = frees sig cl `minus` getOpSyms t
                                         v = replaceByApprox i x u
                mkConc t = simplifyIter sig $ mkAny xs $ mkConjunct $ eqs t
                           where xs = frees sig t `minus` getOpSyms t
        g (F "==>" [_,cl])  = g cl
        g (F "<===" [at,_]) = at
        g t                 = t
        
-- | compressAll sig k axs transforms the axioms of axs into a single axiom
-- (if b = True) and inverts it (if b = False). 
-- compressAll is used by compressAxioms (see Ecom).
compressAll :: (Enum t, Num t, Show t) =>
               Bool -> Sig -> t -> [TermS] -> (TermS, t)
compressAll b sig i axs = compressOne b sig i [] axs $ h $ head axs
                          where h (F "==>" [_,cl])  = h cl
                                h (F "===>" [at,_]) = h at
                                h (F "<===" [at,_]) = h at
                                h (F "=" [t,_])     = t
                                h t                     = t

combineOne :: (Enum a, Num a, Show a) => Sig
           -> a -> [Int] -> TermS -> [TermS] -> (TermS, a)
combineOne sig i ks ax axs = compressOne True sig i ks cls t
                         where cls = [axs!!i | i <- indices_ axs, all (f i) ks]
                               t = h ax
                               ts = getArgs t
                               tss = map (getArgs . h) axs
                               f i k = eqTerm ((tss!!i)!!k) (ts!!k) 
                               h (F "==>" [_,cl])  = h cl
                               h (F "===>" [at,_]) = h at
                               h (F "<===" [at,_]) = h at
                               h (F "=" [t,_])     = t
                               h t                    = t

compressOne :: (Enum a, Num a, Show a) =>
               Bool
               -> Sig
               -> a
               -> [Int]
               -> [TermS]
               -> TermS
               -> (TermS, a)
compressOne b sig i ks cls t
        | isPred sig x = (g (updArgs t us) $ compressHorn sig eqs cls, j)
        | isDefunct sig x =
          (g (mkEq (updArgs t us) z) $ compressHornEq sig eqs' cls, j + 1)
        | otherwise = (h (updArgs t us) $ compressCoHorn sig eqs cls, j)
     where (x,ts) = getOpArgs t
           (us,j) = foldr f ([],i) $ indices_ ts
           eqs = mkEqsWithArgs sig (map newVar [i..j-1]) ks
           z = newVar j 
           eqs' t u = mkEq z u:eqs t
           f i (us,k) = if i `elem` ks then (ts!!i:us,k) else (newVar k:us,k+1)
           (g,h) = if b then (mkHorn,mkCoHorn) else (mkCoHorn,mkHorn)

-- | compressHorn sig eqs transforms Horn axioms for a predicate into the
-- premise of an equivalent single Horn axiom. 
compressHorn :: Sig
             -> (TermS -> [TermS]) -> [TermS] -> TermS
compressHorn sig eqs = mkDisjunct . map mkPrem
      where mkPrem (F "==>" [guard,F "<===" [t,u]]) =
                                        mkPrem $ mkHorn t $ mkConjunct [guard,u]
            mkPrem cl@(F "<===" [t,u]) = simplifyIter sig prem
                                   where prem = mkAny xs $ mkConjunct $ u:eqs t
                                         xs = frees sig cl `minus` getOpSyms t
            mkPrem t = simplifyIter sig $ mkAny xs $ mkConjunct $ eqs t
                       where xs = frees sig t `minus` getOpSyms t

-- | compressHornEq sig eqs transforms Horn axioms for a defined function into
-- the premise of an equivalent single Horn axiom.
compressHornEq :: Sig
                  -> (TermS -> TermS -> [TermS])
                  -> [TermS]
                  -> TermS
compressHornEq sig eqs = mkDisjunct . map mkPrem
      where mkPrem (F "==>" [guard,F "<===" [t,u]]) =
                                        mkPrem $ mkHorn t $ mkConjunct [guard,u]
            mkPrem cl@(F "<===" [F "=" [t,u],v]) = simplifyIter sig prem
                                 where prem = mkAny xs $ mkConjunct $ v:eqs t u
                                       xs = frees sig cl `minus` getOpSyms t
            mkPrem cl@(F "=" [t,u]) = simplifyIter sig prem
                                   where prem = mkAny xs $ mkConjunct $ eqs t u
                                         xs = frees sig cl `minus` getOpSyms t
            mkPrem t = t

-- | compressCoHorn sig eqs transforms co-Horn axioms for a copredicate into the 
-- conclusion of an equivalent single co-Horn axiom.
compressCoHorn :: Sig
               -> (TermS
               -> [TermS])
               -> [TermS]
               -> TermS
compressCoHorn sig eqs = mkConjunct . map mkConc
      where mkConc (F "==>" [guard,F "===>" [t,u]]) =
                                            mkConc $ mkCoHorn t $ mkImpl guard u
            mkConc cl@(F "===>" [t,u]) = simplifyIter sig conc
                          where conc = mkAll xs $ mkImpl (mkConjunct (eqs t)) u
                                xs = frees sig cl `minus` getOpSyms t
            mkConc t = t

-- | moveUp sig vc x us is moves the quantifiers from positions 
-- q++[is!!0],...,q++[is!!length is-1] of t to position q. F x us is the
-- original term at position q. moveUp is used by shiftQuants (see Ecom).
moveUp :: Sig
          -> VarCounter
          -> String
          -> [TermS]
          -> [Int]
          -> ([String], [String], TermS, VarCounter)
moveUp sig vc "==>" us@[u,v] is = (as',es',F "==>" ts,vc')
 where split (ps,qs) i = if isAllQ t then ((i,alls t):ps,qs) 
                                       else (ps,(i,anys t):qs)
                         where t = us!!i
       [u1,v1] = zipWith g us [0,1]
       g u i = if i `elem` is then head $ subterms u else u
       h = renaming vc
       (as',es',ts,vc') = 
        case foldl split nil2 is of 
             ([(0,as0),(1,as1)],[]) -> (map f as1,as0,[u1,renameFree f v1],vc1)
                                       where (f,vc1) = h $ meet as0 as1
             ([],[(0,es0),(1,es1)]) -> (es0,map f es1,[u1,renameFree f v1],vc1)
                                       where (f,vc1) = h $ meet es0 es1
             ([(0,as)],[(1,es)]) -> ([],as++map f es,[u1,renameFree f v1],vc1)
                                    where (f,vc1) = h $ meet as es
             ([(1,as)],[(0,es)]) -> (es++map f as,[],[u1,renameFree f v1],vc1)
                                     where (f,vc1) = h $ meet as es
             ([(0,as)],[])       -> ([],map f as,[renameFree f u1,v1],vc1)
                                    where zs = frees sig v `meet` as
                                          (f,vc1) = h zs
             ([(1,as)],[])       -> (map f as,[],[u1,renameFree f v1],vc1)
                                    where zs = frees sig u `meet` as
                                          (f,vc1) = h zs
             ([],[(0,es)])       -> (map f es,[],[renameFree f u1,v1],vc1)
                                    where zs = frees sig v `meet` es
                                          (f,vc1) = h zs
             ([],[(1,es)])       -> ([],map f es,[u1,renameFree f v1],vc1)
                                    where zs = frees sig u `meet` es
                                          (f,vc1) = h zs
moveUp _ vc "Not" [u] _ = (anys u,alls u,F "Not" [head (subterms u)],vc)
moveUp sig vc x us is   = (joinMap snd ps',joinMap snd qs',F x ts',vc')
       where (ps,qs) = foldl split nil2 is 
             split (ps,qs) i = if isAllQ t then ((i,alls t):ps,qs) 
                                           else (ps,(i,anys t):qs)
                               where t = us!!i
             free = freesL sig $ contextM is ts
             ts = zipWith h us $ indices_ us
                  where h u i = if i `elem` is then head $ subterms u else u
             (ts',vc',ps',qs') = loop1 (ts,vc,ps,qs) ps
             loop1 (ts,vc,ps,qs) (p@(i,xs):ps1) = loop1 (ts',vc',ps',qs) ps1
                             where rest = ps `minus1` p
                                   zs = if x == "&" then free 
                                        else join free $ joinMap snd $ rest++qs
                                   (f,vc') = renaming vc (xs `meet` zs)
                                   ts' = updList ts i $ renameFree f $ ts!!i
                                   ps' = (i,map f xs):rest
             loop1 state _ = loop2 state qs
             loop2 (ts,vc,ps,qs) (q@(i,xs):qs1) = loop2 (ts',vc',ps,qs') qs1
                             where rest = qs `minus1` q
                                   zs = if x == "|" then free 
                                        else join free $ joinMap snd $ rest++ps
                                   (f,vc') = renaming vc $ meet xs zs
                                   ts' = updList ts i $ renameFree f $ ts!!i
                                   qs' = (i,map f xs):rest
             loop2 state _ = state

shiftSubformulas :: Sig -> TermS -> [[Int]] -> Maybe TermS
shiftSubformulas sig t ps =
  case search (isImpl . getSubterm1 t) qs of
       Just i | (p == left || p == right) && length ps > 1 && all (== r) rs
         -> if p == left && r == right && isDisjunct conc 
            then impl t q prem1 conc1
            else do guard $ p == right && r == left && isConjunct prem
                    impl t q prem2 conc2
            where p = ps!!i; q = qs!!i
                  left = q++[0]; right = q++[1]
                  r:rs = context i qs 
                  F _ [prem,conc] = getSubterm1 t q
                  ms = map last $ context i ps
                  ns cl = indices_ (subterms cl) `minus` ms
                  f i = getSubterm1 conc [i]
                  g i = getSubterm1 prem [i]
                  prem1 = mkConjunct $ map (mkNot sig . f) ms
                  --conc1 = mkDisjunct $ neg prem:map f (ns conc)
                  conc1 = mkImpl prem $ mkDisjunct $ map f $ ns conc
                  prem2 = mkConjunct $ mkNot sig conc:map g (ns prem)
                  conc2 = mkDisjunct $ map (mkNot sig . g) ms
       Nothing | notnull qs
         -> if all (== r) rs && isDisjunct u 
            then impl t r (mkConjunct $ map (mkNot sig . v) ns) $
                               mkDisjunct $ map v ks
            else let r:rs = map init qs
                     u = getSubterm1 t r
                     F _ [prem,conc] = u
                     ns k = map last [ps!!i | i <- ms, last (qs!!i) == k]
                     cs = indices_ (subterms prem) `minus` ns 0
                     ds = indices_ (subterms conc) `minus` ns 1
                     pr i = getSubterm1 prem [i]
                     co i = getSubterm1 conc [i]
                     --concs = map (neg . pr) $ ns 0
                     newImpl = mkImpl $ mkConjunct $ map pr $ ns 0
                     prems = map (mkNot sig . co) $ ns 1
                     prem1 = mkConjunct $ map pr cs++prems
                     --conc1 = mkDisjunct $ concs++map co ds
                     conc1 = newImpl $ mkDisjunct $ map co ds
                     prem2 = mkConjunct $ map pr cs
                     --conc2 = mkDisjunct $ conc:concs
                     conc2 = newImpl conc
                     prem3 = mkConjunct $ prem:prems
                     conc3 = mkDisjunct $ map co ds
                 in do guard $ all notnull qs && isImpl u && all (== r) rs
                       if isConjunct prem
                          then if isDisjunct conc then impl t r prem1 conc1
                                                  else impl t r prem2 conc2
                          else impl t r prem3 conc3
            where r:rs = qs
                  u = getSubterm1 t r
                  ms = indices_ ps
                  ns = map last [ps!!i | i <- ms]
                  ks = indices_ (subterms u) `minus` ns
                  v i = getSubterm1 u [i]
       _ -> Nothing
  where qs = map init ps
        impl t p u v = Just $ replace1 t p $ mkImpl u v

-- | getOtherSides t p ts ps looks for in/equations eq in the
-- premises/conclusions
-- of t such that one side of eq agrees with some u in ts. If so, u is replaced
-- by the other side of q. p and ps are the positions of t and ts, respectively.
-- getOtherSides is used by replaceSubtrees (see Ecom).
getOtherSides :: TermS -> [Int] -> [TermS] -> [[Int]] -> Maybe [TermS]
getOtherSides t p ts ps =
    case t of F "==>" [F "&" prems,
                  F "|" concs]           -> f prems (p0 prems) concs $ p1 concs
              F "==>" [F "&" prems,conc] -> f prems (p0 prems) [conc] [p++[1]]
              F "==>" [prem,F "|" concs] -> f [prem] [p++[0]] concs $ p1 concs
              F "==>" [prem,conc]        -> f [prem] [p++[0]] [conc] [p++[1]]
              F "&" prems                  -> f prems (succsInd p prems) [] []
              F "|" concs                -> f [] [] concs $ succsInd p concs
              _                          -> Nothing
    where p0 = succsInd $ p++[0]
          p1 = succsInd $ p++[1]
          b eqps i k = not (eqps!!i <<= ps!!k)
          f prems ps1 concs ps2 = Just (g1 ts [] prems 0)
                where g1 ts rest1 (t@(F "=" [l,r]):rest2) i =
                         case search (== l) ts of
                         Just k | b ps1 i k
                           -> g1 (updList ts k r) (rest1++[t]) rest2 (i+1)
                         _ -> case search (== r) ts of
                              Just k | b ps1 i k
                                -> g1 (updList ts k l) (rest1++[t]) rest2 (i+1)
                              _ -> g1 ts (rest1++[t]) rest2 (i+1)
                      g1 ts rest1 (t:rest2) i = g1 ts (rest1++[t]) rest2 (i+1)
                      g1 ts _ _ _             = g2 ts [] concs 0 
                      g2 ts rest1 (t@(F "=/=" [l,r]):rest2) i =
                         case search (== l) ts of
                         Just k | b ps2 i k
                           -> g2 (updList ts k r) (rest1++[t]) rest2 (i+1)
                         _ -> case search (== r) ts of
                              Just k | b ps2 i k 
                                -> g2 (updList ts k l) (rest1++[t]) rest2 (i+1)
                              _ -> g2 ts (rest1++[t]) rest2 (i+1)
                      g2 ts rest1 (t:rest2) i = g2 ts (rest1++[t]) rest2 (i+1)
                      g2 ts _ _ _             = ts

