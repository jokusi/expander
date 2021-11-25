-- {-# OPTIONS_GHC -fmax-pmcheck-iterations=4000000 #-}
{-|
Module      : Esolve (update from July 20, 2021)
Copyright   : (c) Peter Padawitz and Jos Kusiek, 2021
License     : BSD3
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

import Eterm
import Epaint (hilbshelf,reducePath)
import Prelude ()
import qualified Base.Haskell as Haskell
import Base.Gui
import Data.Array

-- * __String parser__ into signatures and signature maps

signature syms = concat [do key <- oneOf keywords; sigrest key syms,
                         return syms]

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
                                                 updRel hs x es),
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

showSignature :: ([String],[String],[String],[String],[String],PairsS) 
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

-- arithmetic expressions

data Arith a = Arith
    { parseA    :: TermS -> Maybe a
    , zeroA,one :: a
    , inv       :: a -> a
    , plus,minusA,timesA,divA,minA,maxA :: a -> a -> a
    }

-- Arith-algebras for integers, reals, linear functions and binary relations

intAlg :: Arith Int
intAlg = Arith
    { parseA = parseInt
    , zeroA = 0
    , one = 1
    , inv = \i -> -i
    , plus = (+)
    , minusA = (-)
    , timesA = (*)
    , divA = div
    , minA = min
    , maxA = max
    }

realAlg :: Arith Double
realAlg = Arith
    { parseA = parseReal
    , zeroA = 0
    , one = 1
    , inv = \r -> -r
    , plus = (+)
    , minusA = (-)
    , timesA = (*)
    , divA = (/)
    , minA = min
    , maxA = max
    }

linAlg :: Arith LinEq
linAlg = Arith
    { parseA = parseLin
    , zeroA = ([],0)
    , one = ([],1)
    , inv = mulLin ((-1)*)
    , plus = addLin
    , minusA = subLin
    , timesA = \f (_,a) -> mulLin (*a) f
    , divA = \f (_,a) -> mulLin (/a) f
    , minA = \_ _ -> ([],0)
    , maxA = \_ _ -> ([],1)
    }

relAlg :: Sig -> Arith (BinRel TermS)
relAlg sig = Arith
    { parseA = parseRel $ states sig
    , zeroA = []
    , one = [(x,x) | x <- states sig]
    , inv = minus pairs
    , plus = join
    , minusA = minus
    , timesA = \ps qs -> [p | p@(x,y) <- pairs, any ((== x) . fst) ps,
                                                any ((== y) . snd) qs]
    , divA = meet
    , minA = min
    , maxA = max
    }
    where pairs = prod2 (states sig) $ states sig
                   
foldArith :: Eq a => Arith a -> TermS -> Maybe a
foldArith alg = f
 where f (F "-" [t])        = do a <- f t; Just $ inv alg a
       f (F "+" [t,u])      = do a <- f t; b <- f u; Just $ plus alg a b
       f (F "sum" [F x ts]) | collector x
                            = do as <- mapM f ts; Just $ sum_ as
       f (F "-" [t,u])      = do a <- f t; b <- f u; Just $ minusA alg a b
       f (F "*" [t,u])      = do a <- f t; b <- f u; Just $ timesA alg a b
       f (F "product" [F x ts]) | collector x
                            = do as <- mapM f ts; Just $ prod as
       f (F "**" [t,u])     = do a <- f t; n <- parseNat u
                                 Just $ prod $ replicate n a
       f (F "/" [t,u])      = do a <- f t; b <- f u; guard $ b /= zeroA alg
                                 Just $ divA alg a b
       f (F "min" [t,u])    = do a <- f t; b <- f u; Just $ minA alg a b
       f (F "max" [t,u])    = do a <- f t; b <- f u; Just $ maxA alg a b
       f (F "min" [F x ts]) | collector x
                            = do as@(_:_)<- mapM f ts
                                 Just $ foldl1 (minA alg) as
       f (F "max" [F x ts]) | collector x
                            = do as@(_:_)<- mapM f ts
                                 Just $ foldl1 (maxA alg) as
       f t                  = parseA alg t
       sum_ = foldl (plus alg) $ zeroA alg
       prod = foldl (timesA alg) $ one alg

-- modal formulas

type Table a b = [Row a b]
type Row a b = [(a,b)]

data Modal state label atom = Modal {
           state'                     :: TermS -> Maybe state,
           label'                     :: TermS -> Maybe label,
           atom'                      :: TermS -> Maybe atom,
           trans'                     :: state -> [state],
           transL'                    :: state -> label -> [state],
           value'                     :: atom -> [state],
           valueL'                    :: atom -> label -> [state],
           preds'                     :: state -> [state],
           predsL'                    :: state -> label -> [state],
           out'                       :: state -> [atom],
           outL'                      :: state -> label -> [atom],
           detAuto                    :: Bool,
           unfoldD,unfoldND,unfoldNDS :: state -> [label] -> [atom],
           satP                       :: TermS -> [state],
           satR                       :: TermS -> BinRel state,
           selectS                    :: TermS -> BinRel state -> [state],
           topS,botS                  :: [state],
           notS                       :: [state] -> [state],
           orS,andS                   :: [state] -> [state] -> [state],
           divS,existsS,forallS       :: BinRel state -> [state] -> [state],
           pi1,pi2                    :: BinRel state -> [state],
           topR,botR                  :: BinRel state,
           invR,notR                  :: BinRel state -> BinRel state,
           orR,andR,comp :: BinRel state -> BinRel state -> BinRel state,
           prodR         :: [state] -> [state] -> BinRel state,
           child         :: [label] -> BinRel state,
           equivStep     :: BinRel state -> BinRel state,
           mkRow         :: state -> Row label state,
           mkTab         :: state -> Table label state,
           projectRow    :: [label] -> Row label state -> Row label state,
           project       :: [label] -> Table label state -> Table label state,
           mkInstance    :: TermS   -> Row label state   -> Bool,
           selectT       :: TermS   -> Table label state -> Table label state,
           orT,andT,minusT,njoin,prodT,divT
                 :: Table label state -> Table label state-> Table label state,
           sortT :: label -> Table label state -> Table label state}

getStateRel :: ([TermS] -> [a]) -> [TermS] -> BinRel a
getStateRel f = foldl g []
                where g rel (F "()" pair) = case f pair of [a,b] -> (a,b):rel
                                                           _ -> rel
                      g rel _ = rel

-- Modal-algebra for state sets, relations and tables

intModAlg :: Sig -> Modal Int Int Int
intModAlg sig = Modal { state'      = searchS sig,
                        label'      = searchL sig,
                        atom'       = searchA sig,
                        trans'      = trans',
                        transL'     = transL',
                        value'      = (value sig!!),
                        valueL'     = \i k -> valueL sig!!i!!k,
                        preds'      = (preds sig!!),
                        predsL'     = \i k -> predsL sig!!i!!k,
                        out'        = out',
                        outL'       = \i k -> outL sig!!i!!k,
                        detAuto     = all (all ((== 1) . length)) $ transL sig,
                        unfoldD     = \i -> out' . foldl detTransL i,
                        unfoldND    = \i -> out' <=< foldlM transL' i,
                        unfoldNDS   = \i -> out' <=< foldlMS succs transL' i,
                        satP        = toStates . satisfying sig,
                        satR        = getStateRel toStates . satisfyingR sig,
                        selectS     = selectS,
                        topS        = sts,
                        botS        = [],
                        notS        = minus sts,
                        orS         = join,
                        andS        = meet,
                        divS        = divS,
                        existsS     = existsS,
                        forallS     = forallS,
                        pi1         = mapSet fst,
                        pi2         = mapSet snd,
                        topR        = sts2,
                        botR        = [],
                        invR        = invR,
                        notR        = minus sts2,
                        orR         = join,
                        andR        = meet,
                        comp        = comp,
                        prodR       = prodR,
                        child       = child,
                        equivStep   = equivStep,
                        mkRow       = mkRow,
                        mkTab       = map mkRow . (trans sig!!),
                        projectRow  = projectRow,
                        project     = map . projectRow,
                        mkInstance  = mkInstance,
                        selectT     = filter . mkInstance,
                        orT         = join,
                        andT        = meet,
                        minusT      = minus,
                        njoin       = njoin,
                        prodT       = prodT,
                        divT        = divT,
                        sortT       = sortT } 
    where sts         = indices_ $ states sig
          labs        = indices_ $ labels sig
          ats         = indices_ $ atoms sig
          sts2        = [(i,j) | i <- sts, j <- sts]
          toStates ts = [get st | st <- map (searchS sig) ts]
          trans' i    = trans sig!!i
          transL' i k = transL sig!!i!!k
          detTransL i = head . transL' i
          out' i      = out sig!!i
          succs i     = successors trans' [i] 
          selectS p r = [i | i <- sts, isTrue $ sapply sig p $ mkList $ 
                                       map (states sig!!) $ relToFun r i]
          existsS r s = [i | i <- sts, relToFun r i `shares` s]
          forallS r s = [i | i <- sts, relToFun r i `subset` s]
          divS r s    = [i | i <- sts, s `subset` relToFun r i]
          invR r      = [(j,i) | (i,j) <- r]
          comp r r'   = [(i,k) | (i,j) <- r, (j',k) <- r', j == j']
          prodR s s'  = [(i,j) | i <- s, j <- s']
          child []    = [(i,j) | i <- sts, j <- trans sig!!i]
          child ks    = [(i,j) | i <- sts, k <- ks, j <- transL sig!!i!!k]
          equivStep r = [p | p@(i,j) <- r, i < j, outEquiv sig i j,
                             let rel i j = i == j || [(i,j),(j,i)] `shares` r
                                 f = forallThereis rel
                                 rs (is,js) = f is js && f js is,
                             all rs $ transEquiv sig i j]
          mkRow i  = fst $ foldr f ([],last labs) $ transL sig!!i where
                     f is (row,k) = if length is == 1 then ((k,head is):row,k-1)
                                                      else (row,k-1)
          projectRow ks    = filter $ (`elem` ks) . fst
          mkInstance p row = isTrue $ simplifyIter sig $ subst p where
                             subst p | just k && just i = states sig!!get i
                                                   where k = searchL sig p
                                                         i = lookup (get k) row
                             subst (F x ps) = F x $ map subst ps
                             subst p        = p
          njoin t t' = do row <- t; row' <- t'
                          let p lab = lookup lab row == lookup lab row'
                          guard $ all p $ map fst row `meet` map fst row'
                          [row `join` row']
          prodT t t' = do row <- t; row' <- t'
                          guard $ map fst row `disjoint` map fst row'
                          [row `join` row']
          divT t t'  = if (labs2 `subset` labs1) && notnull t'
                       then pi t `minus` pi (prodT (pi t) t' `minus` t) else []
                       where labs1 = mapSet fst $ joinM t
                             labs2 = mapSet fst $ joinM t'
                             pi = map $ projectRow $ labs1 `minus` labs2
          sortT k = qsort rel where
                    rel row1 row2 = nothing st2 || just st1 && just st2 &&
                                                   f st1 < f st2
                                    where st1 = lookup k row1
                                          st2 = lookup k row2
                                          f = (states sig!!) . get

foldPred :: Eq state => Modal state label atom
                     -> (String -> Maybe [state])
                     -> (String -> Maybe (BinRel state)) -> TermS -> [state]
foldPred alg g h t =
      case t of V x | just s             -> get s where s = g x
                F "true" []              -> topS alg
                F "false" []             -> botS alg
                F "pi1" [r]              -> pi1 alg $ evalR r
                F "pi2" [r]              -> pi2 alg $ evalR r
                F "not" [s]              -> notS alg $ evalP g s
                F "\\/" [s,s']           -> orS alg (evalP g s) $ evalP g s'
                F "/\\" [s,s']           -> andS alg (evalP g s) $ evalP g s'
                F "/" [r,s]              -> divS alg (evalR r) $ evalP g s
                F "$" [F "exists" [r],s] -> existsS alg (evalR r) $ evalP g s
                F "$" [F "forall" [r],s] -> forallS alg (evalR r) $ evalP g s
                F "$" [F "select" [p],r] -> selectS alg p $ evalR r
                F "trans" [t] | just st  -> trans' alg $ get st
                                            where st = state' alg t
                F "preds" [t] | just st  -> preds' alg $ get st
                                            where st = state' alg t
                F "$" [F "transL" [t],u] | just st && just lab
                                         -> transL' alg (get st) $ get lab
                                            where st  = state' alg t
                                                  lab = label' alg u
                F "$" [F "valueL" [t],u] | just at && just lab
                                         -> valueL' alg (get at) $ get lab
                                            where at  = atom' alg t
                                                  lab = label' alg u
                F ('m':'u':' ':x) [s]    -> fixpt subset (step x s) $ botS alg
                F ('n':'u':' ':x) [s]    -> fixpt supset (step x s) $ topS alg
                t | just at              -> value' alg $ get at
                                            where at = atom' alg t
                t | just st              -> [get st] where st = state' alg t
                F "[]" ts                -> toStates ts
                p                        -> satP alg p
      where step x s s' = evalP (upd g x $ Just s') s
            evalP g = foldPred alg g h
            evalR   = foldRel alg g h
            toStates ts = [get st | st <- map (state' alg) ts]

evalPred :: Sig -> TermS -> [Int]
evalPred sig = foldPred (intModAlg sig) (const Nothing) (const Nothing) .
               simplifyIter sig

-- used by simplifyS "eval/evalG"

foldOut :: Eq state => Modal state label atom -> TermS -> [atom]
foldOut alg t =
      case t of F "out" [t] | just st    -> out' alg $ get st
                                            where st = state' alg t
                F "$" [F "outL" [t],u] | just st && just lab
                                         -> outL' alg (get st) $ get lab
                                            where st  = state' alg t
                                                  lab = label' alg u 
                F "$" [F "unfoldD" [t],F "[]" ts] | just st && detAuto alg
                                         -> unfoldD alg (get st) $ toLabels ts
                                            where st  = state' alg t
                F "$" [F "unfoldND" [t],F "[]" ts] | just st
                                         -> unfoldND alg (get st) $ toLabels ts
                                            where st  = state' alg t
                F "$" [F "unfoldNDS" [t],F "[]" ts] | just st
                                         -> unfoldNDS alg (get st) $ toLabels ts
                                            where st  = state' alg t 
                _ -> []
      where toLabels ts = [get lab | lab <- map (label' alg) ts]

evalOut :: Sig -> TermS -> [Int]
evalOut sig = foldOut (intModAlg sig) . simplifyIter sig

-- used by simplifyS "evalO"

foldRel :: Eq state => Modal state label atom
                    -> (String -> Maybe [state])
                    -> (String -> Maybe (BinRel state)) -> TermS -> BinRel state
foldRel alg g h t =
      case t of V x | just r          -> get r where r = h x
                F "true" []           -> topR alg
                F "false" []          -> botR alg
                F "inv" [r]           -> invR alg $ evalR h r
                F "not" [r]           -> notR alg $ evalR h r
                F "\\/" [r,r']        -> orR alg (evalR h r) $ evalR h r'
                F "/\\" [r,r']        -> andR alg (evalR h r) $ evalR h r'
                F ";" [r,r']          -> comp alg (evalR h r) $ evalR h r'
                F "*" [s,s']          -> prodR alg (evalP s) $ evalP s'
                F "child" [F "[]" ts] | all just labs
                                      -> child alg $ map get labs
                                         where labs = map (label' alg) ts
                F ('m':'u':' ':x) [r] -> fixpt subset (step x r) $ botR alg
                F ('n':'u':' ':x) [r] -> fixpt supset (step x r) $ topR alg
                F "~" []              -> fixpt supset (equivStep alg) $ topR alg
                F "[]" ts             -> getStateRel toStates ts
                r                     -> satR alg r
       where step x r r' = evalR (upd h x $ Just r') r
             evalP   = foldPred alg g h
             evalR h = foldRel alg g h
             toStates ts = [get st | st <- map (state' alg) ts]

evalRel :: Sig -> TermS -> BinRel Int
evalRel sig = foldRel (intModAlg sig) (const Nothing) (const Nothing) .
              simplifyIter sig

-- used by evalRelPairs and simplifyS "evalRM"

evalRelPairs :: Sig -> (Int -> a) -> (Int -> b) -> TermS -> Pairs a b
evalRelPairs sig f g = map h . foldr h' [] . evalRel sig
                       where h (i,js) = (f i,map g js)
                             h' (i,j) rel = updRel rel i [j]

-- used by simplifyS "evalR/evalRG"

foldTab :: Modal state label atom -> TermS -> Table label state
foldTab alg t =
    case t of
         F "\\/" [t,t']           -> orT alg (foldTab alg t) $ foldTab alg t'
         F "/\\" [t,t']           -> andT alg (foldTab alg t) $ foldTab alg t'
         F "-" [t,t']             -> minusT alg (foldTab alg t) $ foldTab alg t'
         F "*" [t,t']             -> prodT alg (foldTab alg t) $ foldTab alg t'
         F "/" [t,t']             -> divT alg (foldTab alg t) $ foldTab alg t'
         F "$" [F "project" [F "[]" ts],t] | all just labs
                                  -> project alg (map get labs) $ foldTab alg t
                                     where labs = map (label' alg) ts
         F "$" [F "select" [p],t] -> selectT alg p $ foldTab alg t
         F "$" [F "njoin" [t],t'] -> njoin alg (foldTab alg t) $ foldTab alg t'
         F "$" [F "tsort" [t],u] | just lab
                                  -> sortT alg (get lab) $ foldTab alg u
                                     where lab = label' alg t
         t | just st              -> mkTab alg $ get st where st = state' alg t
         _ -> []

evalTab :: Sig -> TermS -> [(TermS,TermS,TermS)]
evalTab sig = f . foldTab (intModAlg sig) . simplifyIter sig where
              f tab = concatMap g $ indices_ tab where
                      g i = map h $ tab!!i where
                            h (k,st) = (mkConst i,labels sig!!k,states sig!!st)

-- used by simplifyS "evalT/evalM"

searchS,searchL,searchA :: Sig -> TermS -> Maybe Int
searchS sig t = search (== t) $ states sig
searchL sig t = search (== t) $ labels sig
searchA sig t = search (== t) $ atoms sig

-- satisfying sig p returns all states that satisfy p
-- satisfyingR sig p returns all pairs of states that satisfy p

satisfying,satisfyingR :: Sig -> TermS -> [TermS]
satisfying sig p  = filter (isTrue . sapply sig p) $ states sig
satisfyingR sig p = filter (isTrue . sapply sig p) pairs where
                    pairs = [mkPair t u | t <- states sig, u <- states sig]

-- partial evaluation (includes interpretation in the above Arith-algebras)

evaluate :: Sig -> TermS -> TermS
evaluate sig = eval where
       eval (F "<==>" [t,u]) | isTrue t   = eval u
                             | isTrue u   = eval t
                             | isFalse t  = mkNot sig $ eval u
                             | isFalse u  = mkNot sig $ eval t
                             | eqTerm t u = mkTrue
       eval (F "==>" [t,u])  | isTrue t   = eval u
                             | isTrue u   = mkTrue
                             | isFalse t  = mkTrue
                             | isFalse u  = mkNot sig $ eval t
       eval (F "&" ts)               = mkConjunct $ map eval ts
       eval (F "|" ts)               = mkDisjunct $ map eval ts
       eval (F ('A':'n':'y':x) [t])  = evalQ mkAny x $ eval t
       eval (F ('A':'l':'l':x) [t])  = evalQ mkAll x $ eval t
       eval (F "Not" [t])            = mkNot sig $ eval t
       eval (F "id" [t])             = eval t
       eval (F "head" [F ":" [t,_]]) = eval t
       eval (F "tail" [F ":" [_,t]]) = eval t
       eval (F "head" [t])    = case eval t of F "[]" (t:_) -> t
                                               t -> F "head" [t]
       eval (F "tail" [t])    = case eval t of F "[]" (_:ts) -> mkList ts
                                               t -> F "tail" [t]
       eval (F "bool" [t])    = case eval t of F "True" [] -> mkConst 1
                                               F "False" [] -> leaf "0"
                                               t -> F "bool" [t]
       eval (F "ite" [t,u,v]) = case eval t of F "True" [] -> eval u
                                               F "False" [] -> eval v
                                               t -> F "ite" [t,u,v]
       eval (F ":" [t,u])     = case eval u of F "[]" ts -> mkList $ t':ts
                                               u -> F ":" [t',u]
                                where t' = eval t
       eval (F "!!" [t,u])    = case eval t of
                                   F "[]" ts | just i && k < length ts -> ts!!k
                                   t -> F "!!" [t,eval u]
                                where i = foldArith intAlg u; k = get i
       eval (F "length" [t])  = case eval t of F "[]" ts -> mkConst $ length ts
                                               t ->  F "length" [t]
       eval (F "range" [t,u]) | just i && just k
                              = mkList $ map mkConst [get i..get k]
                                where i = foldArith intAlg t
                                      k = foldArith intAlg u
       eval (F "$" [F "lsec" [t,F x []],u]) = F x [eval t,eval u]
       eval (F "$" [F "rsec" [F x [],t],u]) = F x [eval u,eval t]
       eval (F "$" [F x [],F "()" ts])      = F x $ map eval ts
       eval (F "$" [F x [],t])              = F x [eval t]
       eval (F "Value" [t])                 = mkConst $ isValue sig t
       eval (F "List" [t])                  = mkConst $ isList t
       eval (F "Int" [t])  | just i         = mkTrue
                           | isValue sig t  = mkFalse
                                              where i = foldArith intAlg t
       eval (F "Real" [t]) | just r         = mkTrue
                           | isValue sig t  = mkFalse
                                              where r = foldArith realAlg t
       eval (F "suc" [t])  | just i         = mkConst $ get i+1
                                              where i = foldArith intAlg t
       eval (F x p@[_,_])  | isRel x && just ip = mkAtom x $ get ip
                           | isRel x && just rp = mkAtom x $ get rp
                           | isRel x && just fp = mkAtom x $ get fp
                           | isRel x && just sp = mkAtom x $ get sp
                                         where ip = mapM (parseA intAlg) p
                                               rp = mapM (parseA realAlg) p
                                               fp = mapM (parseA linAlg) p
                                               sp = mapM (parseA $ relAlg sig) p
       eval (F "=" [t,u])   = evalEq t u
       eval (F "=/=" [t,u]) = evalNeq t u
       eval (F "<+>" ts)    = mkSum $ map eval ts
       eval t | just i = mkConst $ get i
              | just r = mkConst $ get r
              | just f = mkLin $ get f
              | just s = mkList $ map (uncurry mkPair) $ sort (<) $ get s
                                          where i = foldArith intAlg t
                                                r = foldArith realAlg t
                                                f = foldArith linAlg t
                                                s = foldArith (relAlg sig) t
       eval (F x ts) = F x $ map eval ts
       eval t        = t

       evalQ f x t = f (words x `meet` frees sig t) t

       evalEq t u | eqTerm t u = mkTrue
       evalEq (F x ts) (F y us) | x == y && f x && f y && all g ts && all g us
                                       = mkConst $ ts `eqset` us
                                         where f x = x `elem` ["{}","<+>"]
                                               g = isValue sig
       evalEq t (F "suc" [u]) | just n = evalEq (mkConst $ get n-1) u
                                         where n = parsePnat t
       evalEq (F "suc" [u]) t | just n = evalEq u (mkConst $ get n-1)
                                         where n = parsePnat t
       evalEq (F "[]" (t:ts)) (F ":" [u,v]) =
                                   mkConjunct [evalEq t u,evalEq (mkList ts) v]
       evalEq (F ":" [u,v]) (F "[]" (t:ts)) =
                                   mkConjunct [evalEq u t,evalEq v $ mkList ts]
       evalEq (F x ts) (F y us) | all (isConstruct sig) [x,y] =
                                        if x == y && length ts == length us
                                        then mkConjunct $ zipWith (evalEq) ts us
                                        else mkFalse
       evalEq t u = mkEq (eval t) $ eval u

       evalNeq t u | eqTerm t u = mkFalse
       evalNeq (F "{}" ts) (F "{}" us)
                   | just qs && just rs = mkConst $ not $ get qs `eqset` get rs
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
                                       then mkDisjunct $ zipWith (evalNeq) ts us
                                       else mkTrue
       evalNeq t u = mkNeq (eval t) $ eval u

-- used by getReduct and Ecom > evaluateTrees

-- FLOWGRAPH ANALYSIS

-- stepwise global model checking of state formulas (backward analysis)

initState :: Sig -> TermS -> Maybe TermS
initState sig = f where
                f t@(V _)        = Just t
                f (F "true" [])  = jList $ states sig
                f (F "false" []) = Just mkNil
                f (F "mu" [t])   = do t <- f t; Just $ F "mu []" [t]
                f (F "nu" [t])   = do t <- f t; Just $ F ("nu "++sts) [t]
                f (F "$" [F "exists" [F "child" [t@(F "[]" labs)]],u])
                                 = do p labs; u <- f u; Just $ F "<>" [t,u]
                f (F "$" [F "forall" [F "child" [t@(F "[]" labs)]],u])
                                 = do p labs; u <- f u; Just $ F "#" [t,u]
                f t@(F x ts) | x `elem` words "not \\/ /\\"
                                 = do ts <- mapM f ts; Just $ F x ts
                f t@(F "[]" sts) = do mapM (searchS sig) sts; Just t
                f at             = do i <- searchA sig at
                                      jList $ map (states sig!!) 
                                            $ value sig!!i
                p = guard . just . mapM (searchL sig)
                sts = showTerm0 $ mkList $ states sig

evalStep :: Sig -> TermS -> (TermS,Bool)
evalStep sig t = down t where
  getVal :: TermS -> Maybe [TermS]
  getVal (V x)        = getVal $ getSubterm t $ tail $ getPos x
  getVal (F "[]" sts) = Just sts
  getVal (F x ts)     = do [_,val] <- Just $ words x
                           F "[]" sts <- parse (term sig) val; Just sts
  chg n x val = take n x ++ ' ':showTerm0 (mkList val)
  lfp x = take 2 x == "mu" 
  gfp x = take 2 x == "nu" 
  hasFix (F x ts) = lfp x || gfp x || or (map hasFix ts)
  hasFix t        = False
  down t@(F x [u]) | take 3 x == "not" && not (hasFix u) && just val2
                  = if isList u then (mkList val3,True)
                    else (F z [v], b || nothing val1 || get val1 /= val3)
                    where (v,b) = down u
                          val1 = getVal t; val2 = getVal u
                          val3 = states sig `minus` get val2
                          z = chg 3 x val3
  down t@(F x ts) | (dis || con) && all (not . hasFix) ts && all just vals
                  = if and $ map isList ts then (mkList val2,True)
                    else (F z us, or bs || nothing val1 || get val1 /= val2)
                    where (us,bs) = unzip $ map down ts
                          dis = take 2 x == "\\/"; con = take 2 x == "/\\"
                          val1 = getVal t; vals = map getVal ts
                          val2 = if dis then joinMap get vals
                                        else meetMap get vals
                          z = chg 2 x val2
  down t@(F x [F "[]" labs,u]) | (dia || box) && not (hasFix u) && just val2
                  = if isList u then (mkList val3,True)
                    else (F z [mkList labs,v],
                          b || nothing val1 || get val1 /= val3)
                    where (v,b) = down u
                          dia = take 2 x == "<>"; box = head x == '#'
                          val1 = getVal t; val2 = getVal u
                          val3 = filter (f . g) $ states sig
                          z = chg (if dia then 2 else 1) x val3
                          f = if dia then shares $ get val2
                                     else flip subset $ get val2
                          g = map (states sig!!) . h . get . searchS sig
                          h i = if null labs then trans sig!!i
                                else joinMap tr $ get $ mapM (searchL sig) labs
                                where tr k = transL sig!!i!!k
  down t@(F x [u]) | (lfp x || gfp x) && not (hasFix u) && just val2
                = (if lfp x && subset (get val2) val1 ||
                      gfp x && subset val1 (get val2)
                   then if b then F x [v] else mkList val1 else F z [v],True)
                   where (v,b) = down u
                         val1 = get $ getVal t; val2 = getVal u
                         z = chg 2 x $ if lfp x then val1 `join` get val2
                                                else val1 `meet` get val2
  down (F x ts) = (F x us,or bs) where (us,bs) = unzip $ map down ts
  down t        = (t,False)

-- postflow and subsflow

data Flow a = In (Flow a) a | Atom a | Assign String TermS (Flow a) a |
              Ite TermS (Flow a) (Flow a) a | Fork [Flow a] a | Pointer [Int]

mkFlow :: Sig -> (TermS -> a) -> TermS -> Flow a
mkFlow sig mkVal = f where
   f (F x [t]) | take 7 x == "inflow "       = In (f t) $ dropVal 7 x
   f (F x [V z,e,t]) | take 7 x == "assign " = Assign z e (f t) $ dropVal 7 x
   f (F x [c,t,t'])  | take 4 x == "ite "    = Ite c (f t) (f t') $ dropVal 4 x
   f (F x ts)  | take 5 x == "fork "         = Fork (map f ts) $ dropVal 5 x
   f (V x) | isPos x                         = Pointer $ getPos x
   dropVal n = mkVal . get . parse (term sig) . drop n

-- mkFlowTerm computes the term representation of a flowgraph

mkFlowTerm :: Sig -> (a -> TermS) -> Flow a -> TermS
mkFlowTerm sig mkTerm = f where
                        f (In g val)            = h "inflow " val [f g]
                        f (Atom val)            = mkTerm val
                        f (Assign x e g val)    = h "assign " val [V x,e,f g]
                        f (Ite c g1 g2 val)     = h "ite " val [c,f g1,f g2]
                        f (Fork gs val)         = h "fork " val $ map f gs
                        f (Pointer p)           = mkPos p
                        h x val = F $ x ++ showTerm0 (mkTerm val)

-- getVal g p computes the value at the first non-pointer value position of g
-- that is reachable from p. The position is also returned.

getVal :: Flow a -> [Int] -> (a,[Int])
getVal f p = h f p p where h (In g _) (0:p) q         = h g p q
                           h (In _ val) _ q           = (val,q)
                           h (Atom val) _ q           = (val,q)
                           h (Assign _ _ g _) (2:p) q = h g p q
                           h (Assign _ _ _ val) _ q   = (val,q)
                           h (Ite _ g _ _) (1:p) q    = h g p q
                           h (Ite _ _ g _) (2:p) q    = h g p q
                           h (Ite _ _ _ val) _ q      = (val,q)
                           h (Fork gs _) p@(_:_) q    = hL gs p q
                           h (Fork _ val) _ q         = (val,q)
                           h (Pointer p) _ _          = h f p p
                           hL (g:_)  (0:p) = h g p
                           hL (_:gs) (n:p) = hL gs $ (n-1):p

-- mkCycles replaces the bounded variables of fixpoint subformulas by back
-- pointers to their bodies. Alternating fixpoints may lead to wrong results.

mkCycles :: [Int] -> TermS -> TermS
mkCycles p t@(F x _) | isFix x = addToPoss p $ eqsToGraph0 eqs
                                 where (_,eqs,_) = fixToEqs t 0
mkCycles p (F x ts)            = F x $ zipWithSucs mkCycles p ts

-- used by simplifyS "initState"

fixToEqs :: TermS -> Int -> (TermS,[IterEq],Int)
fixToEqs (F x [t]) n | isFix x = (V z,Equal z (F mu [u]):eqs,k)
                            where mu:y:_ = words x
                                  b = y `elem` foldT f t
                                  f x xss = if isFix x then joinM xss `join1` y
                                                       else joinM xss
                                            where _:y:_ = words x
                                  z = if b then y++show n else y
                                  (u,eqs,k) = if b then fixToEqs v $ n+1
                                                   else fixToEqs t n
                                  v = t >>> for (V z) y
fixToEqs (F x ts) n = (F x us,eqs,k)
                            where (us,eqs,k) = f ts n
                                  f (t:ts) n = (u:us,eqs++eqs',k')
                                               where (u,eqs,k) = fixToEqs t n
                                                     (us,eqs',k') = f ts k
                                  f _ n      = ([],[],n)
fixToEqs t n        = (t,[],n)

-- used by mkCycles

-- verification of postconditions (backward-all analysis)

initPost :: TermS -> TermS
initPost (F op ts) | op `elem` words "assign fork ite"
           = F (op++" bool(True)") $ map initPost ts
initPost t = t

evalPost :: (TermS -> TermS) -> Flow TermS -> (Flow TermS,Bool)
evalPost simplify flow = up [] flow where
                 selVal = fst . getVal flow
                 up p (Assign x e g t) = (Assign x e g1 v, b1 || b2)
                            where q = p++[2]
                                  (g1,b1) = up q g
                                  u = selVal q
                                  (v,b2) = mkMeet t $ u>>>(e`for`x)
                 up p (Ite c g1 g2 t) = (Ite c g3 g4 t, b1 || b2 || b3)
                            where q1 = p++[1]; q2 = p++[2]
                                  (g3,b1) = up q1 g1; (g4,b2) = up q2 g2
                                  u = selVal q1; v = selVal q2
                                  c1 = mkDisjunct [c,u]
                                  c2 = mkDisjunct [F "Not" [c],v]
                                  (val,b3) = mkMeet t $ mkConjunct [c1,c2]
                 up p (Fork gs t) = (Fork gs1 u, or bs || b)
                            where qs = succsInd p gs
                                  (gs1,bs) = unzip $ zipWith up qs gs
                                  (u,b) = mkMeet t $ mkConjunct $ map selVal qs
                 up _ g = (g,False)
                 mkMeet t u = if isTrue $ simplify $ mkImpl t u then (t, False)
                                 else (simplify $ mkConjunct [t,u], True)

-- computation of program states (forward-any analysis)

initSubs :: TermS -> TermS
initSubs = f
       where f (F "inflow" [c,val]) = F ("inflow "++showTerm0 val) [initSubs c]
             f (F "assign" [x,e,c]) = F "assign [[]]" [x,e,initSubs c]
             f (F "ite" [b,c,c'])   = F "ite []" [b,initSubs c,initSubs c']
             f (F "fork" ts)        = F "fork []" $ map initSubs ts
             f t = t

evalSubs :: (TermS -> TermS) -> Flow [SubstS] -> [String]
                                              -> (Flow [SubstS],Bool)
evalSubs simplify flow xs = down flow False [] flow
  where down flow b p (In g val) = down flow1 (b || b1) q g
                             where q = p++[0]
                                   (flow1,b1) = change flow q val
        down flow b p (Assign x e g val) = down flow1 (b || b1) q g
                             where q = p++[2]
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
                                f (flow,b) q = (flow1, b || b1) where
                                               (flow1,b1) = change flow q val
                                h (flow,b) q g = down flow b q g
        down flow b _ _ = (flow,b)
        change g p val = if subSubs xs val oldVal then (g,False)
                                                  else (rep g q,True)
                  where (oldVal,q) = getVal g p
                        newVal = joinSubs xs val oldVal
                        rep (In g val) (0:p)         = In (rep g p) val
                        rep (Atom _) _               = Atom newVal
                        rep (Assign x e g val) (2:p) = Assign x e (rep g p) val
                        rep (Assign x e g _) _       = Assign x e g newVal
                        rep (Ite c g1 g2 val) (1:p)  = Ite c (rep g1 p) g2 val
                        rep (Ite c g1 g2 val) (2:p)  = Ite c g1 (rep g2 p) val
                        rep (Ite c g1 g2 _) _        = Ite c g1 g2 newVal
                        rep (Fork gs val) p@(_:_)    = Fork (rep' gs p) val
                        rep (Fork gs _) _            = Fork gs newVal
                        rep' (g:gs) (0:p)            = rep g p:gs
                        rep' (g:gs) (n:p)            = g:rep' gs ((n-1):p)


-- * __Subsumption__

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
        perm xs ys zs t u = h (renameFree sig (fold2 upd id xs zs) t) u ||
                            ys /= zs' && perm xs ys zs' t u
                            where zs' = nextPerm zs
        sub f ts = [f $ map (ts!!) ns | ns <- subsets $ length ts]
        noFrees xs = disjoint xs . frees sig

-- used by simplifyF, implToConc and Ecom > subsumeSubtrees

-- * __Simplification__

simplifyIter,simplifyFix :: Sig -> TermS -> TermS
simplifyIter sig = loop 0 100
                   where loop _ 0 t = t
                         loop k m t = case step PA (simplifyOne sig) t of
                                           Just t -> loop (k+1) (m-1) t
                                           _ -> t
simplifyFix sig  = pr1 . simplifyLoop sig 100 PA

-- simplifyLoop sig limit strat t applies simplification rules at most limit
-- times to the maximal subtrees of t and returns the simplified tree together
-- with the number of actually applied steps.

simplifyLoop :: Sig -> Int -> Strategy -> TermS -> (TermS,Int,Bool)
simplifyLoop sig limit strat t = loop 0 limit [t] where
             loop k 0 (t:_)    = (t,k,False)
             loop k m ts@(t:_) = case step strat (simplifyOne sig) t of
                                 Just t -> loop' t
                                 _ -> case step DF (expandFix sig True []) t of
                                      Just t -> loop' t
                                      _ -> (t,k,False)
                                 where loop' t = if just $ search (== t) ts
                                                 then (t,k,True)
                                                 else loop (k+1) (m-1) $ t:ts

-- used by simplifyFix and Ecom > simplify',simplifySubtree

step :: Strategy -> (TermS -> [Int] -> Maybe TermS) -> TermS -> Maybe TermS
step DF simplify t = f [] t where                            -- depthfirst
                     f p u = concat $ simplify t p:zipWithSucs f p (subterms u)
step BF simplify t = f [[]] [t] where                        -- breadthfirst
                     f ps us = do guard $ notnull ps
                                  concat (map (simplify t) ps) ++ f qs vs
                               where (qs,vs) = unzip $ concat $
                                               zipWith (zipWithSucs (,)) ps $
                                               map subterms us
step _ simplify t  = do let u = f t [] t                     -- parallel
                        guard $ t /= u; Just u
                     where f t p u = case simplify t p of
                                          Just t -> t
                                          _ -> fold2 f t (succsInd p us) us
                                     where us = subterms u
-- used by simplifyLoop

sapply sig t  = simplifyIter sig . apply t

sapplyL sig t = simplifyIter sig . applyL t

searchTerm :: Sig -> TermS -> [TermS] -> Maybe TermS
searchTerm sig p (t:ts) = if isTrue $ f t then Just t
                          else do guard $ isFalse $ f t; searchTerm sig p ts
                          where f = sapply sig p
searchTerm _ _ _        = Nothing

filterTerms :: Sig -> TermS -> [TermS] -> Maybe [TermS]
filterTerms sig p (t:ts) = do ts <- filterTerms sig p ts
                              if isTrue $ f t then Just $ t:ts
                              else do guard $ isFalse $ f t; Just ts
                           where f = sapply sig p
filterTerms _ _ _        = Just []

applyDrawFun :: Sig -> TermS -> TermS -> TermS
applyDrawFun sig drawFun t | drawFun == leaf "id"     = t
                           | drawFun == leaf "expand" = expand 0 t []
                           | True = mapW $ simplifyIter sig 
                                         $ F "$" [drawFun,add1ToPoss t] 
     where mapW :: TermS -> TermS
           mapW (F "$" [F "$" [F "mapW" [m],f],t]) | just m' = g t pt
              where m' = parsePnat m
                    order = case get m' of 1 -> levelTerm; 2 -> preordTerm
                                           3 -> heapTerm;  _ -> hillTerm
                    (pt,n) = order black (const id) t
                    g :: TermS -> TermI -> TermS
                    g (F x ts) (F k us) | just u  = F "widg" $ vs++[h (get u) k]
                                        | True    = F x vs
                                                    where vs = zipWith g ts us
                                                          u = parser x
                    g t@(V x) (F k _)   | isPos x = mkPos $ tail $ getPos x
                                        | True    = F "widg" [h t k]
                    g t _ = t
                    h t k = sapplyL sig f [t,mkConst k,mkConst n]
           mapW (F "$" [F "mapW" [f],t]) = g t
              where g :: TermS -> TermS
                    g (F x ts) | just u  = F "widg" $ vs++[h $ get u]
                               | True    = F x vs where vs = map g ts
                                                        u = parser x
                    g t@(V x)  | isPos x = mkPos $ tail $ getPos x
                               | True    = F "widg" [h t]
                    g t = t
                    h = sapply sig f
           mapW t = t
           parser = parse $ termsum sig

-- mapW(f)(t) replaces each subgraph x(t1,..,tn) of t by the subgraph 
-- widg(t1,...,tn,f(x)).

-- mapW(m)(f)(t) replaces each subtree x(t1,...,tn) of t by the subtree 
-- widg(t1,...,tn,f(x,k,max)) where k is the position of x within t with respect
-- to level order (m=1), prefix order (m=2), heap order (m=3) or hill order 
-- (m>3) and max is the maximum of positions of t.

-- If the interpreter widgetTree is applied to the resulting term, node x is 
-- replaced by the widget f(x) resp. f(x,k,max).

-- used by Ecom > showSubtreePicts,showTreePicts,showTrans

-- simplifyOne sig t p applies the first applicable simplification rule at
-- position p of t.

simplifyOne :: Sig -> TermS -> [Int] -> Maybe TermS
simplifyOne sig t p = concat [collapseUnary t p,try 1 True,try 2 True,
                              try 3 True,try 2 False,try 3 False,fixCycles]
    where u = mapT block t
          block x = if blocked sig x then "BLOCK"++x else x
          unblock ('B':'L':'O':'C':'K':x) = x
          unblock x = x
          try mode b = do (reduct,ps) <- aux mode b u
                          v <- foldlM (derefPreds 2 mode b) u $ map (p++) ps
                          (reduct,_) <- aux mode b v
                          Just . mapT unblock $ replace1 v p $ chgTargets reduct
          aux mode b t = do reduct <- getReduct mode b sig t p redex
                            let ps = targets redex `minus` markPoss 't' reduct
                            Just (reduct,ps)
                         where redex = addTargets u p
                               u = if b then getSubterm t p else expand 0 t p
          derefPreds n mode b t q
              = do (reduct,_) <- aux mode b $ addChar 's' t srcs
                   let ps = filter f srcs
                       f src = src `elem` markPoss 's' reduct
                       r:rs = ps
                       u = if null ps then t else foldl g (dereference t [r]) rs
                       g t p = replace0 t p $ mkPos r
                   (_,qs) <- aux mode b u
                   if null qs || n == 0 then Just u
                                        else derefPreds (n-1) mode b u q
                where srcs = sources q t
          fixCycles = do reduct <- getReduct 3 False sig u p $ getSubterm1 u p
                         Just . mapT unblock $ replace1 u p reduct

-- used by simplifyLoop and Ecom > simplifyPar

-- If node p of t is labelled with a pointer to target, then collapseUnary t p
-- identifies the parent q of p with the parent r of target if q and r are
-- labelled with the same unary operator.

collapseUnary t p = do guard $ notnull p && isPos x && f q == 1 &&
                               notnull target && f r == 1 &&
                               label t q == label t r
                       Just $ replace t q $ mkPos r
                    where x = label t p
                          target = getPos x
                          q = init p
                          r = init target
                          f = outdegree . getSubterm t
-- used by simplifyOne

getReduct 1 _ sig t p redex = do guard $ notSafe sig && polarity True t p
                                 simplCoInd sig redex
getReduct 2 _ sig _ _ redex = do guard $ redex /= reduct; Just reduct
                              where reduct = evaluate sig redex
getReduct _ b sig _ _ redex = do guard $ b || isF redex; simplifyF sig redex

-- used by simplifyOne

-- expandFix sig t p expands the fixpoint formula of t at position p or pointed
-- to from position p. After the expansion, all copies of the fixpoint formula
-- in the reduct are merged into a single one.

expandFix :: Sig -> Bool -> [Int] -> TermS -> [Int] -> Maybe TermS
expandFix sig firstCall muPos t p =
                    do guard $ not $ blocked sig "fixes"
                       F mu [body] <- Just redex
                       guard $ isFix mu
                       let [_,x] = words mu
                           u = collapseVars sig [x] body
                           v = if firstCall then redex else V $ 'e':mkPos0 muPos
                           f = if x `elem` frees sig u then v `for` x else V
                           reduct = instantiate (const id) u f []
                       Just $ replace1 t p $ reduct
                    where redex = addTargets (getSubterm t p) p

-- used by simplifyLoop

simplCoInd,simplifyF,simplifyA,simplifyS :: Sig -> TermS -> Maybe TermS

-- fixpoint induction rules

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
    | leader x "mu" && monotone sig xs t =                             -- MU
                            Just $ F "`then`" [t>>>forL us xs,u]
                            where _:xs = words x; us = mkGets xs u

simplCoInd sig (F "==>" [F "$" [F x [t],arg],u])
    | leader x "nu" && null (subterms arg) && monotone sig xs t =      -- NU
                            Just $ mkAll [root arg]
                                 $ mkImpl (apply (t>>>forL us xs) arg) u
                            where _:xs = words x
                                  us = mkGets xs $ F "rel" [arg,u]

-- fixpoint coinduction rules

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

-- graph producing rules

simplifyF _ (F "$" [F "mapG" [f@(F _ ts)],F x us@(_:_)]) | collector x =
                                  Just $ F x $ if null ts then map (apply f) us
                                               else map g $ indices_ us
                                  where g 0 = apply f $ vs!!0
                                        g i = apply (mkPos [0,0]) $ vs!!i
                                        vs = changeLPoss p q us
                                        p i = [1,i]; q i = [i,1]

simplifyF _ (F "$" [F "replicateG" [t],u]) | just n =
                    jList $ changePoss [1] [0] u:replicate (get n-1) (mkPos [0])
                    where n = parsePnat t

simplifyF _ (F "concat" [t@(F "[]" ts)]) | all isList ts =
                    if all isList ts then jList $ concatMap (subterms . f) ts
                    else Just $ apply (apply (F "foldl" [leaf "++"]) mkNil) t
                    where subs i = subterms $ ts!!i
                          f t = foldl g t $ indices_ ts
                          g t i = foldl (h i) t $ indices_ $ subs i 
                          h i t k = changePoss [0,i,k] [lg (i-1)+k] t
                          lg (-1) = 0
                          lg i    = lg (i-1) + length (subs i)

simplifyF sig (F "$" [F "concRepl" [t],u@(F "[]" us)]) | just n =
                   simplifyF sig $ F "concat" [addToPoss [0] $ mkList vs]
                   where n = parsePnat t
                         vs = changePoss [1] [0] u:
                              replicate (get n-1) (mkList $ map f $ indices_ us)
                         f i = mkPos [0,i]

simplifyF _ (F "$" [F "**" [f,t],u]) | just n =   -- collapse into first f-occ.
                   Just $ if null $ subterms f then iterate (apply f) v!!m
                          else apply copy $ iterate (apply $ mkPos [0]) v!!(m-1)
                   where n = parsePnat t; m = get n
                         v = changePoss [1] (replicate m 1) u
                         copy = changePoss [0,0] [0] f

simplifyF _ (F "$" [F "***" [f,t],u]) | just n =  -- collapse into last f-occ.
                Just $ if null $ subterms f then iterate (apply f) v!!m
                       else iterate (apply $ mkPos funpos) (apply copy v)!!(m-1)
                where n = parsePnat t; m = get n
                      v = changePoss [1] (replicate m 1) u
                      funpos = replicate (m-1) 1++[0]
                      copy = changePoss [0,0] funpos f
                   -- collapse into last copy of f

simplifyF _ (F "$" [F x [n],F "[]" ts])
           | x `elem` words "cantor hilbert mirror snake transpose" && just k =
                                    jList $ f (get k) $ changeLPoss p single ts
                                    where k = parsePnat n
                                          f = case head x of 'c' -> cantorshelf
                                                             'h' -> hilbshelf
                                                             'm' -> mirror
                                                             's' -> snake
                                                             _ -> transpose
                                          p i = [1,i]

simplifyF _ (F "permute" (t:ts)) | isObdd t =
                   if n == 0 then Just t
                   else if null ts
                        then perm [t,changePoss [0] [1] t,mkConsts [0..n-1]]
                        else do [u,ns] <- Just ts; ns <- parseNats ns
                                let permute s = map (s!!) ns
                                    v = add1ToPoss $ binsToObddP (n-1) ns
                                                   $ map permute $ funToBins fn
                                perm [t,if size v < size u then v else u,
                                        mkConsts $ nextPerm ns]
                   where fn@(_,n) = obddToFun $ drop0FromPoss t
                         perm = Just . F "permute"

-- rules preferred to user-defined rules

simplifyF _ (F "++" [F x ts,F y us]) | collectors x y = Just $ F x $ ts++us

simplifyF _ (F "++" [F "++" [t,F x ts],F y us])
                              | collectors x y = Just $ F "++" [t,F x $ ts++us]

simplifyF _ (F "++" [F x ts,F "++" [F y us,t]])
                              | collectors x y = Just $ F "++" [F x $ ts++us,t]

-- user-defined rules

simplifyF sig t | notnull ts = Just $ mkSum ts
                               where ts = simplReducts sig False t

simplifyF sig (F x ts@(_:_)) | notnull us =
                               Just $ applyL (mkSum us) $ map (mapT f) ts
                               where us = simplReducts sig False $ F x []
                                     f x = if isPos x && notnull p
                                           then mkPos0 $ head p+1:tail p else x
                                           where p = getPos x

simplifyF sig (F "$" [t,u]) | notnull ts = Just $ apply (mkSum ts) u
                                           where ts = simplReducts sig False t

-- LOGICAL REDUCTIONS

simplifyF _ (F "===>" [t,u]) = Just $ mkImpl t u
simplifyF _ (F "<===" [t,u]) = Just $ mkImpl u t

simplifyF sig (F "<==>" [t,u]) | subsumes sig t u = Just $ mkImpl u t
                               | subsumes sig u t = Just $ mkImpl t u

-- distribute ==> over the factors of the conclusion of an implication

simplifyF _ (F "==>" [t,F "&" ts]) = Just $ mkConjunct $ map (mkImpl t) ts

-- distribute ==> over the summands the premise of an implication

simplifyF _ (F "==>" [F "|" ts,t]) = Just $ mkConjunct $ map (flip mkImpl t) ts

-- try subsumption, reduce components and replace non-constructor-headed
-- subterms by in/equivalent constructor-headed ones

simplifyF sig (F "==>" [t,u])
 | subsumes sig t u = Just mkTrue
 | notnull vsfs     = Just mkTrue
 | notnull vsf      = Just $ mkImpl (mkConjunct tsf) $ mkConjunct usf1
 | notnull vss      = Just $ mkImpl (mkDisjunct tss1) $ mkDisjunct uss
 | notnull vssf     = Just $ F "&" [mkImpl (mkDisjunct tss2) $ mkConjunct vssf,
                                    mkImpl (mkDisjunct vssf) $ mkConjunct usf2]
 | just pair1       = Just $ mkImpl (mkConjunct ts1) $ mkDisjunct us1
 | just pair2       = Just $ mkImpl (mkConjunct ts2) $ mkDisjunct us2
                      where tsf = mkFactors t; tss = mkSummands t
                            usf = mkFactors u; uss = mkSummands u
                            vsfs = meetTerm tsf uss
                            vsf = meetTerm tsf usf; usf1 = removeTerms usf vsf
                            vss = meetTerm tss uss; tss1 = removeTerms tss vss
                            vssf = meetTerm tss usf
                            tss2 = removeTerms tss vssf
                            usf2 = removeTerms usf vssf
                            pair1 = replaceTerms sig "=" tsf uss
                            pair2 = replaceTerms sig "=/=" uss tsf
                            (ts1,us1) = get pair1
                            (us2,ts2) = get pair2

-- move quantifiers out of an implication

simplifyF sig c@(F "==>" [t,u]) | b = Just result
           where (result,b) = moveAny [] t u False
                 moveAny zs (F ('A':'n':'y':x) [t]) u _ = 
                         moveAll (zs++map f xs) (renameAll f t) u True
                         where xs = words x
                               ys = sigVars sig u
                               f = getSubAwayFrom c xs ys
                 moveAny zs t u b = moveAll zs t u b
                 moveAll zs t (F ('A':'l':'l':x) [u]) _ = 
                         (mkAll (zs++map f xs) $ mkImpl t $ renameAll f u,True)
                         where xs = words x
                               ys = sigVars sig t
                               f = getSubAwayFrom c xs ys
                 moveAll zs t u b = (mkAll zs $ mkImpl t u,b)

-- move universal quantifiers out of a disjunction

simplifyF sig c@(F "|" ts) | b = Just result
         where (result,b) = move [] ts [] False
               move zs (F ('A':'l':'l':x) [t]:ts) us _ = 
                       move (zs++map f xs) ts (renameAll f t:us) True
                       where xs = words x
                             ys = joinMap (sigVars sig) $ ts++us
                             f = getSubAwayFrom c xs ys
               move zs (t:ts) us b = move zs ts (t:us) b
               move zs _ us b      = (mkAll zs $ mkDisjunct us,b)

-- move existential quantifiers out of a conjunction

simplifyF sig c@(F "&" ts) | b = Just result
         where (result,b) = move [] ts [] False
               move zs (F ('A':'n':'y':x) [t]:ts) us _ =
                           move (zs++map f xs) ts (renameAll f t:us) True
                       where xs = words x
                             ys = joinMap (sigVars sig) $ ts++us
                             f = getSubAwayFrom c xs ys
               move zs (t:ts) us b = move zs ts (t:us) b
               move zs _ us b      = (mkAny zs $ mkConjunct us,b)

-- restrict a disjunction to its maximal summands with respect to subsumption
-- and replace non-constructor-headed subterms by inequivalent
-- constructor-headed ones

simplifyF sig (F "|" ts) | just t = t
                         | just p = Just $ mkDisjunct $ fst $ get p
                                    where t = subsumeDisj sig ts []
                                          p = replaceTerms sig "=/=" ts []

-- restrict a conjunction to its minimal factors with respect to subsumption and
-- replace non-constructor-headed subterms by equivalent constructor-headed 
-- ones

simplifyF sig (F "&" ts) | just t = t
                            | just p = Just $ mkConjunct $ fst $ get p
                                      where t = subsumeConj sig ts []
                                            p = replaceTerms sig "=" ts []

simplifyF _ (F "$" [F "any" [p],F x ts]) | collector x =
                                           Just $ mkDisjunct $ map (apply p) ts

simplifyF _ (F "$" [F "all" [p],F x ts]) | collector x =
                                        Just $ mkConjunct $ map (apply p) ts

simplifyF _ (F "$" [F "allany" [r],F "()" [F x ts,F y us]])
                    | collector x && collector y = Just $ mkConjunct $ map q ts
                                          where q t = mkDisjunct $ map (f t) us
                                                f t u = applyL r [t,u]

-- modus ponens ... & prem ==> conc & ... & prem & ...
--          --> ... & conc          & ... & prem & ...

simplifyF _ (F "&" ts) | notnull is = Just $ mkConjunct $ map f $ indices_ ts
                                where is = [i | i <- getIndices isImpl ts,
                                                let F _ [prem,_] = ts!!i,
                                                prem `elem` context i ts]
                                      f i = if i `elem` is then conc else ts!!i
                                            where F _ [_,conc] = ts!!i

simplifyF _ (F "$" [F "prodE" ts,u])  = Just $ mkTup $ map (flip apply u) ts

-- remove in/equational summands or factors with a quantified variable on one
-- side.

simplifyF sig t | just u = u where u = removeEq sig t

simplifyF _ (F x [F "bool" [t],F "bool" [u]]) | isNEq x
                         = Just $ if x == "=/=" then F "Not" [v] else v
                           where v = F "<==>" [t,u]

simplifyF sig t = simplifyA sig t

-- AXIOM-BASED SIMPLIFICATION

-- simplReducts sig True t returns the reducts of all axioms of transitions sig
-- that are applicable to t.
-- simplReducts sig False t returns the reduct of the first axiom of simpls sig
-- that is applicable to t.

simplReducts :: Sig -> Bool -> TermS -> [TermS]
simplReducts sig isTrans t = if isTrans then concatMap f $ transitions sig
                             else if null reds then [] else [head reds]
  where reds = concatMap f $ simpls sig
        reduce = if isTrans then simplifyIter sig else id
        f (u,cs,v) = case matchSubs sig xs t u of
                          Just (sub,ts,is,bag) | just sub'
                            -> map (mkBag . h is ts . toElems)
                                   $ mkTerms $ reduce $ v>>>get sub'
                               where sub' = g sub cs xs
                                     toElems = if bag then mkElems else single
                          _ -> []
                     where xs = frees sig u
                           h is ts us = f 0 0 $ length ts where
                                        f _ _ 0 = []
                                        f i k n = if i `elem` is
                                                  then us!!k:f (i+1) (k+1) (n-1)
                                                  else ts!!i:f (i+1) k (n-1)
        g sub (c:cs) xs | isTrue $ simplifyIter sig $ c>>>sub = g sub cs xs
        g sub (c@(F "=" [t,u]):cs) xs | frees sig t `subset` xs &&
                                        xs `disjoint` zs && just h
                               = g (sub `andThen` get h) cs $ xs++zs where
                                 zs = frees sig u
                                 h = match sig zs (simplifyIter sig $ t>>>sub) u
        g sub [] _ = Just sub
        g _ _ _    = Nothing

-- used by simplifyF,simplifyS,buildTrans{Loop},getRHS

-- buildTrans sig ts constructs the binary and ternary relations generated by ts
-- and the transition rules of sig.

buildTrans :: Sig -> [TermS] -> ([TermS],PairsT,TriplesT)
buildTrans sig ts = (states sig `join` joinM reds1 `join` joinM reds2,
                     zip ts reds1,zipL pairs reds2)
                    where reds1 = reduce ts
                          reds2 = reduce [mkPair t lab | (t,lab) <- pairs]
                          reduce = map $ simplReducts sig True
                          pairs = prod2 ts $ labels sig

-- used by Ecom > buildKripke 3/4,buildKripkeValues

-- buildTransLoop sig mode constructs the transition system generated by
-- states sig and the transition rules of sig.

buildTransLoop :: Sig -> Int -> ([TermS],PairsT,TriplesT)
buildTransLoop sig mode = loop (states sig) (states sig) [] [] where
                   loop old sts ps psL =
                      if null new then (old,rs,rsL)
                                  else loop (old `join` new) new rs rsL
                      where new = (joinM redss `minus` old) `join`
                                  (joinM redssL `minus` old)
                            redss  = reduce sts
                            redssL = reduce [mkPair st lab | (st,lab) <- pairs]
                            reduce = map $ simplReducts sig True
                            pairs = prod2 sts $ labels sig
                            qs = zip sts redss
                            qsL = zipL pairs redssL
                            meetNew = map $ meet new
                            (rs,rsL) = case mode of
                                        0 -> (ps++map removeCycles qs,
                                              psL++map removeCyclesL qsL)
                                        1 -> (ps++zip sts (meetNew redss),
                                              psL++zipL pairs (meetNew redssL))
                                        _ -> (ps++qs,psL++qsL)
                            removeCycles (st,reds) = (st,f st reds)
                            removeCyclesL (st,lab,reds) = (st,lab,f st reds)
                            f st sts = [st' | st' <- sts,
                                   st `notElem` fixpt subset (joinMap g) [st']]
                            g st = (case lookup st ps of Just sts -> sts
                                                         _ -> [])
                                   `join` joinMap f (labels sig) `join1` st
                                   where f lab = case lookupL st lab psL of
                                                      Just sts -> sts
                                                      _ -> []

-- used by Ecom > buildKripke 0/1/2

getFrom :: Sig -> [TermS] -> String -> [TermS]
getFrom sig axioms str = if null ts then []
                                    else case simplifyIter sig $ head ts of
                                              F "[]" ts -> ts
                                              _ -> []
                         where ts = do F "==" [F x [],u] <- axioms
                                       guard $ x == str
                                       [u]

-- used by Ecom > buildKripke 0/1/2

removeEq sig t =
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
                F ('A':'n':'y':x) ts | just $ f "=" (words x) ts
                  -> Just mkTrue
                    | just $ f "=" (words x) ts -> Just mkTrue
                _ -> Nothing
      where f rel xs = g [] 
              where g rest (t@(F z us@[l,r]):ts) 
                          | z == rel && (notSafe sig || xs `shares` map root us)
                                  = case unifyS sig xs l r of
                                    Just h -> Just (map (>>>h) $ ts++rest,h)
                                    _ -> g (rest++[t]) ts
                    g rest (t:ts) = g (rest++[t]) ts
                    g _ _         = Nothing

-- used by simplifyF

-- replaceTerms sig rel ts vs replaces l in vs by r if ts contains the
-- atom (l rel r) or (r rel l). At first, atoms (t rel t) are removed.

replaceTerms :: Sig -> String -> [TermS] -> [TermS] -> Maybe ([TermS],[TermS])
replaceTerms sig rel ts vs = f [] ts
                where f us ts = do t:ts <- Just ts
                                   let vs = us++ts; rest = f (t:us) ts
                                   case t of F x [l,r] | x == rel 
                                               -> if l == r then f us ts 
                                                  else h l r vs++h r l vs++rest
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

-- subsume summands

subsumeDisj sig (t:ts) rest = if subsumes sig t u
                              then Just u else subsumeDisj sig ts $ rest++[t]
                              where u = mkDisjunct $ ts++rest
subsumeDisj _ _ _ = Nothing

-- subsume factors

subsumeConj sig (t:ts) rest = if subsumes sig u t
                              then Just u else subsumeConj sig ts $ rest++[t]
                              where u = mkConjunct $ ts++rest
subsumeConj _ _ _ = Nothing

-- LAMBDA APPLICATIONS
-- see: https://fldit-www.cs.uni-dortmund.de/~peter/CTL.pdf, page 133 ff.

bodyAndSub sig lazy app pat k arg =
               if lazy then Just (u,forL (map f xs) xs)
                       else do sub <- match sig xs arg' pat; Just (u,sub)
               where xs = sigVars sig pat
                     arg' = dropFromPoss [1] arg
                     f x = apply (F "fun" [pat,mkVar sig x]) arg'
                     bodyPos = [0,k]
                     body = getSubterm1 app bodyPos
                     h = getSubAwayFrom body (bounded sig body) $ frees sig arg'
                     t = collapseVars sig xs $ renameBound sig h body
                     u = addChar 't' t $ targets t `minus` markPoss 't' t

simplifyA sig app@(F "$" [F x [F "~" [pat],body],arg])
   | lambda x && just tsub = Just $ t>>>sub
                             where tsub = bodyAndSub sig True app pat 1 arg
                                   (t,sub) = get tsub

simplifyA sig app@(F "$" [F x [pat,body],arg])
   | lambda x && just tsub = Just $ t>>>sub
                             where tsub = bodyAndSub sig False app pat 1 arg
                                   (t,sub) = get tsub

simplifyA sig app@(F "$" [F x ts,arg])
   | lambda x && lg > 2 && even lg = Just $ F "CASE" $ pr1
                                          $ fold2 f ([],0,1) pats bodies where
     lg = length ts; pats = evens ts; bodies = odds ts
     f (cases,i,k) pat body = if just t then (cases++[get t],i+1,k+2)
                                        else (cases,i,k+2)
      where t = concat [do F "||" [pat,b] <- Just pat; result pat b,
                        result pat mkTrue]
            result pat b = do (u,sub) <- bodyAndSub sig False app pat k arg
                              Just $ F "->" [b>>>sub,addToPoss [i,1] $ u>>>sub]

simplifyA _ (F "`IN`" [t,F x ts])    | collector x = jConst $ inTerm t ts

simplifyA _ (F "`NOTIN`" [t,F x ts]) | collector x = jConst $ notInTerm t ts

simplifyA sig (F "`in`" [t,F x ts]) 
   | collector x = do guard $ all f ts
                      if f t then jConst $ inTerm t ts 
                             else do guard $ orTree (isVar sig) t 
                                     Just $ mkDisjunct $ map (mkEq t) ts
                   where f = isValue sig

simplifyA sig (F "`NOTin`" [t,F x ts]) 
   | collector x = do guard $ all f ts
                      if f t then jConst $ notInTerm t ts 
                             else do guard $ orTree (isVar sig) t
                                     Just $ mkConjunct $ map (mkNeq t) ts
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

simplifyA sig t = simplifyS sig t

mat matrix = F "mat" [Hidden matrix]

simplifyS sig (F "`meet`" [F x ts,F y us])
  | collectors x y = do guard $ all f ts && all f us; jList $ meetTerm ts us
                        jList $ meetTerm ts us
                     where f = isValue sig

simplifyS sig (F "`join`" [F x ts,F y us])
  | collectors x y = do guard $ all f ts && all f us; jList $ joinTerms ts us
                        jList $ joinTerms ts us
                     where f = isValue sig

simplifyS sig (F "-" [F x ts,F y us])
  | collectors x y = do guard $ all f ts && all f us; jList $ removeTerms ts us
                        jList $ removeTerms ts us
                     where f = isValue sig

simplifyS sig (F "$" [F "search" [p],F x ts])
 | collector x && just t = Just $ get t where t = searchTerm sig p ts

simplifyS sig (F "$" [F "filter" [p],F x ts])
 | collector x && just us = Just $ F x $ get us where us = filterTerms sig p ts

-- strict fold

simplifyS sig (F "$" [F "$" [F "sfold" [f],a],F x []]) | collector x = Just a

simplifyS sig (F "$" [F "$" [F "sfold" [f],a],F x (t:ts)]) | collector x =
                        Just $ apply (apply (F "sfold" [f])
                                            $ simplifyIter sig $ applyL f [a,t])
                                     $ F x ts

simplifyS sig (F "string" [t])    = Just $ leaf $ showTerm0 $ simplifyIter sig t

simplifyS sig (F "term" [F x []]) = parse (term sig) x   -- inverse of "string"

simplifyS sig (F "$" [F "mapT" [t],u]) = Just $ mapT f u where
                                     f x = case parse (term sig) x of
                                           Just v -> showTerm0 $ sapply sig t v
                                           _ -> x

simplifyS sig (F "subst" [t,u,v]) | isVar sig x =
                     Just $ collapseVars sig [x] v >>> for t x where x = root u

-- LR parsing

simplifyS sig (F "parseLR" [input@(F "[]" ts)]) =
            do guard $ isLRmodel sig && ts `subset` map (labels sig!!) terminals
               Just $ F "parseLR" [mkList [states sig!!0],mkNil,input]
            where terminals = indices_ (labels sig) `minus` nonterminals sig

simplifyS sig (F "parseLR" [s@(F "[]" sts),a@(F "[]" asts),F "[]" input]) =
                       Just $ case nextLR sig sts asts input of
                                   Success t -> t
                                   More sts asts input
                                     -> F "parseLR" [s,a,mkList input]
                                   _ -> leaf "no parse"

-- ONE-STEP SIMPLIFICATIONS BY MODAL-FORMULA FOLDING

-- evaluate a unary state predicate phi

simplifyS sig (F "eval" [phi])  = jList $ map (states sig!!) $ evalPred sig phi

simplifyS sig (F "evalG" [phi]) = Just $ mapT f $ relToGraph pairs trips
                                                $ map showTerm0 $ inits sig
                       where is = evalPred sig phi
                             [sts,labs,_] = showSLA sig
                             pairs = mkPairs sts sts $ trans sig
                             trips = mkTrips sts labs sts $ transL sig
                             f st | isPos st || st == "<+>"  = st
                                  | st `elem` map (sts!!) is = "dark green_"++st
                                  | True                     = "red_"++st

-- evaluate an output formula phi

simplifyS sig (F "evalO" [phi])   = jList $ map (atoms sig!!) $ evalOut sig phi

-- evaluate a binary state predicate rel

simplifyS sig (F "evalR" [rel])   = jList $ map g $ evalRelPairs sig f f rel
                                    where f = (states sig!!)
                                          g (t,us) = mkPair t $ mkList us

simplifyS sig (F "evalRG" [rel])  = Just $ relToGraphAll pairs []
                                    where pairs = evalRelPairs sig f f rel
                                          f = showTerm0 . (states sig!!)

simplifyS sig (F "evalRM" [rel])  = Just $ mat $ BoolMat dom1 dom2 pairs
                                    where (dom1,dom2) = sortDoms pairs
                                          pairs = map f $ evalRel sig rel
                                          f (i,j) = (g i,g j)
                                          g = showTerm0 . (states sig!!)
-- evaluate a table formula tab

simplifyS sig (F "evalT" [tab]) = jList $ map f $ evalTab sig tab
                                  where f (t,u,v) = mkTrip t u v

simplifyS sig (F "evalM" [tab]) = Just $ mat $ TermMat trips 
                                  where trips = map f $ evalTab sig tab
                                        f (t,u,v) = (showTerm0 t,showTerm0 u,v)

-- SIMPLIFICATIONS FOR THE CURRENT KRIPKE MODEL OUTSIDE eval*

-- state equivalence

simplifyS sig (F "~" [st,st']) = do i <- searchS sig st; j <- searchS sig st'
                                    let cli = search (elem i) part
                                        clj = search (elem j) part
                                    Just $ mkConst $ cli == clj
                      where part = partition (indices_ $ states sig) $ bisim sig

-- stepwise minimization

simplifyS sig (F x@"minAuto" []) = Just $ Hidden $ EquivMat sig $ bisim0 sig

simplifyS sig (Hidden (EquivMat _ trips)) | trips /= new
                                 = Just $ mat $ EquivMat sig new
                                   where new = bisimStep trips

-- (state,label)-paths from st to st' without internal cycles

simplifyS sig (F "$" [F "traces" st,st']) =
                         do i <- searchS sig stt
                            j <- searchS sig st'
                            Just $ mkSum $ map f $ traces tr trL ks i j
                         where stt = mkTup st
                               ks = indices_ $ labels sig
                               tr i = trans sig!!i
                               trL i k = transL sig!!i!!k
                               f trace = leaf $ showTerm0 stt++concatMap g trace
                               g (Left j) = h $ states sig!!j
                               g (Right (k,j)) = h (labels sig!!k) ++
                                                 h (states sig!!j)
                               h t = '-':showTerm0 t
                 
-- sum of all states a that satisfy with p(a) = True

simplifyS sig (F "sat" [p]) = Just $ mkSum $ satisfying sig p

-- sum of all pairs (a,b) of states with r(a,b) = True

simplifyS sig (F "satR" [r]) = Just $ mkSum $ satisfyingR sig r

-- flowgraph initialization

simplifyS sig (F "initState" [t]) | just u  = Just $ F "runState" [get u]
                    where u = initState sig $ mkCycles [0] $ simplifyIter sig t

simplifyS _ (F "initPost" [t]) | just eqs = Just $ F "runPost" [initPost g]
                                where eqs = parseEqs t
                                      g = addToPoss [0] $ eqsToGraph0 $ get eqs

simplifyS _ (F "initSubs" [t]) | just eqs = Just $ F "runSubs" [initSubs g]
                                where eqs = parseEqs t
                                      g = addToPoss [0] $ eqsToGraph0 $ get eqs

-- flowgraph transformation

simplifyS sig (F x@"runState" [t]) | changed  = Just $ F x [u]
                                   | isList u = Just u
                                     where (u,changed) = evalStep sig t

simplifyS sig (F x@"runPost" [t]) =
                 Just $ if changed then F x [mkFlowTerm sig mkBool flow] else t
                 where (flow,changed) = evalPost (simplifyIter sig) $
                                                 mkFlow sig (head . subterms) t

simplifyS sig (F x@"runSubs" [t]) =
           Just $ if changed then F x [mkFlowTerm sig toEqs flow'] else t
           where flow = mkFlow sig subs t; xs = vars flow
                 vars (In g _)         = vars g
                 vars (Assign x _ g _) = vars g `join1` x
                 vars (Ite _ g1 g2 _)  = vars g1 `join` vars g2
                 vars (Fork gs _)      = joinMap vars gs
                 vars flow             = []
                 (flow',changed) = evalSubs (simplifyIter sig) flow xs
                 subs (F "[]" ts) = map sub ts
                 sub (F "[]" ts) = forL ts xs where (xs,ts) = unzip $ map eq ts
                 eq (F "=" [V x,t]) = (x,t)
                 toEqs = mkList . concatMap mkEqs
                 mkEqs f = if null ys then [] else [mkList $ map g ys]
                           where ys = domSub xs f; g x = mkEq (V x) $ f x

-- regular expressions and acceptors

simplifyS sig (F "showRE" [t])  | just e = Just $ showRE $ fst $ get e
                                           where e = parseRE sig t

simplifyS sig (F "deltaBro" [t,F x []])
                                | just e && just e' = Just $ showRE $ get e'
                               where e = parseRE sig t
                                     e' = deltaBro (getRHS sig) (fst $ get e) x
                                               
simplifyS sig (F "betaBro" [t]) | just e && just b = Just $ mkConst $ get b
                                   where e = parseRE sig t
                                         b = betaBro (getRHS sig) $ fst $ get e

simplifyS sig (F "$" [F "unfoldBro" [t],F "[]" xs]) | just e && just b =
                                                      Just $ mkConst $ get b
                   where e = parseRE sig t
                         b = unfoldBro (getRHS sig) (fst $ get e) $ map root xs

simplifyS sig (F "auto" [t]) | just e = Just $ relToGraph pairs trips ["0"]
          where e = parseRE sig t
                (e',labs) = get e
                (sts,(trans,transL)) = regToAuto e'
                pairs = [(show q,map show $ trans q) | q <- sts]
                trips = [(show q,a,map show $ transL q a) | q <- sts, a <- labs]

simplifyS _ t = simplifyT t

getRHS :: Sig -> String -> Maybe RegExp
getRHS sig x = do [rhs] <- Just $ simplReducts sig False $ F "step" [leaf x]
                  (e,_) <- parseRE sig rhs; Just e

-- * __Signature-independent simplification__

simplifyT :: TermS -> Maybe TermS

simplifyT (F x [F "skip" []]) = Just $ leaf "skip"

simplifyT (F x [F mu [F "()" ts]])
        | just i && isFix mu && k < length ts && foldT f t = Just t
                                             where i = parse (strNat "get") x
                                                   k = get i
                                                   t = ts!!k
                                                   [_,z] = words mu
                                                   f x bs = x /= z && and bs

simplifyT (F x [F "()" ts]) 
        | just i && k < length ts          = Just $ ts!!k
        | not $ collector x || binder x || x `elem` words "~ List Value string"
                                           = Just $ F x ts 
                                             where i = parse (strNat "get") x
                                                   k = get i

simplifyT (F "$" [F "get" [n],t]) | just i = Just $ F ("get"++show (get i)) [t]
                                             where i = parseNat n

simplifyT (F "$" [F "." [g,f],t])            = Just $ apply g $ apply f t

simplifyT (F "$" [F "$" [F "flip" [f],t],u]) = Just $ apply (apply f u) t

simplifyT (F "$" [F "map" [f@(F _ _)],F x us]) | collector x
                                             = Just $ F x $ map (apply f) us

simplifyT (F "$" [F "replicate" [t],u]) | just n = jList $ replicate (get n) u
                                                   where n = parsePnat t

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
                                where t `less` u = getInd all t < getInd all u

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

simplifyT (F "$" [F "$" [F "zipWith" _,F x _],F ":" _])
                          | collector x = Just mkNil

simplifyT (F "$" [F "$" [F "zipWith" _,F ":" _],F x _])
                          | collector x = Just mkNil

simplifyT (F "$" [F "$" [F "zipWith" [f],F ":" [t,ts]],F ":" [u,us]]) =
            Just $ F ":" [applyL f [t,u],apply (apply (F "zipWith" [f]) ts) us]

simplifyT (F "$" [F "$" [F "zipWith" [f],F x ts],F y us]) | collectors x y =
                           jList $ zipWith g ts us where g t u = applyL f [t,u]

simplifyT (F "CASE" (F "->" [t,u]:_))  | isTrue t  = Just u

simplifyT (F "CASE" (F "->" [t,_]:ts)) | isFalse t = Just $ F "CASE" ts

simplifyT (F "size" [F "{}" ts]) = jConst $ length $ mkSet ts

simplifyT (F "height" [t])       = jConst $ height t

simplifyT (F "getCols" [F x ts]) = Just $ if null z then F x $ map f ts
                                          else F col [F (tail z) $ map f ts]
                                   where (col,z) = span (/= '$') x
                                         f t = F "erect" [t]

simplifyT (F "bag" [F x ts])      | collector x = Just $ mkBag ts

simplifyT (F "tup" [F x ts])      | collector x = Just $ mkTup ts
          
simplifyT (F "initup" [F x ts,t]) | collector x = Just $ mkTup $ ts++[t]

simplifyT (F "branch" [F x ts])   | collector x = Just $ mkSum ts

simplifyT (F "set" [F x ts])      | collector x = Just $ mkSetTerm ts

simplifyT (F "null" [F x ts])     | collector x = jConst $ null ts

simplifyT (F "NOTnull" [F x ts])  | collector x = jConst $ not $ null ts

simplifyT (F "column" [F x ts])   | collector x =
                                             Just $ leaf $ tail $ concatMap f ts
                                             where f t = '\'':showTerm0 t

simplifyT (F "prodL" [F x ts])    | all collector (x:map root ts) =
                                jList $ map mkTup $ accumulate $ map subterms ts

simplifyT t | f == "curry" && notnull tss && length us == 1 =
                                        Just $ applyL (head us) $ concat uss
                                        where (f,tss) = unCurry t; us:uss = tss


simplifyT (F "index" [t,F x ts])
                         | collector x = do i <- search (eqTerm t) ts; jConst i

simplifyT (F "indices" [F x ts])
                          | collector x = jList $ map mkConst [0..length ts-1]

simplifyT (F "singles" [F x ts])
                          | collector x = jList $ map (mkList . single) ts

simplifyT (F "subsets" [F x ts]) 
                          | collector x = jList $ map (F x) subs
                             where subs = [map (ts!!) ns | ns <- subsetsB lg lg]
                                   lg = length ts

simplifyT (F "subsetsB" [F x ts,t]) 
                          | collector x && just i =jList $ map (F x) subs
                        where lg = length ts; i = parseInt t
                              subs = [map (ts!!) ns | ns <- subsetsB lg $ get i]

simplifyT (F "perms" [F "[]" ts])   = jList $ map mkList $ perms ts

simplifyT (F "reverse" [F "[]" ts]) = jList $ reverse ts

simplifyT (F "shuffle" [F x ts])
        | all ((== "[]") . root) ts = jList $ shuffle $ map subterms ts

simplifyT (F "sort" [F "[]" ts])
        | all just is = jConsts $ qsort (<=) $ map get is
        | all just rs = jConsts $ qsort (<=) $ map get rs
        | True        = jList $ sort (<) ts
                        where is = map (foldArith intAlg) ts
                              rs = map (foldArith realAlg) ts

simplifyT (F "subperms" [F "[]" ts]) = jList $ map mkList $ subperms ts

simplifyT (F "=" [F "^" ts@(t:ts'),F "^" us@(u:us')]) =
                   case search (eqTerm t) us of
                        Just n -> Just $ mkEq (mkBag ts') $ mkBag $ context n us
                        _ -> do n <- search (eqTerm u) ts
                                Just $ mkEq (mkBag $ context n ts) $ mkBag us'

simplifyT (F "`mod`" [t,u]) | just i && just j && k /= 0 =
                                 jConst $ mod (get i) k
                                 where i = parseInt t; j = parseInt u; k = get j

simplifyT (F x [F "+" [t,u],n]) | isRel x && just i && just j =
                                          Just $ F x [u,mkConst $ get i-get j]
                                | isRel x && just i && just k =
                                          Just $ F x [u,mkConst $ get i-get k]
                            where i = parseInt n; j = parseInt t; k = parseInt u

simplifyT (F x [n,F "+" [t,u]]) | isRel x && just i && just j =
                                          Just $ F x [mkConst $ get i-get j,u]
                                | isRel x && just i && just k =
                                          Just $ F x [mkConst $ get i-get k,t]
                            where i = parseInt n; j = parseInt t; k = parseInt u

simplifyT (F "+" [n,F "+" [t,u]]) | just i && just j =
                                          Just $ F "+" [mkConst $ get i+get j,u]
                                  | just i && just k =
                                          Just $ F "+" [mkConst $ get i+get k,t]
                            where i = parseInt n; j = parseInt t; k = parseInt u

simplifyT (F "+" [F "+" [t,u],n]) | just i && just j =
                                          Just $ F "+" [mkConst $ get i+get j,u]
                                  | just i && just k =
                                          Just $ F "+" [mkConst $ get i+get k,t]
                            where i = parseInt n; j = parseInt t; k = parseInt u

simplifyT (F ">" [F "()" (t:ts),F "()" (u:us)]) =
             Just $ F "|" [mkGr t u,F "&" [mkEq t u,mkGr (mkTup ts) $ mkTup us]]

simplifyT (F "color" [i,n]) = do i <- parseNat i; n <- parseNat n
                                 jConst $ hue 0 red n i

simplifyT (F x [F z _]) | just col1 && just col2
                            = Just $ if get col1 == fst (get col2) then mkTrue
                                     else mkFalse
                              where col1 = parse color x; col2 = parse colPre z

simplifyT (F "dnf" [t]) | isObdd t
                         = jConsts $ funToBins $ obddToFun $ drop0FromPoss t

simplifyT (F "obdd" [t]) = do bins <- parseBins t; Just $ binsToObdd bins

simplifyT (F "minDNF" [t]) | just bins = jConsts $ minDNF $ get bins
                                          where bins = parseBins t

simplifyT (F "minOBDD" [t]) | isObdd t = Just $ drop0FromPoss $ collapse True
                                              $ removeVar t

simplifyT (F "minterms" [t]) | just bins =
                                jConsts $ concatMap minterms $ get bins
                                where bins = parseBins t

simplifyT (F "gauss" [t]) | just eqs =
                             Just $ F "bool" [mkLinEqs $ get $ gauss $ get eqs]
                             where eqs = parseLinEqs t

simplifyT (F x@"gaussI" [t]) | just eqs =
                               case gauss1 $ get eqs of
                                    Just eqs -> f eqs
                                    _ -> do eqs <- gauss2 $ get eqs; f eqs
                               where eqs = parseLinEqs t
                                     f eqs = Just $ F x [mkLinEqs $ gauss3 eqs]

simplifyT (F "pascal" [t]) = do n <- parseNat t; jConsts $ pascal n

simplifyT (F "concept" [F "[]" ts,F "[]" us,F "[]" vs]) | f us && f vs =
                              Just $ h $ concept ts (g us) $ g vs
                              where f = all $ (== "()") . root
                                    g = map $ map root . subterms
                                    h = mkSum . map (mkTup . map leaf)

simplifyT (F "[]" ts) | length us < length ts = jList us 
                                                where us = mergeActs ts

simplifyT (F "{}" ts) | length us < length ts = Just $ F "{}" us 
                                                where us = joinTerms [] ts

simplifyT (F "nextperm" [F x ns]) | collector x
                                     = do ns <- mapM parseInt ns
                                          Just $ F x $ map mkConst $ nextPerm ns

-- changes the variable ordering of a DNF or an OBDD

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
                                 Just $ F x [mkList $ map mkConstPair qs]
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

-- * __Rewriting and narrowing__

data Reducts = Sum [TermS] (String -> Int) |
               Backward [TermS] (String -> Int) |
               Forward [TermS] (String -> Int) | Stop |
               MatchFailure String -- generated only by genMatchFailure

-- quantify sig add ts t quantifies the free variables xs of ts.

quantify :: Sig -> ([String] -> TermS -> TermS) -> [TermS] -> TermS -> TermS
quantify sig add ts reduct = add (filter (noExcl &&& (`elem` ys)) xs) reduct
                             where xs = joinMap (frees sig) ts
                                   ys = sigVars sig reduct

addTo _ [] t                  = t
addTo True rest (F "=" [t,u]) = mkEq (mkBag $ t:rest) u
addTo True _ t                = t
addTo _ rest t                = mkBag $ t:rest

-- used by searchReds,applyAx{ToTerm},applySingle

-- searchReds .. ts reds .. pars tries to unify ts with a subset of reds such
-- that the instance of a given guard by the unifier is solvable by applying
-- given axioms. The guard and the axioms are part of pars.

searchReds check rewrite vc ts reds b t sig xs pars = sr Stop ts [] reds []
  where lg = length ts
        sr _ (t:ts) us reds vs =
                          do (reduct,red,rest) <- h us' reds vs $ length reds-1
                             sr reduct ts us' rest $ red:vs
                          where us' = t:us
        sr reduct _ _ _ _ = Just reduct
        h ts reds vs i =
           do guard $ i >= 0
              case unifyList True sig xs V ts (red:vs) (V"") (V"") ps ps of
                   Def (f,True) -> case checkOrRewrite f sig xs vc pars of
                                        Stop -> h ts reds vs (i-1)
                                        reduct -> Just (reduct,red,rest)
                   _ -> h ts reds vs (i-1)
           where red = reds!!i; rest = context i reds
                 ps = replicate lg' []; lg' = length ts
                 checkOrRewrite = if lg == lg' then rewrite $ addTo b rest t
                                               else check

-- used by applyAx{ToTerm}

-- solveGuard guard axs applies axs by narrowing at most 100 times to guard.
-- axs are also the axioms applied to the guards of axs. Reducts are simplified,
-- but irreducible subtrees are not removed.

solveGuard :: Sig -> TermS -> [TermS] -> (String -> Int) -> Maybe [[IterEq]]
solveGuard sig cond axs vc = do guard $ notnull sols; Just sols
                  where sols = Haskell.mapMaybe f (mkSummands $ pr1 t)
                        f = parseSol $ solEq sig
                        t = applyLoop cond 100 vc axs axs sig True 2 False True

-- used by applyAx,rewrite,rewriteTerm

-- applyLoop t 0 m ... axs preAxs sig nar match refute simplify applies axioms
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

applyLoop :: TermS -> Int -> (String -> Int) -> [TermS] -> [TermS] -> Sig 
                    -> Bool -> Int -> Bool -> Bool -> (TermS,Int,String -> Int)
applyLoop t m vc axs preAxs sig nar match refute simplify = f t 0 m vc
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
                     rules | isVarRoot sig redex = []
                           | nar                 = filtered
                           | True                = filter unconditional filtered
                     (axs',vc') = renameApply sig t vc rules
                     f = if nar then modifyF $ applyAxs axs' axs' preAxs
                                else modifyT $ applyAxsToTerm axs' axs' preAxs
       modifyF f redex t p vc
            | isDefunct sig sym = do (q,at,r) <- atomPosition sig t p
                                     Backward reds vc <- g at r
                                     Just (replace t q $ mkDisjunct reds,vc)
            | notnull p && isTerm sig redex
                                = do at@(F "->" [_,_]) <- Just $ getSubterm t q
                                     0 <- Just $ last p
                                     Backward reds vc <- g at [0]
                                     Just (replace t q $ mkDisjunct reds,vc)
            | isPred sig sym    = do Backward reds vc <- g redex []
                                     Just (replace t p $ mkDisjunct reds,vc)
            | True              = do guard $ isCopred sig sym
                                     Forward reds vc <- g redex []
                                     Just (replace t p $ mkConjunct reds,vc)
                             where sym = getOp redex
                                   q = init p
                                   g at r = Just $ fst $ f redex at r sig vc uni
       modifyT f redex t p vc = do Sum reds vc <- Just $ fst $ f redex sig vc
                                   Just (replace t p $ mkSum reds,vc)

-- used by solveGuard and Ecom > narrowStep

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
              case f redex t p vc' of Just (t,vc,rand) -> Just (simpl t,vc,rand)  
                                      _ -> modifyL $ succsInd p $ subterms redex
              where redex = getSubterm t p
                    filtered = filterClauses sig redex axs
                    rules | isVarRoot sig redex = []
                          | nar                 = filtered
                          | True                = filter unconditional filtered
                    (axs',vc') = renameApply sig t vc rules
                    f = if nar then modifyF $ applyAxsR axs' axs' preAxs rand
                        else modifyT $ applyAxsToTermR axs' axs' preAxs rand
                    modifyL ps@(_:_) = modify t (ps!!i) vc (nextRand rand) ++
                                       modifyL (context i ps)
                                       where i = mod rand $ length ps
                    modifyL _        = Nothing
       modifyF f redex t p vc
          | isDefunct sig sym = do (q,at,r) <- atomPosition sig t p
                                   (Backward reds vc,rand) <- g at r
                                   Just (replace t q $ mkDisjunct reds,vc,rand)
          | notnull p && isTerm sig redex
                              = do at@(F "->" [_,_]) <- Just $ getSubterm t q
                                   0 <- Just $ last p
                                   (Backward reds vc,rand) <- g at [0]
                                   Just (replace t q $ mkDisjunct reds,vc,rand)
          | isPred sig sym    = do (Backward reds vc,rand) <- g redex []
                                   Just (replace t p $ mkDisjunct reds,vc,rand)
          | True              = do guard $ isCopred sig sym
                                   (Forward reds vc,rand) <- g redex []
                                   Just (replace t p $ mkConjunct reds,vc,rand)
                     where sym = getOp redex
                           q = init p
                           g at r = Just $ (pr1***pr3) $ f redex at r sig vc uni
       modifyT f redex t p vc =
                    do (Sum reds vc,rand) <- Just $ (pr1***pr3) $ f redex sig vc
                       Just (replace t p $ mkSum reds,vc,rand)

-- used by Ecom > narrowStep

-- NARROWING OF FORMULAS (includes resolution and coresolution)

-- applyAxs cls axs preAxs redex u r computes all narrowing/rewriting reducts
-- of the redex at position r of u that result from unifying/matching redex
-- against axs. The guards of axs are narrowed by preAxs. cls is the original,
-- non-extended and non-renamed version of axs.
-- uni = True  --> The redex is unified against axs.
-- uni = False --> The redex is matched against axs.

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

-- used by applyLoop,applyPar and Ecom > narrowPar

-- applyAxsR axs preAxs rand redex t p computes the narrowing/rewriting 
-- reducts of the redex at position p of t that result from unifying/matching 
-- redex against a random element of axs. The guards of axs are narrowed by 
-- preAxs.

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
applyAxsR cls [] _ rand redex _ _ _ _ _             = (Stop,[],rand)
applyAxsR cls axs preAxs rand redex at p sig vc uni =
  case applyAx ax preAxs redex at p sig vc uni of
       Stop -> applyAxsR cls' axs' preAxs (nextRand rand) redex at p sig vc uni
       reduct -> (reduct,[cl],rand)
  where n = rand `mod` length axs
        cl = cls!!n; cls' = removeTerm cls cl
        ax = axs!!n; axs' = removeTerm axs ax

-- used by applyLoopRandom and Ecom > narrowPar

-- applyAx ax axs redex at p sig vc applies the axiom ax to the redex at
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
            -> try (reds,[0..lg-1]) 100 where
                   lg = length reds
                   b = product [2..lg] > 100
                   xs = frees sig redex
                   pars = (guard,axs,left,right,prem,uni)
                   try pair 0 | b    = Backward [F "^" $ fst $ permute pair] vc
                              | True = Stop
                   try pair n = case searchReds checkGuard rewrite vc ts
                                              (fst pair) True eq sig xs pars of
                                     Just reduct -> reduct
                                     _ -> try (permute pair) $ n-1
          _ -> foldl (applyTo reds) Stop $ indices_ reds
     _ -> applyTo [redex] Stop 0
     where eq = mkEq right r
           applyTo reds reduct i =               
                case partialUnify guard axs left right prem at eq p sig vc uni
                                  $ reds!!i of
                     reduct'@(Backward ts vc)
                       -> case reduct of Backward reducts vc
                                           -> Backward (reducts++reducts') vc
                                         _ -> Backward reducts' vc
                          where reducts' = map (addTo True $ context i reds) ts
                     _ -> reduct

applyAx (F "==>" [guard,F "<===" [F "=" [left,right],prem]]) axs redex at p sig
     vc uni = partialUnify guard axs left right prem at (replace at p right) p
                           sig vc uni redex

applyAx (F "==>" [guard,F "<===" [at,prem]]) axs redex _ _ sig vc uni =
     case unify0 True sig xs at redex redex [] of
     TotUni f
       -> genMatchFailure sig uni dom at $
                  case u of F "True" _  -> Backward [mkRed []] vc
                            F "False" _ -> Stop
                            _ -> case solveGuard sig u axs vc of
                                      Just sols -> Backward (map mkRed sols) vc
                                      _ -> Stop
          where dom = domSub xs f
                u = simplifyIter sig $ guard>>>f
                mkRed sol = quantify sig addAnys [at,prem] $ mkConjunct $
                                     prem>>>g:substToEqs g (domSub xs g)
                            where g = f `andThen` mkSubst sol
     ParUni f dom -> genMatchFailure sig uni dom at $ Backward [t] vc
                     where t = quantify sig addAnys [at] $ mkConjunct $
                                        redex>>>f:substToEqs f dom
     _ -> Stop
     where xs = frees sig redex

applyAx (F "==>" [guard,F "===>" [at,conc]]) axs redex _ _ sig vc uni =
     case unify0 True sig xs at redex redex [] of
     TotUni f
       -> genMatchFailure sig uni dom at $
                  case u of F "True" _  -> Forward [mkRed []] vc
                            F "False" _ -> Stop
                            _ -> case solveGuard sig u axs vc of
                                      Just sols -> Forward (map mkRed sols) vc
                                      _ -> Stop
          where dom = domSub xs f
                u = simplifyIter sig $ guard>>>f
                mkRed sol = quantify sig addAlls [at,conc] $ mkDisjunct $
                                     conc>>>g:substToIneqs g (domSub xs g)
                            where g = f `andThen` mkSubst sol
     ParUni f dom -> genMatchFailure sig uni dom at $ Forward [t] vc
                     where t = quantify sig addAlls [at] $ mkDisjunct $
                                        redex>>>f:substToIneqs f dom
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

-- used by applyAxs{R}

checkGuard f sig xs vc (guard,_,left,_,_,uni) =
       genMatchFailure sig uni (domSub xs f) left $
         if isFalse $ simplifyIter sig $ guard>>>f then Stop else Backward [] vc

-- used by applyAx

genMatchFailure sig uni dom t reduct =
       if uni || null dom then reduct
       else if any (isHovar sig) dom then Stop
       else MatchFailure $ "Some redex does not match " ++ showTree False t

-- used by applyAx,partialUnify,checkGuard,rewrite

partialUnify guard axs left right prem at at' p sig vc uni redex =
       case unify0 True sig xs left redex at p of
            TotUni f -> rewrite at' f sig xs vc (guard,axs,left,right,prem,uni)
            ParUni f dom -> genMatchFailure sig uni dom left $ Backward [t] vc
                            where t = quantify sig addAnys [left] $ mkConjunct
                                      $ at>>>f:substToEqs f dom
            _ -> Stop
       where xs = frees sig redex

-- used by applyAx

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

-- used by applyAx,partialUnify

-- REWRITING OF TERMS

applyAxsToTerm (cl:cls) (ax:axs) preAxs redex sig vc =
    case applyAxToTerm ax preAxs redex sig vc of
    reduct@(Sum reds vc) -> case applyAxsToTerm cls axs preAxs redex sig vc of
                            (Sum reds' vc,cls) -> (Sum (reds++reds') vc,cl:cls)
                            _ -> (reduct,[cl])
    _ -> applyAxsToTerm cls axs preAxs redex sig vc
applyAxsToTerm _ _ _ _ _ _ = (Stop,[])

-- used by applyLoop and Ecom > rewritePar

applyAxsToTermR cls [] _ rand redex _ _          = (Stop,[],rand)
applyAxsToTermR cls axs preAxs rand redex sig vc =
    case applyAxToTerm ax preAxs redex sig vc of
         Stop -> applyAxsToTermR cls' axs' preAxs (nextRand rand) redex sig vc
         reduct -> (reduct,[cl],rand)
    where n = rand `mod` length axs
          cl = cls!!n; cls' = removeTerm cls cl
          ax = axs!!n; axs' = removeTerm axs ax

-- used by applyLoopRandom and Ecom > rewritePar

-- applyAxToTerm ax is applied only within a TERM. Hence ax must be a
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
                     try pair 0 | b    = Sum [F "^" $ fst $ permute pair] vc
                                | True = Stop
                     try pair n = case searchReds checkGuardT rewriteTerm vc ts
                                          (fst pair) False right sig xs pars of
                                       Just reduct -> reduct
                                       _ -> try (permute pair) $ n-1
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
            
applyAxToTerm (F "==>" [guard,F "=" [left,right]]) axs redex sig vc =
    totalUnify guard axs left right sig vc redex

applyAxToTerm t@(F _ [_,_]) axs redex sig vc =
    applyAxToTerm (F "==>" [mkTrue,t]) axs redex sig vc

applyAxToTerm _ _ _ _ _ = Stop

-- used by applyAxsToTerm{R}

checkGuardT f sig xs vc (guard,_,left) =
     if notnull $ domSub xs f then Stop
     else if isFalse $ simplifyIter sig $ guard>>>f then Stop else Sum [] vc

-- used by applyAxToTerm

totalUnify guard axs left right sig vc redex =
     case unify0 True sig xs left redex redex [] of
          TotUni f -> rewriteTerm right f sig xs vc (guard,axs,left)
          _ -> Stop
     where xs = frees sig redex

-- used by applyAxToTerm

rewriteTerm :: TermS
            -> (String -> TermS)
            -> Sig
            -> [String]
            -> (String -> Int)
            -> (TermS, [TermS], t)
            -> Reducts
rewriteTerm right f sig xs vc (guard,axs,left) =
     if notnull dom then Stop
     else case u of F "True" _ -> Sum [mkRed []] vc
                    F "False" _ -> Stop
                    _ -> case solveGuard sig u axs vc of
                              Just sols -> Sum (map mkRed sols) vc
                              _ -> Stop
     where dom = domSub xs f
           u = simplifyIter sig $ guard>>>f
           mkRed sol = right>>>(f `andThen` mkSubst sol)

-- used by applyAxToTerm,totalUnify

-- * __Application of theorems__

-- applySingle and applyMany work similarly to applyAxs, but apply only single
-- non-guarded clauses.

applySingle th@(F "<===" [F "False" _,prem]) redex t p sig =
       Just $ replace t p $ mkImpl (mkNot sig redex) conc
       where conc = mkAny (frees sig prem) prem

applySingle th@(F "===>" [F "True" _,conc]) redex t p sig =
       Just $ replace t p $ mkImpl prem redex
       where prem = mkAll (frees sig conc) conc

applySingle th@(F "<===" [F "->" [left,right],prem]) redex t p sig
       | notnull p && isTerm sig redex =
                 do (F "->" [_,r],0) <- Just (getSubterm t q,last p)
                    (f,rest) <- unify left
                    let eq = addTo True rest $ mkEq right r
                        eqs = substToEqs f $ domSub xs f
                        reduct = mkConjunct $ eq>>>f:prem>>>f:eqs
                        reduct' = quantify sig addAnys [left,right,prem] reduct
                    Just $ replace t q reduct'
                 where xs = frees sig redex; reds = mkElems redex; q = init p
                       unify (F "^" ts) = unifyAC sig xs V ts reds
                       unify t          = unifyAC sig xs V [t] reds

applySingle th@(F "<===" [at,prem]) redex t p sig =
       case unify0 True sig xs at redex t p of
         TotUni f
           -> Just $ replace t p $ quantify sig addAnys [at,prem] reduct
              where reduct = mkConjunct $ prem>>>f:substToEqs f (domSub xs f)
         _ -> do F _ [F "=" [left,right], F "True" _] <- Just th
                 TotUni f <- Just $ unify0 True sig xs left redex t p
                 let dom = domSub xs f
                     ts = prem>>>f:substToEqs f dom
                     bind = quantify sig addAnys [left,right,prem] . mkConjunct
                 (q,at,r) <- atomPosition sig t p
                 Just $ replace t q $ bind $ replace at r right>>>f:ts
       where xs = frees sig redex

applySingle th@(F "===>" [at,conc]) redex t p sig =
       do TotUni f <- Just $ unify0 True sig xs at redex t p
          let reduct = mkDisjunct $ conc>>>f:substToIneqs f (domSub xs f)
          Just $ replace t p $ quantify sig addAlls [at,conc] reduct
       where xs = frees sig redex

applySingle at redex t p sig = applySingle (mkHorn at mkTrue) redex t p sig

-- used by Ecom > applyTheorem

-- applyMany presupposes that the redices are factors re summands of the same
-- conjunction resp. disjunction.

applyMany forward different left right redices t ps pred qs sig =
      do Def (f,True) <- Just $ unifyList True sig xs V left redices (V"") t
                                          (replicate (length left) []) ps
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
         Just $ replace t pred reduct3
      where xs = joinMap (frees sig) redices

-- used by Ecom > finishDisCon

applyToHead sig axs = f where
       f (t:cls) vc =
         case t of F x [h,b] | x `elem` words "<=== ===>"
                     -> (F x [redh,b]:clsh,vch) where (redh,clsh,vch) = redvc h
                   _ -> (redt:clst,vct)         where (redt,clst,vct) = redvc t
         where redvc t = (reduct,cls',vc3) where
                         (axs',vc1) = renameApply sig t vc axs
                         (reduct,vc2) = applyPar sig axs' (noRefPoss t) t vc1
                         (cls',vc3) = f cls vc2
       f _ vc = ([],vc)

-- used by Ecom > applyInd

-- applyPar axs t ps sig applies axs in parallel at all positions of t in ps.

applyPar sig axs (p:ps) t vc
 | isVarRoot sig redex = proceed0
 | isDefunct sig sym = case atomPosition sig t p of
                            Just (q,at,r)
                              -> case apply at r of
                                 Backward reds vc -> proceed mkDisjunct reds vc
                                 _ -> proceed0
                            _ -> proceed0
 | isPred sig sym    = case apply redex [] of
                            Backward reds vc -> proceed mkDisjunct reds vc
                            _ -> proceed0
 | isCopred sig sym  = case apply redex [] of
                            Forward reds vc -> proceed mkConjunct reds vc
                            _ -> proceed0
 | True              = proceed0
             where redex = getSubterm t p
                   sym = getOp redex
                   cls = filterClauses sig redex axs
                   apply at r = fst $ applyAxs cls cls [] redex at r sig vc True
                   proceed0 = applyPar sig axs ps t vc
                   proceed mk = applyPar sig axs ps . replace t p . mk
applyPar _ _ _ t vc = (t,vc)

-- used by applyToHead

-- mkComplAxiom sig ax transforms an axiom ax for p into an axiom for NOTp.

mkComplAxiom sig t =
        case t of F "==>" [guard,t] -> mkImpl guard $ mkComplAxiom sig t
                  F "===>" [t,F "False" _] -> t
                  F "===>" [t,u] -> mkHorn (neg t) $ simplifyIter sig $ neg u
                  F "<===" [t,u] -> mkCoHorn (neg t) $ simplifyIter sig $ neg u
                  t -> mkCoHorn t mkFalse
        where neg = mkNot sig

-- used by Ecom > negateAxioms

-- flatten k xs cl turns cl into an equivalent clause cl' such that all
-- equations t=u of cl' are flat wrt xs, i.e. either root(t) is in xs and all
-- other symbols of t or u are not in xs or u=t is flat wrt xs.

flatten k [] cl                     = (cl,k)
flatten k xs (F "==>" [guard,cl])   = (F "==>" [guard,cl'],n)
                                      where (cl',n) = flatten k xs cl
flatten k xs (F "<===" [conc,prem]) = mkFlatEqs k xs conc prem
flatten k xs at                     = mkFlatEqs' k xs at

mkFlatEqs k xs conc prem = 
                      if null tps && null ups then (mkHorn conc prem,k)
                      else mkFlatEqs n xs conc' (mkConjunct (prem':eqs1++eqs2))
                      where tps = flatCands xs [] conc
                            ups = flatCands xs [] prem
                            (conc',eqs1,m) = mkEqs tps conc [] k
                            (prem',eqs2,n) = mkEqs ups prem [] m

mkFlatEqs' k xs at = if null tps then (at,k) 
                                 else mkFlatEqs n xs at' (mkConjunct eqs)
                     where tps = flatCands xs [] at
                           (at',eqs,n) = mkEqs tps at [] k

-- mkEqs tps t [] k creates for each (u,p) in tps an equation u=zn with n>=k and
-- replaces u in t by zn.

mkEqs ((u,p):s) t eqs k = mkEqs s (replace t p new) (eqs++[mkEq u new]) $ k+1
                          where new = newVar k
mkEqs _ t eqs k         = (t,eqs,k)

-- flatCands xs [] t returns the list of pairs (u,p) such that u is the subterm
-- of t at position p and the root of u is in xs, but u is not the left- or
-- right-hand side of a flat equation.

flatCands :: [String] -> [Int] -> TermS -> [(TermS, [Int])]
flatCands xs p (F "=" [l,r])
          | x `elem` xs = pairs ps tss ++ flatCands xs p1 r
          | y `elem` xs = flatCands xs p0 l ++ pairs qs uss 
            where (x,tss) = unCurry l; (y,uss) = unCurry r
                  p0 = p++[0]; p1 = p++[1]
                  ps = curryPositions p0 tss; qs = curryPositions p1 uss
                  pairs ps tss = concat $ zipWith (flatCands xs) ps $ concat tss
flatCands xs p t | getOp t `elem` xs = [(t,p)]
flatCands xs p (F _ ts)              = concat $ zipWithSucs (flatCands xs) p ts
flatCands _ _ _                      = []

-- curryPositions [] [ts1,...,tsn] = ps1++...++psn iff for all 1<=i<=n, psi
-- are the root positions of tsi within a term of the form f(ts1)...(tsn).

curryPositions :: [Int] -> [[a]] -> [[Int]]
curryPositions _ []   = []
curryPositions p [ts] = succsInd p ts
curryPositions p tss  = map (0:) (curryPositions p $ init tss) ++
                        succsInd p (last tss)

-- preStretch conc f t checks whether the premises (conc = False) or conclusions
-- (conc = True) of t can be stretched. If so, then preStretch returns their
-- leading function/relation x and the positions varps of all subterms to be
-- replaced by variables. f is a condition on x.

preStretch :: Bool -> (String -> Bool) -> TermS -> Maybe (String,[Int])
preStretch conc f t =
   case t of F "&" ts -> do guard $ conc || all isImpl ts || all isEq ts
                            s <- mapM g ts
                            let (xs,tss@(ts:uss)) = unzip s
                                varps = joinMap toBeReplaced tss `join`
                                        [i | i <- indices_ ts,
                                             any (neqTerm (ts!!i) . (!!i)) uss]
                            guard $ allEqual xs && allEqual (map length tss)
                            Just (head xs,varps)
             F "==>" [F "=" [u,_],v] -> do (x,ts) <- g $ if conc then v else u
                                           Just (x,toBeReplaced ts)
             F "==>" [u,v] -> do (x,ts) <- g $ if conc then v else u
                                 Just (x,toBeReplaced ts)
             F "=" [u,_]   -> do (x,ts) <- g $ if conc then t else u
                                 Just (x,toBeReplaced ts)
             _ -> do guard conc; (x,ts) <- g t; Just (x,toBeReplaced ts)
   where g t = do guard $ f x; Just (x,concat tss) where (x,tss) = unCurry t
         toBeReplaced ts = [i | i <- indices_ ts, let t = ts!!i; x = root t,
                                isF t || not (noExcl x) ||
                                any (x `isin`) (context i ts) ]

-- used by Ecom > applyClause,createInvariant,{co}induction,stretch

-- stretchConc k ns t replaces the subterms of t at positions ns by variables
-- zk,z(k+1),... and turns t into a Horn axiom.

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

-- used by Ecom > applyClause,coinduction,stretch

-- stretchPrem k ns t replaces the subterms of t at positions ns by variables
-- zk,z(k+1),... and turns t into a co-Horn axiom to be used by a proof by
-- fixpoint induction.

stretchPrem k ns (F "&" (cl:cls)) = (mkCoHorn prem $ mkConjunct $ conc:cls',
                                     maximum $ n:ks)
 where (F "===>" [prem,conc],n) = f cl
       (cls',ks) = unzip $ map g cls
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
       g (F "==>" [F "=" [t,r],conc]) = (mkImpl (mkConjunct eqs') conc,m)
                      where (x,tss) = unCurry t
                            (us,eqs,n) = addEqs (concat tss) [] [] k ns 0
                            (eqs',m) = if isV r && root r `notElem` map root us
                                       then (eqs,n)
                                       else (mkEq (newVar n) r:eqs,n+1)
       g (F "==>" [t,conc]) = (mkImpl (mkConjunct eqs) conc,n)
                              where (x,tss) = unCurry t
                                    eqs = addEqs0 (concat tss) [] k ns 0
       g (F "=" [t,r])      = (mkImpl (mkConjunct eqs) $ mkEq (newVar n) r,n+1)
                              where (x,tss) = unCurry t
                                    eqs = addEqs0 (concat tss) [] k ns 0
stretchPrem k ns cl = stretchPrem k ns $ F "&" [cl]

-- used by Ecom > applyClause,createInvariant,induction,stretch

-- For each term t of ts at a position in ns, addEqs ts [] [] k ns 0 replaces
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

-- used by mk{Co}HornLoop

updArgsA :: TermS -> TermS -> [TermS] -> TermS
updArgsA (F "$" [t,_]) i ts = applyL (F "$" [addLoop t,i]) ts
updArgsA (F x _) i ts       = F (x++"Loop") $ i:ts
updArgsA t _ _              = t

-- used by mk{Co}HornLoop

addLoop :: TermS -> TermS
addLoop (F "$" [t,u]) = F "$" [addLoop t,u]
addLoop (F x ts)      = F (x++"Loop") ts
addLoop t             = t

mkEqsWithArgs :: t -> [TermS] -> [Int] -> TermS -> [TermS]
mkEqsWithArgs _ zs is = zipWith mkEq zs . contextM is . getArgs

-- used by mk{Co}HornLoop,compressAll

-- mkHornLoop sig x transforms the co-Horn axioms for x into an equivalent set
-- of three Horn axioms.

mkHornLoop :: Sig -> t -> [TermS] -> TermS -> Int -> ([TermS], Int)
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

-- used by Ecom > kleeneAxioms

-- mkCoHornLoop sig x transforms the Horn axioms for x into an equivalent set
-- of three co-Horn axioms.

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

-- used by Ecom > kleeneAxioms

-- compressAll sig k axs transforms the axioms of axs into a single axiom
-- (if b = True) and inverts it (if b = False).

compressAll b sig i axs = compressOne b sig i [] axs $ h $ head axs
                          where h (F "==>" [_,cl])  = h cl
                                h (F "===>" [at,_]) = h at
                                h (F "<===" [at,_]) = h at
                                h (F "=" [t,_])     = t
                                h t                     = t

-- used by Ecom > compressAxioms

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

compressOne b sig i ks cls t
   | isPred sig x    = (g (updArgs t us) $ compressHorn sig eqs cls, j)
   | isDefunct sig x = (g (mkEq (updArgs t us) z) $ compressHornEq sig eqs' cls,
                        j+1)
   | True            = (h (updArgs t us) $ compressCoHorn sig eqs cls, j)
     where (x,ts) = getOpArgs t
           (us,j) = foldr f ([],i) $ indices_ ts
           eqs = mkEqsWithArgs sig (map newVar [i..j-1]) ks
           z = newVar j 
           eqs' t u = mkEq z u:eqs t
           f i (us,k) = if i `elem` ks then (ts!!i:us,k) else (newVar k:us,k+1)
           (g,h) = if b then (mkHorn,mkCoHorn) else (mkCoHorn,mkHorn)

-- compressHorn sig eqs transforms Horn axioms for a predicate into the premise
-- of an equivalent single Horn axiom.

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

-- moveUp sig vc x us is moves the quantifiers from noRefPositions 
-- q++[is!!0],...,q++[is!!length is-1] of t to position q. 
-- F x us is the original term at position q. 

moveUp sig vc "==>" us@[u,v] is = (as',es',F "==>" ts,vc')
 where split (ps,qs) i = if isAllQ t then ((i,alls t):ps,qs) 
                                       else (ps,(i,anys t):qs)
                         where t = us!!i
       [u1,v1] = zipWith g us [0,1]
       g u i = if i `elem` is then head $ subterms u else u
       h = renaming vc
       rename = renameFree sig
       (as',es',ts,vc') =
               case foldl split nil2 is of
               ([(0,as0),(1,as1)],[]) -> (map f as1,as0,[u1,rename f v1],vc1)
                                         where (f,vc1) = h $ meet as0 as1
               ([],[(0,es0),(1,es1)]) -> (es0,map f es1,[u1,rename f v1],vc1)
                                         where (f,vc1) = h $ meet es0 es1
               ([(0,as)],[(1,es)])    -> ([],as++map f es,[u1,rename f v1],vc1)
                                         where (f,vc1) = h $ meet as es
               ([(1,as)],[(0,es)])    -> (es++map f as,[],[u1,rename f v1],vc1)
                                         where (f,vc1) = h $ meet as es
               ([(0,as)],[])          -> ([],map f as,[rename f u1,v1],vc1)
                                         where zs = frees sig v `meet` as
                                               (f,vc1) = h zs
               ([(1,as)],[])          -> (map f as,[],[u1,rename f v1],vc1)
                                         where zs = frees sig u `meet` as
                                               (f,vc1) = h zs
               ([],[(0,es)])          -> (map f es,[],[rename f u1,v1],vc1)
                                         where zs = frees sig v `meet` es
                                               (f,vc1) = h zs
               ([],[(1,es)])          -> ([],map f es,[u1,rename f v1],vc1)
                                         where zs = frees sig u `meet` es
                                               (f,vc1) = h zs
moveUp _ vc "Not" [u] _ = (anys u,alls u,F "Not" [head (subterms u)],vc)
moveUp sig vc x us is   = (joinMap snd ps',joinMap snd qs',F x ts',vc')
       where (ps,qs) = foldl split nil2 is 
             split (ps,qs) i = if isAllQ t then ((i,alls t):ps,qs) 
                                           else (ps,(i,anys t):qs)
                               where t = us!!i
             free = joinMap (frees sig) $ contextM is ts
             ts = zipWith h us $ indices_ us
                  where h u i = if i `elem` is then head $ subterms u else u
             (ts',vc',ps',qs') = loop1 (ts,vc,ps,qs) ps
             loop1 (ts,vc,ps,qs) (p@(i,xs):ps1) = loop1 (ts',vc',ps',qs) ps1
                            where rest = ps `minus1` p
                                  zs = if x == "&" then free
                                       else join free $ joinMap snd $ rest++qs
                                  (f,vc') = renaming vc (xs `meet` zs)
                                  ts' = updList ts i $ renameFree sig f $ ts!!i
                                  ps' = (i,map f xs):rest
             loop1 state _ = loop2 state qs
             loop2 (ts,vc,ps,qs) (q@(i,xs):qs1) = loop2 (ts',vc',ps,qs') qs1
                            where rest = qs `minus1` q
                                  zs = if x == "|" then free
                                       else join free $ joinMap snd $ rest++ps
                                  (f,vc') = renaming vc $ meet xs zs
                                  ts' = updList ts i $ renameFree sig f $ ts!!i
                                  qs' = (i,map f xs):rest
             loop2 state _ = state

-- used by Ecom > shiftQuants

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
                  conc1 = mkImpl prem $ mkDisjunct $ map f $ ns conc
                       -- mkDisjunct $ neg prem:map f (ns conc)
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
                     newImpl = mkImpl $ mkConjunct $ map pr $ ns 0
                     prems = map (mkNot sig . co) $ ns 1
                  -- concs = map (neg . pr) $ ns 0
                     prem1 = mkConjunct $ map pr cs++prems
                     conc1 = newImpl $ mkDisjunct $ map co ds
                          -- mkDisjunct $ concs++map co ds
                     prem2 = mkConjunct $ map pr cs
                     conc2 = newImpl conc
                          -- mkDisjunct $ conc:concs
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

-- used by Ecom > shiftSubs'

-- getOtherSides t p ts ps looks for in/equations eq in a formula t such that
-- one side of eq agrees with some u in ts. u is replaced by the other side of
-- eq if the replacement leads to to a formula that is equivalent to t.
-- p and ps are the positions of t and ts, respectively.

getOtherSides :: TermS -> [Int] -> [TermS] -> [[Int]] -> Maybe [TermS]
getOtherSides t p ts ps =
    case t of F "==>" [F "&" prems,
                       F "|" concs]      -> f prems (p0 prems) concs $ p1 concs
              F "==>" [F "&" prems,conc] -> f prems (p0 prems) [conc] [p++[1]]
              F "==>" [prem,F "|" concs] -> f [prem] [p++[0]] concs $ p1 concs
              F "==>" [prem,conc]        -> f [prem] [p++[0]] [conc] [p++[1]]
              F "&" prems                  -> f prems (succsInd p prems) [] []
              F "|" concs                -> f [] [] concs $ succsInd p concs
              _                          -> Nothing
    where p0 = succsInd $ p++[0]
          p1 = succsInd $ p++[1]
          b :: [[Int]] -> Int -> Int -> Bool
          b eqps i k = not (eqps!!i <<= ps!!k)
          f :: [TermS] -> [[Int]] -> [TermS] -> [[Int]] -> Maybe [TermS]
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

-- used by Ecom > replaceSubtrees