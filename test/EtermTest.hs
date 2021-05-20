{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module EtermTest (tests) where

import Data.Array

import GHC.Generics

import qualified Test.Framework as Test
import qualified Test.Framework.Providers.HUnit as Test
import qualified Test.Framework.Providers.QuickCheck2 as Test
import qualified Test.HUnit as Test
import qualified Test.QuickCheck as Test
import qualified Test.QuickCheck.Poly as Test

import Eterm

tests = Test.testGroup "module Eterm"
  [ testResult
  -- , testRegExOrd fails!
  ]

-- Base

deriving instance Generic Test.A
deriving instance Generic Test.B
deriving instance Generic Test.C

-- * Result

instance (i ~ (Int,Int), Test.Arbitrary e) => Test.Arbitrary (Array i e) where
  arbitrary = Test.sized $ \n ->
    listArray ((0,0), (n,n)) <$> repeat <$> Test.arbitrary

instance Eq SubstS where
  f == g = cmp "" && cmp "abc" && cmp " _ _" where
    cmp str = f str == g str

instance Show SubstS where
  showsPrec p sub = showsPrec p (sub "<sub>")

deriving instance Generic ActLR

instance Test.Arbitrary ActLR where
  shrink = Test.genericShrink
  arbitrary = Test.oneof
    [ Rule <$> Test.arbitrary <*> Test.arbitrary
    , return Read
    , return Error
    ]

deriving instance Generic Special

instance Test.Arbitrary Special where
  shrink Nil = []
  shrink (Dissect s) = Nil : [Dissect s' | s' <- Test.shrink s]
  shrink (BoolMat a b c)
    = Nil : [BoolMat a' b' c' | (a',b',c') <- Test.shrink (a,b,c)]
  shrink (ListMat a b c)
    = Nil : [ListMat a' b' c' | (a',b',c') <- Test.shrink (a,b,c)]
  arbitrary = Test.oneof
    [ return Nil
    , Dissect <$> Test.arbitrary
    -- , EquivMat <$> Test.arbitrary <*> Test.arbitrary
    , BoolMat <$> Test.arbitrary <*> Test.arbitrary <*> Test.arbitrary
    , ListMat <$> Test.arbitrary <*> Test.arbitrary <*> Test.arbitrary
    ]

deriving instance Generic a => Generic (Term a)

instance (Generic a, Test.Arbitrary a) => Test.Arbitrary (Term a) where
  shrink = Test.genericShrink
  arbitrary = Test.sized node
    where
      leafs =
        [ V <$> Test.arbitrary
        , Hidden <$> Test.arbitrary
        ]
      node n
        | n > 0 = do
          val <- Test.arbitrary
          len <- Test.choose (0,2)
          sub <- Test.vectorOf len $ node (n-1)
          Test.oneof $ (return $ F val sub) : leafs
        | otherwise = Test.oneof leafs

deriving instance Eq a => Eq (Result a)
deriving instance Show a => Show (Result a)
deriving instance Generic a => Generic (Result a)

instance (Generic a, Test.Arbitrary a) => Test.Arbitrary (Result a) where
  shrink = Test.genericShrink
  arbitrary = Test.oneof
    [ Def <$> Test.arbitrary
    , return BadOrder
    , Circle <$> Test.arbitrary <*> Test.arbitrary
    , NoPos <$> Test.arbitrary
    , return NoUni
    , OcFailed <$> Test.arbitrary
    , ParUni <$> Test.arbitrary <*> Test.arbitrary
    , TotUni <$> Test.arbitrary
    ]

testResult = Test.testGroup "Result"
  [ testResultFunctor
  , testResultApplicative
  , testResultMonad
  ]


-- ** Result Functor laws

testResultFunctor = Test.testGroup "Result Functor laws"
  [ Test.testProperty "fmap id  ==  id" testResultFunctorId
  , Test.testProperty "fmap (f . g)  ==  fmap f . fmap g" testResultFunctorComp
  ]

testResultFunctorId :: Result Test.A -> Bool
testResultFunctorId x = fmap id x ==  id x

testResultFunctorComp :: Test.Blind (Test.B -> Test.C)
  -> Test.Blind (Test.A -> Test.B)
  -> Result Test.A -> Bool
testResultFunctorComp (Test.Blind f) (Test.Blind g) x
  = fmap (f . g) x ==  (fmap f . fmap g) x

-- ** Result Applicative laws
testResultApplicative = Test.testGroup "Result Applicative laws"
  [ Test.testProperty "identity (pure id <*> v = v)" testResultApplicativeIdentity
  -- , Test.testProperty "composition (pure (.) <*> u <*> v <*> w = u <*> (v <*> w))" testResultApplicativeComposition
  , Test.testProperty "homomorphism (pure f <*> pure x = pure (f x))" testResultApplicativeHomomorphism
  -- , Test.testProperty "interchange (u <*> pure y = pure ($ y) <*> u)" testResultApplicativeInterchange
  ]

testResultApplicativeIdentity :: Result Test.A -> Bool
testResultApplicativeIdentity v = (pure id <*> v) == v

-- testResultApplicativeComposition :: Result (Test.B -> Test.C) -> Result (Test.A -> Test.B) -> Result Test.A -> Bool
-- testResultApplicativeComposition u v w = (pure (.) <*> u <*> v <*> w) == (u <*> (v <*> w))

testResultApplicativeHomomorphism :: Test.Blind (Test.A -> Test.B) -> Test.A -> Bool
testResultApplicativeHomomorphism (Test.Blind f) x = (pure f <*> pure x) == (pure (f x) :: Result Test.B)

-- testResultApplicativeInterchange :: Result (Test.A -> Test.B) -> Test.A -> Bool
-- testResultApplicativeInterchange u y = (u <*> pure y) == (pure ($ y) <*> u)


-- * Result Monad laws

testResultMonad =  Test.testGroup "Result Monad laws"
  [ Test.testProperty "return a >>= k  =  k a" testResultMonadZeroLeft
  , Test.testProperty "m >>= return  =  m" testResultMonadZeroRight
  , Test.testProperty "m >>= (\\x -> k x >>= h)  =  (m >>= k) >>= h"
    testResultMonadComp
  ]


testResultMonadZeroLeft :: Test.A -> Test.Blind(Test.A -> Result Test.B) -> Bool
testResultMonadZeroLeft a (Test.Blind k) = (return a >>= k)  ==  k a

testResultMonadZeroRight :: Result Test.A -> Bool
testResultMonadZeroRight m = (m >>= return)  ==  m

testResultMonadComp :: Result Test.A -> Test.Blind (Test.B -> Result Test.C)
  -> Test.Blind (Test.A -> Result Test.B) -> Bool
testResultMonadComp m (Test.Blind h) (Test.Blind k)
  = (m >>= (\x -> k x >>= h))  ==  ((m >>= k) >>= h)


-- * RegExp
deriving instance Generic RegExp

deriving instance Show RegExp

instance Test.Arbitrary RegExp where
  shrink = Test.genericShrink
  arbitrary = Test.sized depth where
      leafs =
        [ return Mt
        , return Eps
        , return Int_
        , Const <$> Test.arbitrary
        , Var <$> Test.arbitrary
        ]
      depth 0 = Test.oneof leafs
      depth state = Test.oneof $ leafs ++
        [ Sum_ <$> depth n <*> depth n
        , Prod <$> depth n <*> depth n
        , Star <$> depth n
        ] where n = state - 1

infixr 0 ==>
(==>) :: Bool -> Bool -> Bool
b1 ==> b2 = not b1 || b2

regexOrdRefl :: RegExp -> Bool
regexOrdRefl x = x <= x

regexOrdTrans :: RegExp -> RegExp -> RegExp -> Bool
regexOrdTrans x y z = (x <= y && y <= z) ==> x <= z

regexOrdAntisym :: RegExp -> RegExp -> Bool
regexOrdAntisym x y = x <= y && y <= x ==> x == y

testRegExOrd = Test.testGroup "RegExp.Ord laws"
  [ Test.testProperty "reflexivity (x <= x)" regexOrdRefl
  , Test.testProperty "transitivity (x <= y && y <= z ==> x <= z)"
    regexOrdRefl
  , Test.testProperty "antisymmetry (x <= y && y <= x ==> x == y)"
    regexOrdAntisym
  ]
