module Main where

import Test.Framework
import Test.Framework.Providers.HUnit
import Test.HUnit

import qualified EtermTest
import qualified EpaintTest
import qualified EsolveTest
import qualified EcomTest

tests = 
  [ EtermTest.tests
  , EpaintTest.tests
  , EsolveTest.tests
  , EcomTest.tests
  ]

main = defaultMain tests
