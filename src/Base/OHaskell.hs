{-# LANGUAGE BangPatterns #-}
module Base.OHaskell
  ( module Prelude
  , module Paths
  , module Data.IORef
  , module Data.Char
  , when
  , guard
  , unless
  , MonadPlus
  , Action
  , Request
  , Template
  , Cmd
  , zero
  , (++)
  , concat
  , accumulate
  , sequence
  , while
  , done
  ) where

import Paths (getDataDir)

import Control.Monad (MonadPlus,when,guard,unless)
import qualified Control.Monad as Haskell
import Data.Char (chr, ord, toLower, isLower, isDigit, isAlpha)
import Data.IORef
import Prelude hiding ((++),concat,(<*),sequence)


-- O'Haskell types
type Action = IO ()
type Request = IO
type Template = IO
type Cmd = IO

-- O'Haskell functions
infixr 5 ++

zero :: MonadPlus m => m a
zero = Haskell.mzero

(++) :: MonadPlus m => m a -> m a -> m a
(++) = Haskell.mplus

concat :: MonadPlus m => [m a] -> m a
concat = Haskell.msum

accumulate :: Monad m => [m a] -> m [a]
accumulate = Haskell.sequence

sequence :: Monad m => [m a] -> m ()
sequence = Haskell.sequence_

-- O'Haskell constructs
while :: Request Bool -> Action -> Action
while mb act = do
    b <- mb 
    Haskell.when b $ do
        act
        while mb act 

done :: Action
done = return ()
