{-# LANGUAGE BangPatterns #-}
module Base.OHaskell
  ( module Prelude
  , module Paths
  , module Data.IORef
  , module Data.Char
  , when
  , guard
  , MonadPlus
  , Action
  , Request
  , Template
  , Cmd
  , zero
  , (++)
  , concat
  , while
  , done
  ) where

import Paths (getDataDir)

import Control.Monad (when, MonadPlus(mzero,mplus), msum, guard)
import Data.Char (chr, ord, toLower, isLower, isDigit)
import Data.IORef
import Prelude hiding ((++),concat,(<*))


-- O'Haskell types
type Action = IO ()
type Request = IO
type Template = IO
type Cmd = IO

-- O'Haskell functions
infixr 5 ++

zero :: MonadPlus m => m a
zero = mzero

(++) :: MonadPlus m => m a -> m a -> m a
(++) = mplus

concat :: MonadPlus m => [m a] -> m a
concat = msum

-- O'Haskell constructs
while :: Request Bool -> Action -> Action
while mb act = do
    b <- mb 
    when b $ do
        act
        while mb act 

done :: Action
done = return ()
