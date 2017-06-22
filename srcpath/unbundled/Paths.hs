module Paths (getDataDir) where

import qualified Paths_expander as P

getDataDir :: IO FilePath
getDataDir = P.getDataDir
