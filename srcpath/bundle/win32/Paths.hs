module Paths (getDataDir) where

import System.Environment (getExecutablePath)
import System.FilePath ((</>), takeDirectory)

getDataDir :: IO FilePath
getDataDir = do
    return $ ".." </> "share" </> "expander"
