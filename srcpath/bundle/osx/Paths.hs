module Paths (getDataDir) where

import System.Environment (getExecutablePath)
import System.FilePath ((</>), takeDirectory)

getDataDir :: IO FilePath
getDataDir = do
    exePath <- getExecutablePath
    return $ takeDirectory (takeDirectory exePath)
        </> "Resources" </> "share" </> "expander"
