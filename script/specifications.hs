-- stack --resolver lts-12.9 script
-- Generates list of files in data/Examples
import System.Directory
import System.FilePath
import Control.Monad
import Data.List

datapath = "data"
path = datapath </> "Examples"

main :: IO ()
main = do
    list0 <- listDirectory $ path
    let list1 = sort list0
        list2 = map (path </>) list1
        list3 = filter (not . hasExtension) list2
    list4 <- filterM doesFileExist list3
    let list5 = map (drop $ length datapath + 1) list4
    forM_ list5 $ \item -> do
        putStr "                   , \""
        putStr item
        putStrLn "\""

