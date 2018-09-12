-- stack --resolver lts-12.9 script
-- Generate list of known failure for test/SpecificationTest.isKnownFailure.
import System.Environment
import Control.Monad
import Data.List
import Data.List.Extra
import Data.Maybe

suffix = ": [Failed]"

main :: IO ()
main = do
    args <- getArgs
    when (null args) $ error "Filename argument expected!"
    ls <- lines <$> readFile (last args)
    print $ map (trim . fromJust . stripSuffix suffix) $ filter ( suffix `isSuffixOf`) ls