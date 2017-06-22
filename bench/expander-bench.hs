import qualified EtermBench
import qualified GuiBench
import Criterion.Main
import qualified Criterion.Types as Config (Config(..))


reportFile :: FilePath
reportFile = "expander_bench.html"

main = do
    defaultMainWith defaultConfig{Config.reportFile = Just reportFile}
        [ EtermBench.benchs
        , GuiBench.benchs
        ]

