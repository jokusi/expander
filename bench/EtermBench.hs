module EtermBench (benchs) where

import Eterm
import Criterion.Main
import Data.Foldable (foldl')

minmax' :: (Num a, Num b, Ord a, Ord b) => [(a, b)] -> (a, b, a, b)
minmax' s@((x,y):_) = foldl' minmax1 (x,y,x,y) s
      where minmax1 (x1,y1,x2,y2) (x,y) =
                let x1' = min x x1
                    y1' = min y y1
                    x2' = max x x2
                    y2' = max y y2
                in x1' `seq` y1' `seq` x2' `seq` y2' `seq` (x1', y1', x2', y2')
minmax' _             = (0,0,0,0)

minmaxList :: Int -> [(Int, Int)]
minmaxList x = take (4 * x) $ cycle
                $ [(3,4), (9,5), (1000,100), (5,5)] :: [(Int, Int)]

bench_minmax_lazy :: Benchmark
bench_minmax_lazy =
    let
        ls1 = minmaxList 1
        ls10 = minmaxList 10
        ls100 = minmaxList 100
    in ls1 `seq` ls10 `seq` ls100 `seq` bench "minmax lazy" $ nf minmax ls100

bench_minmax_strict :: Benchmark
bench_minmax_strict =
    let
        ls1 = minmaxList 1
        ls10 = minmaxList 10
        ls100 = minmaxList 100
    in ls1 `seq` ls10 `seq` ls100 `seq` bench "minmax strict" $ nf minmax' ls100

benchs :: Benchmark
benchs = bgroup "Eterm"
    [ bench_minmax_lazy
    , bench_minmax_strict
    ]
