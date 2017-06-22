module GuiBench (benchs) where

import Gui
import Criterion.Main

sinus, logarithm, square :: [(Double, Double)]
sinus = [(0.0,0.0),(1.0,0.8414709848078965),(2.0,0.9092974268256817),(3.0,0.1411200080598672),(4.0,-0.7568024953079282),(5.0,-0.9589242746631385),(6.0,-0.27941549819892586),(7.0,0.6569865987187891),(8.0,0.9893582466233818),(9.0,0.4121184852417566),(10.0,-0.5440211108893698),(11.0,-0.9999902065507035),(12.0,-0.5365729180004349),(13.0,0.4201670368266409),(14.0,0.9906073556948704),(15.0,0.6502878401571168),(16.0,-0.2879033166650653),(17.0,-0.9613974918795568),(18.0,-0.750987246771676),(19.0,0.14987720966295234),(20.0,0.9129452507276277),(21.0,0.8366556385360561),(22.0,-8.851309290403876e-3),(23.0,-0.8462204041751706),(24.0,-0.9055783620066239),(25.0,-0.13235175009777303),(26.0,0.7625584504796027),(27.0,0.956375928404503),(28.0,0.27090578830786904),(29.0,-0.6636338842129675),(30.0,-0.9880316240928618),(31.0,-0.404037645323065),(32.0,0.5514266812416906),(33.0,0.9999118601072672),(34.0,0.5290826861200238),(35.0,-0.428182669496151),(36.0,-0.9917788534431158),(37.0,-0.6435381333569995),(38.0,0.2963685787093853),(39.0,0.9637953862840878),(40.0,0.7451131604793488),(41.0,-0.158622668804709),(42.0,-0.9165215479156338),(43.0,-0.8317747426285983),(44.0,1.7701925105413577e-2),(45.0,0.8509035245341184),(46.0,0.9017883476488092),(47.0,0.123573122745224),(48.0,-0.7682546613236668),(49.0,-0.9537526527594719),(50.0,-0.26237485370392877)]
logarithm = [(1.0,0.0),(2.0,0.6931471805599453),(3.0,1.0986122886681098),(4.0,1.3862943611198906),(5.0,1.6094379124341003),(6.0,1.791759469228055),(7.0,1.9459101490553132),(8.0,2.0794415416798357),(9.0,2.1972245773362196),(10.0,2.302585092994046),(11.0,2.3978952727983707),(12.0,2.4849066497880004),(13.0,2.5649493574615367),(14.0,2.6390573296152584),(15.0,2.70805020110221),(16.0,2.772588722239781),(17.0,2.833213344056216),(18.0,2.8903717578961645),(19.0,2.9444389791664403),(20.0,2.995732273553991),(21.0,3.044522437723423),(22.0,3.091042453358316),(23.0,3.1354942159291497),(24.0,3.1780538303479458),(25.0,3.2188758248682006),(26.0,3.258096538021482),(27.0,3.295836866004329),(28.0,3.332204510175204),(29.0,3.367295829986474),(30.0,3.4011973816621555),(31.0,3.4339872044851463),(32.0,3.4657359027997265),(33.0,3.4965075614664802),(34.0,3.5263605246161616),(35.0,3.5553480614894135),(36.0,3.58351893845611),(37.0,3.6109179126442243),(38.0,3.6375861597263857),(39.0,3.6635616461296463),(40.0,3.6888794541139363),(41.0,3.713572066704308),(42.0,3.7376696182833684),(43.0,3.7612001156935624),(44.0,3.784189633918261),(45.0,3.8066624897703196),(46.0,3.828641396489095),(47.0,3.8501476017100584),(48.0,3.871201010907891),(49.0,3.8918202981106265),(50.0,3.912023005428146)]
square = [(0.0,0.0),(1.0,1.0),(2.0,4.0),(3.0,9.0),(4.0,16.0),(5.0,25.0),(6.0,36.0),(7.0,49.0),(8.0,64.0),(9.0,81.0),(10.0,100.0),(11.0,121.0),(12.0,144.0),(13.0,169.0),(14.0,196.0),(15.0,225.0),(16.0,256.0),(17.0,289.0),(18.0,324.0),(19.0,361.0),(20.0,400.0),(21.0,441.0),(22.0,484.0),(23.0,529.0),(24.0,576.0),(25.0,625.0),(26.0,676.0),(27.0,729.0),(28.0,784.0),(29.0,841.0),(30.0,900.0),(31.0,961.0),(32.0,1024.0),(33.0,1089.0),(34.0,1156.0),(35.0,1225.0),(36.0,1296.0),(37.0,1369.0),(38.0,1444.0),(39.0,1521.0),(40.0,1600.0),(41.0,1681.0),(42.0,1764.0),(43.0,1849.0),(44.0,1936.0),(45.0,2025.0),(46.0,2116.0),(47.0,2209.0),(48.0,2304.0),(49.0,2401.0),(50.0,2500.0)]

bench_smooth_lazy :: Benchmark
bench_smooth_lazy = bgroup "smooth lazy"
  [ bench_smooth_lazy_sinus
  , bench_smooth_lazy_logarithm
  , bench_smooth_lazy_square
  ]

bench_smooth_lazy_sinus :: Benchmark
bench_smooth_lazy_sinus = bench "sinus" $ nf smooth sinus

bench_smooth_lazy_logarithm :: Benchmark
bench_smooth_lazy_logarithm = bench "logarithm" $ nf smooth logarithm

bench_smooth_lazy_square :: Benchmark
bench_smooth_lazy_square = bench "square" $ nf smooth square

bench_smooth_strict :: Benchmark
bench_smooth_strict = bgroup "smooth strict"
  [ bench_smooth_strict_sinus
  , bench_smooth_strict_logarithm
  , bench_smooth_strict_square
  ]

bench_smooth_strict_sinus :: Benchmark
bench_smooth_strict_sinus = bench "sinus" $ nf smooth' sinus

bench_smooth_strict_logarithm :: Benchmark
bench_smooth_strict_logarithm = bench "logarithm" $ nf smooth' logarithm

bench_smooth_strict_square :: Benchmark
bench_smooth_strict_square = bench "square" $ nf smooth' square

benchs :: Benchmark
benchs = bgroup "Gui"
    [ bench_smooth_lazy
    , bench_smooth_strict
    ]

smooth :: [(Double,Double)] -> [(Double,Double)]
smooth = interpolate . clean . spline
    where clean (p:ps) = p : dropWhile (==p) ps
          clean [] = []

interpolate :: [(Double,Double)] -> [(Double,Double)]
interpolate pss@(p1:p2:_:_) = p1:q1:interpolate' pss
    where scale = 0.35
          closed = p1 == last pss
          p0 = last $ init pss
          mag (x,y) = sqrt ((x ** 2) + (y ** 2))
          skalar s (x,y) = (s*x,s*y)
          norm v = skalar (1 / mag v) v
          calc op (x1,y1) (x2,y2) = (x1 `op` x2, y1 `op` y2)
          sub = calc (-)
          add = calc (+)
          -- mul = calc (*)
          tangent = if closed then norm $ sub p2 p0
                    else sub p2 p1
          q1 = if closed
               then add p1 $ skalar (scale * mag (sub p2 p1)) tangent
               else add p1 $ skalar scale tangent
          interpolate' (p0:p1:p2:ps) = q0:p1:q1:interpolate' (p1:p2:ps)
            where tangent = norm $ sub p2 p0
                  q0 = sub p1 $ skalar (scale * mag (sub p1 p0)) tangent
                  q1 = add p1 $ skalar (scale * mag (sub p2 p1)) tangent
          interpolate' [p0, p1] = [q0, p1]
            where tangent = if closed then norm $ sub p2 p0
                            else sub p1 p0
                  q0 = if closed
                       then sub p1 $ skalar (scale * mag (sub p1 p0)) tangent
                       else sub p1 (skalar scale tangent)
          interpolate' _ = error "Gui.interpolate: interpolate' should never be\
                                \ called with list of length < 2."
interpolate pss = pss


