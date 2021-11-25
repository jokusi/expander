module Main where

import Base.OHaskell
import Base.Gui
import Base.System
import Epaint
import Ecom

import Graphics.UI.Gtk
import Data.IORef

main :: IO ()
main = do
    installJavaScript
    
    initGUI
    loadCSS
    
    -- fix
    solve1Ref <- newIORef undefined
    solve2Ref <- newIORef undefined
    paint1 <- painter 820 solve1Ref solve2Ref
    paint2 <- painter 820 solve2Ref solve1Ref
    enum1 <- enumerator solve1Ref
    enum2 <- enumerator solve2Ref
    solve1 <- solver "Solver1" solve2Ref enum1 paint1
    solve2 <- solver "Solver2" solve1Ref enum2 paint2
    writeIORef solve1Ref solve1
    writeIORef solve2Ref solve2
    
    buildSolve solve1
    buildSolve solve2
    backWin solve2
    
    mainGUI
