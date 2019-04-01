module Base.System
  ( module Base.Gui
  , module System.CPUTime
  , module System.FilePath
  , home
  , builtinLibDir
  , builtinLib
  , userLibDir
  , userLib
  , pixpath
  , mkDir
  , renewDir
  , mkFile
  , loadPhoto
  , savePic
  , lookupLibs
  , (&=)
  , html
  , mkHtml
  , mkSecs
  , installJavaScript
  ) where

import Prelude ()
import Base.Gui

import System.CPUTime (getCPUTime)
import System.Directory
import System.FilePath ((<.>),(</>),hasExtension,splitExtension,takeExtension)
import System.IO.Error (catchIOError)

infixl 6 &=


-- | Program folder.
home :: IO FilePath
home = getAppUserDataDirectory "expander"

-- | Builtin library/example folder.
builtinLibDir :: IO FilePath
builtinLibDir = do
    dataDir <- getDataDir
    return $ dataDir </> "Examples"

-- | Builtin library/example files.
builtinLib :: FilePath -> IO FilePath
builtinLib file = do
    dir <- builtinLibDir
    return $ dir  </> file

-- | User library example folder.
-- Unix: $HOME/.expander/Examples
-- Windows: $APPDATA\\expander\\Examples
userLibDir :: IO FilePath
userLibDir = do
  dir <- home
  return $ dir </> "ExpanderLib"

-- | User library example files.
userLib :: FilePath -> IO FilePath
userLib file = do
  dir <- userLibDir
  return $ dir </> file


pixpath :: FilePath -> IO FilePath
pixpath file = do
    dir <- userLibDir
    return $ dir </> "Pix" </> file

mkDir :: FilePath -> IO ()
mkDir = createDirectoryIfMissing True

renewDir :: FilePath -> IO ()
renewDir dir = do
  exists <- doesDirectoryExist dir
  when exists $ removeDirectoryRecursive dir
  mkDir dir

mkFile :: String -> Int -> String
mkFile dir i | i < 10  = enclose "00"
             | i < 100 = enclose "0"
             | True    = enclose ""
               where enclose str = dir </> str ++ show i ++ ".png"

-- Customized for Expander3 to be able to load animation frames from gif.
loadPhoto :: Int -> Bool -> FilePath -> IO (Maybe Image)
loadPhoto pos alpha file = do
    userPath' <- userLib file'
    isUserFile <- doesFileExist userPath'
    if isUserFile then imageFromFile userPath' -- file in user lib
    else do
      userPath <- userLib file
      isUserDir <- doesDirectoryExist userPath
      if isUserDir then imageFromFile $ str userPath -- dir in user lib
      else do
        buildinPath' <- builtinLib file'
        isBuildinFile <- doesFileExist buildinPath'
        if isBuildinFile then imageFromFile buildinPath' -- file in builtin lib
        else do
          buildinPath <- builtinLib file
          isBuildinDir <- doesDirectoryExist buildinPath
          if isBuildinDir
          then imageFromFile $ str buildinPath -- dir in builtin lib
          else return Nothing -- does not exist
    where file' = if hasExtension file then file else file <.> "gif"
          imageFromFile path = do
            anim <- pixbufAnimationNewFromFile path
            let start = GTimeVal 0 0
            iter <- pixbufAnimationGetIter anim (Just start)
            step <- pixbufAnimationIterGetDelayTime iter
            let time = gTimeValAdd start $ fromIntegral ((pos-1) * step * 1000)
            _ <- pixbufAnimationIterAdvance iter (Just time)
            image <- pixbufAnimationIterGetPixbuf iter
            return $ Just $ Image alpha image
          str path  = path </> (file++'_':show pos) <.> "gif"


savePic :: String -> Canvas -> String -> Cmd String
savePic _ = canvasSave


lookupLibs :: FilePath -> IO String
lookupLibs file = do
        path <- userLib file
        readFile path
    `catchIOError` \_ -> do
        path <- builtinLib file
        readFile path
    `catchIOError` \_ -> return ""

(&=) :: String -> String -> String
x &= val = x ++ "=\"" ++ val ++ "\""

html :: String -> String -> [String] -> IO ()
html dirPath dir files
  | null files  = return ()
  | otherwise = writeFile (dirPath ++ ".html") $
    "<html>\n<head>\n<title>" ++ dir ++ 
    "</title>\n<script type"&="text/javascript" ++
    ">\nvar images = new Array(" ++ '\"':first ++ '\"':concatMap f rest ++ 
    ")\n</script>\n<script type"&="text/javascript" ++ " src"&="Painter.js" ++
    ">\n</script>\n</head>\n<body style"&="background-color: rgb(221,221,255)"++
    ">\n<input type"&="button" ++
    " value"&="|<<" ++ " onclick"&="backStop(this)"++
    ">\n<input type"&="button" ++
    " value"&="<" ++ " onclick"&="back()" ++ "> " ++
    show n ++ " picture" ++ (if n == 1 then "" else "s") ++
    "\n<input type"&="button" ++ " value"&=">" ++ " onclick"&="forth()" ++
    ">\n<input type"&="button" ++ " value"&=">>|" ++
    " onclick"&="forthStop(this)"++
    ">\n<input type"&="button" ++ " value"&="loop" ++ " onclick"&="loop(this)"++
    ">\n<br><input id"&="fileSlider" ++ " type"&="range" ++ " min"&="0" ++
    " max"&=show (n-1) ++ " value"&="0" ++ " onchange"&="showFile(this.value)"++
    ">\n<span id"&="file" ++ '>':first ++
    "</span>\n<br>\n<input type"&="range" ++
    " min"&="0" ++ " max"&="2000" ++ " value"&="30" ++
    " onchange"&="showTime(this.value)" ++ ">\n<span id"&="time" ++
    ">30</span> millisecs\n<br><br><br>\n<iframe id"&="img" ++ " src"&=first ++
    " width"&="1800" ++ " height"&="900" ++ " frameborder"&="0" ++
    ">\n</iframe>\n</body>\n</html>"
  where first:rest = files
        n = length files
        f file = ",\"" ++ file ++ "\""

mkHtml :: Canvas -> String -> String -> Int -> Cmd ()
mkHtml canv dir dirPath n = do
       _ <- savePic ".png" canv $ mkFile dirPath n
       files <- getDirectoryContents dirPath
       html dirPath dir [dir ++ "/" ++ file |
                            file <- files, let lg = length file, lg > 4,
                            drop (lg-4) file
                                   `elem` words ".eps .gif .jpg .pdf .png .svg"]



mkSecs :: Integral a => a -> a -> a
mkSecs t1 t2 = (t2-t1)`div`1001500

installJavaScript :: IO ()
installJavaScript = do
    userDir <- userLibDir
    dataDir <- getDataDir
    let dest = userDir </> path
        src = dataDir </> path
    fileExists <- doesFileExist dest
    when (not fileExists) $ do
        mkDir $ userDir </> pix
        copyFile src dest
    where
        pix = "Pix"
        path = pix </> "Painter" <.> "js"
