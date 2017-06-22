module System.Expander where

import Paths (getDataDir)
import Gui

import Control.Monad (when, unless)
import System.Directory
    ( doesFileExist, createDirectoryIfMissing, copyFile
    , getDirectoryContents, removeDirectoryRecursive, doesDirectoryExist
    , getAppUserDataDirectory)
import System.FilePath ((<.>), (</>), hasExtension)
import System.IO.Error (catchIOError)
import Graphics.UI.Gtk (pixbufNewFromFile)

infixl 6 &=

-- | Program name.
prog, examplesFolder :: String
prog = "expander"
examplesFolder = "Examples"
pixFolder = "Pix"

-- | Program folder.
home :: IO FilePath
home = getAppUserDataDirectory prog

-- | Files from user folder.
-- Unix: $HOME/.expander
-- Windows: $APPDATA\\expander
expanderLib :: FilePath -> IO FilePath
expanderLib file = do
  lib <- home
  return $ lib </> file

-- | User library example files.
-- Unix: $HOME/.expander/Examples
-- Windows: $APPDATA\\expander\\Examples
userLib :: FilePath -> IO FilePath
userLib file = do
  lib <- expanderLib examplesFolder
  return $ lib </> file

-- | Builtin library/example files.
builtinLib :: FilePath -> IO FilePath
builtinLib file = do
    dataDir <- getDataDir
    return $ dataDir </> examplesFolder </> file

pixpath :: FilePath -> IO FilePath
pixpath file = do
    lib <- home
    return $ lib </> pixFolder </> file

mkFile :: FilePath -> Int -> FilePath
mkFile dir i | i < 10    = dir </> ('0':'0':show i)
             | i < 100   = dir </> ('0':show i)
             | otherwise = dir </> show i

renewDir :: FilePath -> IO ()
renewDir dir = do
  exists <- doesDirectoryExist dir
  when exists $ removeDirectoryRecursive dir
  createDirectoryIfMissing True dir

loadPhoto :: FilePath -> IO (Maybe Image)
loadPhoto file = do
    path <- userLib file'
    b <- doesFileExist path
    if b then do
        image <- pixbufNewFromFile path
        return $ Just $ Image image
    else do
            path <- builtinLib file'
            image <- pixbufNewFromFile $ path
            return $ Just $ Image image
        `catchIOError` \_ -> return Nothing
    where file' = if hasExtension file then file else file <.> "gif"


lookupLibs :: FilePath -> IO String
lookupLibs file = do
        path <- userLib file
        readFile path
    `catchIOError` \_ -> do
        path <- builtinLib file
        readFile path
    `catchIOError` \_ -> return ""



pix :: FilePath -> [String] -> [FilePath]
pix dir files = [dir </> file | file <- files, isPic file]
    where isPic file = lg > 4 && 
                       drop (lg-4) file `elem` words ".eps .gif .jpg .png .svg"
                       where lg = length file

(&=) :: String -> String -> String
x &= val = x ++ "=\"" ++ val ++ "\""

html :: String -> String -> [String] -> IO ()
html dirPath dir files
  | null files = writeFile (dirPath ++ ".html") $
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
  | otherwise  = return ()
  where first:rest = files
        n = length files
        f file = ",\"" ++ file ++ "\""

mkHtml :: Canvas -> String -> String -> Int -> IO ()
mkHtml screen dir dirPath n = do
  file <- canvasSave screen PNG $ mkFile dirPath n
  files <- getDirectoryContents dirPath
  html dirPath dir $ pix dir files

mkSecs :: Integral a => a -> a -> a
mkSecs t1 t2 = (t2-t1)`div`1001500

installJavaScript :: IO ()
installJavaScript = do
    userDir <- home
    dataDir <- getDataDir
    let dest = userDir </> path
        src = dataDir </> path
    fileExists <- doesFileExist dest
    unless fileExists $ do
        createDirectoryIfMissing True $ userDir </> pix
        copyFile src dest
    where
        pix = "Pix"
        path = pix </> "Painter" <.> "js"
