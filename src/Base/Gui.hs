{-# LANGUAGE BangPatterns #-}
module Base.Gui
  ( module Base.OHaskell
  , module Graphics.UI.Gtk
  , module Graphics.UI.Gtk.Gdk.PixbufAnimation
  , module System.Glib.GDateTime
  , Text.unpack
  , iconPixbuf
  , ImageFileType(..)
  , Canvas(..)
  , canvasSize
  , canvasBackground
  , canvasCursor
  , canvas
  , loadCSS
  , loadGlade
  , setBackground
  , addContextClass
  , Color(..)
  , black
  , white
  , red
  , green
  , blue
  , yellow
  , grey
  , magenta
  , cyan
  , orange
  , brown
  , darkGreen
  , GtkColor
  , gtkColor
  , toGtkColor
  , gtkGet
  , gtkSet
  , None(..)
  , AnchorType(..)
  , ReliefType(..)
  , VertSide(..)
  , WrapType(..)
  , SelectType(..)
  , Align(..)
  , Round(..)
  , ArcStyleType(..)
  , CapStyleType(..)
  , JoinStyleType(..)
  , ArrowType(..)
  , Rotation(..)
  , Anchor(..)
  , ArcStyle(..)
  , Arrow(..)
  , Background(..)
  , CapStyle(..)
  , Fill(..)
  , Image(..)
  , JoinStyle(..)
  , Justify(..)
  , Outline(..)
  , Smooth(..)
  , Width(..)
  , TextOpt(..)
  , textOpt
  , LineOpt(..)
  , lineOpt
  , PolygonOpt(..)
  , polygonOpt
  , ArcOpt(..)
  , arcOpt
  , OvalOpt(..)
  , ovalOpt
  , ImageOpt(..)
  , imageOpt
  , Pos
  , gtkDelay
  , Runnable(..)
  , periodic
  , MenuOpt(..)
  , menuOpt
  , cascade
  , smooth'
  ) where

import Prelude ()
import Base.OHaskell
import qualified Base.Haskell as Haskell
import qualified Codec.Picture as Picture
import Control.DeepSeq
import qualified Data.Text as Text
import Graphics.Rendering.Cairo as Cairo hiding (x,y,width,height,Path)
import Graphics.UI.Gtk hiding (Color,Action,Font,ArrowType,Arrow,Fill,Table,
                               ArrowClass,Image,Star,Circle,Point,Dot,get,set)
import qualified Graphics.UI.Gtk as Gtk (get,set,Color(..))
import Graphics.UI.Gtk.Gdk.PixbufAnimation
import Graphics.UI.Gtk.General.CssProvider
import Graphics.UI.Gtk.General.Enums (PathPriorityType(PathPrioApplication))
import Graphics.UI.Gtk.General.StyleContext
import System.Directory
import System.FilePath
import System.Glib.GDateTime

-- main window icon file

iconFile, cssFile :: FilePath
iconFile = "icon" <.> "png"
cssFile  = "style" <.> "css"

stylePath :: IO FilePath
stylePath = do
    dataDir <- getDataDir
    return $ dataDir </> "style"

-- Graphics.UI.Gtk.Gdk.Pixbuf.Pixbuf for main window icon file

iconPixbuf :: IO Pixbuf
iconPixbuf = do
    sty <- stylePath
    pixbufNewFromFile $ sty </> iconFile

pixbufRemoveAlpha :: Color -> Pixbuf -> IO ()
pixbufRemoveAlpha (RGB r g b) pixbuf = do
    hasAlpha <- pixbufGetHasAlpha pixbuf
    bitsPerSample <- pixbufGetBitsPerSample pixbuf
    nChannels <- pixbufGetNChannels pixbuf
    when (hasAlpha && bitsPerSample == 8 && nChannels == 4) $ do
        pixels <- pixbufGetPixels pixbuf :: IO (PixbufData Int Haskell.Word8)
        (start',end') <- Haskell.getBounds pixels
        let start = start' + nChannels - 1
            end = end' - 1
        mapM_ (setByteMax pixels) [start,start+nChannels .. end]
    return ()
    where
        setByteMax arr i = do
          alpha <- Haskell.readArray arr i
          when (alpha == 0) $ do
            Haskell.writeArray arr (i-3) (fromIntegral r)
            Haskell.writeArray arr (i-2) (fromIntegral g)
            Haskell.writeArray arr (i-1) (fromIntegral b)
            Haskell.writeArray arr i maxBound
            
type Pos   = (Int,Int)
type Point = (Double,Double)
type Path  = [Point]

data ImageFileType = PNG | PDF | PS | SVG deriving (Read,Show,Enum,Eq)

data Canvas = Canvas
    { canvasOval           :: Point -> Point
                           -> OvalOpt -> Action
    , canvasArc            :: Point -> Double -> Point -> ArcOpt -> Action
    , canvasRectangle      :: Pos -> Pos -> OvalOpt -> Action
    , line                 :: [Pos] -> LineOpt -> Action
    , canvasPolygon        :: [Pos] -> PolygonOpt -> Action
    , canvasText           :: Pos -> TextOpt -> String -> Action
    , canvasImage          :: Pos -> ImageOpt -> Image -> Action
  --, cwindow              :: Pos -> [CWindowOpt] -> Request CWindow
    , clear                :: Action
    , canvasSave           :: FilePath -> Request FilePath
    , canvasSetSize        :: Pos -> Action
    , canvasGetSize        :: Request Pos
    , canvasSetBackground  :: Color -> Action
    , canvasGetBackground  :: Request Color
    , getDrawingArea       :: DrawingArea
    , getSurface           :: Request Surface
    , getTextWidth         :: FontDescription -> String -> Request Double
    , getTextHeight        :: FontDescription -> Request Pos
    , canvasSetCursor      :: CursorType -> Action
    }

-- Canvas GLib attributes

canvasSize :: Attr Canvas Pos
canvasSize = newNamedAttr "size" canvasGetSize canvasSetSize

canvasBackground :: Attr Canvas Color
canvasBackground = newNamedAttr "background" canvasGetBackground 
                                             canvasSetBackground

canvasCursor :: WriteAttr Canvas CursorType
canvasCursor = writeNamedAttr "cursor" canvasSetCursor

-- SMOOTHING

-- interpolate' computes multiple auxiliary positions for beziere curves from a
-- straight line path.

smooth',interpolate',spline' :: Path -> Path
smooth' ps = interpolate' $!! clean $!! spline' ps
             where clean (p':ps') = p' : dropWhile (==p') ps'
                   clean [] = []
interpolate' pss@(p1:p2:_:_) = p1:q1:interpolate0 pss
    where scl = 0.35 -- scaling factor
          !closed = p1 == last pss
          p0 = last $!! init pss
          mag (x,y) = let !r1 = (x ** 2)
                          !r2 = (y ** 2)
                      in sqrt $! (r1 + r2)
          skalar s (x,y) = let !r1 = s*x
                               !r2 = s*y
                           in (r1, r2)
          norm v = skalar (1 / mag v) v
          calc op (x1,y1) (x2,y2) = let !r1 = x1 `op` x2
                                        !r2 = y1 `op` y2
                                    in (r1, r2)
          csub = calc (-)
          cadd = calc (+)
          -- mul = calc (*)
          tangent = if closed then norm $!! csub p2 p0 else csub p2 p1
          q1 = if closed
               then cadd p1 $ skalar (scl * mag (csub p2 p1)) tangent
               else cadd p1 $ skalar scl tangent
          interpolate0 (p0':p1':p2':ps') = q0':p1':q1':interpolate0(p1':p2':ps')
            where tangent' = norm $!! csub p2' p0'
                  q0' = csub p1' $!! skalar (scl * mag (csub p1' p0')) tangent'
                  q1' = cadd p1' $!! skalar (scl * mag (csub p2' p1')) tangent'
          interpolate0 [p0', p1'] = [q0', p1'] where
             tangent' = if closed then norm $!! csub p2 p0' else csub p1' p0'
             q0' = if closed then csub p1' $!! 
                                      skalar (scl * mag (csub p1' p0')) tangent'
                             else csub p1' $ skalar scl tangent'
          interpolate0 _ = error $ "Gui.interpolate: interpolate' should never "
                                   ++ "be called with list of length < 2."
interpolate' pss = pss                         
spline' ps@(p:_:_:_) = if p == last ps then spline0' True $!! init ps
                                       else spline0' False ps
spline' ps           = ps

spline0' :: Bool -> Path -> Path
spline0' isClosed ps = first:map f [1..resolution] ++ map g [1..9] ++
                       [if isClosed then first else ps!!(n-1)]
        where add2 (x,y) (a,b) = let !r1 = a+x
                                     !r2 = b+y
                                 in (r1,r2)
              apply2 fun (x,y) = let !r1 = fun x
                                     !r2 = fun y
                                 in (r1,r2)
              first = f 0; !n = length ps; !resolution = n*6
              f, g :: Int -> Point
              f i = point $!! upb*fromIntegral i/fromIntegral resolution 
              g i = point $!! upb+fromIntegral i/10
              !n' = fromIntegral n
              upb = n'-if isClosed then 1 else 3
              point v = Haskell.foldl1' add2 $!! map helper [0..n-1]
                        where helper i = apply2 (*z) $ ps!!i
                                      where z | isClosed && v < u i
                                                      = blend2 u i $!! v-u 0+u n
                                              | isClosed     = blend2 u i v
                                              | True         = blend2 sub2 i v 
              sub2 i = if i < 3 then 0 else fromIntegral (min i n)-2
              u i = if i <= n then fromIntegral i else u (i-1)+u (i-n)-u (i-n-1)
              h 0 _ = 0
              h _ s = s
              blend2 t i v = h denom1 sum1+h denom2 sum2
                             where ti = t i; ti3 = t $!! i+3
                                   denom1 = t (i+2)-ti;  num1 = v-ti
                                   denom2 = ti3-t (i+1); num2 = ti3-v
                                   sum1 = num1/denom1*blend1 t i v
                                   sum2 = num2/denom2*blend1 t (i+1) v
              blend1 t i v = h denom1 sum1+h denom2 sum2
                             where ti = t i; ti1 = t $ i+1; ti2 = t $ i+2
                                   denom1 = ti1-ti;  num1 = v-ti 
                                   denom2 = ti2-ti1; num2 = ti2-v
                                   sum1 = if b i then num1/denom1 else 0
                                   sum2 = if b $ i+1 then num2/denom2 else 0
                                   b i' = t i' <= v && v < t (i'+1)
    
canvas :: Template Canvas
canvas = do
    surfaceRef <- newIORef undefined
    sizeRef <- newIORef (0, 0)
    backgroundRef <- newIORef $ RGB 0 0 0
    
    surface0 <- createImageSurface FormatRGB24 1 1
    writeIORef surfaceRef surface0
    drawingArea <- drawingAreaNew
    _ <- drawingArea `on` draw $ do
        surface <- liftIO $ readIORef surfaceRef
        setSourceSurface surface 0 0
        paint
    
    return $ let
        calcVertexes :: Pos -> Pos -> (Point,Point)
        calcVertexes tip end = ((x1, y1), (x2, y2))
            where len = 7
                  degree = 0.5
                  (tipX, tipY) = fromInt2 tip
                  (endX, endY) = fromInt2 end
                  angle  = atan2 (tipY - endY) (tipX - endX) + pi
                  x1 = tipX + len * cos (angle - degree)
                  y1 = tipY + len * sin (angle - degree)
                  x2 = tipX + len * cos (angle + degree)
                  y2 = tipY + len * sin (angle + degree)
        
        arrowTriangle :: Pos -> Pos -> Render ()
        arrowTriangle tip@(tipX, tipY) end = do
            let (x1, y1) = (fromIntegral tipX, fromIntegral tipY)
                ((x2, y2), (x3, y3)) = calcVertexes tip end
            moveTo x1 y1
            lineTo x2 y2
            lineTo x3 y3
            closePath
            Cairo.fill
        
        arrow :: Maybe ArrowType -> [Pos] -> Render ()
        arrow (Just First) (p1:p2:_) = arrowTriangle p1 p2
        arrow (Just Last) ps@(_:_:_) = arrowTriangle p1 p2
            where last2 (p1':[p2']) = (p1',p2')
                  last2 (_:ps')  = last2 ps'
                  last2 []      = error "Gui.arrow.last2: List is empty."
                  (p2, p1) = last2 ps
        arrow (Just Both) ps@(_:_:_)
            = arrow (Just First) ps >> arrow (Just Last) ps
        arrow _ _ = return ()
        
        setLineOpt :: LineOpt -> Render ()
        setLineOpt (LineOpt col wdth _ cap joinStyle aa _) = do
            setColor col
            setLineWidth wdth
            setLineCap cap
            setLineJoin joinStyle
            setAntialias $ if aa then AntialiasDefault else AntialiasNone
        
        finishOval :: OvalOpt -> Render ()
        finishOval opt@OvalOpt{ ovalFill = c } = do
            save
            when (Haskell.isJust c) $ do
                setColor $ Haskell.fromJust c
                fillPreserve
            setColor $ ovalOutline opt
            setLineWidth $ ovalWidht opt
            stroke
            restore
        
        canvasOval :: Point -> Point -> OvalOpt -> Action
        canvasOval (x,y) (rx,ry) opt = do
            surface <- readIORef surfaceRef
            renderWith surface $ do
                save
                translate x y
                scale rx ry
                arc 0 0 1 0 (2 * pi)
                restore
                finishOval opt
            widgetQueueDraw drawingArea

        canvasArc :: Point -> Double -> Point -> ArcOpt -> Action
        canvasArc (x,y) radius (angle1,angle2) 
                        opt@ArcOpt {arcStyle = style,
                                    arcOutline = col,
                                    arcFill = c} = do
            surface <- readIORef surfaceRef
            renderWith surface $ do
                save
                setLineWidth $ arcWidth opt
                -- draw arc
                arc x y radius angle1 angle2
                -- draw chord
                when (style == Chord) closePath
                -- draw slice
                when (style == Pie) $ do
                    lineTo x y
                    closePath
                when (Haskell.isJust c && (style /= Perimeter)) $ do
                    setColor $ Haskell.fromJust c
                    fillPreserve
                setColor col
                stroke
                restore
            widgetQueueDraw drawingArea
                  
        curve :: Path -> Render ()
        curve ((x1,y1):(x2,y2):(x3,y3):ps) = do
            curveTo x1 y1 x2 y2 x3 y3
            curve ps
        curve ((x,y):_) = lineTo x y
        curve _ = return () 
        
        line :: [Pos] -> LineOpt -> Action
        line [] _ = return ()
        line pss opt@LineOpt {lineArrow = at, lineSmooth = isSmooth} = do
            surface <- readIORef surfaceRef
            let dpss = map fromInt2 pss
                ((x, y):ps) = if isSmooth then smooth' dpss else dpss
            renderWith surface $ do
                save
                setLineOpt opt
                moveTo x y
                if isSmooth then curve ps
                else mapM_ (uncurry lineTo) ps
                stroke
                arrow at pss
                restore
            widgetQueueDraw drawingArea
        
        canvasPolygon :: [Pos] -> PolygonOpt -> Action
        canvasPolygon [] _ = error "Gui.canvasPolygon: empty list."
        canvasPolygon pss
                opt@PolygonOpt{ polygonFill = c, polygonAntialias = aa
                              , polygonSmooth = isSmooth } = do
            surface <- readIORef surfaceRef
            let dpss = map fromInt2 pss
                ((x, y):ps) = if isSmooth then smooth' dpss else dpss
            renderWith surface $ do
                save
                setAntialias $ if aa then AntialiasDefault else AntialiasNone
                setLineWidth $ polygonWidth opt
                moveTo x y
                if isSmooth then curve ps
                else mapM_ (uncurry lineTo) ps
                closePath
                when (Haskell.isJust c) $ do
                    setColor $ Haskell.fromJust c
                    fillPreserve
                setColor $ polygonOutline opt
                stroke
                restore
            widgetQueueDraw drawingArea
        
        canvasRectangle :: Pos -> Pos -> OvalOpt -> Action
        canvasRectangle pos dim opt = do
            surface <- readIORef surfaceRef
            renderWith surface $ do
                save
                Cairo.rectangle x y width height
                restore
                finishOval opt
            widgetQueueDraw drawingArea
            where (x, y) = fromInt2 pos
                  (width, height) = fromInt2 dim
        
        canvasText :: Pos -> TextOpt -> String -> Action
        canvasText (x,y) (TextOpt fnt align anchor col) str = do
            surface <- readIORef surfaceRef
            renderWith surface $ do
                save
                setColor col
                layout <- createLayout str
                liftIO $ layoutSetFontDescription layout fnt
                liftIO $ layoutSetAlignment layout 
                       $ case align of LeftAlign   -> AlignLeft
                                       CenterAlign -> AlignCenter
                                       RightAlign  -> AlignRight
                (PangoRectangle xBearing yBearing width height,_) 
                                             <- liftIO $ layoutGetExtents layout
                let baseX = fromIntegral x - xBearing
                    baseY = fromIntegral y -- - yBearing
                    (x',y') = getAnchorPos baseX baseY width height anchor
                updateLayout layout
                moveTo x' $ baseY-8
                showLayout layout
                restore
            widgetQueueDraw drawingArea
        
        getAnchorPos :: Double -> Double -> Double -> Double -> AnchorType
                                                             -> Point
        getAnchorPos x y width height anchor =
            let x' = case anchor of
                        NW -> x
                        N -> x - (width / 2)
                        NE -> x - width
                        W -> x
                        C -> x - (width / 2)
                        E -> x - width
                        SW -> x
                        S -> x - (width / 2)
                        SE -> x - width
                y' = case anchor of
                        NW -> y
                        N -> y
                        NE -> y
                        W -> y - (height / 2)
                        C -> y - (height / 2)
                        E -> y - (height / 2)
                        SW -> y - height
                        S -> y - height
                        SE -> y - height
            in (x',y')
        
        canvasImage :: Pos -> ImageOpt -> Image -> Action
        canvasImage pos opt (Image alpha image) = do
          when (not alpha) $ do rgb <- readIORef backgroundRef
                                pixbufRemoveAlpha rgb image
          surface <- readIORef surfaceRef
          width <- fromIntegral <$> pixbufGetWidth image
          height <- fromIntegral <$> pixbufGetHeight image
          let (x,y)   = fromInt2 pos
              (x',y') = getAnchorPos x y width height anchor
          renderWith surface $ do setSourcePixbuf image x' y'
                                  rotate $ imageRotate opt
                                  scale sclFactor sclFactor
                                  paint
          widgetQueueDraw drawingArea
          where anchor      = imageAnchor opt
                sclFactor   = imageScale opt
        
        clear = do
            surface <- readIORef surfaceRef
            background <- readIORef backgroundRef
            renderWith surface $ do setColor background
                                    paint

        canvasSave file = do
          createDirectoryIfMissing True $ takeDirectory file
          let ext = takeExtension file
              format = dups $ map toLower $ if null ext then ext else tail ext
              formattext = Text.pack format
          surface <- readIORef surfaceRef
          width <- imageSurfaceGetWidth surface
          height <- imageSurfaceGetHeight surface
          -- workaround for gif
          if format == "gif"
            then do let tmpfile = file -<.> "png"
                    _ <- canvasSave tmpfile
                    eitherimg <- Picture.readImage tmpfile
                    either (const $ putStrLn "gif failed") id $ 
                           do img <- eitherimg
                              Picture.saveGifImage file img
                    exist <- doesFileExist tmpfile
                    when exist $ removeFile tmpfile        
          -- vector
          else if format `elem` ["ps", "pdf", "svg"]
            then do
              let withSurface = case format of
                    "pdf" -> withPDFSurface
                    "ps"  -> withPSSurface
                    "svg" -> withSVGSurface
                    _ -> error $ "Gui.Canvas.canvasSave: Vector format "
                            ++ format ++ " should never happen."
              withSurface file (fromIntegral width) (fromIntegral height)
                $ \image -> renderWith image $ do
                  setSourceSurface surface 0 0
                  paint
          -- pixel
          else if formattext `elem` pixbufGetFormats
            then do
              pbuf <- pixbufNewFromSurface surface 0 0 width height
              pixbufSave pbuf file formattext ([] :: [(String,String)])
            else putStrLn "format not supported"
          return file
          where
            dups "jpg" = "jpeg"
            dups "eps" = "ps"
            dups name  = name
            
        
        canvasSetSize size@(width, height) = do
            writeIORef sizeRef size
            background <- readIORef backgroundRef
            surface <- createImageSurface FormatRGB24 width height
            drawingArea `Gtk.set` [ widgetWidthRequest  := width
                              , widgetHeightRequest := height
                              ]
            renderWith surface $ do
                setColor background
                paint
            writeIORef surfaceRef surface
        
        fromInt2 :: (Int,Int) -> Point
        fromInt2 = fromIntegral Haskell.*** fromIntegral
        
        setColor :: Color -> Render ()
        setColor (RGB r g b)
            = setSourceRGB
                (fromIntegral r / 255)
                (fromIntegral g / 255)
                (fromIntegral b / 255)
        
        getTextWidth font str = do
            surface <- readIORef surfaceRef
            textWidth <- newIORef undefined
            renderWith surface $ do
             layout <- createLayout str
             liftIO $ layoutSetFontDescription layout $ Just font
             (PangoRectangle _ _ width _, _) <- liftIO $ layoutGetExtents layout
             liftIO $ writeIORef textWidth width
            readIORef textWidth
        
        getTextHeight font = do
            surface <- readIORef surfaceRef
            textHeight <- newIORef undefined
            renderWith surface $ do
                 layout <- createLayout "BASE"
                 liftIO $ layoutSetFontDescription layout $ Just font
                 (PangoRectangle _ _ _ ht,_) <- liftIO $ layoutGetExtents layout
                 liftIO $ writeIORef textHeight (floor $ ht/2,floor $ (ht+ht)/3)
            readIORef textHeight
        
        canvasSetCursor :: CursorType -> Action
        canvasSetCursor ct = do
            cursor <- cursorNew ct
            root <- widgetGetRootWindow drawingArea
            drawWindowSetCursor root $ Just cursor
        
      in Canvas {canvasOval          = canvasOval,
                 canvasArc           = canvasArc,
                 line                = line,
                 canvasPolygon       = canvasPolygon,
                 canvasRectangle     = canvasRectangle,
                 canvasText          = canvasText,
                 canvasImage         = canvasImage,
                 clear               = clear,
                 canvasSave          = canvasSave,
                 canvasSetSize       = canvasSetSize,
                 canvasGetSize       = readIORef sizeRef,
                 canvasSetBackground = writeIORef backgroundRef,
                 canvasGetBackground = readIORef backgroundRef,
                 getDrawingArea      = drawingArea,
                 getSurface          = readIORef surfaceRef,
                 getTextWidth        = getTextWidth,
                 getTextHeight       = getTextHeight,
                 canvasSetCursor     = canvasSetCursor}

-- CSS
loadCSS :: IO ()
loadCSS = do
    provider <- cssProviderNew
    Just display <- displayGetDefault
    screen <- displayGetDefaultScreen display
    styleContextAddProviderForScreen screen provider
        (fromEnum PathPrioApplication)
    path <- stylePath
    cssProviderLoadFromPath provider (path </> cssFile)

-- glade
loadGlade :: String -> IO Builder
loadGlade glade = do
    builder <- builderNew
    path <- stylePath
    let file = path </> glade <.> "glade"
    builderAddFromFile builder file
    return builder

-- sets background of a GTK+ widget
setBackground :: WidgetClass widget => widget -> Background -> Action
setBackground w (Background name) = do
    sc <- widgetGetStyleContext w
    classes <- styleContextListClasses sc :: IO [String]
    let f cl = when ("bg_" `Haskell.isPrefixOf` cl) $ 
                    styleContextRemoveClass sc cl
    Haskell.forM_ classes f
    styleContextAddClass sc name

-- adds a CSS class to a GTK+ widget
addContextClass :: WidgetClass widget => widget -> String -> Action
addContextClass widget cl = do
    context <- widgetGetStyleContext widget
    styleContextAddClass context cl
    
-- Colors

data Color = RGB Int Int Int deriving (Read,Eq)

black,white,red,green,blue,yellow,grey,magenta,cyan,orange,brown,darkGreen 
         :: Color
black     = RGB 0 0 0
white     = RGB 255 255 255
red       = RGB 255 0 0
green     = RGB 0 255 0
blue      = RGB 0 0 255
yellow    = RGB 255 255 0
grey      = RGB 200 200 200
magenta   = RGB 255 0 255
cyan      = RGB 0 255 255
orange    = RGB 255 180 0
brown     = RGB 0 160 255
darkGreen = RGB 0 150 0

type GtkColor = Gtk.Color

gtkColor :: Haskell.Word16 -> Haskell.Word16 -> Haskell.Word16 -> GtkColor
gtkColor = Gtk.Color

toGtkColor :: Color -> GtkColor
toGtkColor (RGB r g b)
    = Gtk.Color (fromIntegral r) (fromIntegral g) (fromIntegral b)

gtkGet :: o -> ReadWriteAttr o a b -> IO a
gtkGet = Gtk.get

gtkSet :: o -> [AttrOp o] -> IO ()
gtkSet = Gtk.set

-- Auxiliary types for options

data None             = None
data AnchorType       = NW | N | NE | W | C | E | SW | S | SE 
data ReliefType       = Raised | Sunken | Flat | Ridge | Solid | Groove
data VertSide         = Top | Bottom 
data WrapType         = NoWrap | CharWrap | WordWrap
data SelectType       = Single | Multiple
data Align            = LeftAlign | CenterAlign | RightAlign
data Round            = Round
data ArcStyleType     = Pie | Chord | Perimeter deriving (Read,Eq)
data CapStyleType     = Butt | Proj 
data JoinStyleType    = Bevel | Miter 
data ArrowType        = First | Last | Both deriving (Show, Eq, Enum)
data Rotation         = Counterclockwise | RotateUpsidedown | RotateClockwise
                        deriving (Show, Eq, Enum)

-- Options

data Anchor       = Anchor AnchorType
data ArcStyle     = ArcStyle ArcStyleType
data Arrow a      = Arrow a
data Background   = Background String
data CapStyle a   = CapStyle a
data Fill         = Fill Color
data Image        = Image Bool Pixbuf
data JoinStyle a  = JoinStyle a
data Justify      = Justify Align
data Outline      = Outline Color
data Smooth       = Smooth Bool
data Width        = Width Double

data TextOpt = TextOpt
    { textFont :: Maybe FontDescription
    , textJustify :: Align
    , textAnchor :: AnchorType
    , textFill :: Color
    }

textOpt :: TextOpt
textOpt = TextOpt
    Nothing
    LeftAlign
    C
    black

data LineOpt = LineOpt
    { lineFill :: Color
    , lineWidth :: Double
    , lineArrow :: Maybe ArrowType
    , lineCapStyle :: LineCap
    , lineJoinStyle :: LineJoin
    , lineAntialias :: Bool
    , lineSmooth    :: Bool
    } deriving (Show, Eq)

lineOpt :: LineOpt
lineOpt = LineOpt black 1 Nothing LineCapButt LineJoinMiter True False

data PolygonOpt = PolygonOpt
    { polygonAntialias :: Bool
    , polygonOutline   :: Color
    , polygonFill      :: Maybe Color
    , polygonWidth     :: Double
    , polygonSmooth    :: Bool
    }
polygonOpt :: PolygonOpt
polygonOpt = PolygonOpt True black Nothing 1 False

data ArcOpt = ArcOpt
    { arcFill    :: Maybe Color
    , arcWidth   :: Double
    , arcOutline :: Color
    , arcStyle   :: ArcStyleType
    }

arcOpt :: ArcOpt
arcOpt = ArcOpt Nothing 1 black Pie

data OvalOpt = OvalOpt
    { ovalFill    :: Maybe Color
    , ovalWidht   :: Double
    , ovalOutline :: Color
    }

ovalOpt :: OvalOpt
ovalOpt = OvalOpt Nothing 1 black

data ImageOpt = ImageOpt
  { imageRotate :: Double
  , imageScale  :: Double
  , imageAnchor :: AnchorType
  }

imageOpt :: ImageOpt
imageOpt = ImageOpt 0.0 1.0 C

-- imageGetSize :: Image -> IO Pos
-- imageGetSize (Image _ buf)
--   = (,) <$> (pixbufGetWidth buf) <*> (pixbufGetHeight buf)

-- data MenuOpt        > WindowOpt, Enabled
-- data MButtonOpt     > StdOpt, FontOpt, PadOpt, Img, Btmp, Underline, 

-- Unparser

instance Show ArcStyleType where show Pie       = "pieslice"
                                 show Chord     = "chord"
                                 show Perimeter = "arc"


instance Show Color where 
   showsPrec _ (RGB r g b) rest = "#" ++ concatMap (hex 2 "") [r,g,b] ++ rest
                    where hex :: Int -> [Char] -> Int -> [Char]
                          hex 0 rs _ = rs
                          hex t rs 0 = hex (t-1) ('0':rs) 0
                          hex t rs i = hex (t-1)(chr (48+m+7*div m 10):rs) d
                                       where m = mod i 16; d = div i 16

-- TODO What is the String for?

gtkDelay :: Int -> Action -> Action
gtkDelay millisecs act = Haskell.void $ timeoutAdd (act>>return False) millisecs

data Runnable = Runnable {runnableStart :: Action, runnableStop :: Action}
    
-- periodic uses Graphics.UI.Gtk.General.General.timoutAdd from thegtk3 package 
-- to synchronize with GTK3 main loop
-- Tcl/Tk version does something similar

periodic :: Int -> Cmd () -> Request Runnable
periodic millisecs act = do
    handlerID <- newIORef Nothing -- Nothing == not running
    
    return Runnable
        { runnableStart = do
            maybeID <- readIORef handlerID
            when (Haskell.isNothing maybeID) $ do -- if not running
                hID <- timeoutAdd (act >> return True) millisecs
                writeIORef handlerID $ Just hID
        , runnableStop  = do
            maybeID <- readIORef handlerID
            when (Haskell.isJust maybeID) $ do -- if running
                timeoutRemove $Haskell.fromJust maybeID
                writeIORef handlerID Nothing
        }

data MenuOpt = MenuOpt {menuFont :: Maybe String,
                        menuBackground :: Maybe Background}
                        
menuOpt :: MenuOpt
menuOpt = MenuOpt {menuFont = Nothing, menuBackground = Nothing}

-- Tk.Menu.cascade

cascade :: Menu -> String -> MenuOpt -> Request Menu
cascade menu label MenuOpt{ menuFont = mFont, menuBackground = bg } = do
  item <- menuItemNewWithLabel label
  menuShellAppend menu item
  doMaybe (addContextClass item) mFont
  doMaybe (setBackground item) bg
  subMenu <- menuNew
  item `Gtk.set` [ menuItemSubmenu := subMenu, widgetVisible := True ]
  return subMenu
  where
    doMaybe act (Just v) = act v
    doMaybe _ Nothing    = return ()
