{-# LANGUAGE BangPatterns #-}
module Gui.Canvas where

import Paths (getDataDir)
import System.Expander
import Gui.Base

import Control.Monad (forM_, void, when)
import Control.Arrow ((***))
import Control.DeepSeq
import Data.Char (chr, toLower)
import Data.IORef
import Data.List (isPrefixOf, foldl1')
import Data.Maybe (isJust, isNothing, fromJust)
import Graphics.UI.Gtk
  hiding (Color, Action, Font, ArrowType, Arrow, Fill, ArrowClass, Image,get,set)
import qualified Graphics.UI.Gtk as Gtk (get,set)
import qualified Graphics.UI.Gtk as Gtk (Color(..))
import Graphics.Rendering.Cairo as Cairo
import Graphics.UI.Gtk.General.CssProvider
import Graphics.UI.Gtk.General.StyleContext
import Graphics.UI.Gtk.General.Enums (PathPriorityType(PathPrioApplication))
import System.Directory
import System.FilePath
import qualified Data.Text as Text
import qualified Codec.Picture as Picture


-- | Canvas GLib attributes.
canvasSize :: Attr Canvas Pos
canvasSize = newNamedAttr "size" canvasGetSize canvasSetSize

canvasBackground :: Attr Canvas Color
canvasBackground
    = newNamedAttr "background" canvasGetBackground canvasSetBackground

canvasCursor :: WriteAttr Canvas CursorType
canvasCursor = writeNamedAttr "cursor" canvasSetCursor
    
canvas :: Template Canvas
canvas = do
    surfaceRef <- newIORef undefined
    sizeRef <- newIORef (0, 0)
    backgroundRef <- newIORef $ RGB 0 0 0
    
    surface <- createImageSurface FormatRGB24 1 1
    writeIORef surfaceRef surface
    drawingArea <- drawingAreaNew
    drawingArea `on` draw $ do
        surface <- liftIO $ readIORef surfaceRef
        setSourceSurface surface 0 0
        paint
    
    return $ let
        calcVertexes :: Pos -> Pos -> ((Double, Double), (Double, Double))
        calcVertexes tip end = ((x1, y1), (x2, y2))
            where length = 7
                  degree = 0.5
                  (tipX, tipY) = fromInt2 tip
                  (endX, endY) = fromInt2 end
                  angle  = atan2 (tipY - endY) (tipX - endX) + pi
                  x1 = tipX + length * cos (angle - degree)
                  y1 = tipY + length * sin (angle - degree)
                  x2 = tipX + length * cos (angle + degree)
                  y2 = tipY + length * sin (angle + degree)
        
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
            where last2 (p1:[p2]) = (p1,p2)
                  last2 (_:ps)  = last2 ps
                  last2 []      = error "Gui.arrow.last2: List is empty."
                  (p2, p1) = last2 ps
        arrow (Just Both) ps@(_:_:_)
            = arrow (Just First) ps >> arrow (Just Last) ps
        arrow _ _ = return ()
        
        setLineOpt :: LineOpt -> Render ()
        setLineOpt (LineOpt col width _ cap joinStyle aa _) = do
            setColor col
            setLineWidth width
            setLineCap cap
            setLineJoin joinStyle
            setAntialias $ if aa then AntialiasDefault else AntialiasNone
        
        finishOval :: OvalOpt -> Render ()
        finishOval opt@OvalOpt{ ovalFill = c } = do
            save
            when (isJust c) $ do
                setColor $ fromJust c
                fillPreserve
            setColor $ ovalOutline opt
            setLineWidth $ ovalWidht opt
            stroke
            restore
        
        canvasOval' :: (Double, Double) -> (Double, Double) -> OvalOpt -> Action
        canvasOval' (x, y) (rx, ry) opt = do
            surface <- readIORef surfaceRef
            renderWith surface $ do
                save
                translate x y
                scale rx ry
                arc 0 0 1 0 (2 * pi)
                restore
                finishOval opt
            widgetQueueDraw drawingArea

        canvasArc' :: (Double, Double) -> Double
                   -> (Double, Double) -> ArcOpt -> Action
        canvasArc' (x, y) radius (angle1, angle2) opt@ArcOpt{ arcStyle = style
                                   , arcOutline = col
                                   , arcFill = c} = do
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
                when (isJust c && (style /= Perimeter)) $ do
                    setColor $ fromJust c
                    fillPreserve
                setColor col
                stroke
                restore
            widgetQueueDraw drawingArea
                  
        curve :: [(Double, Double)] -> Render ()
        curve ((x1,y1):(x2,y2):(x3,y3):ps) = do
            curveTo x1 y1 x2 y2 x3 y3
            curve ps
        curve ((x,y):_) = lineTo x y
        curve _ = return () 
        
        line' :: [Pos] -> LineOpt -> Action
        line' [] _ = return ()
        line' pss opt@LineOpt{ lineArrow = at
                , lineSmooth = isSmooth } = do
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
        
        canvasPolygon' :: [Pos] -> PolygonOpt -> Action
        canvasPolygon' [] _ = error "Gui.canvasPolygon: empty list."
        canvasPolygon' pss
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
                when (isJust c) $ do
                    setColor $ fromJust c
                    fillPreserve
                setColor $ polygonOutline opt
                stroke
                restore
            widgetQueueDraw drawingArea
        
        canvasRectangle' :: Pos -> Pos -> OvalOpt -> Action
        canvasRectangle' pos dim opt = do
            surface <- readIORef surfaceRef
            renderWith surface $ do
                save
                Cairo.rectangle x y width height
                restore
                finishOval opt
            widgetQueueDraw drawingArea
            where (x, y) = fromInt2 pos
                  (width, height) = fromInt2 dim
        
        canvasText' :: Pos -> TextOpt -> String -> Action
        canvasText' (x, y) (TextOpt font align anchor col) str = do
            surface <- readIORef surfaceRef
            renderWith surface $ do
                save
                setColor col
                layout <- createLayout str
                liftIO $ layoutSetFontDescription layout font
                liftIO $ layoutSetAlignment layout $ case align of
                    LeftAlign   -> AlignLeft
                    CenterAlign -> AlignCenter
                    RightAlign  -> AlignRight
                (PangoRectangle xBearing yBearing width height,_) <- liftIO
                                            $ layoutGetExtents layout
                let baseX = fromIntegral x - xBearing
                    baseY = fromIntegral y - yBearing
                    (x', y') = getAnchorPos baseX baseY width height anchor
                updateLayout layout
                moveTo x' y'
                showLayout layout
                restore
            widgetQueueDraw drawingArea
        
        getAnchorPos :: Double -> Double -> Double -> Double -> AnchorType
                     -> (Double, Double)
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
            in (x', y')
        
        canvasImage' :: Pos -> ImageOpt -> Image -> Action
        canvasImage' pos opt (Image image) = do
          surface <- readIORef surfaceRef
          width <- fromIntegral <$> pixbufGetWidth image
          height <- fromIntegral <$> pixbufGetHeight image
          let (x, y)   = fromInt2 pos
              (x', y') = getAnchorPos x y width height anchor
          renderWith surface $ do
              setSourcePixbuf image x' y'
              rotate $ imageRotate opt
              scale sclFactor sclFactor
              paint
          widgetQueueDraw drawingArea
          where
            anchor      = imageAnchor opt
            sclFactor   = imageScale opt
            
        
        clear' = do
            surface <- readIORef surfaceRef
            background <- readIORef backgroundRef
            
            renderWith surface $ do
                setColor background
                paint

        canvasSave' file = do
          createDirectoryIfMissing True $ takeDirectory file
          let ext = takeExtension file
              format = dups $ map toLower $ if null ext then ext else tail ext
              formattext = Text.pack format
          surface <- readIORef surfaceRef
          width <- imageSurfaceGetWidth surface
          height <- imageSurfaceGetHeight surface
          -- workaround for gif
          if format == "gif"
            then do
              tmpfile <-  userLib (takeFileName file -<.> "png")
              let tmpfile = file -<.> "png"
              canvasSave' tmpfile
              eitherimg <- Picture.readImage tmpfile
              either (const $ putStrLn "gif failed") id $ do
                img <- eitherimg
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
                    _ -> error $ "Gui.Canvas.canvasSave: Voxel format "
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
            
        
        canvasSetSize' size@(width, height) = do
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
                
        canvasSetBackground' = writeIORef backgroundRef
        
        fromInt2 :: (Int, Int) -> (Double, Double)
        fromInt2 = fromIntegral *** fromIntegral
        
        setColor :: Color -> Render ()
        setColor (RGB r g b)
            = setSourceRGB
                (fromIntegral r / 255)
                (fromIntegral g / 255)
                (fromIntegral b / 255)
        
        getTextWidth' font str = do
            surface <- readIORef surfaceRef
            
            widthRef <- newIORef undefined
            renderWith surface $ do
                layout <- createLayout str
                liftIO $ layoutSetFontDescription layout $ Just font
                (PangoRectangle _ _ width _, _) <- liftIO
                                $ layoutGetExtents layout
                liftIO $ writeIORef widthRef width
            readIORef widthRef
        
        getTextHeight' font = do
            surface <- readIORef surfaceRef
            
            textHeight <- newIORef undefined
            renderWith surface $ do
                layout <- createLayout "BASE"
                liftIO $ layoutSetFontDescription layout $ Just font
                (PangoRectangle _ _ _ height, _) <- liftIO
                                $ layoutGetExtents layout
                
                liftIO
                    $ writeIORef textHeight (round (height/2), round (height/2))
            readIORef textHeight
        
        canvasSetCursor' :: CursorType -> Action
        canvasSetCursor' ct = do
            cursor <- cursorNew ct
            root <- widgetGetRootWindow drawingArea
            drawWindowSetCursor root $ Just cursor
            
        
      in Canvas
        { canvasOval          = canvasOval'
        , canvasArc           = canvasArc'
        , line                = line'
        , canvasPolygon       = canvasPolygon'
        , canvasRectangle     = canvasRectangle'
        , canvasText          = canvasText'
        , canvasImage         = canvasImage'
        , clear               = clear'
        , canvasSave          = canvasSave'
        , canvasSetSize       = canvasSetSize'
        , canvasGetSize       = readIORef sizeRef
        , canvasSetBackground = canvasSetBackground'
        , canvasGetBackground = readIORef backgroundRef
        , getDrawingArea      = drawingArea
        , getSurface          = readIORef surfaceRef
        , getTextWidth        = getTextWidth'
        , getTextHeight       = getTextHeight'
        , canvasSetCursor     = canvasSetCursor'
        }
