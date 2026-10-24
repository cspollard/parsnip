{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- SVG elements as XML
--
-- Smart constructors for the SVG vocabulary, built on the total
-- constructors of `Data.XML.Sanitize`: the tag and attribute names here
-- are valid, and runtime values are repaired if they are not legal XML.
------------------------------------------------------------------------

module Data.SVG where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Data.XML.AST using (XMLM)
open import Data.XML.Sanitize using (element)

private variable
  A : Set

Attrs : Set
Attrs = List (String × String)

svg : Attrs → List (XMLM A) → XMLM A
svg attrs children = element "svg" (("xmlns" , "http://www.w3.org/2000/svg") ∷ attrs) children

g : Attrs → List (XMLM A) → XMLM A
g attrs children = element "g" attrs children

path : (d : String) → Attrs → XMLM A
path d attrs = element "path" (("d" , d) ∷ attrs) []

circle : (cx cy r : String) → Attrs → XMLM A
circle cx cy r attrs = element "circle" (("cx" , cx) ∷ ("cy" , cy) ∷ ("r" , r) ∷ attrs) []

rect : (x y width height : String) → Attrs → XMLM A
rect x y w h attrs = element "rect" (("x" , x) ∷ ("y" , y) ∷ ("width" , w) ∷ ("height" , h) ∷ attrs) []

polygon : (points : String) → Attrs → XMLM A
polygon pts attrs = element "polygon" (("points" , pts) ∷ attrs) []

polyline : (points : String) → Attrs → XMLM A
polyline pts attrs = element "polyline" (("points" , pts) ∷ attrs) []
