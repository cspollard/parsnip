{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- A small HTML vocabulary over `Data.HTML.Sanitize`
--
-- Each constructor takes attributes and content and returns an `Item`,
-- so that elements nest; `html` makes the root.  The right kind of
-- element (void, raw-text, or with content) is chosen from the tag.
------------------------------------------------------------------------

module Data.HTML.Elements where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_)
open import Data.String using (String)

open import Data.HTML.AST using (Elem)
open import Data.HTML.Sanitize using (Item; txt; el; element; text)

Attrs : Set
Attrs = List (String × String)

tag : String → Attrs → List Item → Item
tag n as is = el (element n as is)

html : Attrs → List Item → Elem
html = element "html"

head body title : Attrs → List Item → Item
head  = tag "head"
body  = tag "body"
title = tag "title"

div p span a ul ol li h1 h2 h3 pre : Attrs → List Item → Item
div  = tag "div"
p    = tag "p"
span = tag "span"
a    = tag "a"
ul   = tag "ul"
ol   = tag "ol"
li   = tag "li"
h1   = tag "h1"
h2   = tag "h2"
h3   = tag "h3"
pre  = tag "pre"

-- Void elements have no content.
br hr img meta link : Attrs → Item
br   as = tag "br" as []
hr   as = tag "hr" as []
img  as = tag "img" as []
meta as = tag "meta" as []
link as = tag "link" as []

-- Raw-text elements take a body, which is not escaped.
script style : Attrs → String → Item
script as s = tag "script" as (text s ∷ [])
style  as s = tag "style" as (text s ∷ [])
