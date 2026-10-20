{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

module Data.XML.Print where

open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.String as String using (String; toList; fromList)
open import Data.List as List using (List; []; _∷_; _++_; concat)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.XML.AST

open import Data.List.Relation.Unary.Any using (Any; here; there; any?)

------------------------------------------------------------------------
-- Helpers: Tag Name, Attribute, & Text Escaping
------------------------------------------------------------------------

-- Association table membership via Char decidable equality
_∈-table?_ : (c : Char) (table : List (Char × Char)) → Dec (Any (λ (k , _) → c ≡ k) table)
c ∈-table? table = any? (λ (k , _) → c ≟ k) table

lookupEscape : ∀ {c : Char} {table : List (Char × Char)} → Any (λ (k , _) → c ≡ k) table → Char
lookupEscape (here {x = _ , v} _) = v
lookupEscape (there p)            = lookupEscape p

escapeList : List (Char × Char) → List Char → List Char
escapeList table []       = []
escapeList table (c ∷ cs) with c ∈-table? table
... | yes p = '\\' ∷ lookupEscape p ∷ escapeList table cs
... | no  _ = c ∷ escapeList table cs

-- Escape tables
escapeNameChars : List (Char × Char)
escapeNameChars =
  ('\\' , '\\') ∷
  (' '  , 's')  ∷
  ('\t' , 't')  ∷
  ('\n' , 'n')  ∷
  ('\r' , 'r')  ∷
  ('>'  , 'g')  ∷
  ('/'  , 'f')  ∷
  ('='  , 'e')  ∷
  ('<'  , 'l')  ∷
  ('!'  , 'b')  ∷ []

escapeAttrChars : List (Char × Char)
escapeAttrChars =
  ('\\' , '\\') ∷
  ('"'  , '"')  ∷
  ('<'  , 'l')  ∷
  ('>'  , 'g')  ∷
  ('&'  , 'a')  ∷ []

escapeTextChars : List (Char × Char)
escapeTextChars =
  ('\\' , '\\') ∷
  ('<'  , 'l')  ∷
  ('>'  , 'g')  ∷
  ('&'  , 'a')  ∷
  (' '  , 's')  ∷
  ('\t' , 't')  ∷
  ('\n' , 'n')  ∷
  ('\r' , 'r')  ∷ []

escapeName : List Char → List Char
escapeName = escapeList escapeNameChars

printName : String → List Char
printName s with toList s
... | []     = '\\' ∷ '0' ∷ []
... | c ∷ cs = escapeName (c ∷ cs)

escapeAttr : List Char → List Char
escapeAttr = escapeList escapeAttrChars

-- Format a single attribute: ` key="val"`
printAttribute : Attribute → List Char
printAttribute (k , v) =
  ' ' ∷ printName k ++ ('=' ∷ '"' ∷ escapeAttr (toList v) ++ ('"' ∷ []))

printAttributes : Attributes → List Char
printAttributes []       = []
printAttributes (a ∷ as) = printAttribute a ++ printAttributes as

escapeText : List Char → List Char
escapeText = escapeList escapeTextChars

printTextContent : String → List Char
printTextContent s = escapeText (toList s) ++ ('\\' ∷ 'e' ∷ [])

------------------------------------------------------------------------
-- XML Serialization
------------------------------------------------------------------------

printXML : XMLDoc → List Char
printXML = foldXMLM (λ ()) printText printElem
  where
    printText : String → List Char
    printText = printTextContent

    printElem : String → Attributes → List (List Char) → List Char
    printElem tag attrs [] =
      '<' ∷ printName tag ++ printAttributes attrs ++ (' ' ∷ '/' ∷ '>' ∷ [])
    printElem tag attrs (c ∷ cs) =
      '<' ∷ printName tag ++ printAttributes attrs ++ ('>' ∷ concat (c ∷ cs) ++ ('<' ∷ '/' ∷ printName tag ++ ('>' ∷ [])))

-- Render XML document to String
renderXML : XMLDoc → String
renderXML = fromList ∘ printXML

------------------------------------------------------------------------
-- Direct SVG Document Rendering (Compliant & Fast Serialization)
------------------------------------------------------------------------

escapeSVGChar : Char → List Char
escapeSVGChar '&' = '&' ∷ 'a' ∷ 'm' ∷ 'p' ∷ ';' ∷ []
escapeSVGChar '<' = '&' ∷ 'l' ∷ 't' ∷ ';' ∷ []
escapeSVGChar '>' = '&' ∷ 'g' ∷ 't' ∷ ';' ∷ []
escapeSVGChar '"' = '&' ∷ 'q' ∷ 'u' ∷ 'o' ∷ 't' ∷ ';' ∷ []
escapeSVGChar c   = c ∷ []

escapeSVGChars : List Char → List Char
escapeSVGChars []       = []
escapeSVGChars (c ∷ cs) = escapeSVGChar c ++ escapeSVGChars cs

printSVGTextContent : String → List Char
printSVGTextContent s = escapeSVGChars (toList s)

printSVGAttribute : Attribute → List Char
printSVGAttribute (k , v) =
  ' ' ∷ toList k ++ ('=' ∷ '"' ∷ escapeSVGChars (toList v) ++ ('"' ∷ []))

printSVGAttributes : Attributes → List Char
printSVGAttributes []       = []
printSVGAttributes (a ∷ as) = printSVGAttribute a ++ printSVGAttributes as

printSVGDoc : XMLDoc → List Char
printSVGDoc = foldXMLM (λ ()) printSVGTextContent printSVGElem
  where
    printSVGElem : String → Attributes → List (List Char) → List Char
    printSVGElem tag attrs [] =
      '<' ∷ toList tag ++ printSVGAttributes attrs ++ (' ' ∷ '/' ∷ '>' ∷ [])
    printSVGElem tag attrs (c ∷ cs) =
      '<' ∷ toList tag ++ printSVGAttributes attrs ++ ('>' ∷ concat (c ∷ cs) ++ ('<' ∷ '/' ∷ toList tag ++ ('>' ∷ [])))

renderSVG : XMLDoc → String
renderSVG = fromList ∘ printSVGDoc
