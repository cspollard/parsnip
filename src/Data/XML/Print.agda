{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Printing XML
--
-- One printer, a catamorphism (`foldXMLM`) over the AST.  Text and
-- attribute values are escaped with the predefined entities; characters
-- that XML parsers normalise away (`\r` everywhere, tab and newline in
-- values) are written as numeric references so that they survive
-- parsing.  An element with no content is self-closing.
------------------------------------------------------------------------

module Data.XML.Print where

open import Data.Char using (Char)
open import Data.String as String using (String; fromList)
open import Data.List as List using (List; []; _∷_; _++_; concat; map)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)

open import Data.XML.AST

------------------------------------------------------------------------
-- Escaping
------------------------------------------------------------------------

entity : String → List Char
entity s = '&' ∷ String.toList s ++ ';' ∷ []

-- Escapes common to text and attribute values.
escapeCommon : Char → List Char
escapeCommon '&'  = entity "amp"
escapeCommon '<'  = entity "lt"
escapeCommon '>'  = entity "gt"
escapeCommon '\r' = entity "#13"
escapeCommon c    = c ∷ []

escapeText : Text → List Char
escapeText = concat ∘ map escapeCommon

escapeValue : Text → List Char
escapeValue = concat ∘ map esc
  where
  esc : Char → List Char
  esc '"'  = entity "quot"
  esc '\t' = entity "#9"
  esc '\n' = entity "#10"
  esc c    = escapeCommon c

------------------------------------------------------------------------
-- Elements
------------------------------------------------------------------------

printAttribute : Attribute → List Char
printAttribute (k , v) = ' ' ∷ k ++ '=' ∷ '"' ∷ escapeValue v ++ '"' ∷ []

printAttributes : Attributes → List Char
printAttributes = concat ∘ map printAttribute

printElement : Name → Attributes → Content (List Char) → List Char
printElement tag attrs ([] , []) = '<' ∷ tag ++ printAttributes attrs ++ ' ' ∷ '/' ∷ '>' ∷ []
printElement tag attrs (t , cs)  =
  '<' ∷ tag ++ printAttributes attrs ++ '>' ∷
  escapeText t ++ concat (map (λ { (c , t′) → c ++ escapeText t′ }) cs) ++
  '<' ∷ '/' ∷ tag ++ '>' ∷ []

printXML : XMLDoc → List Char
printXML = foldXMLM (λ ()) printElement

renderXML : XMLDoc → String
renderXML = fromList ∘ printXML
