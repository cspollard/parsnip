{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Printing XML
--
-- One printer, a catamorphism (`foldXMLM`) over the AST.  Text and
-- attribute values are escaped as in `Data.XML.Escape`.  An element with
-- no content is self-closing.
------------------------------------------------------------------------

module Data.XML.Print where

open import Data.Char using (Char)
open import Data.String as String using (String; fromList)
open import Data.List as List using (List; []; _∷_; _++_; concat; map)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)

open import Data.XML.AST
open import Data.XML.Escape using (escapeText; escapeValue)

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
