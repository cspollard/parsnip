{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Printing XML
--
-- The printer is the token printer after the token stream of the AST:
-- `printXML = printTokenList ∘ printTokens`.  Text and attribute values
-- are escaped as in `Data.XML.Escape`.  An element with no content is
-- self-closing.
------------------------------------------------------------------------

module Data.XML.Print where

open import Data.Char using (Char)
open import Data.String using (String; fromList)
open import Data.List using (List)
open import Function using (_∘_)

open import Data.XML.AST using (XMLDoc)
open import Data.XML.Token using (printTokenList)
open import Data.XML.Tokens using (printTokens)

printXML : XMLDoc → List Char
printXML = printTokenList ∘ printTokens

renderXML : XMLDoc → String
renderXML = fromList ∘ printXML
