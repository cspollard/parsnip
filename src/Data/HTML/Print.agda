{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Printing HTML
--
-- `printBody` is the token printer after the token stream of the tree
-- (`printTokenList ∘ tokensElem`): text and attribute values are escaped
-- as in `Data.XML.Escape`, void elements are `<br />`, and raw-text
-- bodies are verbatim.  `printHTML` puts `<!DOCTYPE html>` in front.
------------------------------------------------------------------------

module Data.HTML.Print where

open import Data.Char using (Char)
open import Data.String using (String; fromList; toList)
open import Data.List using (List; _++_)
open import Function using (_∘_)

open import Data.HTML.AST using (Elem)
open import Data.HTML.Token using (printTokenList)
open import Data.HTML.Tokens using (tokensElem)

doctype : List Char
doctype = toList "<!DOCTYPE html>"

printBody : Elem → List Char
printBody = printTokenList ∘ tokensElem

printHTML : Elem → List Char
printHTML e = doctype ++ printBody e

renderHTML : Elem → String
renderHTML = fromList ∘ printHTML
