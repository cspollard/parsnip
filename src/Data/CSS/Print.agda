{-# OPTIONS --safe --cubical-compatible #-}

------------------------------------------------------------------------
-- Printing a CSS tree
------------------------------------------------------------------------

module Data.CSS.Print where

open import Data.Char using (Char)
open import Data.List using (List)
open import Data.String using (String; fromList)
open import Function using (_∘_)

open import Data.CSS.AST using (CSS)
open import Data.CSS.Tokens using (printTokens)
open import Data.CSS.Lexer using (printList)

printCSS : CSS → List Char
printCSS = printList ∘ printTokens

renderCSS : CSS → String
renderCSS = fromList ∘ printCSS
