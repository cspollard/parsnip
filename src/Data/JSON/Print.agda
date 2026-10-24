{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Compact JSON printing
--
-- `printJSON` is the `to` of `jsonStage` (`Data.JSON.RoundTrip`): the
-- tokens of the value (`Data.JSON.Tokens`), spelled out by `printToken`.
-- The parser is proved to be its right inverse, up to `_≈ⱼ_`.
------------------------------------------------------------------------

module Data.JSON.Print where

open import Data.Char using (Char)
open import Data.List using (List)
open import Data.String using (String; fromList)
open import Function using (_∘_)

open import Data.JSON.AST using (JSON)
open import Data.JSON.Number using (printNumber) public
open import Data.JSON.String using (printStringLiteral) public
open import Data.JSON.Token using (printTokenList)
open import Data.JSON.Tokens using (printTokens)

printJSON : JSON → List Char
printJSON = printTokenList ∘ printTokens

-- Render to standard Agda String
renderJSON : JSON → String
renderJSON = fromList ∘ printJSON
