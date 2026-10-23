{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The headline theorem: parsing inverts printing, lexing included
--
-- `jsonStage` is the composite of `parser` and `lexer`, two stdlib
-- `RightInverse`s (`Function.Construct.Composition.rightInverse`):
--
--   to        = printJSON
--   from      = total parser (tokenize, check, parse; `nullⱼ` on failure)
--   inverseʳ  = from (printJSON v) ≈ⱼ v
--
-- `parseJSON` is the partial `Maybe` parser used at runtime, and
-- `parseJSON-printJSON` is the same law stated for it.
------------------------------------------------------------------------

module Data.JSON.RoundTrip where

open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; _×_; _,_)
open import Function.Bundles using (RightInverse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Function.Construct.Composition as Composition

open import Data.JSON.AST using (JSON)
open import Data.JSON.Equality using (_≈ⱼ_; JSONSetoid)
open import Data.JSON.Lexer using (lexer; tokenize; tokenize-printTokenList)
open import Data.JSON.Parser using (parser; parseTokens; parseTokens-printTokens)
open import Data.JSON.Print using (printJSON)
open import Data.JSON.Stage using (Chars)
open import Data.JSON.Token using (printTokenList)
open import Data.JSON.Tokens using (printTokens; printTokens-valid)

jsonStage : RightInverse JSONSetoid Chars
jsonStage = Composition.rightInverse parser lexer

-- The printer of `jsonStage` is `printJSON`.
to-printJSON : ∀ v → RightInverse.to jsonStage v ≡ printJSON v
to-printJSON v = refl

-- The partial parser: tokenize, then parse the whole stream.
parseJSON : List Char → Maybe JSON
parseJSON cs = Maybe.maybe parseTokens nothing (tokenize cs)

parseJSON-printJSON : ∀ v → ∃ λ v′ → parseJSON (printJSON v) ≡ just v′ × v′ ≈ⱼ v
parseJSON-printJSON v with parseTokens-printTokens v
... | v′ , eq , ≈v =
  v′ ,
  Eq.trans (cong (Maybe.maybe parseTokens nothing)
                 (tokenize-printTokenList (printTokens v) (printTokens-valid v)))
           eq ,
  ≈v
  where module Eq = Relation.Binary.PropositionalEquality
