{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The headline theorem: parsing inverts printing, lexing included
--
-- `xmlStage` is the composite of `parser` and `lexer`, two stdlib
-- `RightInverse`s (`Function.Construct.Composition.rightInverse`):
--
--   to        = printXML
--   from      = total parser (tokenize, check, parse; `defaultDoc` on failure)
--   inverseʳ  = from (printXML v) ≈ₓ v
--
-- `parseXML` is the partial `Maybe` parser used at runtime, and
-- `parseXML-printXML` is the same law stated for it.
------------------------------------------------------------------------

module Data.XML.RoundTrip where

open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; _×_; _,_)
open import Function.Bundles using (RightInverse)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)
import Function.Construct.Composition as Composition

open import Data.XML.AST using (XMLDoc)
open import Data.XML.Equality using (_≈ₓ_; XMLSetoid)
open import Data.XML.Lexer using (lexer; tokenize; tokenize-printTokenList)
open import Data.XML.Parser using (parser; parseTokens; parseTokens-printTokens)
open import Data.XML.Print using (printXML)
open import Data.JSON.Stage using (Chars)
open import Data.XML.Tokens using (printTokens; printTokens-valid)

xmlStage : RightInverse XMLSetoid Chars
xmlStage = Composition.rightInverse parser lexer

-- The printer of `xmlStage` is `printXML`.
to-printXML : ∀ v → RightInverse.to xmlStage v ≡ printXML v
to-printXML v = refl

-- The partial parser: tokenize, then parse the whole stream.
parseXML : List Char → Maybe XMLDoc
parseXML cs = Maybe.maybe parseTokens nothing (tokenize cs)

parseXML-printXML : ∀ v → ∃ λ v′ → parseXML (printXML v) ≡ just v′ × v′ ≈ₓ v
parseXML-printXML v with parseTokens-printTokens v
... | v′ , eq , ≈v =
  v′ ,
  Eq.trans (cong (Maybe.maybe parseTokens nothing)
                 (tokenize-printTokenList (printTokens v) (printTokens-valid v)))
           eq ,
  ≈v
