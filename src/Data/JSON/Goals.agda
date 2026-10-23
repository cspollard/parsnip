{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- JSON round-trip goals (temporary; see JSONPlan.md, Phase 1)
--
-- The top-level contract of the JSON pipeline, with every implementation
-- left as a hole.  Each hole is a work item; once filled, the definition
-- moves to its home module and this file shrinks.  Deleted in Phase 9.
--
-- Every stage is a stdlib `Function.Bundles.RightInverse`:
--
--   RightInverse A B   has   to : A → B     (our `print`)
--                            from : B → A   (our `parse`, total, with a
--                                            default witness on failure)
--                            inverseʳ :  from (to x) ≈ x
--
-- so stages compose with `Function.Construct.Composition.rightInverse`,
-- products with `Data.Product.Function.NonDependent.Setoid._×-rightInverse_`
-- (dependent: `Data.Product.Function.Dependent.Setoid.rightInverse`), and no
-- hand-written "tokenize (print ts) ≡ …" statements are needed.
------------------------------------------------------------------------

module Data.JSON.Goals where

open import Level using (0ℓ)
open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Unit using (⊤)
open import Function.Bundles using (RightInverse)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality using (setoid)

open import Data.JSON.AST using (JSON; JSONNumber)
open import Data.JSON.Stage using (Chars; Subtype)

------------------------------------------------------------------------
-- Done
--
-- Phase 3: `Data.JSON.Number.numberStage`
-- Phase 4: `Data.JSON.String.stringStage`, `Data.JSON.Keyword.keywordStage`
-- Phase 5: `Data.JSON.Equality.{_≈ⱼ_, JSONSetoid}`
-- Phase 6 (lexing): `Data.JSON.Token.tokenStage`,
--          `Data.JSON.Lexer.{ValidTokenSeq, ValidTokens, lexer}`
------------------------------------------------------------------------

open import Data.JSON.Equality using (_≈ⱼ_; JSONSetoid)
open import Data.JSON.Number using (numberStage)
open import Data.JSON.String using (stringStage)
open import Data.JSON.Keyword using (Keyword; keywordStage)
open import Data.JSON.Token using (JSONToken; tokenStage)
open import Data.JSON.Lexer using (ValidTokenSeq; ValidTokens; lexer)

------------------------------------------------------------------------
-- Syntactic stage (tokens → JSON)
------------------------------------------------------------------------

-- `to` is the token printer; that its output satisfies `ValidTokenSeq`
-- (no two adjacent number tokens) is part of its type, so there is no
-- separate compatibility lemma.  `to-cong` is "printing respects `_≈ⱼ_`".
parser : RightInverse JSONSetoid ValidTokens
parser = ?

------------------------------------------------------------------------
-- The whole pipeline
------------------------------------------------------------------------

import Function.Construct.Composition as Composition

-- Headline theorem: `parseJSON (printJSON v) ≈ⱼ v`, lexing included.
jsonStage : RightInverse JSONSetoid Chars
jsonStage = Composition.rightInverse parser lexer
