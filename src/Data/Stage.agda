{-# OPTIONS --safe --cubical-compatible #-}

------------------------------------------------------------------------
-- Stages of the JSON pipeline as stdlib right inverses
--
-- A stage between a structured type `A` (a setoid) and its printed form
-- is `Function.Bundles.RightInverse A (Chars)`:
--
--   to        = print           (respects the equivalence on `A`)
--   from      = parse           (total; `default` where parsing fails)
--   inverseʳ  = parse (print x) ≈ x
--
-- Stages compose with `Function.Construct.Composition.rightInverse`.
-- `mkStage` builds a stage from the partial `Maybe`-parser actually used
-- at runtime, so the executable and the proof share one definition.
------------------------------------------------------------------------

module Data.Stage where

open import Level using (0ℓ)
open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁)
open import Function.Bundles using (RightInverse)
open import Relation.Binary using (Setoid)
open import Relation.Binary.Construct.On as On using ()
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; setoid)

private variable
  A : Set

------------------------------------------------------------------------
-- Setoids
------------------------------------------------------------------------

-- Printed text.
Chars : Setoid 0ℓ 0ℓ
Chars = setoid (List Char)

-- The sub-setoid of `S` cut out by a predicate; equality ignores the
-- proof.  Used for values with a validity side-condition (e.g. token
-- streams with no two adjacent numbers).
Subtype : (S : Setoid 0ℓ 0ℓ) → (Setoid.Carrier S → Set) → Setoid 0ℓ 0ℓ
Subtype S P = On.setoid S (λ (p : Σ[ x ∈ Setoid.Carrier S ] P x) → proj₁ p)

------------------------------------------------------------------------
-- Building a stage from a partial parser
------------------------------------------------------------------------

-- `parseOr d p` is the total parser: `p`, with `d` where `p` fails.
parseOr : A → (List Char → Maybe A) → List Char → A
parseOr d p cs = fromMaybe d (p cs)

module _ (S : Setoid 0ℓ 0ℓ) where
  private module S = Setoid S

  -- A stage from `print`, a partial `parse`, and a default witness.
  -- `parse-print` is the round-trip law in `Maybe` form; the equivalence
  -- on `S` is only required to be respected by `print`.
  mkStage : (print : S.Carrier → List Char)
            (parse : List Char → Maybe S.Carrier)
            (default : S.Carrier) →
            (∀ {x y} → x S.≈ y → print x ≡ print y) →
            (∀ x → ∃[ y ] parse (print x) ≡ just y × y S.≈ x) →
            RightInverse S Chars
  mkStage print parse default print-cong parse-print = record
    { to        = print
    ; from      = parseOr default parse
    ; to-cong   = print-cong
    ; from-cong = λ { refl → S.refl }
    ; inverseʳ  = inv
    }
    where
    inv : ∀ {x cs} → cs ≡ print x → parseOr default parse cs S.≈ x
    inv {x} refl with parse (print x) | parse-print x
    ... | .(just y) | y , refl , y≈x = y≈x
