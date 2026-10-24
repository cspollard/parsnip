{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Bisimilarity of XML documents
--
-- `x ≈ₓ y` holds when `x` and `y` have the same tag, attributes and text
-- slots at every element and their children are pairwise bisimilar.
-- Without funext this is the strongest equality on container values that
-- can be proved of parsed/printed XML (cf. `Data.JSON.Equality`).
--
-- The validity proofs in the shapes are not compared (the constructor
-- leaves them unrelated), and tag and attributes are one shared index.
-- The arity may differ in form only: `e : n ≡ m` transports the text
-- slots and the children.
------------------------------------------------------------------------

module Data.XML.Equality where

open import Level using (0ℓ)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Data.Vec using (Vec)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Data.XML.AST
open import Data.XML.Valid

infix 4 _≈ₓ_

data _≈ₓ_ : Rel XMLDoc 0ℓ where
  ≈element : ∀ {tag attrs n m} {ts : Vec Text (suc n)} {ts′ : Vec Text (suc m)}
               {pt pt′ pa pa′ px px′} {f : Fin n → XMLDoc} {g : Fin m → XMLDoc}
             (e : n ≡ m) → subst (λ k → Vec Text (suc k)) e ts ≡ ts′ →
             (∀ i → f i ≈ₓ g (subst Fin e i)) →
             impure (shape tag attrs n ts pt pa px , f) ≈ₓ impure (shape tag attrs m ts′ pt′ pa′ px′ , g)

≈ₓ-refl : ∀ {x} → x ≈ₓ x
≈ₓ-refl {pure ()}
≈ₓ-refl {impure (shape tag attrs n ts pt pa px , f)} = ≈element refl refl (λ i → ≈ₓ-refl)

≈ₓ-sym : ∀ {x y} → x ≈ₓ y → y ≈ₓ x
≈ₓ-sym (≈element refl refl h) = ≈element refl refl (λ i → ≈ₓ-sym (h i))

≈ₓ-trans : ∀ {x y z} → x ≈ₓ y → y ≈ₓ z → x ≈ₓ z
≈ₓ-trans (≈element refl refl h) (≈element refl refl k) =
  ≈element refl refl (λ i → ≈ₓ-trans (h i) (k i))

≈ₓ-isEquivalence : IsEquivalence _≈ₓ_
≈ₓ-isEquivalence = record
  { refl  = ≈ₓ-refl
  ; sym   = ≈ₓ-sym
  ; trans = ≈ₓ-trans
  }

XMLSetoid : Setoid 0ℓ 0ℓ
XMLSetoid = record { isEquivalence = ≈ₓ-isEquivalence }
