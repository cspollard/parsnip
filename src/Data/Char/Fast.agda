{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Fast decidable equality on characters, and list membership
--
-- `Data.Char.Properties._≟_` goes through `map′` and a `Dec` of the
-- underlying naturals, and `Data.List.Membership.DecPropositional._∈?_`
-- through `any?` and `_⊎-dec_`; lexers call them for every character,
-- and profiling put them at over half of the tokenizer's time and
-- allocation.  These are the same functions at the same types, but
-- compare the code points with the primitive `_≡ᵇ_` and recurse
-- directly, so they are drop-in replacements.
------------------------------------------------------------------------

module Data.Char.Fast where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char; toℕ)
open import Data.Char.Properties using () renaming (toℕ-injective to toℕ-inj)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (_≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

infix 4 _≟_ _∈_ _∈?_

_≟_ : (c d : Char) → Dec (c ≡ d)
c ≟ d = go (toℕ c ≡ᵇ toℕ d) refl
  where
  go : ∀ b → (toℕ c ≡ᵇ toℕ d) ≡ b → Dec (c ≡ d)
  go true  eq = yes (toℕ-inj c d (≡ᵇ⇒≡ _ _ (subst T (sym eq) tt)))
  go false eq = no λ c≡d → subst T eq (≡⇒≡ᵇ _ _ (cong toℕ c≡d))

-- Membership, as in `Data.List.Membership.Propositional`.
_∈_ : Char → List Char → Set
c ∈ cs = Any (c ≡_) cs

_∈?_ : (c : Char) (cs : List Char) → Dec (c ∈ cs)
c ∈? []       = no λ ()
c ∈? (x ∷ xs) with c ≟ x
... | yes p = yes (here p)
... | no ¬p with c ∈? xs
...   | yes q = yes (there q)
...   | no ¬q = no λ { (here p) → ¬p p ; (there q) → ¬q q }
