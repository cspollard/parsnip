{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Bisimilarity of JSON values
--
-- `v ≈ⱼ w` holds when `v` and `w` have the same shape at every node and
-- their children are pointwise bisimilar.  One layer is the stdlib's
-- `Data.Container.Relation.Binary.Pointwise`; the free monad closes it
-- under recursion.  Without funext this is the strongest equality on
-- container values that can be proved of parsed/printed JSON.
------------------------------------------------------------------------

module Data.JSON.Equality where

open import Level using (0ℓ)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Fin using (Fin; zero; suc)
import Data.Nat as ℕ
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym; trans)

open import Data.JSON.AST
open JSONCont using (JSONC; array; object; prim; Key)

infix 4 _≈ⱼ_

-- One constructor per kind of node, so that the shape equality is an
-- equation on `ℕ` (array length) or `List Key` (object keys) rather than
-- on the dependent pair of shape components; children are compared
-- through `subst` along it.  Leaves must carry the same payload.
data _≈ⱼ_ : Rel JSON 0ℓ where
  ≈prim   : ∀ {t x f g} → impure ((prim t , x) , f) ≈ⱼ impure ((prim t , x) , g)
  ≈array  : ∀ {n m} {f : Fin n → JSON} {g : Fin m → JSON} (e : n ≡ m) →
            (∀ i → f i ≈ⱼ g (subst Fin e i)) →
            impure ((array , n) , f) ≈ⱼ impure ((array , m) , g)
  ≈object : ∀ {ks ls} {f : Fin (length ks) → JSON} {g : Fin (length ls) → JSON} (e : ks ≡ ls) →
            (∀ i → f i ≈ⱼ g (subst (Fin ∘ length) e i)) →
            impure ((object , ks) , f) ≈ⱼ impure ((object , ls) , g)

≈ⱼ-refl : ∀ {v} → v ≈ⱼ v
≈ⱼ-refl {pure ()}
≈ⱼ-refl {impure ((object , ks) , f)} = ≈object refl (λ i → ≈ⱼ-refl)
≈ⱼ-refl {impure ((array , n) , f)} = ≈array refl (λ i → ≈ⱼ-refl)
≈ⱼ-refl {impure ((prim t , x) , f)} = ≈prim

≈ⱼ-sym : ∀ {v w} → v ≈ⱼ w → w ≈ⱼ v
≈ⱼ-sym ≈prim            = ≈prim
≈ⱼ-sym (≈array refl h)  = ≈array refl (λ i → ≈ⱼ-sym (h i))
≈ⱼ-sym (≈object refl h) = ≈object refl (λ i → ≈ⱼ-sym (h i))

≈ⱼ-trans : ∀ {u v w} → u ≈ⱼ v → v ≈ⱼ w → u ≈ⱼ w
≈ⱼ-trans ≈prim            ≈prim            = ≈prim
≈ⱼ-trans (≈array refl h)  (≈array refl k)  = ≈array refl (λ i → ≈ⱼ-trans (h i) (k i))
≈ⱼ-trans (≈object refl h) (≈object refl k) = ≈object refl (λ i → ≈ⱼ-trans (h i) (k i))

≈ⱼ-isEquivalence : IsEquivalence _≈ⱼ_
≈ⱼ-isEquivalence = record
  { refl  = ≈ⱼ-refl
  ; sym   = ≈ⱼ-sym
  ; trans = ≈ⱼ-trans
  }

-- `Data.JSON.Goals.JSONSetoid`.
JSONSetoid : Setoid 0ℓ 0ℓ
JSONSetoid = record { isEquivalence = ≈ⱼ-isEquivalence }

------------------------------------------------------------------------
-- Arrays and objects rebuilt from their children
--
-- These are the structural facts the parser proof needs: if a list `xs`
-- is pointwise bisimilar to the children of a node, then the node built
-- from `xs` (with `arrayⱼ` / `objectFromList′`) is bisimilar to it.
------------------------------------------------------------------------

private
  -- `subst` along `cong ℕ.suc e` / `cong (k ∷_) e` fixes `zero` and commutes with `suc`.
  subst-Fin-zero : ∀ {a b} (e : a ≡ b) → subst Fin (cong ℕ.suc e) zero ≡ zero
  subst-Fin-zero refl = refl

  subst-Fin-suc : ∀ {a b} (e : a ≡ b) (i : Fin a) →
                  subst Fin (cong ℕ.suc e) (suc i) ≡ suc (subst Fin e i)
  subst-Fin-suc refl i = refl

arrayⱼ-go : ∀ n (f : Fin n → JSON) (xs : List JSON) →
            Pointwise _≈ⱼ_ xs (JSONCont.listCToList (n , f)) →
            arrayⱼ xs ≈ⱼ impure ((array , n) , f)
arrayⱼ-go ℕ.zero    f []       []         = ≈array refl (λ ())
arrayⱼ-go (ℕ.suc n) f (x ∷ xs) (x≈ ∷ ps) with arrayⱼ-go n (f ∘ suc) xs ps
... | ≈array e h = ≈array (cong ℕ.suc e) λ
  { zero    → subst (λ j → x ≈ⱼ f j) (sym (subst-Fin-zero e)) x≈
  ; (suc i) → subst (λ j → _ ≈ⱼ f j) (sym (subst-Fin-suc e i)) (h i)
  }

private
  subst-Fin-zero′ : ∀ k {a b : List Key} (e : a ≡ b) → subst (Fin ∘ length) (cong (k ∷_) e) zero ≡ zero
  subst-Fin-zero′ k refl = refl

  subst-Fin-suc′ : ∀ k {a b : List Key} (e : a ≡ b) (i : Fin (length a)) →
                   subst (Fin ∘ length) (cong (k ∷_) e) (suc i) ≡ suc (subst (Fin ∘ length) e i)
  subst-Fin-suc′ k refl i = refl

-- Keyed children are related when their keys agree and their values are bisimilar.
EntryRel : Rel (Key × JSON) 0ℓ
EntryRel (k , x) (k′ , y) = k ≡ k′ × x ≈ⱼ y

objectFromList′-go : ∀ ks (f : Fin (length ks) → JSON) (kvs : List (Key × JSON)) →
                     Pointwise EntryRel kvs (JSONCont.objectCToEntries (ks , f)) →
                     objectFromList′ kvs ≈ⱼ impure ((object , ks) , f)
objectFromList′-go []       f []              []                 = ≈object refl (λ ())
objectFromList′-go (k ∷ ks) f ((k₀ , x) ∷ kvs) ((refl , x≈) ∷ ps)
  with objectFromList′-go ks (f ∘ suc) kvs ps
... | ≈object e h = ≈object (cong (k ∷_) e) λ
  { zero    → subst (λ j → x ≈ⱼ f j) (sym (subst-Fin-zero′ k e)) x≈
  ; (suc i) → subst (λ j → _ ≈ⱼ f j) (sym (subst-Fin-suc′ k e i)) (h i)
  }
