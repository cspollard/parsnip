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
import Data.Nat as ℕ
open import Data.Nat.Properties using (suc-injective)
open import Data.List.Properties using (length-map)
open import Data.List using (List; []; _∷_; length; map; zip)
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise; []; _∷_)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym; trans)

open import Data.JSON.AST
open import Data.Container.List using (Pos; castP; pointwise-table; tabulate; length-tabulate)
open JSONCont using (JSONC; array; object; prim; Key)

infix 4 _≈ⱼ_

-- One constructor per kind of node, so that the shape equality is an
-- equation on `ℕ` (array length) or `List Key` (object keys) rather than
-- on the dependent pair of shape components; children are compared
-- through `subst` along it.  Leaves must carry the same payload.
data _≈ⱼ_ : Rel JSON 0ℓ where
  ≈prim   : ∀ {t x f g} → impure ((prim t , x) , f) ≈ⱼ impure ((prim t , x) , g)
  ≈array  : ∀ {n m} {f : Pos n → JSON} {g : Pos m → JSON} (e : n ≡ m) →
            (∀ i → f i ≈ⱼ g (castP e i)) →
            impure ((array , n) , f) ≈ⱼ impure ((array , m) , g)
  ≈object : ∀ {ks ls} {f : Pos (length ks) → JSON} {g : Pos (length ls) → JSON} (e : ks ≡ ls) →
            (∀ i → f i ≈ⱼ g (castP (cong length e) i)) →
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

-- If `xs` is pointwise bisimilar to the children of an array, the array
-- built from `xs` is bisimilar to it.
arrayⱼ-go : ∀ n (f : Pos n → JSON) (xs : List JSON) →
            Pointwise _≈ⱼ_ xs (JSONCont.listCToList (n , f)) →
            arrayⱼ xs ≈ⱼ impure ((array , n) , f)
arrayⱼ-go n f xs pw = ≈array (proj₁ pt) (proj₂ pt)
  where pt = pointwise-table xs n f pw

-- Keyed children are related when their keys agree and their values are bisimilar.
EntryRel : Rel (Key × JSON) 0ℓ
EntryRel (k , x) (k′ , y) = k ≡ k′ × x ≈ⱼ y

private
  -- Entries related to `zip ks vs` have those keys and related values.
  zip-split : ∀ (kvs : List (Key × JSON)) ks (vs : List JSON) → length ks ≡ length vs →
              Pointwise EntryRel kvs (zip ks vs) →
              map proj₁ kvs ≡ ks × Pointwise _≈ⱼ_ (map proj₂ kvs) vs
  zip-split []              []        []        _  []  = refl , []
  zip-split []              []        (v ∷ vs)  () _
  zip-split []              (k ∷ ks)  []       ()  _
  zip-split []              (k ∷ ks)  (v ∷ vs) _   ()
  zip-split (kv ∷ kvs)      []        vs        _   ()
  zip-split (kv ∷ kvs)      (k ∷ ks)  []        ()  _
  zip-split ((k₀ , x) ∷ kvs) (k ∷ ks) (v ∷ vs)  lt  ((refl , x≈) ∷ ps)
    with zip-split kvs ks vs (suc-injective lt) ps
  ... | e , pw = cong (k₀ ∷_) e , x≈ ∷ pw

objectFromList′-go : ∀ ks (f : Pos (length ks) → JSON) (kvs : List (Key × JSON)) →
                     Pointwise EntryRel kvs (JSONCont.objectCToEntries (ks , f)) →
                     objectFromList′ kvs ≈ⱼ impure ((object , ks) , f)
objectFromList′-go ks f kvs pw = ≈object (proj₁ zs) (λ i → proj₂ pt (castP (trans (length-map proj₁ kvs) (sym (length-map proj₂ kvs))) i))
  where
  zs = zip-split kvs ks (tabulate (length ks) f) (sym (length-tabulate (length ks) f)) pw
  pt = pointwise-table (map proj₂ kvs) (length ks) f (proj₂ zs)
