{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

open import Relation.Binary using (DecSetoid)

module Data.JSON.ObjectC {c ℓ} (D : DecSetoid c ℓ) where

import Data.Container as Cont
open Cont using (Container; _▷_; ⟦_⟧)
open import Level using (0ℓ; Level; _⊔_)
open import Data.Product using (∃; ∃-syntax; _,_; -,_)
open import Data.List.Relation.Unary.Unique.DecSetoid D
import Data.List.Membership.DecSetoid D as LM
open import Data.List as L using (List; []; _∷_)
open DecSetoid D
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.Any as Any
open Any using (Any)
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Function using (flip; _on_)
open import Relation.Binary using (Rel)
import Data.List.Relation.Unary.AllPairs as AllPairs
open AllPairs using (AllPairs; []; _∷_)
open import Relation.Binary.Construct.On
  using () renaming (decSetoid to on-decSetoid)
import Data.List.Relation.Unary.Unique.DecSetoid.Properties as U
open import Data.Product
open import Function using (_∘_; id)

private variable
  a b : Level
  A : Set a
  B : Set b

Key : Set _
Key = Carrier

-- Shape: a list of keys that are proven to be unique
-- Position: a key along with a proof that it's in the list
ObjectC : Container (c ⊔ ℓ) (c ⊔ ℓ)
ObjectC = ∃ Unique ▷ λ { (l , _) → ∃[ s ] s LM.∈ l }

all∈ : (l : List Key) → All (LM._∈ l) l
all∈ [] = []
all∈ (x ∷ l) = (Any.here refl) ∷ All.map Any.there (all∈ l)

fromObjectC : ⟦ ObjectC ⟧ A → List (Key × A)
fromObjectC ((keys , keys-unique) , lookup) =
  flip All.reduce
    (all∈ keys)
    λ {k} k∈keys → k , lookup (k , k∈keys)

toObjectC : List (Key × A) → ⟦ ObjectC ⟧ A
toObjectC l =
  let pairs-unique = U.deduplicate-! (on-decSetoid D proj₁) l
      keys-unique = allpairson pairs-unique
  in  (-, keys-unique)
      , λ { (k , k∈keys) → proj₂ (Any.lookup (AnyP.map⁻ k∈keys)) }
  where
    allpairson
      : ∀ {r} {xs : List A} {f : A → B} {R : Rel B r}
      → AllPairs (R on f) xs
      → AllPairs R (L.map f xs)
    allpairson {xs = []} [] = AllPairs.[]
    allpairson {xs = x ∷ xs} (all ∷ allpairs) =
      AllP.map⁺ all AllPairs.∷ allpairson allpairs

Object : Set a → Set (a ⊔ c ⊔ ℓ)
Object = ⟦ ObjectC ⟧

foldObjectC : (f : B → (Key × A) → B) → B → Object A  → B
foldObjectC f b = L.foldl f b ∘ fromObjectC

objectToList : Object A → List (Key × A)
objectToList obj = foldObjectC (λ f x → f ∘ (x ∷_)) id obj []
  where open import Data.List
