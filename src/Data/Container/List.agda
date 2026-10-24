{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Lists as a container
--
-- `ListC = ℕ ▷ Fin`: a list is its length together with one element per
-- position.  Shared by the JSON and XML ASTs, where it describes the
-- children of an array / element.
------------------------------------------------------------------------

module Data.Container.List where

open import Level using (Level; 0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
import Data.List as L
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Fin using (Fin; zero; suc)
open import Function using (_∘_)
open import Data.Container using (Container; ⟦_⟧; _▷_)

private variable
  a b : Level
  A : Set a
  B : Set b

ListC : Container 0ℓ 0ℓ
ListC = ℕ ▷ Fin

foldListC : (A → B → B) → B → ⟦ ListC ⟧ A → B
foldListC f b (n , lookup) = go n lookup
  where
  go : ∀ n → (Fin n → _) → _
  go zero    _   = b
  go (suc k) pos = f (pos zero) (go k (pos ∘ suc))

listCToList : ⟦ ListC ⟧ A → List A
listCToList = foldListC _∷_ []

listToListC : List A → ⟦ ListC ⟧ A
listToListC = L.foldr add (zero , λ ())
  where
  add : _ → ⟦ ListC ⟧ _ → ⟦ ListC ⟧ _
  add x p = suc (proj₁ p) , λ { zero → x; (suc i) → proj₂ p i }
