{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Random access to a list's elements
--
-- A node's children are a function from positions (`Data.Container.Pos`),
-- and a function built from a list by `lookup` costs `O(i)` at position
-- `i`.  `table xs` is the same function backed by a balanced tree built
-- once (`O(n log n)`), so that each access costs `O(log n)`.
--
-- The tree stores the size of every left subtree, so a lookup is a walk
-- of `<ᵇ` tests and subtractions on machine integers.  `lookup-build`
-- says it agrees with `nth?`, the obvious `O(i)` lookup.
------------------------------------------------------------------------

module Data.Container.Table where

open import Level using (Level)
open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.List using (List; []; _∷_; length; take; drop)
open import Data.List.Properties using (length-take; length-drop)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _/_; _<ᵇ_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.DivMod using (m/n<m; m≥n⇒m/n>0)
open import Data.Nat.Properties
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.Container.Pos

private variable
  a : Level
  A : Set a

------------------------------------------------------------------------
-- The specification: lookup in the list itself
------------------------------------------------------------------------

nth? : List A → ℕ → Maybe A
nth? []       _       = nothing
nth? (x ∷ xs) zero    = just x
nth? (x ∷ xs) (suc k) = nth? xs k

-- The element at a position (total, by the bound).
nth : (xs : List A) → Pos (length xs) → A
nth []       p = noPos p
nth (x ∷ xs) p with view p
... | isZero  = x
... | isSuc q = nth xs q

------------------------------------------------------------------------
-- The tree
------------------------------------------------------------------------

data Tree (A : Set a) : Set a where
  none : Tree A
  one  : A → Tree A
  bin  : ℕ → Tree A → Tree A → Tree A   -- the size of the left subtree

lookupT : Tree A → ℕ → Maybe A
lookupT none        _       = nothing
lookupT (one x)     zero    = just x
lookupT (one x)     (suc _) = nothing
lookupT (bin l L R) k       = if k <ᵇ l then lookupT L k else lookupT R (k ∸ l)

-- Balanced by halving, with fuel (the length suffices).
build : ℕ → List A → Tree A
build zero    _            = none
build (suc f) []           = none
build (suc f) (x ∷ [])     = one x
build (suc f) (x ∷ y ∷ zs) = split (length (x ∷ y ∷ zs) / 2) (x ∷ y ∷ zs)
  where
  split : ℕ → List _ → Tree _
  split h xs = bin h (build f (take h xs)) (build f (drop h xs))

------------------------------------------------------------------------
-- The tree agrees with the list
------------------------------------------------------------------------

take-nth? : ∀ h (xs : List A) k → suc k ≤ h → nth? (take h xs) k ≡ nth? xs k
take-nth? zero    xs       k       ()
take-nth? (suc h) []       k       _        = refl
take-nth? (suc h) (x ∷ xs) zero    _        = refl
take-nth? (suc h) (x ∷ xs) (suc k) (s≤s lt) = take-nth? h xs k lt

drop-nth? : ∀ h (xs : List A) k → nth? (drop h xs) k ≡ nth? xs (h + k)
drop-nth? zero    xs       k = refl
drop-nth? (suc h) []       k = refl
drop-nth? (suc h) (x ∷ xs) k = drop-nth? h xs k

-- A split at `h` with both parts within the fuel is looked up like the list.
split-lookup : ∀ f h (xs : List A) →
  (∀ ys → length ys ≤ f → ∀ k → lookupT (build f ys) k ≡ nth? ys k) →
  h ≤ length xs → length (take h xs) ≤ f → length (drop h xs) ≤ f →
  ∀ k → lookupT (bin h (build f (take h xs)) (build f (drop h xs))) k ≡ nth? xs k
split-lookup f h xs ih h≤ lt₁ lt₂ k with k <ᵇ h in eq
... | true  = trans (ih (take h xs) lt₁ k)
                    (take-nth? h xs k (<ᵇ⇒< k h (subst T (sym eq) _)))
  where open import Data.Unit using (tt)
... | false =
  let ¬lt : ¬ (k < h)
      ¬lt = λ lt → subst T eq (<⇒<ᵇ {k} {h} lt)
      hk : h ≤ k
      hk  = ≮⇒≥ ¬lt
  in trans (ih (drop h xs) lt₂ (k ∸ h))
           (trans (drop-nth? h xs (k ∸ h)) (cong (nth? xs) (m+[n∸m]≡n hk)))

lookup-build : ∀ f (xs : List A) → length xs ≤ f → ∀ k → lookupT (build f xs) k ≡ nth? xs k
lookup-build zero    []             _  k = refl
lookup-build zero    (x ∷ xs)       () k
lookup-build (suc f) []             _  k = refl
lookup-build (suc f) (x ∷ [])       _  zero    = refl
lookup-build (suc f) (x ∷ [])       _  (suc k) = refl
lookup-build (suc f) (x ∷ y ∷ zs)   lt k =
  split-lookup f h ys (lookup-build f) h≤L
    (≤-trans (≤-reflexive take-len) h≤f) (≤-trans (≤-reflexive drop-len) L∸h≤f) k
  where
  ys : List _
  ys = x ∷ y ∷ zs

  L : ℕ
  L = length ys

  h : ℕ
  h = L / 2

  h<L : h < L
  h<L = m/n<m L 2 (s≤s (s≤s z≤n))

  h≤L : h ≤ L
  h≤L = <⇒≤ h<L

  h≥1 : 1 ≤ h
  h≥1 = m≥n⇒m/n>0 {L} {2} (s≤s (s≤s z≤n))

  take-len : length (take h ys) ≡ h
  take-len = trans (length-take h ys) (m≤n⇒m⊓n≡m h≤L)

  drop-len : length (drop h ys) ≡ L ∸ h
  drop-len = length-drop h ys

  h≤f : h ≤ f
  h≤f = ≤-pred (≤-trans h<L lt)

  L∸h≤f : L ∸ h ≤ f
  L∸h≤f = ≤-trans (∸-monoʳ-≤ L h≥1) (∸-monoˡ-≤ 1 lt)

nth?-nth : ∀ (xs : List A) (p : Pos (length xs)) → nth? xs (index p) ≡ just (nth xs p)
nth?-nth []       p = noPos p
nth?-nth (x ∷ xs) p with view p
... | isZero  = refl
... | isSuc q = nth?-nth xs q

------------------------------------------------------------------------
-- The table
------------------------------------------------------------------------

-- `xs` as a function of positions, backed by a tree that is built once
-- (when the function is first applied) and shared by every application.
table : (xs : List A) → Pos (length xs) → A
table []           = noPos
table (x ∷ xs)     = at x (build (suc (length xs)) (x ∷ xs))
  where
  at : _ → Tree _ → Pos (suc (length xs)) → _
  at d t p = fromMaybe d (lookupT t (index p))

table-nth : ∀ (xs : List A) (p : Pos (length xs)) → table xs p ≡ nth xs p
table-nth []           p = noPos p
table-nth xs@(x ∷ xs′) p =
  cong (fromMaybe x)
    (trans (lookup-build (length xs) xs ≤-refl (index p)) (nth?-nth xs p))
