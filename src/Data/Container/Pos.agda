{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Positions below a bound, as numbers
--
-- `Fin n` is unary: the `i`th position is `i` constructors deep, so
-- enumerating the `n` positions of a node (which every fold over an
-- array, object or element does) costs `O(n²)` however it is done.
-- `Pos n` is a number `index < n` whose bound is an irrelevant
-- (erased) proof, so a position is one machine integer.
--
-- The bound is the boolean `index <ᵇ n`, so that `zeroP` and `sucP`
-- need no arithmetic: `T (suc i <ᵇ suc n)` is `T (i <ᵇ n)`.
------------------------------------------------------------------------

module Data.Container.Pos where

open import Level using (Level)
open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Nat.Properties using (<⇒<ᵇ)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

private variable
  a : Level
  A : Set a
  n m : ℕ

record Pos (n : ℕ) : Set where
  constructor mkPos
  field
    index : ℕ
    .bound : T (index <ᵇ n)

open Pos public

zeroP : Pos (suc n)
zeroP = mkPos zero tt

sucP : Pos n → Pos (suc n)
sucP (mkPos i b) = mkPos (suc i) b

-- There are no positions below zero.
noPos : Pos zero → A
noPos (mkPos i ())

-- Positions are determined by their index.
pos-≡ : (p q : Pos n) → index p ≡ index q → p ≡ q
pos-≡ (mkPos i b) (mkPos .i c) refl = refl

-- Every position below `suc n` is `zeroP` or `sucP` of one below `n`.
data View : ∀ {n} → Pos (suc n) → Set where
  isZero : ∀ {n} → View (zeroP {n})
  isSuc  : ∀ {n} (p : Pos n) → View (sucP p)

view : ∀ {n} (p : Pos (suc n)) → View p
view (mkPos zero    b) = isZero
view (mkPos (suc i) b) = isSuc (mkPos i b)

-- Transport along an equality of bounds.  The equation is irrelevant (it
-- is only needed for the erased bound), so a cast costs nothing, however
-- the equation was proved.
castP : ∀ {n m} → .(n ≡ m) → Pos n → Pos m
castP {n} {m} e (mkPos i b) = mkPos i (subst (λ k → T (i <ᵇ k)) e b)

castP-id : ∀ {n} (e : n ≡ n) (p : Pos n) → castP e p ≡ p
castP-id e p = refl

castP-zero : ∀ {n m} (e : suc n ≡ suc m) → castP e (zeroP {n}) ≡ zeroP {m}
castP-zero e = refl

castP-suc : ∀ {n m} (e : suc n ≡ suc m) (e′ : n ≡ m) (p : Pos n) → castP e (sucP p) ≡ sucP (castP e′ p)
castP-suc e e′ p = refl

-- From `Fin`, for code written against the unary positions.
fromFin : Fin n → Pos n
fromFin {n} i = mkPos (toℕ i) (<⇒<ᵇ (toℕ<n i))
