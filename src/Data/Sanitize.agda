{-# OPTIONS --safe --cubical-compatible #-}

------------------------------------------------------------------------
-- Generic helpers for repairing runtime data (shared by XML, CSS, ...)
--
-- A repair replaces each character that fails a test by a fixed
-- replacement that passes it, so the output is valid and valid input is
-- unchanged.
------------------------------------------------------------------------

module Data.Sanitize where

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_; T)
open import Data.Bool.ListAction using (all)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; map)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Char.Class using (isValidChar)

fromEq : ∀ {b} → b ≡ true → T b
fromEq refl = tt

both : ∀ {x y} → x ≡ true → y ≡ true → x ∧ y ≡ true
both refl refl = refl

-- `c` if it satisfies `ok`, and the replacement `d` otherwise.
fixWith : (Char → Bool) → Char → Char → Char
fixWith ok d c = if ok c then c else d

fixWith-ok : ∀ (ok : Char → Bool) (d : Char) → ok d ≡ true →
             ∀ (c : Char) → ok (fixWith ok d c) ≡ true
fixWith-ok ok d hd c = go (ok c) refl
  where
  go : ∀ (b : Bool) → ok c ≡ b → ok (if b then c else d) ≡ true
  go true  eq = eq
  go false eq = hd

all-map : ∀ (p : Char → Bool) (f : Char → Char) → (∀ c → p (f c) ≡ true) →
          ∀ (cs : List Char) → all p (map f cs) ≡ true
all-map p f h []       = refl
all-map p f h (c ∷ cs) rewrite h c = all-map p f h cs

-- Characters that are not legal XML become U+FFFD.
fixText : List Char → List Char
fixText = map (fixWith isValidChar '\xFFFD')

fixText-valid : ∀ t → all isValidChar (fixText t) ≡ true
fixText-valid = all-map isValidChar (fixWith isValidChar '\xFFFD') (fixWith-ok isValidChar '\xFFFD' refl)
