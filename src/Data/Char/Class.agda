{-# OPTIONS --safe --cubical-compatible #-}

------------------------------------------------------------------------
-- Boolean character classes
--
-- The building blocks of the character predicates of the text formats
-- (`Data.XML.Valid`, `Data.CSS.Valid`): equality with a literal and
-- membership of a code point range, and `isValidChar`, the characters
-- that XML 1.0 allows in documents (and which the other formats here,
-- whose style sheets and pages can be embedded in XML, restrict their
-- text to).  They are `Bool`-valued, so that
-- evidence of them is `T b`, which is definitionally irrelevant for
-- concrete characters.
------------------------------------------------------------------------

module Data.Char.Class where

open import Data.Bool using (Bool; _∧_; _∨_; not)
open import Data.Char using (Char; toℕ)
open import Data.Nat using (ℕ; suc; _<ᵇ_; _≡ᵇ_)

-- `lo ≤ toℕ c ≤ hi`
inRange : ℕ → ℕ → Char → Bool
inRange lo hi c = not (toℕ c <ᵇ lo) ∧ (toℕ c <ᵇ suc hi)

is : Char → Char → Bool
is c d = toℕ c ≡ᵇ toℕ d

range : Char → Char → Char → Bool
range lo hi = inRange (toℕ lo) (toℕ hi)

-- The XML 1.0 `Char` production
-- (#x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] | [#x10000-#x10FFFF]).
-- Other Agda `Char`s (e.g. NUL) are not XML.
isValidChar : Char → Bool
isValidChar c =
    is '\t' c ∨ is '\n' c ∨ is '\r' c
  ∨ inRange 0x20 0xD7FF c ∨ inRange 0xE000 0xFFFD c ∨ inRange 0x10000 0x10FFFF c
