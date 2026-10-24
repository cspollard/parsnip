{-# OPTIONS --safe --cubical-compatible #-}

------------------------------------------------------------------------
-- What counts as well-formed XML content
--
-- The XML AST carries evidence of these predicates in its node shapes, so
-- ill-formed documents are unrepresentable.  They are `Bool`-valued and
-- the evidence is `T b`, which is `⊤` or `⊥`: it is definitionally
-- proof-irrelevant (a record with eta), and for concrete data Agda
-- solves it by computation.
--
-- * characters:  the XML 1.0 `Char` production
--                (#x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD]
--                 | [#x10000-#x10FFFF]); other Agda `Char`s (e.g. NUL)
--                are not XML.
-- * names:       an ASCII grammar, `[A-Za-z_:][A-Za-z0-9_:.-]*`, which
--                covers SVG.  Widening it only changes `isNameStart` and
--                `isNameChar`.
-- * attributes:  valid names and values, and no name occurs twice
--                (the "Unique Att Spec" well-formedness constraint).
------------------------------------------------------------------------

module Data.XML.Valid where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; T)
open import Data.Char using (Char; toℕ)
open import Data.Nat using (ℕ; suc; _<ᵇ_; _≡ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Bool.ListAction using (all; any)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_)

Name Text : Set
Name = List Char
Text = List Char

Attribute : Set
Attribute = Name × Text

Attributes : Set
Attributes = List Attribute

------------------------------------------------------------------------
-- Characters
------------------------------------------------------------------------

-- `lo ≤ toℕ c ≤ hi`
inRange : ℕ → ℕ → Char → Bool
inRange lo hi c = not (toℕ c <ᵇ lo) ∧ (toℕ c <ᵇ suc hi)

is : Char → Char → Bool
is c d = toℕ c ≡ᵇ toℕ d

range : Char → Char → Char → Bool
range lo hi = inRange (toℕ lo) (toℕ hi)

isValidChar : Char → Bool
isValidChar c =
    is '\t' c ∨ is '\n' c ∨ is '\r' c
  ∨ inRange 0x20 0xD7FF c ∨ inRange 0xE000 0xFFFD c ∨ inRange 0x10000 0x10FFFF c

isValidText : Text → Bool
isValidText = all isValidChar

------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------

isNameStart : Char → Bool
isNameStart c = range 'A' 'Z' c ∨ range 'a' 'z' c ∨ is '_' c ∨ is ':' c

isNameChar : Char → Bool
isNameChar c = isNameStart c ∨ range '0' '9' c ∨ is '-' c ∨ is '.' c

isValidName : Name → Bool
isValidName []       = false
isValidName (c ∷ cs) = isNameStart c ∧ all isNameChar cs

------------------------------------------------------------------------
-- Attributes
------------------------------------------------------------------------

eqName : Name → Name → Bool
eqName []       []       = true
eqName (c ∷ cs) (d ∷ ds) = is c d ∧ eqName cs ds
eqName _        _        = false

hasKey : Name → Attributes → Bool
hasKey k = any (λ a → eqName k (proj₁ a))

uniqueKeys : Attributes → Bool
uniqueKeys []             = true
uniqueKeys ((k , _) ∷ as) = not (hasKey k as) ∧ uniqueKeys as

isValidAttribute : Attribute → Bool
isValidAttribute a = isValidName (proj₁ a) ∧ isValidText (proj₂ a)

isValidAttrs : Attributes → Bool
isValidAttrs as = all isValidAttribute as ∧ uniqueKeys as

------------------------------------------------------------------------
-- The text slots of an element
------------------------------------------------------------------------

isValidTexts : ∀ {n} → Vec Text n → Bool
isValidTexts []       = true
isValidTexts (t ∷ ts) = isValidText t ∧ isValidTexts ts
