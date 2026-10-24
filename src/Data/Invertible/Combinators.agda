{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

module Data.Invertible.Combinators where

open import Level using (0ℓ)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_; _$_)
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

open import Data.Invertible.Core
open import Data.Invertible.Char using (litChar)

------------------------------------------------------------------------
-- Unit Elimination Isomorphisms
------------------------------------------------------------------------

×-identityʳ : ∀ {A : Set} → (A × ⊤) ↔ A
×-identityʳ = mk↔ₛ′ proj₁ (λ x → x , tt) (λ _ → refl) (λ { (x , tt) → refl })

×-identityˡ : ∀ {A : Set} → (⊤ × A) ↔ A
×-identityˡ = mk↔ₛ′ proj₂ (λ x → tt , x) (λ _ → refl) (λ { (tt , x) → refl })

------------------------------------------------------------------------
-- Sequencing with Ignored Unit Separators
------------------------------------------------------------------------

-- Parse left operand and discard trailing unit token
_⨂ˡ_ : ∀ {A : Set} → InvertibleParser A → InvertibleParser ⊤ → InvertibleParser A
p₁ ⨂ˡ p₂ = mapIso (p₁ ⨂ p₂) ×-identityʳ

-- Discard leading unit token and parse right operand
_⨂ʳ_ : ∀ {B : Set} → InvertibleParser ⊤ → InvertibleParser B → InvertibleParser B
p₁ ⨂ʳ p₂ = mapIso (p₁ ⨂ p₂) ×-identityˡ

infixr 6 _⨂ˡ_ _⨂ʳ_

------------------------------------------------------------------------
-- Delimited / Bracketed Combinators
------------------------------------------------------------------------

-- Parse content enclosed between open and close tokens
between : ∀ {A : Set} → InvertibleParser ⊤ → InvertibleParser ⊤ → InvertibleParser A → InvertibleParser A
between openP closeP p = openP ⨂ʳ (p ⨂ˡ closeP)

-- Enclosed in square brackets `[ ... ]`
brackets : ∀ {A : Set} → InvertibleParser A → InvertibleParser A
brackets = between (litChar '[') (litChar ']')

-- Enclosed in curly braces `{ ... }`
braces : ∀ {A : Set} → InvertibleParser A → InvertibleParser A
braces = between (litChar '{') (litChar '}')

------------------------------------------------------------------------
-- Invertible String Literal Parser
------------------------------------------------------------------------

litString : List Char → InvertibleParser ⊤
litString []       = unitP
litString (c ∷ cs) = litChar c ⨂ʳ litString cs
