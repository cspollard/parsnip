{-# OPTIONS --safe --cubical-compatible #-}



module Data.Invertible.Core where

open import Level using (0ℓ)
open import Data.Char using (Char)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; _$_)
open import Function.Bundles using (Inverse; _↔_)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

------------------------------------------------------------------------
-- The Invertible Parser Type
------------------------------------------------------------------------

-- An InvertibleParser couples a prefix parser with a serializer,
-- equipped with a formal proof that parsing the printed output
-- recovers the original value and preserves trailing input.
record InvertibleParser (A : Set) : Set where
  constructor mkParser
  field
    parse   : List Char → Maybe (A × List Char)
    print   : A → List Char
    correct : ∀ (x : A) (rest : List Char) →
              parse (print x ++ rest) ≡ just (x , rest)

open InvertibleParser public

------------------------------------------------------------------------
-- Exact (Whole-String) Parsing
------------------------------------------------------------------------

parseExact : ∀ {A} → InvertibleParser A → List Char → Maybe A
parseExact p input with parse p input
... | just (x , [])    = just x
... | just (_ , _ ∷ _) = nothing
... | nothing          = nothing

-- Whole-string round-trip theorem
roundTripExact : ∀ {A} (p : InvertibleParser A) (x : A) →
                 parseExact p (print p x) ≡ just x
roundTripExact p x with parse p (print p x)
  | trans (cong (parse p) (sym (++-identityʳ (print p x)))) (correct p x [])
... | .(just (x , [])) | refl = refl

------------------------------------------------------------------------
-- Standard Library LeftInverse Derivation
------------------------------------------------------------------------

open import Function.Bundles using (LeftInverse; _↩_; mk↩)

-- Total parser with default fallback value
parseExactTotal : ∀ {A} → InvertibleParser A → A → List Char → A
parseExactTotal p default cs with parseExact p cs
... | just x  = x
... | nothing = default

-- Retraction lemma: parseExactTotal p default (print p x) ≡ x
parserRetraction : ∀ {A} (p : InvertibleParser A) (default : A) (x : A) →
                   parseExactTotal p default (print p x) ≡ x
parserRetraction p default x with parseExact p (print p x) | roundTripExact p x
... | .(just x) | refl = refl

-- Closed LeftInverse bundle from any InvertibleParser with a default witness
toLeftInverse : ∀ {A} → InvertibleParser A → A → (List Char ↩ A)
toLeftInverse p default = mk↩ {to = parseExactTotal p default} {from = print p}
  (λ { refl → parserRetraction p default _ })


------------------------------------------------------------------------
-- Combinators
------------------------------------------------------------------------

-- Trivial parser for unit consuming no input and producing no output
unitP : InvertibleParser ⊤
unitP = mkParser
  (λ rest → just (tt , rest))
  (λ _ → [])
  (λ tt rest → refl)


-- Sequential composition of invertible parsers (_⨂_)
_⨂_ : ∀ {A B : Set} → InvertibleParser A → InvertibleParser B → InvertibleParser (A × B)
_⨂_ {A} {B} p₁ p₂ = mkParser parseSeq printSeq correctSeq

  where
  parseSeq : List Char → Maybe ((A × B) × List Char)
  parseSeq input with parse p₁ input
  ... | nothing          = nothing
  ... | just (a , rest₁) with parse p₂ rest₁
  ...   | nothing          = nothing
  ...   | just (b , rest₂) = just ((a , b) , rest₂)

  printSeq : A × B → List Char
  printSeq (a , b) = print p₁ a ++ print p₂ b

  correctSeq : ∀ (pair : A × B) (rest : List Char) →
               parseSeq (printSeq pair ++ rest) ≡ just (pair , rest)
  correctSeq (a , b) rest =
    let input = (print p₁ a ++ print p₂ b) ++ rest
        p₁-goal = parse p₁ (print p₁ a ++ (print p₂ b ++ rest))
    in begin
      parseSeq input
        ≡⟨ cong parseSeq (++-assoc (print p₁ a) (print p₂ b) rest) ⟩
      parseSeq (print p₁ a ++ (print p₂ b ++ rest))

        ≡⟨ step₁ ⟩
      just ((a , b) , rest)
    ∎
    where
    open ≡-Reasoning

    step₁ : parseSeq (print p₁ a ++ (print p₂ b ++ rest)) ≡ just ((a , b) , rest)
    step₁ with parse p₁ (print p₁ a ++ (print p₂ b ++ rest)) | correct p₁ a (print p₂ b ++ rest)
    ... | .(just (a , print p₂ b ++ rest)) | refl with parse p₂ (print p₂ b ++ rest) | correct p₂ b rest
    ...   | .(just (b , rest)) | refl = refl

-- Iso mapping: transport an invertible parser across a bijection
mapIso : ∀ {A B : Set} → InvertibleParser A → (A ↔ B) → InvertibleParser B
mapIso {A} {B} p iso = mkParser parseIso printIso correctIso
  where
  open Inverse iso

  parseIso : List Char → Maybe (B × List Char)
  parseIso input with parse p input
  ... | nothing         = nothing
  ... | just (a , rest) = just (to a , rest)

  printIso : B → List Char
  printIso b = print p (from b)

  correctIso : ∀ (b : B) (rest : List Char) →
               parseIso (printIso b ++ rest) ≡ just (b , rest)
  correctIso b rest with parse p (print p (from b) ++ rest) | correct p (from b) rest
  ... | .(just (from b , rest)) | refl = cong (λ x → just (x , rest)) (strictlyInverseˡ b)
