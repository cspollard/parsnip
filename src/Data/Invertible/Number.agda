{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

module GeoAgda.Parsing.Invertible.Number where

open import Level using (0ℓ)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _*_) renaming (_+_ to _+ℕ_)
open import Data.Fin.Base as Fin using (Fin; zero; suc; toℕ)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; 0ℤ)
open import Data.Sign.Base as Sign using (Sign; +; -)
open import Data.Char.Base using (Char)
open import Data.List.Base as List using (List; []; _∷_; _++_; reverse)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Unit.Base using (⊤; tt)
open import Function.Base using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; refl; sym; trans; cong)

open import GeoAgda.Data.JSON.AST using (JSONNumber; jsonNumber)
open import GeoAgda.Parsing.Invertible.Core
open import GeoAgda.Parsing.Invertible.Char using (parseDigit; printDigit; parsePrintDigit)

------------------------------------------------------------------------
-- Positional Arithmetic: Digits to Natural Numbers
------------------------------------------------------------------------

-- Convert a list of base-10 digits (most significant first) to ℕ via Horner's rule
digitsToNatAcc : ℕ → List (Fin 10) → ℕ
digitsToNatAcc acc []       = acc
digitsToNatAcc acc (d ∷ ds) = digitsToNatAcc ((acc * 10) +ℕ (toℕ d)) ds

digitsToNat : List (Fin 10) → ℕ
digitsToNat = digitsToNatAcc 0

------------------------------------------------------------------------
-- Integer Conversions
------------------------------------------------------------------------

signNatToℤ : Sign → ℕ → ℤ
signNatToℤ + n       = +_ n
signNatToℤ - zero    = 0ℤ


signNatToℤ - (suc n) = -[1+ n ]

ℤToSignNat : ℤ → Sign × ℕ
ℤToSignNat (+_ n)    = (+ , n)
ℤToSignNat -[1+ n ]  = (- , suc n)


------------------------------------------------------------------------
-- Parsing Sequences of Digits
------------------------------------------------------------------------

-- Parse consecutive digits until a non-digit character is encountered
parseDigitsLoop : List Char → List (Fin 10) × List Char
parseDigitsLoop []       = ([] , [])
parseDigitsLoop (c ∷ cs) with parseDigit c
... | nothing = ([] , c ∷ cs)
... | just d  with parseDigitsLoop cs
...   | (ds , rest) = (d ∷ ds , rest)

-- Parse at least one digit
parseDigits1 : List Char → Maybe (List (Fin 10) × List Char)
parseDigits1 []       = nothing
parseDigits1 (c ∷ cs) with parseDigit c
... | nothing = nothing
... | just d  with parseDigitsLoop cs
...   | (ds , rest) = just (d ∷ ds , rest)

-- Print a list of digits to characters
printDigits : List (Fin 10) → List Char
printDigits []       = []
printDigits (d ∷ ds) = printDigit d ∷ printDigits ds

-- Correctness of digit sequence parsing over printed output
correctDigitsLoop : ∀ (ds : List (Fin 10)) (rest : List Char) →
  (c : Char) → (parseDigit c ≡ nothing) →
  parseDigitsLoop (printDigits ds ++ (c ∷ rest)) ≡ (ds , c ∷ rest)
correctDigitsLoop [] rest c noD rewrite noD = refl

correctDigitsLoop (d ∷ ds) rest c noD
  rewrite parsePrintDigit d
  rewrite correctDigitsLoop ds rest c noD = refl

------------------------------------------------------------------------
-- Sign Parser
------------------------------------------------------------------------

parseSign : List Char → Sign × List Char
parseSign ('-' ∷ cs) = (- , cs)
parseSign ('+' ∷ cs) = (+ , cs)
parseSign cs         = (+ , cs)

printSign : Sign → List Char
printSign + = []
printSign - = '-' ∷ []
