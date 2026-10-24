{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

module GeoAgda.Parsing.Invertible.Char where

open import Level using (0ℓ)
open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F; 8F; 9F)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Bundles using (Inverse; _↔_; mk↔ₛ′)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; refl; sym; trans; cong)

open import GeoAgda.Parsing.Invertible.Core

------------------------------------------------------------------------
-- Digit Encodings and Decoders
------------------------------------------------------------------------

-- Print a base-10 digit (Fin 10) to its corresponding ASCII character
printDigit : Fin 10 → Char
printDigit 0F = '0'
printDigit 1F = '1'
printDigit 2F = '2'
printDigit 3F = '3'
printDigit 4F = '4'
printDigit 5F = '5'
printDigit 6F = '6'
printDigit 7F = '7'
printDigit 8F = '8'
printDigit 9F = '9'

-- Parse an ASCII character into a Fin 10 digit
parseDigit : Char → Maybe (Fin 10)
parseDigit '0' = just 0F
parseDigit '1' = just 1F
parseDigit '2' = just 2F
parseDigit '3' = just 3F
parseDigit '4' = just 4F
parseDigit '5' = just 5F
parseDigit '6' = just 6F
parseDigit '7' = just 7F
parseDigit '8' = just 8F
parseDigit '9' = just 9F
parseDigit _   = nothing

-- Proof that parsing the printed digit recovers the original Fin 10
parsePrintDigit : ∀ (d : Fin 10) → parseDigit (printDigit d) ≡ just d
parsePrintDigit 0F = refl
parsePrintDigit 1F = refl
parsePrintDigit 2F = refl
parsePrintDigit 3F = refl
parsePrintDigit 4F = refl
parsePrintDigit 5F = refl
parsePrintDigit 6F = refl
parsePrintDigit 7F = refl
parsePrintDigit 8F = refl
parsePrintDigit 9F = refl

------------------------------------------------------------------------
-- Digit Parser
------------------------------------------------------------------------

digitParser : InvertibleParser (Fin 10)
digitParser = mkParser parseDigitPrefix printDigitList correctDigit
  where
  parseDigitPrefix : List Char → Maybe (Fin 10 × List Char)
  parseDigitPrefix []       = nothing
  parseDigitPrefix (c ∷ cs) with parseDigit c
  ... | just d  = just (d , cs)
  ... | nothing = nothing

  printDigitList : Fin 10 → List Char
  printDigitList d = printDigit d ∷ []

  correctDigit : ∀ (d : Fin 10) (rest : List Char) →
                 parseDigitPrefix (printDigitList d ++ rest) ≡ just (d , rest)
  correctDigit d rest rewrite parsePrintDigit d = refl

------------------------------------------------------------------------
-- Literal Character Parser
------------------------------------------------------------------------

litChar : (expected : Char) → InvertibleParser ⊤
litChar expected = mkParser parseLit printLit correctLit
  where
  parseLit : List Char → Maybe (⊤ × List Char)
  parseLit []       = nothing
  parseLit (c ∷ cs) with c ≟ expected
  ... | yes _ = just (tt , cs)
  ... | no  _ = nothing

  printLit : ⊤ → List Char
  printLit tt = expected ∷ []

  correctLit : ∀ (u : ⊤) (rest : List Char) →
               parseLit (printLit u ++ rest) ≡ just (u , rest)
  correctLit tt rest with expected ≟ expected
  ... | yes _ = refl
  ... | no  ¬p = ⊥-elim (¬p refl)


------------------------------------------------------------------------
-- Predicate: IsDigit & DigitChar Bijection
------------------------------------------------------------------------

-- Character is a decimal digit
record IsDigit (c : Char) : Set where
  constructor isDigitWitness
  field
    digitVal : Fin 10
    digitEq  : printDigit digitVal ≡ c

DigitChar : Set
DigitChar = ∃ IsDigit

toDigitChar : Fin 10 → DigitChar
toDigitChar d = printDigit d , isDigitWitness d refl

fromDigitChar : DigitChar → Fin 10
fromDigitChar (_ , isDigitWitness d _) = d

open import Function.Bundles using (Inverse; _↔_; mk↔ₛ′)

finDigitIso : Fin 10 ↔ DigitChar
finDigitIso = mk↔ₛ′ toDigitChar fromDigitChar
  (λ { (_ , isDigitWitness d refl) → refl })
  (λ _ → refl)


