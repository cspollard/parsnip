{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

module GeoAgda.Parsing.Invertible.Char where

open import Level using (0ℓ)
open import Data.Char.Base using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
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
printDigit (zero)                                         = '0'
printDigit (suc zero)                                     = '1'
printDigit (suc (suc zero))                               = '2'
printDigit (suc (suc (suc zero)))                         = '3'
printDigit (suc (suc (suc (suc zero))))                   = '4'
printDigit (suc (suc (suc (suc (suc zero)))))             = '5'
printDigit (suc (suc (suc (suc (suc (suc zero))))))       = '6'
printDigit (suc (suc (suc (suc (suc (suc (suc zero))))))) = '7'
printDigit (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = '8'
printDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = '9'

-- Parse an ASCII character into a Fin 10 digit
parseDigit : Char → Maybe (Fin 10)
parseDigit '0' = just (zero)
parseDigit '1' = just (suc zero)
parseDigit '2' = just (suc (suc zero))
parseDigit '3' = just (suc (suc (suc zero)))
parseDigit '4' = just (suc (suc (suc (suc zero))))
parseDigit '5' = just (suc (suc (suc (suc (suc zero)))))
parseDigit '6' = just (suc (suc (suc (suc (suc (suc zero))))))
parseDigit '7' = just (suc (suc (suc (suc (suc (suc (suc zero)))))))
parseDigit '8' = just (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
parseDigit '9' = just (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
parseDigit _   = nothing

-- Proof that parsing the printed digit recovers the original Fin 10
parsePrintDigit : ∀ (d : Fin 10) → parseDigit (printDigit d) ≡ just d
parsePrintDigit zero                                         = refl
parsePrintDigit (suc zero)                                     = refl
parsePrintDigit (suc (suc zero))                               = refl
parsePrintDigit (suc (suc (suc zero)))                         = refl
parsePrintDigit (suc (suc (suc (suc zero))))                   = refl
parsePrintDigit (suc (suc (suc (suc (suc zero)))))             = refl
parsePrintDigit (suc (suc (suc (suc (suc (suc zero))))))       = refl
parsePrintDigit (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
parsePrintDigit (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl
parsePrintDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = refl

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


