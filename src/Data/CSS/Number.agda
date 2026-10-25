{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- CSS numbers: representation, printer and lexer
--
-- A number is `sign integral . fraction`, exactly as in
-- `Data.JSON.Number` but without an exponent: the strict subset has no
-- scientific notation (`1e3` lexes as the dimension `1` with unit
-- `e3`).  The printer and the digit lemmas are those of
-- `Data.Number.Digits`; the lexer differs from JSON's in that a `.` is
-- part of the number only if a digit follows it (`1.` is `1` and a
-- delimiter), and in that `.5` is a number.
--
-- `lexNumber-print` is the prefix round trip: the number is read back
-- from its printed form, followed by any text that does not continue a
-- number (does not start with a digit or a `.`).
------------------------------------------------------------------------

module Data.CSS.Number where

open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sign using (Sign)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Data.Invertible.Char using (parseDigit; printDigit; parsePrintDigit)
open import Data.Number.Digits

record CSSNumber : Set where
  constructor cssNumber
  field
    sign     : Sign
    integral : ℕ
    fraction : List (Fin 10)

printNumber : CSSNumber → List Char
printNumber (cssNumber s i f) = printSign s ++ printNat i ++ printFraction f

------------------------------------------------------------------------
-- Lexing
------------------------------------------------------------------------

-- A fraction: `.` and at least one digit.
lexFraction : List Char → List (Fin 10) × List Char
lexFraction₁ : Char → List Char → List (Fin 10) × List Char → List (Fin 10) × List Char

lexFraction []       = [] , []
lexFraction (c ∷ cs) with c ≟ '.'
... | no  _ = [] , c ∷ cs
... | yes _ = lexFraction₁ c cs (parseDigitsLoop cs)

lexFraction₁ c cs ([]     , _)    = [] , c ∷ cs
lexFraction₁ c cs (d ∷ ds , rest) = d ∷ ds , rest

-- An unsigned number: digits, then perhaps a fraction.  (`.5` is a number
-- with no integral digits.)
lexNumber : Sign → List Char → Maybe (CSSNumber × List Char)
lexNumber₁ : Sign → List (Fin 10) × List Char → Maybe (CSSNumber × List Char)
lexNumber₂ : Sign → List (Fin 10) → List (Fin 10) × List Char → Maybe (CSSNumber × List Char)

lexNumber s cs = lexNumber₁ s (parseDigitsLoop cs)

lexNumber₁ s (ds , rest) = lexNumber₂ s ds (lexFraction rest)

lexNumber₂ s []       ([] , _)   = nothing
lexNumber₂ s ds       (f , rest) = just (cssNumber s (digitsToNat ds) f , rest)

------------------------------------------------------------------------
-- Round trip
------------------------------------------------------------------------

private
  noDigit-printFraction : ∀ f rest → NoLeadingDigit rest → NoLeadingDigit (printFraction f ++ rest)
  noDigit-printFraction []      rest noD = noD
  noDigit-printFraction (d ∷ ds) rest _  = refl

  lexFraction-print : ∀ f rest → NoLeadingDigit rest → NoLeadingDot rest →
                      lexFraction (printFraction f ++ rest) ≡ (f , rest)
  lexFraction-print [] [] _ _ = refl
  lexFraction-print [] (c ∷ cs) _ nd with c ≟ '.'
  ... | yes _ = ⊥-elim nd
  ... | no  _ = refl
  lexFraction-print (d ∷ ds) rest noD _
    rewrite parsePrintDigit d
    rewrite correctDigitsLoopGen ds rest noD = refl

lexNumber-print : ∀ s i f rest → NoLeadingDigit rest → NoLeadingDot rest →
  lexNumber s ((printNat i ++ printFraction f) ++ rest) ≡ just (cssNumber s i f , rest)
lexNumber-print s i f rest noD noDot
  rewrite ++-assoc (printNat i) (printFraction f) rest
  with natToDigits i | digitsToNat-natToDigits i | natToDigits-nonEmpty i
... | []     | _     | ()
... | d ∷ ds | eqInt | _
  rewrite parsePrintDigit d
  rewrite correctDigitsLoopGen ds (printFraction f ++ rest) (noDigit-printFraction f rest noD)
  rewrite lexFraction-print f rest noD noDot
  rewrite eqInt = refl
