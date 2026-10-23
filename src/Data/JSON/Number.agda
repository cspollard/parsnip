{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- JSON numbers (RFC 8259 §6): representation, printer and lexer
--
-- `printNumber` and `lexNumber` are related by `correctLexNumberSign`
-- (prefix round trip under a follow-condition) and, at the lexeme level,
-- by `numberStage`, a stdlib `RightInverse`.
------------------------------------------------------------------------

module Data.JSON.Number where

open import Level using (0ℓ)
open import Data.Nat as ℕ using (ℕ; zero; suc; _*_; _≤′_; ≤′-refl; ≤′-step; NonZero; nonZero) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; *-identityʳ; *-distribˡ-+; *-comm; m≤m+n; ≤⇒≤′; module ≤-Reasoning)
open import Data.Nat.Induction using (<′-Rec; <′-rec)
open import Data.Nat.DivMod using (DivMod; result; _divMod_)
open import Data.Digit using (Expansion; fromDigits; toDigits)
open import Data.Fin as Fin using (Fin; zero; suc; toℕ)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; 0ℤ)
open import Data.Sign as Sign using (Sign; +; -)
open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.List as List using (List; []; _∷_; _++_; reverse; _∷ʳ_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; unfold-reverse; reverse-++; length-reverse)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_; _$_)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import GeoAgda.Parsing.Invertible.Char using (parseDigit; printDigit; parsePrintDigit)

------------------------------------------------------------------------
-- Exact representation of JSON numbers according to RFC 8259:
--   sign * (integral + fraction * 10^(- length fraction)) * 10^exponent
------------------------------------------------------------------------

record JSONNumber : Set where
  constructor jsonNumber
  field
    sign     : Sign
    integral : ℕ
    fraction : List (Fin 10)
    exponent : ℤ

------------------------------------------------------------------------
-- Base-10 Digit Conversion & Round-Trip Properties
------------------------------------------------------------------------

digitsToNatAcc : ℕ → List (Fin 10) → ℕ
digitsToNatAcc acc []       = acc
digitsToNatAcc acc (d ∷ ds) = digitsToNatAcc ((acc * 10) +ℕ (toℕ d)) ds

digitsToNat : List (Fin 10) → ℕ
digitsToNat = digitsToNatAcc 0

digitsToNatAcc-++ : ∀ acc xs ys → digitsToNatAcc acc (xs ++ ys) ≡ digitsToNatAcc (digitsToNatAcc acc xs) ys
digitsToNatAcc-++ acc []       ys = refl
digitsToNatAcc-++ acc (x ∷ xs) ys = digitsToNatAcc-++ ((acc * 10) +ℕ toℕ x) xs ys

digitsToNatAcc-snoc : ∀ acc xs d → digitsToNatAcc acc (xs ++ (d ∷ [])) ≡ (digitsToNatAcc acc xs * 10) +ℕ toℕ d
digitsToNatAcc-snoc acc xs d = digitsToNatAcc-++ acc xs (d ∷ [])

digitsToNat-reverse : ∀ (ds : List (Fin 10)) → digitsToNat (reverse ds) ≡ fromDigits ds
digitsToNat-reverse []       = refl
digitsToNat-reverse (d ∷ ds) = begin
  digitsToNat (reverse (d ∷ ds))
    ≡⟨ cong digitsToNat (unfold-reverse d ds) ⟩
  digitsToNat (reverse ds ++ (d ∷ []))
    ≡⟨ digitsToNatAcc-snoc 0 (reverse ds) d ⟩
  (digitsToNat (reverse ds) * 10) +ℕ toℕ d
    ≡⟨ cong (λ x → (x * 10) +ℕ toℕ d) (digitsToNat-reverse ds) ⟩
  (fromDigits ds * 10) +ℕ toℕ d
    ≡⟨ +-comm (fromDigits ds * 10) (toℕ d) ⟩
  toℕ d +ℕ (fromDigits ds * 10)
  ∎
  where open ≡-Reasoning

NonEmptyList : ∀ {A : Set} → List A → Set
NonEmptyList []      = ⊥
NonEmptyList (_ ∷ _) = ⊤

nonEmpty-++ : ∀ {A : Set} (xs ys : List A) → NonEmptyList xs → NonEmptyList (xs ++ ys)
nonEmpty-++ []       _ ()
nonEmpty-++ (x ∷ xs) _ _ = tt

nonEmpty-reverse : ∀ {A : Set} (xs : List A) → NonEmptyList xs → NonEmptyList (reverse xs)
nonEmpty-reverse []       ()
nonEmpty-reverse (x ∷ xs) _ with reverse xs | unfold-reverse x xs
... | []     | eq rewrite eq = tt
... | y ∷ ys | eq rewrite eq = tt

-- Base-10 digit expansion with non-emptiness packaged in the predicate
toDigits10 : (n : ℕ) → ∃ λ (ds : Expansion 10) → (fromDigits ds ≡ n) × NonEmptyList ds
toDigits10 n = <′-rec Pred helper n
  where
  Pred : ℕ → Set
  Pred m = ∃ λ (ds : Expansion 10) → (fromDigits ds ≡ m) × NonEmptyList ds

  lem′ : ∀ x k → (x +ℕ x) +ℕ (k +ℕ (x * k)) ≡ k +ℕ (x * (2 +ℕ k))
  lem′ x k = begin
    (x +ℕ x) +ℕ (k +ℕ (x * k))   ≡⟨ sym (+-assoc (x +ℕ x) k (x * k)) ⟩
    ((x +ℕ x) +ℕ k) +ℕ (x * k)   ≡⟨ cong (_+ℕ (x * k)) (+-comm (x +ℕ x) k) ⟩
    (k +ℕ (x +ℕ x)) +ℕ (x * k)   ≡⟨ +-assoc k (x +ℕ x) (x * k) ⟩
    k +ℕ ((x +ℕ x) +ℕ (x * k))   ≡⟨ cong (k +ℕ_) (begin
      (x +ℕ x) +ℕ (x * k)       ≡⟨ +-assoc x x (x * k) ⟩
      x +ℕ (x +ℕ (x * k))       ≡⟨ cong (λ z → x +ℕ (z +ℕ (x * k))) (sym (*-identityʳ x)) ⟩
      x +ℕ ((x * 1) +ℕ (x * k)) ≡⟨ cong₂ _+ℕ_ (sym (*-identityʳ x)) (sym (*-distribˡ-+ x 1 k)) ⟩
      (x * 1) +ℕ (x * suc k)    ≡⟨ sym (*-distribˡ-+ x 1 (suc k)) ⟩
      x * (2 +ℕ k)              ∎) ⟩
    k +ℕ (x * (2 +ℕ k))          ∎
    where open ≡-Reasoning

  lem : ∀ x r → (2 +ℕ x) ≤′ (r +ℕ ((1 +ℕ x) * 10))
  lem x r = ≤⇒≤′ $ begin
    2 +ℕ x                                  ≤⟨ m≤m+n (2 +ℕ x) ((x +ℕ ((1 +ℕ x) * 8)) +ℕ r) ⟩
    (2 +ℕ x) +ℕ ((x +ℕ ((1 +ℕ x) * 8)) +ℕ r) ≡⟨ cong ((2 +ℕ x) +ℕ_) (+-comm (x +ℕ ((1 +ℕ x) * 8)) r) ⟩
    (2 +ℕ x) +ℕ (r +ℕ (x +ℕ ((1 +ℕ x) * 8))) ≡⟨ sym (+-assoc (2 +ℕ x) r (x +ℕ ((1 +ℕ x) * 8))) ⟩
    ((2 +ℕ x) +ℕ r) +ℕ (x +ℕ ((1 +ℕ x) * 8)) ≡⟨ cong (_+ℕ (x +ℕ ((1 +ℕ x) * 8))) (+-comm (2 +ℕ x) r) ⟩
    (r +ℕ (2 +ℕ x)) +ℕ (x +ℕ ((1 +ℕ x) * 8)) ≡⟨ +-assoc r (2 +ℕ x) (x +ℕ ((1 +ℕ x) * 8)) ⟩
    r +ℕ ((2 +ℕ x) +ℕ (x +ℕ ((1 +ℕ x) * 8))) ≡⟨ cong (r +ℕ_) (cong (λ z → 2 +ℕ z) (sym (+-assoc x x ((1 +ℕ x) * 8)))) ⟩
    r +ℕ (2 +ℕ ((x +ℕ x) +ℕ ((1 +ℕ x) * 8))) ≡⟨ cong (λ z → r +ℕ (2 +ℕ z)) (lem′ x 8) ⟩
    r +ℕ (2 +ℕ (8 +ℕ (x * 10)))              ≡⟨⟩
    r +ℕ ((1 +ℕ x) * 10)                     ∎
    where open ≤-Reasoning

  helper : ∀ m → <′-Rec Pred m → Pred m
  helper m rec with m divMod 10
  ... | result zero    r eq   = (r ∷ [] , sym eq , tt)
  ... | result (suc x) r refl =
    let (ds , eq , _) = rec (lem x (toℕ r))
    in (r ∷ ds , cong (λ i → toℕ r +ℕ (i * 10)) eq , tt)

natToDigits : ℕ → List (Fin 10)
natToDigits n = reverse (proj₁ (toDigits10 n))

digitsToNat-natToDigits : ∀ n → digitsToNat (natToDigits n) ≡ n
digitsToNat-natToDigits n = trans (digitsToNat-reverse (proj₁ (toDigits10 n))) (proj₁ (proj₂ (toDigits10 n)))

natToDigits-nonEmpty : ∀ n → NonEmptyList (natToDigits n)
natToDigits-nonEmpty n = nonEmpty-reverse (proj₁ (toDigits10 n)) (proj₂ (proj₂ (toDigits10 n)))

------------------------------------------------------------------------
-- Digit Stream Parsing & Printing
------------------------------------------------------------------------

parseDigitsLoop : List Char → List (Fin 10) × List Char
parseDigitsLoop []       = ([] , [])
parseDigitsLoop (c ∷ cs) with parseDigit c
... | nothing = ([] , c ∷ cs)
... | just d  with parseDigitsLoop cs
...   | (ds , rest) = (d ∷ ds , rest)

printDigits : List (Fin 10) → List Char
printDigits []       = []
printDigits (d ∷ ds) = printDigit d ∷ printDigits ds

correctDigitsLoop[] : ∀ (ds : List (Fin 10)) →
  parseDigitsLoop (printDigits ds) ≡ (ds , [])
correctDigitsLoop[] [] = refl
correctDigitsLoop[] (d ∷ ds)
  rewrite parsePrintDigit d
  rewrite correctDigitsLoop[] ds = refl

correctDigitsLoop : ∀ (ds : List (Fin 10)) (rest : List Char) →
  (c : Char) → (parseDigit c ≡ nothing) →
  parseDigitsLoop (printDigits ds ++ (c ∷ rest)) ≡ (ds , c ∷ rest)
correctDigitsLoop [] rest c noD rewrite noD = refl
correctDigitsLoop (d ∷ ds) rest c noD
  rewrite parsePrintDigit d
  rewrite correctDigitsLoop ds rest c noD = refl

NoLeadingDigit : List Char → Set
NoLeadingDigit []       = ⊤
NoLeadingDigit (c ∷ _)  = parseDigit c ≡ nothing

correctDigitsLoopGen : ∀ (ds : List (Fin 10)) (rest : List Char) →
  NoLeadingDigit rest →
  parseDigitsLoop (printDigits ds ++ rest) ≡ (ds , rest)
correctDigitsLoopGen ds []       _   rewrite ++-identityʳ (printDigits ds) = correctDigitsLoop[] ds
correctDigitsLoopGen ds (c ∷ cs) noD = correctDigitsLoop ds cs c noD

------------------------------------------------------------------------
-- Number Delimiter Predicates & Formatting
------------------------------------------------------------------------

NoLeadingExp : List Char → Set
NoLeadingExp []        = ⊤
NoLeadingExp (c ∷ _) with c ≟ 'e' | c ≟ 'E'
... | yes _ | _     = ⊥
... | no  _ | yes _ = ⊥
... | no  _ | no  _ = ⊤

NoLeadingDot : List Char → Set
NoLeadingDot []        = ⊤
NoLeadingDot (c ∷ _) with c ≟ '.'
... | yes _ = ⊥
... | no  _ = ⊤

NoLeadingNumCont : List Char → Set
NoLeadingNumCont cs = NoLeadingDigit cs × NoLeadingDot cs × NoLeadingExp cs

signNatToℤ : Sign → ℕ → ℤ
signNatToℤ + n       = +_ n
signNatToℤ - zero    = 0ℤ
signNatToℤ - (suc n) = -[1+ n ]

printSign : Sign → List Char
printSign + = []
printSign - = '-' ∷ []

printNat : ℕ → List Char
printNat n = printDigits (natToDigits n)

printFraction : List (Fin 10) → List Char
printFraction []       = []
printFraction (d ∷ ds) = '.' ∷ printDigits (d ∷ ds)

printExponent : ℤ → List Char
printExponent (+_ zero)    = []
printExponent (+_ (suc n)) = 'e' ∷ '+' ∷ printNat (suc n)
printExponent -[1+ n ]     = 'e' ∷ '-' ∷ printNat (suc n)

printNumber : JSONNumber → List Char
printNumber n =
  printSign (JSONNumber.sign n) ++
  printNat (JSONNumber.integral n) ++
  printFraction (JSONNumber.fraction n) ++
  printExponent (JSONNumber.exponent n)

------------------------------------------------------------------------
-- Number Lexing & Round-Trip Proofs
------------------------------------------------------------------------

lexFraction : List Char → List (Fin 10) × List Char
lexFraction []       = ([] , [])
lexFraction (c ∷ cs) with c ≟ '.'
... | yes _ = parseDigitsLoop cs
... | no  _ = ([] , c ∷ cs)

lexExponentSign : List Char → ℤ × List Char
lexExponentSign [] = (0ℤ , [])
lexExponentSign (c ∷ cs) with c ≟ '-' | c ≟ '+'
... | yes _ | _     with parseDigitsLoop cs
...   | (ds , rest) = (-[1+ ℕ.pred (digitsToNat ds) ] , rest)
lexExponentSign (c ∷ cs) | no _ | yes _ with parseDigitsLoop cs
...   | (ds , rest) = (+_ (digitsToNat ds) , rest)
lexExponentSign (c ∷ cs) | no _ | no  _ with parseDigitsLoop (c ∷ cs)
...   | (ds , rest) = (+_ (digitsToNat ds) , rest)

lexExponent : List Char → ℤ × List Char
lexExponent []       = (0ℤ , [])
lexExponent (c ∷ cs) with c ≟ 'e' | c ≟ 'E'
... | yes _ | _     = lexExponentSign cs
... | no  _ | yes _ = lexExponentSign cs
... | no  _ | no  _ = (0ℤ , c ∷ cs)

lexNumber : Sign → List Char → Maybe (JSONNumber × List Char)
lexNumber s cs with parseDigitsLoop cs
... | ([] , _) = nothing
... | (d ∷ ds , rest₁) with lexFraction rest₁
...   | (frac , rest₂) with lexExponent rest₂
...     | (exp , rest₃) = just (jsonNumber s (digitsToNat (d ∷ ds)) frac exp , rest₃)

noDigitPrintExponent : ∀ (e : ℤ) (rest : List Char) → NoLeadingDigit rest → NoLeadingDigit (printExponent e ++ rest)
noDigitPrintExponent (+_ zero)    rest noD = noD
noDigitPrintExponent (+_ (suc n)) rest _   = refl
noDigitPrintExponent -[1+ n ]     rest _   = refl

noDotPrintExponent : ∀ (e : ℤ) (rest : List Char) → NoLeadingDot rest → NoLeadingDot (printExponent e ++ rest)
noDotPrintExponent (+_ zero)    rest noDot = noDot
noDotPrintExponent (+_ (suc n)) rest _     = tt
noDotPrintExponent -[1+ n ]     rest _     = tt

noDigitPrintFraction : ∀ (frac : List (Fin 10)) (e : ℤ) (rest : List Char) →
                       NoLeadingDigit rest →
                       NoLeadingDigit (printFraction frac ++ printExponent e ++ rest)
noDigitPrintFraction []       e rest noD = noDigitPrintExponent e rest noD
noDigitPrintFraction (d ∷ ds) e rest _   = refl

correctLexExponent : ∀ (e : ℤ) (rest : List Char) →
                     NoLeadingDigit rest → NoLeadingExp rest →
                     lexExponent (printExponent e ++ rest) ≡ (e , rest)
correctLexExponent (+_ zero) [] _ _ = refl
correctLexExponent (+_ zero) (c ∷ cs) _ noExp with c ≟ 'e' | c ≟ 'E'
... | yes _ | _     = ⊥-elim noExp
... | no  _ | yes _ = ⊥-elim noExp
... | no  _ | no  _ = refl
correctLexExponent (+_ (suc n)) rest noD _
  rewrite correctDigitsLoopGen (natToDigits (suc n)) rest noD
  rewrite digitsToNat-natToDigits (suc n) = refl
correctLexExponent -[1+ n ] rest noD _
  rewrite correctDigitsLoopGen (natToDigits (suc n)) rest noD
  rewrite digitsToNat-natToDigits (suc n) = refl

correctLexFraction : ∀ (frac : List (Fin 10)) (e : ℤ) (rest : List Char) →
                     NoLeadingDigit rest → NoLeadingDot rest →
                     lexFraction (printFraction frac ++ printExponent e ++ rest) ≡ (frac , printExponent e ++ rest)
correctLexFraction [] e rest noD noDot with printExponent e ++ rest | noDotPrintExponent e rest noDot
... | []     | _     = refl
... | c ∷ cs | noDot' with c ≟ '.'
...   | yes _ = ⊥-elim noDot'
...   | no  _ = refl
correctLexFraction (d ∷ ds) e rest noD _
  rewrite parsePrintDigit d
  rewrite correctDigitsLoopGen ds (printExponent e ++ rest) (noDigitPrintExponent e rest noD) = refl

correctLexNumberSign : ∀ (s : Sign) (int : ℕ) (frac : List (Fin 10)) (exp : ℤ) (rest : List Char) →
  NoLeadingNumCont rest →
  lexNumber s ((printNat int ++ printFraction frac ++ printExponent exp) ++ rest) ≡
    just (jsonNumber s int frac exp , rest)
correctLexNumberSign s int frac exp rest (noD , noDot , noExp)
  rewrite ++-assoc (printNat int) (printFraction frac ++ printExponent exp) rest
  rewrite ++-assoc (printFraction frac) (printExponent exp) rest
  with natToDigits int | digitsToNat-natToDigits int | natToDigits-nonEmpty int
... | []     | _     | ()
... | d ∷ ds | eqInt | _
  rewrite parsePrintDigit d
  rewrite correctDigitsLoopGen ds (printFraction frac ++ printExponent exp ++ rest) (noDigitPrintFraction frac exp rest noD)
  rewrite correctLexFraction frac exp rest noD noDot
  rewrite correctLexExponent exp rest noD noExp
  rewrite eqInt = refl

------------------------------------------------------------------------
-- Lexeme-level stage
------------------------------------------------------------------------

open import Data.JSON.Stage using (Chars; mkStage)
open import Relation.Binary.PropositionalEquality using (setoid; subst)
open import Function.Bundles using (RightInverse)

-- A complete number lexeme: an optional `-` and then `lexNumber`.
-- Whatever follows the number is ignored; `lexNumber` is the prefix lexer.
parseNumber : List Char → Maybe JSONNumber
parseNumber []       = Maybe.map proj₁ (lexNumber + [])
parseNumber (c ∷ cs) with c ≟ '-'
... | yes _ = Maybe.map proj₁ (lexNumber - cs)
... | no  _ = Maybe.map proj₁ (lexNumber + (c ∷ cs))

private
  NonMinusHead : List Char → Set
  NonMinusHead []      = ⊤
  NonMinusHead (c ∷ _) = c ≡ '-' → ⊥

  parseNumber-+ : ∀ cs → NonMinusHead cs →
                  parseNumber cs ≡ Maybe.map proj₁ (lexNumber + cs)
  parseNumber-+ []       _  = refl
  parseNumber-+ (c ∷ cs) nm with c ≟ '-'
  ... | yes eq = ⊥-elim (nm eq)
  ... | no  _  = refl

  -- A printed natural number never starts with `-`: its first character
  -- is a digit, and `parseDigit '-'` is `nothing`.
  nonMinusHead-printNat : ∀ n rest → NonMinusHead (printNat n ++ rest)
  nonMinusHead-printNat n rest with natToDigits n | natToDigits-nonEmpty n
  ... | []     | ()
  ... | d ∷ ds | _ = not-minus
    where
    not-minus : printDigit d ≡ '-' → ⊥
    not-minus eq with trans (sym (parsePrintDigit d)) (cong parseDigit eq)
    ... | ()

  -- `correctLexNumberSign` at an empty continuation.
  lexPrinted : ∀ s i f e →
    Maybe.map proj₁ (lexNumber s (printNat i ++ printFraction f ++ printExponent e))
      ≡ just (jsonNumber s i f e)
  lexPrinted s i f e =
    subst (λ cs → Maybe.map proj₁ (lexNumber s cs) ≡ just (jsonNumber s i f e))
          (++-identityʳ (printNat i ++ printFraction f ++ printExponent e))
          (cong (Maybe.map proj₁)
                (correctLexNumberSign s i f e [] (tt , tt , tt)))

parseNumber-printNumber : ∀ n → parseNumber (printNumber n) ≡ just n
parseNumber-printNumber (jsonNumber - i f e) = lexPrinted - i f e
parseNumber-printNumber (jsonNumber + i f e) =
  trans (parseNumber-+ _ (nonMinusHead-printNat i _)) (lexPrinted + i f e)

-- `numberStage` (see `Data.JSON.Goals`).
numberStage : RightInverse (setoid JSONNumber) Chars
numberStage = mkStage (setoid JSONNumber) printNumber parseNumber
  (jsonNumber + 0 [] 0ℤ) (cong printNumber)
  (λ n → n , parseNumber-printNumber n , refl)
