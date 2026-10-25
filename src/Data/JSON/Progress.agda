{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Every token consumes input
--
-- `lexToken-progress`: the rest after a token is strictly shorter than
-- the input.  This is what makes the tokenizer's fuel (one unit per
-- token) irrelevant once it exceeds the input length
-- (`Data.JSON.Lexer.tokenizeLoop-sound`).
------------------------------------------------------------------------

module Data.JSON.Progress where

open import Data.Char using (Char)
open import Data.Char.Fast using (_≟_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; m≤n+m)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sign as Sign using (Sign)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.Invertible.Char using (parseDigit)
open import Data.JSON.Keyword
open import Data.JSON.Number
open import Data.JSON.String using (lexBody; lookupBy; unescapes)
open import Data.JSON.Token

private
  ≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
  ≤-step p = ≤-trans p (n≤1+n _)

  -- `just` is injective, and so are the pair constructors we meet.
  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

------------------------------------------------------------------------
-- Numbers
------------------------------------------------------------------------

parseDigitsLoop-≤ : ∀ cs → length (proj₂ (parseDigitsLoop cs)) ≤ length cs
parseDigitsLoop-≤ []       = z≤n
parseDigitsLoop-≤ (c ∷ cs) with parseDigit c
... | nothing = ≤-refl
... | just d  with parseDigitsLoop cs | parseDigitsLoop-≤ cs
...   | (ds , rest) | ih = ≤-step ih

-- If a digit was read, the rest is strictly shorter.
parseDigitsLoop-< : ∀ cs d ds rest → parseDigitsLoop cs ≡ (d ∷ ds , rest) → length rest < length cs
parseDigitsLoop-< []       d ds rest ()
parseDigitsLoop-< (c ∷ cs) d ds rest h with parseDigit c
parseDigitsLoop-< (c ∷ cs) d ds rest () | nothing
... | just d′ with parseDigitsLoop cs | parseDigitsLoop-≤ cs
parseDigitsLoop-< (c ∷ cs) d ds rest refl | just d′ | (ds′ , rest′) | ih = s≤s ih

lexFraction-≤ : ∀ cs → length (proj₂ (lexFraction cs)) ≤ length cs
lexFraction-≤ []       = z≤n
lexFraction-≤ (c ∷ cs) with c ≟ '.'
... | yes _ = ≤-step (parseDigitsLoop-≤ cs)
... | no  _ = ≤-refl

lexExponentSign-≤ : ∀ cs → length (proj₂ (lexExponentSign cs)) ≤ length cs
lexExponentSign-≤ []       = z≤n
lexExponentSign-≤ (c ∷ cs) with c ≟ '-' | c ≟ '+'
... | yes _ | _     with parseDigitsLoop cs | parseDigitsLoop-≤ cs
...   | (ds , rest) | ih = ≤-step ih
lexExponentSign-≤ (c ∷ cs) | no _ | yes _ with parseDigitsLoop cs | parseDigitsLoop-≤ cs
...   | (ds , rest) | ih = ≤-step ih
lexExponentSign-≤ (c ∷ cs) | no _ | no  _ with parseDigitsLoop (c ∷ cs) | parseDigitsLoop-≤ (c ∷ cs)
...   | (ds , rest) | ih = ih

lexExponent-≤ : ∀ cs → length (proj₂ (lexExponent cs)) ≤ length cs
lexExponent-≤ []       = z≤n
lexExponent-≤ (c ∷ cs) with c ≟ 'e' | c ≟ 'E'
... | yes _ | _     = ≤-step (lexExponentSign-≤ cs)
... | no  _ | yes _ = ≤-step (lexExponentSign-≤ cs)
... | no  _ | no  _ = ≤-refl

lexNumber-< : ∀ s cs n rest → lexNumber s cs ≡ just (n , rest) → length rest < length cs
lexNumber-< s cs n rest h with parseDigitsLoop cs in eq
lexNumber-< s cs n rest () | ([] , _)
lexNumber-< s cs n rest h  | (d ∷ ds , rest₁)
  with lexFraction rest₁ | lexFraction-≤ rest₁
... | (frac , rest₂) | f≤
  with lexExponent rest₂ | lexExponent-≤ rest₂
lexNumber-< s cs n rest refl | (d ∷ ds , rest₁) | (frac , rest₂) | f≤ | (e , rest₃) | e≤ =
  ≤-trans (s≤s (≤-trans e≤ f≤)) (parseDigitsLoop-< cs d ds rest₁ eq)

------------------------------------------------------------------------
-- Strings
------------------------------------------------------------------------

lexBody-≤ : ∀ cs b rest → lexBody cs ≡ just (b , rest) → length rest ≤ length cs
lexBody-≤ []       b rest ()
lexBody-≤ (c ∷ cs) b rest h with c ≟ '"' | c ≟ '\\'
lexBody-≤ (c ∷ cs) b rest refl | yes _ | _ = n≤1+n _
lexBody-≤ (c ∷ cs) b rest h    | no _ | no _ with lexBody cs in eq
lexBody-≤ (c ∷ cs) b rest ()   | no _ | no _ | nothing
lexBody-≤ (c ∷ cs) .(c ∷ b′) rest refl | no _ | no _ | just (b′ , rest′) = ≤-step (lexBody-≤ cs b′ rest eq′)
  where eq′ = eq
lexBody-≤ (c ∷ [])     b rest ()   | no _ | yes _
lexBody-≤ (c ∷ d ∷ cs) b rest h    | no _ | yes _ with lookupBy unescapes d
lexBody-≤ (c ∷ d ∷ cs) b rest ()   | no _ | yes _ | nothing
lexBody-≤ (c ∷ d ∷ cs) b rest h    | no _ | yes _ | just x with lexBody cs in eq
lexBody-≤ (c ∷ d ∷ cs) b rest ()   | no _ | yes _ | just x | nothing
lexBody-≤ (c ∷ d ∷ cs) .(x ∷ b′) rest refl | no _ | yes _ | just x | just (b′ , rest′) =
  ≤-step (≤-step (lexBody-≤ cs b′ rest eq))

------------------------------------------------------------------------
-- Keywords
------------------------------------------------------------------------

stripPrefix-len : ∀ xs ys zs → stripPrefix xs ys ≡ just zs →
                  length ys ≡ length xs + length zs
stripPrefix-len []       ys       zs refl = refl
stripPrefix-len (x ∷ xs) []       zs ()
stripPrefix-len (x ∷ xs) (y ∷ ys) zs h with x ≟ y
... | yes _ = cong suc (stripPrefix-len xs ys zs h)
stripPrefix-len (x ∷ xs) (y ∷ ys) zs () | no _

keywordText-pos : ∀ k → Σ[ n ∈ ℕ ] length (keywordText k) ≡ suc n
keywordText-pos nullK  = 3 , refl
keywordText-pos trueK  = 3 , refl
keywordText-pos falseK = 4 , refl

lexKeywordFrom-< : ∀ ks cs k rest → lexKeywordFrom ks cs ≡ just (k , rest) → length rest < length cs
lexKeywordFrom-< []        cs k rest ()
lexKeywordFrom-< (k′ ∷ ks) cs k rest h with stripPrefix (keywordText k′) cs in eq
... | nothing = lexKeywordFrom-< ks cs k rest h
... | just rest′ with stripPrefix-len (keywordText k′) cs rest′ eq | keywordText-pos k′ | h
lexKeywordFrom-< (k′ ∷ ks) cs .k′ .rest′ h | just rest′ | len | n , pos | refl =
  subst (λ m → length rest′ < m) (sym (trans len (cong (_+ length rest′) pos)))
        (s≤s (m≤n+m (length rest′) n))

------------------------------------------------------------------------
-- Tokens
------------------------------------------------------------------------

private
  map-just : ∀ {A B : Set} (f : A → B) (m : Maybe A) {y} → Maybe.map f m ≡ just y →
             Σ[ x ∈ A ] m ≡ just x × f x ≡ y
  map-just f nothing  ()
  map-just f (just x) refl = x , refl , refl

lexMinus-progress : ∀ c cs d t rest → lexMinus c cs d ≡ just (t , rest) → length rest < suc (length cs)
lexQuote-progress : ∀ c cs d t rest → lexQuote c cs d ≡ just (t , rest) → length rest < suc (length cs)

lexQuote-progress c cs (yes _) t rest h with lexBody cs in eq
lexQuote-progress c cs (yes _) t rest () | nothing
lexQuote-progress c cs (yes _) .(stringT b) rest refl | just (b , rest′) = s≤s (lexBody-≤ cs b rest eq)
lexQuote-progress c cs (no  _) t rest h with lexKeyword (c ∷ cs) in eq
lexQuote-progress c cs (no  _) t rest () | nothing
lexQuote-progress c cs (no  _) t rest refl | just (nullK  , rest′) = lexKeywordFrom-< allKeywords (c ∷ cs) nullK  rest′ eq
lexQuote-progress c cs (no  _) t rest refl | just (trueK  , rest′) = lexKeywordFrom-< allKeywords (c ∷ cs) trueK  rest′ eq
lexQuote-progress c cs (no  _) t rest refl | just (falseK , rest′) = lexKeywordFrom-< allKeywords (c ∷ cs) falseK rest′ eq

lexMinus-progress c cs (yes _) t rest h with lexNumber Sign.- cs in eq
lexMinus-progress c cs (yes _) t rest () | nothing
lexMinus-progress c cs (yes _) .(numberT n) rest refl | just (n , rest′) = ≤-step (lexNumber-< Sign.- cs n rest′ eq)
lexMinus-progress c cs (no  _) t rest h = lexQuote-progress c cs (c ≟ '"') t rest h

lexPunct-progress : ∀ c cs mp t rest → lexPunct c cs mp ≡ just (t , rest) → length rest < suc (length cs)
lexPunct-progress c cs (just t′) .t′ .cs refl = ≤-refl
lexPunct-progress c cs nothing   t  rest h    = lexMinus-progress c cs (c ≟ '-') t rest h

lexToken′-progress : ∀ c cs m t rest → lexToken′ c cs m ≡ just (t , rest) → length rest < suc (length cs)
lexToken′-progress c cs (just _) t rest h with lexNumber Sign.+ (c ∷ cs) in eq
lexToken′-progress c cs (just _) t rest () | nothing
lexToken′-progress c cs (just _) .(numberT n) rest refl | just (n , rest′) = lexNumber-< Sign.+ (c ∷ cs) n rest′ eq
lexToken′-progress c cs nothing t rest h = lexPunct-progress c cs (punct c) t rest h

-- The rest after a token is strictly shorter than the input.
lexToken-progress : ∀ L t rest → lexToken L ≡ just (t , rest) → length rest < length L
lexToken-progress []       t rest ()
lexToken-progress (c ∷ cs) t rest h = lexToken′-progress c cs (parseDigit c) t rest h
