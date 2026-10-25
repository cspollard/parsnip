{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Every token consumes input
--
-- `lexToken-progress`: the rest after a token is strictly shorter than
-- the input.  This is what makes the tokenizer's fuel (one unit per
-- token) irrelevant once it exceeds the input length
-- (`Data.CSS.Lexer.tokenizeLoop-sound`).
------------------------------------------------------------------------

module Data.CSS.Progress where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Char.Fast using (_≟_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; map₁)
open import Data.Sign as Sign using (Sign)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import Data.Invertible.Char using (parseDigit)
open import Data.Number.Digits using (parseDigitsLoop)
open import Data.Lexer.Span using (spanBy; spanBy′)
open import Data.CSS.Valid
open import Data.CSS.Number
open import Data.CSS.Escape
open import Data.CSS.Token

private
  ≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
  ≤-step p = ≤-trans p (n≤1+n _)

------------------------------------------------------------------------
-- Runs and numbers
------------------------------------------------------------------------

spanBy-≤ : ∀ p cs → length (proj₂ (spanBy p cs)) ≤ length cs
spanBy′-≤ : ∀ p c cs b → length (proj₂ (spanBy′ p c cs b)) ≤ suc (length cs)

spanBy-≤ p []       = z≤n
spanBy-≤ p (c ∷ cs) = spanBy′-≤ p c cs (p c)

spanBy′-≤ p c cs true  = ≤-step (spanBy-≤ p cs)
spanBy′-≤ p c cs false = ≤-refl

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

lexFraction₁-≤ : ∀ c cs dr → length (proj₂ dr) ≤ length cs →
                 length (proj₂ (lexFraction₁ c cs dr)) ≤ suc (length cs)
lexFraction₁-≤ c cs ([]     , _) _ = ≤-refl
lexFraction₁-≤ c cs (d ∷ ds , _) h = ≤-step h

lexFraction-≤ : ∀ cs → length (proj₂ (lexFraction cs)) ≤ length cs
lexFraction-≤ []       = z≤n
lexFraction-≤ (c ∷ cs) with c ≟ '.'
... | no  _ = ≤-refl
... | yes _ = lexFraction₁-≤ c cs (parseDigitsLoop cs) (parseDigitsLoop-≤ cs)

-- A non-empty fraction leaves strictly less.
lexFraction₁-< : ∀ c cs dr f fs rest → length (proj₂ dr) ≤ length cs →
                 lexFraction₁ c cs dr ≡ (f ∷ fs , rest) → length rest < suc (length cs)
lexFraction₁-< c cs ([]     , _)    f fs rest _ ()
lexFraction₁-< c cs (d ∷ ds , rest) f fs .rest h refl = s≤s h

lexFraction-< : ∀ cs f fs rest → lexFraction cs ≡ (f ∷ fs , rest) → length rest < length cs
lexFraction-< []       f fs rest ()
lexFraction-< (c ∷ cs) f fs rest h with c ≟ '.'
lexFraction-< (c ∷ cs) f fs rest () | no _
... | yes _ = lexFraction₁-< c cs (parseDigitsLoop cs) f fs rest (parseDigitsLoop-≤ cs) h

lexNumber-< : ∀ s cs n rest → lexNumber s cs ≡ just (n , rest) → length rest < length cs
lexNumber-< s cs n rest h with parseDigitsLoop cs in eq1
... | (ds , rest₁) with lexFraction rest₁ in eq2 | lexFraction-≤ rest₁
...   | (f , rest₂) | f≤ with ds | f | h
lexNumber-< s cs n rest h | (ds , rest₁) | (f , rest₂) | f≤ | [] | [] | ()
lexNumber-< s cs n rest h | (ds , rest₁) | (f , rest₂) | f≤ | [] | x ∷ xs | refl =
  ≤-trans (lexFraction-< rest₁ x xs rest eq2) (subst (λ q → length (proj₂ q) ≤ length cs) eq1 (parseDigitsLoop-≤ cs))
lexNumber-< s cs n rest h | (ds , rest₁) | (f , rest₂) | f≤ | d ∷ ds′ | _ | refl =
  ≤-trans (s≤s f≤) (parseDigitsLoop-< cs d ds′ rest₁ eq1)

------------------------------------------------------------------------
-- String bodies
------------------------------------------------------------------------

private
  map-cons : ∀ {c} (m : Maybe (List Char × List Char)) {b rest} →
             Maybe.map (map₁ (c ∷_)) m ≡ just (b , rest) → ∃ λ b′ → m ≡ just (b′ , rest)
  map-cons nothing         ()
  map-cons (just (b′ , r)) refl = b′ , refl

-- The rest of a decoded body is no longer than the input.
lexBody-≤       : ∀ stop cs b rest → lexBody stop cs ≡ just (b , rest) → length rest ≤ length cs
lexBodyHead-≤   : ∀ stop c cs b rest → lexBodyHead stop c cs ≡ just (b , rest) → length rest ≤ suc (length cs)
lexEsc-≤        : ∀ stop cs b rest → lexEsc stop cs ≡ just (b , rest) → length rest ≤ length cs
lexEsc′-≤       : ∀ stop d ds m b rest → lexEsc′ stop d ds m ≡ just (b , rest) → length rest ≤ suc (length ds)
lexHex-≤        : ∀ stop k acc cs b rest → lexHex stop k acc cs ≡ just (b , rest) → length rest ≤ length cs
lexHex′-≤       : ∀ stop k acc d ds m b rest → lexHex′ stop k acc d ds m ≡ just (b , rest) → length rest ≤ suc (length ds)
lexHexEnd-≤     : ∀ stop m w ws b rest → lexHexEnd stop m w ws ≡ just (b , rest) → length rest ≤ suc (length ws)
lexHexEnd′-≤    : ∀ stop x w ws q b rest → lexHexEnd′ stop x w ws q ≡ just (b , rest) → length rest ≤ suc (length ws)

lexBody-≤ stop []       b rest ()
lexBody-≤ stop (c ∷ cs) b rest h = lexBodyHead-≤ stop c cs b rest h

lexBodyHead-≤ stop c cs b rest h with c ≟ stop
lexBodyHead-≤ stop c cs .[] .(c ∷ cs) refl | yes _ = ≤-refl
... | no _ with c ≟ '\\'
...   | yes _ = ≤-step (lexEsc-≤ stop cs b rest h)
...   | no  _ with c ≟ '\n'
lexBodyHead-≤ stop c cs b rest () | no _ | no _ | yes _
...     | no  _ with map-cons (lexBody stop cs) h
...       | b′ , eq = ≤-step (lexBody-≤ stop cs b′ rest eq)

lexEsc-≤ stop []       b rest ()
lexEsc-≤ stop (d ∷ ds) b rest h = lexEsc′-≤ stop d ds (hexVal d) b rest h

lexEsc′-≤ stop d ds (just v) b rest h = ≤-step (lexHex-≤ stop 5 v ds b rest h)
lexEsc′-≤ stop d ds nothing  b rest h with d ≟ '\n'
lexEsc′-≤ stop d ds nothing  b rest () | yes _
... | no _ with map-cons (lexBody stop ds) h
...   | b′ , eq = ≤-step (lexBody-≤ stop ds b′ rest eq)

lexHex-≤ stop k       acc []       b rest ()
lexHex-≤ stop zero    acc (w ∷ ws) b rest h = lexHexEnd-≤ stop (fromCode acc) w ws b rest h
lexHex-≤ stop (suc k) acc (d ∷ ds) b rest h = lexHex′-≤ stop k acc d ds (hexVal d) b rest h

lexHex′-≤ stop k acc d ds (just v) b rest h = ≤-step (lexHex-≤ stop k _ ds b rest h)
lexHex′-≤ stop k acc d ds nothing  b rest h = lexHexEnd-≤ stop (fromCode acc) d ds b rest h

lexHexEnd-≤ stop nothing  w ws b rest ()
lexHexEnd-≤ stop (just x) w ws b rest h = lexHexEnd′-≤ stop x w ws (isWs w) b rest h

lexHexEnd′-≤ stop x w ws true  b rest h with map-cons (lexBody stop ws) h
... | b′ , eq = ≤-step (lexBody-≤ stop ws b′ rest eq)
lexHexEnd′-≤ stop x w ws false b rest h with map-cons (lexBodyHead stop w ws) h
... | b′ , eq = lexBodyHead-≤ stop w ws b′ rest eq

------------------------------------------------------------------------
-- Tokens
------------------------------------------------------------------------

private
  drop₁-≤ : ∀ cs → length (drop₁ cs) ≤ length cs
  drop₁-≤ []       = z≤n
  drop₁-≤ (_ ∷ cs) = n≤1+n _

lexNumTok₂-≤ : ∀ x rest b₁ b₂ t r → lexNumTok₂ x rest b₁ b₂ ≡ just (t , r) → length r ≤ length rest
lexNumTok₂-≤ x rest true  _     t r refl = drop₁-≤ rest
lexNumTok₂-≤ x rest false true  t r refl = spanBy-≤ isIdentChar rest
lexNumTok₂-≤ x rest false false t r refl = ≤-refl

lexNumTok₁-< : ∀ (cs : List Char) m t r → (∀ n r′ → m ≡ just (n , r′) → length r′ < length cs) →
               lexNumTok₁ m ≡ just (t , r) → length r < length cs
lexNumTok₁-< cs nothing           t r _ ()
lexNumTok₁-< cs (just (x , rest)) t r f h =
  ≤-trans (s≤s (lexNumTok₂-≤ x rest (percentK (headCls rest)) (startsIdent rest) t r h)) (f x rest refl)

-- A number and what follows it consume input.
lexNumTok-< : ∀ s cs t r → lexNumTok s cs ≡ just (t , r) → length r < length cs
lexNumTok-< s cs t r = lexNumTok₁-< cs (lexNumber s cs) t r (λ n r′ → lexNumber-< s cs n r′)

lexIdent₂-≤ : ∀ n rest b t r → lexIdent₂ n rest b ≡ just (t , r) → length r ≤ length rest
lexIdent₂-≤ n rest      false t r refl = ≤-refl
lexIdent₂-≤ n []        true  t r ()
lexIdent₂-≤ n (_ ∷ cs)  true  t r refl = n≤1+n _

-- An identifier that starts with an identifier character consumes it.
spanBy′-true : ∀ p c cs b → b ≡ true → length (proj₂ (spanBy′ p c cs b)) ≤ length cs
spanBy′-true p c cs true  _ = spanBy-≤ p cs
spanBy′-true p c cs false ()

lexIdent₁-≤ : ∀ pr t r → lexIdent₁ pr ≡ just (t , r) → length r ≤ length (proj₂ pr)
lexIdent₁-≤ (n , rest) t r h = lexIdent₂-≤ n rest (lparenK (headCls rest)) t r h

-- An identifier that starts with an identifier character consumes it.
lexIdent-< : ∀ c cs → isIdentChar c ≡ true → ∀ t r → lexIdent (c ∷ cs) ≡ just (t , r) →
             length r < suc (length cs)
lexIdent-< c cs ic t r h =
  s≤s (≤-trans (lexIdent₁-≤ (spanBy isIdentChar (c ∷ cs)) t r h)
               (spanBy′-true isIdentChar c cs (isIdentChar c) ic))

lexComment-≤ : ∀ cs t r → lexComment cs ≡ just (t , r) → length r ≤ length cs
lexComment₁-≤ : ∀ cs b t r → lexComment₁ cs b ≡ just (t , r) → length r ≤ suc (length cs)
lexComment₂-≤ : ∀ cs t r → lexComment₂ cs ≡ just (t , r) → length r ≤ length cs
lexComment₃-≤ : ∀ cs b t r → lexComment₃ cs b ≡ just (t , r) → length r ≤ length cs

lexComment-≤ []       t r ()
lexComment-≤ (c ∷ cs) t r h = lexComment₁-≤ cs ⌊ c ≟ '*' ⌋ t r h

lexComment₁-≤ cs false t r h = ≤-step (lexComment-≤ cs t r h)
lexComment₁-≤ cs true  t r h = ≤-step (lexComment₂-≤ cs t r h)

lexComment₂-≤ []           t r ()
lexComment₂-≤ cs@(d ∷ ds)  t r h = lexComment₃-≤ cs ⌊ d ≟ '/' ⌋ t r h

lexComment₃-≤ (d ∷ ds) true  .commentT .ds refl = n≤1+n _
lexComment₃-≤ []       true  t r ()
lexComment₃-≤ []       false t r h = lexComment-≤ [] t r h
lexComment₃-≤ (d ∷ ds) false t r h = lexComment-≤ (d ∷ ds) t r h

-- `r` is strictly shorter than `c ∷ cs`.
Prog : Char → List Char → List Char → Set
Prog c cs r = length r < suc (length cs)

lexHash₁-prog : ∀ c cs b t r → lexHash₁ c cs b ≡ just (t , r) → Prog c cs r
lexHash₁-prog c cs true  t r refl = s≤s (spanBy-≤ isIdentChar cs)
lexHash₁-prog c cs false t r refl = ≤-refl

lexAt₁-prog : ∀ c cs b t r → lexAt₁ c cs b ≡ just (t , r) → Prog c cs r
lexAt₁-prog c cs true  t r refl = s≤s (spanBy-≤ isIdentChar cs)
lexAt₁-prog c cs false t r refl = ≤-refl

lexSlash₁-prog : ∀ b c cs t r → lexSlash₁ b c cs ≡ just (t , r) → Prog c cs r
lexSlash₁-prog false c cs       t r refl = ≤-refl
lexSlash₁-prog true  c []       t r ()
lexSlash₁-prog true  c (d ∷ ds) t r h    = s≤s (≤-step (lexComment-≤ ds t r h))

lexString₁-prog : ∀ (cs : List Char) m t r → (∀ b rest → m ≡ just (b , rest) → length rest ≤ length cs) →
                  lexString₁ m ≡ just (t , r) → length r < suc (length cs)
lexString₁-prog cs nothing                 t r _ ()
lexString₁-prog cs (just (b , []))         t r _ ()
lexString₁-prog cs (just (b , _ ∷ rest))   t r f refl = ≤-step (f b (_ ∷ rest) refl)

lexMinus₁-prog : ∀ c cs → isIdentChar c ≡ true → ∀ b₁ b₂ t r →
                 lexMinus₁ c cs b₁ b₂ ≡ just (t , r) → Prog c cs r
lexMinus₁-prog c cs ic true  _     t r h = ≤-step (lexNumTok-< Sign.- cs t r h)
lexMinus₁-prog c cs ic false true  t r h = lexIdent-< c cs ic t r h
lexMinus₁-prog c cs ic false false t r refl = ≤-refl

lexPlus₁-prog : ∀ c cs b t r → lexPlus₁ c cs b ≡ just (t , r) → Prog c cs r
lexPlus₁-prog c cs true  t r h    = ≤-step (lexNumTok-< Sign.+ cs t r h)
lexPlus₁-prog c cs false t r refl = ≤-refl

lexDot₁-prog : ∀ c cs b t r → lexDot₁ c cs b ≡ just (t , r) → Prog c cs r
lexDot₁-prog c cs true  t r h    = lexNumTok-< Sign.+ (c ∷ cs) t r h
lexDot₁-prog c cs false t r refl = ≤-refl

lexTok-prog : ∀ c cs k → classOf c ≡ k → ∀ t r → lexTok c cs k ≡ just (t , r) → Prog c cs r
lexTok-prog c cs wsC         _  t r refl = s≤s (spanBy-≤ isWs cs)
lexTok-prog c cs identStartC eq t r h = lexIdent-< c cs (cong identContK eq) t r h
lexTok-prog c cs digitC      _  t r h = lexNumTok-< Sign.+ (c ∷ cs) t r h
lexTok-prog c cs minusC      eq t r h =
  lexMinus₁-prog c cs (cong identContK eq) (startsNumber cs) (startsIdent (c ∷ cs)) t r h
lexTok-prog c cs plusC       _  t r h = lexPlus₁-prog c cs (startsNumber cs) t r h
lexTok-prog c cs dotC        _  t r h = lexDot₁-prog c cs (startsNumber (c ∷ cs)) t r h
lexTok-prog c cs hashC       _  t r h = lexHash₁-prog c cs (identContK (headCls cs)) t r h
lexTok-prog c cs atC         _  t r h = lexAt₁-prog c cs (startsIdent cs) t r h
lexTok-prog c cs slashC      _  t r h = lexSlash₁-prog (starK (headCls cs)) c cs t r h
lexTok-prog c cs starC       _  t r refl = ≤-refl
lexTok-prog c cs percentC    _  t r refl = ≤-refl
lexTok-prog c cs dquoteC     _  t r h = lexString₁-prog cs (lexBody c cs) t r (lexBody-≤ c cs) h
lexTok-prog c cs squoteC     _  t r h = lexString₁-prog cs (lexBody c cs) t r (lexBody-≤ c cs) h
lexTok-prog c cs backslashC  _  t r ()
lexTok-prog c cs lparenC     _  t r refl = ≤-refl
lexTok-prog c cs rparenC     _  t r refl = ≤-refl
lexTok-prog c cs lbrackC     _  t r refl = ≤-refl
lexTok-prog c cs rbrackC     _  t r refl = ≤-refl
lexTok-prog c cs lbraceC     _  t r refl = ≤-refl
lexTok-prog c cs rbraceC     _  t r refl = ≤-refl
lexTok-prog c cs commaC      _  t r refl = ≤-refl
lexTok-prog c cs colonC      _  t r refl = ≤-refl
lexTok-prog c cs semiC       _  t r refl = ≤-refl
lexTok-prog c cs delimC      _  t r refl = ≤-refl
lexTok-prog c cs otherC      _  t r ()

-- The rest after a token is strictly shorter than the input.
lexToken-progress : ∀ L t rest → lexToken L ≡ just (t , rest) → length rest < length L
lexToken-progress []       t rest ()
lexToken-progress (c ∷ cs) t rest h = lexTok-prog c cs (classOf c) refl t rest h
