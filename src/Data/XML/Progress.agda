{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Every XML token consumes input
--
-- `lexToken-progress`: the rest after a token is strictly shorter than
-- the input.  With it the tokenizer's fuel is irrelevant once it exceeds
-- the input length (`Data.Lexer.Lexing.Fuel`), so text in a `String` can
-- be tokenized without first measuring it (`Data.XML.RoundTrip.parseXMLString`).
------------------------------------------------------------------------

module Data.XML.Progress where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Char.Fast using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Lexer.Whitespace using (skipWS; skipWS-≤)
open import Data.XML.Escape
open import Data.XML.Valid
open import Data.XML.Token

private
  ≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
  ≤-step p = ≤-trans p (n≤1+n _)

------------------------------------------------------------------------
-- Bodies (text and attribute values)
------------------------------------------------------------------------

mutual
  lexBody-≤ : ∀ stop cs b rest → lexBody stop cs ≡ just (b , rest) → length rest ≤ length cs
  lexBody-≤ stop []       b rest ()
  lexBody-≤ stop (c ∷ cs) b rest h with c ≟ '&'
  ... | yes _ = ≤-step (lexEntity-≤ stop [] cs b rest h)
  ... | no  _ = lexChar-≤ stop c cs (c ≟ stop) b rest h

  lexChar-≤ : ∀ stop c cs d b rest → lexChar stop c cs d ≡ just (b , rest) → length rest ≤ suc (length cs)
  lexChar-≤ stop c cs (yes _) .[] .(c ∷ cs) refl = ≤-refl
  lexChar-≤ stop c cs (no  _) b rest h with lexBody stop cs in eq
  lexChar-≤ stop c cs (no  _) b rest () | nothing
  lexChar-≤ stop c cs (no  _) .(c ∷ b′) rest refl | just (b′ , r′) with lexBody-≤ stop cs b′ r′ eq
  ... | ih = ≤-step ih

  lexEntity-≤ : ∀ stop acc cs b rest → lexEntity stop acc cs ≡ just (b , rest) → length rest ≤ length cs
  lexEntity-≤ stop acc []       b rest ()
  lexEntity-≤ stop acc (c ∷ cs) b rest h with c ≟ ';'
  ... | no  _ = ≤-step (lexEntity-≤ stop (c ∷ acc) cs b rest h)
  ... | yes _ with resolve (Data.List.reverse acc)
  lexEntity-≤ stop acc (c ∷ cs) b rest () | yes _ | nothing
  ... | just x with lexBody stop cs in eq
  lexEntity-≤ stop acc (c ∷ cs) b rest () | yes _ | just x | nothing
  lexEntity-≤ stop acc (c ∷ cs) .(x ∷ b′) rest refl | yes _ | just x | just (b′ , r′) =
    ≤-step (lexBody-≤ stop cs b′ r′ eq)

-- A body that starts with something other than its terminator consumes input.
lexBody-< : ∀ stop c cs b rest → (c ≡ stop → ⊥) → lexBody stop (c ∷ cs) ≡ just (b , rest) →
            length rest ≤ length cs
lexBody-< stop c cs b rest ns h with c ≟ '&'
... | yes _ = lexEntity-≤ stop [] cs b rest h
... | no  _ with c ≟ stop
...   | yes e = ⊥-elim (ns e)
...   | no  _ with lexBody stop cs in eq
lexBody-< stop c cs b rest ns () | no _ | no _ | nothing
lexBody-< stop c cs .(c ∷ b′) rest ns refl | no _ | no _ | just (b′ , r′) = lexBody-≤ stop cs b′ r′ eq

------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------

lexName-≤ : ∀ cs → length (proj₂ (lexName cs)) ≤ length cs
lexName-≤ []       = z≤n
lexName-≤ (c ∷ cs) with isNameChar c
... | false = ≤-refl
... | true  with lexName cs | lexName-≤ cs
...   | (n , r) | ih = ≤-step ih

-- A non-empty name consumes input.
lexName-< : ∀ cs x n rest → lexName cs ≡ (x ∷ n , rest) → length rest < length cs
lexName-< []       x n rest ()
lexName-< (c ∷ cs) x n rest h with isNameChar c
lexName-< (c ∷ cs) x n rest () | false
... | true with lexName cs | lexName-≤ cs
lexName-< (c ∷ cs) x n rest refl | true | (n′ , r′) | ih = s≤s ih

------------------------------------------------------------------------
-- Attributes
------------------------------------------------------------------------

lexAttr-< : ∀ cs a rest → lexAttr cs ≡ just (a , rest) → length rest < length cs
lexAttr-< cs a rest h with lexName cs in eq
lexAttr-< cs a rest () | [] , r
lexAttr-< cs a rest () | x ∷ k , []
lexAttr-< cs a rest () | x ∷ k , c ∷ []
lexAttr-< cs a rest h  | x ∷ k , c ∷ d ∷ r with lexName-< cs x k (c ∷ d ∷ r) eq
... | nl with c ≟ '=' | d ≟ '"'
lexAttr-< cs a rest () | x ∷ k , c ∷ d ∷ r | nl | no _  | _
lexAttr-< cs a rest () | x ∷ k , c ∷ d ∷ r | nl | yes _ | no _
lexAttr-< cs a rest h  | x ∷ k , c ∷ d ∷ r | nl | yes _ | yes _ with lexBody '"' r in eq₂
lexAttr-< cs a rest () | x ∷ k , c ∷ d ∷ r | nl | yes _ | yes _ | nothing
lexAttr-< cs a rest h  | x ∷ k , c ∷ d ∷ r | nl | yes _ | yes _ | just (v , []) with h
... | ()
lexAttr-< cs a rest h  | x ∷ k , c ∷ d ∷ r | nl | yes _ | yes _ | just (v , e ∷ r′) with e ≟ '"'
lexAttr-< cs a rest () | x ∷ k , c ∷ d ∷ r | nl | yes _ | yes _ | just (v , e ∷ r′) | no _
lexAttr-< cs a rest refl | x ∷ k , c ∷ d ∷ r | nl | yes _ | yes _ | just (v , e ∷ r′) | yes _ =
  ≤-trans (lexBody-≤ '"' r v (e ∷ r′) eq₂) (≤-trans (n≤1+n _) (≤-trans (n≤1+n _) (≤-trans (n≤1+n _) nl)))

mutual
  lexAttrs-≤ : ∀ f cs as b rest → lexAttrs f cs ≡ just (as , b , rest) → length rest ≤ length cs
  lexAttrs-≤ []      cs as b rest ()
  lexAttrs-≤ (_ ∷ f) cs as b rest h = ≤-trans (lexAttrs₁-≤ f (skipWS cs) as b rest h) (skipWS-≤ cs)

  lexAttrs₁-≤ : ∀ f cs as b rest → lexAttrs₁ f cs ≡ just (as , b , rest) → length rest ≤ length cs
  lexAttrs₁-≤ f []       as b rest ()
  lexAttrs₁-≤ f (c ∷ cs) as b rest h = lexAttrs₃-≤ f c cs (isNameChar c) as b rest h

  lexAttrs₃-≤ : ∀ f c cs d as b rest → lexAttrs₃ f c cs d ≡ just (as , b , rest) →
                length rest ≤ suc (length cs)
  lexAttrs₃-≤ f c cs true as b rest h with lexAttr (c ∷ cs) in eq
  lexAttrs₃-≤ f c cs true as b rest () | nothing
  lexAttrs₃-≤ f c cs true as b rest h  | just (a , r) with lexAttrs f r in eq′
  lexAttrs₃-≤ f c cs true as b rest () | just (a , r) | nothing
  lexAttrs₃-≤ f c cs true .(a ∷ as′) b rest refl | just (a , r) | just (as′ , b′ , r′) =
    ≤-trans (lexAttrs-≤ f r as′ b rest eq′) (≤-trans (n≤1+n _) (lexAttr-< (c ∷ cs) a r eq))
  lexAttrs₃-≤ f c cs false as b rest h = ≤-step (lexAttrsEnd-≤ c cs (c ≟ '>') as b rest h)

  lexAttrsEnd-≤ : ∀ c cs d as b rest → lexAttrsEnd c cs d ≡ just (as , b , rest) → length rest ≤ length cs
  lexAttrsEnd-≤ c cs (yes _) .[] .false .cs refl = ≤-refl
  lexAttrsEnd-≤ c cs (no  _) as b rest h with c ≟ '/'
  lexAttrsEnd-≤ c cs (no  _) as b rest () | no _
  lexAttrsEnd-≤ c cs (no  _) as b rest h  | yes _ = lexAttrsEnd₂-≤ cs as b rest h

  lexAttrsEnd₂-≤ : ∀ cs as b rest → lexAttrsEnd₂ cs ≡ just (as , b , rest) → length rest ≤ length cs
  lexAttrsEnd₂-≤ []       as b rest ()
  lexAttrsEnd₂-≤ (d ∷ cs) as b rest h with d ≟ '>'
  lexAttrsEnd₂-≤ (d ∷ cs) as b rest () | no _
  lexAttrsEnd₂-≤ (d ∷ cs) .[] .true .cs refl | yes _ = n≤1+n _

------------------------------------------------------------------------
-- Tags and tokens
------------------------------------------------------------------------

lexOpen-< : ∀ cs t rest → lexOpen cs ≡ just (t , rest) → length rest < length cs
lexOpen-< cs t rest h with lexName cs in eq
lexOpen-< cs t rest () | [] , r
lexOpen-< cs t rest h  | x ∷ n , r with lexAttrs (' ' ∷ r) r in eq′
lexOpen-< cs t rest () | x ∷ n , r | nothing
lexOpen-< cs t rest refl | x ∷ n , r | just (as , b , r′) =
  ≤-trans (s≤s (lexAttrs-≤ (' ' ∷ r) r as b r′ eq′)) (lexName-< cs x n r eq)

lexClose-< : ∀ cs t rest → lexClose cs ≡ just (t , rest) → length rest < length cs
lexClose-< cs t rest h with lexName cs in eq
lexClose-< cs t rest () | [] , r
lexClose-< cs t rest () | x ∷ n , []
lexClose-< cs t rest h  | x ∷ n , d ∷ r with d ≟ '>'
lexClose-< cs t rest () | x ∷ n , d ∷ r | no _
lexClose-< cs t rest refl | x ∷ n , d ∷ r | yes _ =
  ≤-trans (s≤s (n≤1+n _)) (lexName-< cs x n (d ∷ r) eq)

lexTag-≤ : ∀ cs t rest → lexTag cs ≡ just (t , rest) → length rest ≤ length cs
lexTag-≤ []       t rest ()
lexTag-≤ (c ∷ cs) t rest h with isNameChar c
... | true  with lexOpen-< (c ∷ cs) t rest h
...   | s≤s lt = ≤-step lt
lexTag-≤ (c ∷ cs) t rest h | false with c ≟ '/'
lexTag-≤ (c ∷ cs) t rest () | false | no _
lexTag-≤ (c ∷ cs) t rest h  | false | yes _ = ≤-step (≤-trans (n≤1+n _) (lexClose-< cs t rest h))

-- The rest after a token is strictly shorter than the input.
lexToken-progress : ∀ L t rest → lexToken L ≡ just (t , rest) → length rest < length L
lexToken-progress []       t rest ()
lexToken-progress (c ∷ cs) t rest h with c ≟ '<'
... | yes _ = s≤s (lexTag-≤ cs t rest h)
... | no ne with lexBody '<' (c ∷ cs) in eq
lexToken-progress (c ∷ cs) t rest () | no ne | nothing
lexToken-progress (c ∷ cs) .(textT b) rest refl | no ne | just (b , r) = s≤s (lexBody-< '<' c cs b r ne eq)
