{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Every HTML token consumes input
--
-- `lexToken-progress`: the rest after a token is strictly shorter than
-- the input, so the tokenizer's fuel is irrelevant once it exceeds the
-- input length (see `Data.XML.Progress`, which this extends with the
-- raw-text token).
------------------------------------------------------------------------

module Data.HTML.Progress where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Char.Class using (is)
open import Data.XML.Progress using () renaming (lexToken-progress to xmlProgress)
open import Data.XML.Valid using (eqName)
open import Data.XML.Token using (XMLToken; openT; selfT; closeT; textT)
import Data.XML.Token as X
open import Data.HTML.Valid
open import Data.HTML.Token

private
  ≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
  ≤-step p = ≤-trans p (n≤1+n _)

  <-weaken : ∀ {m n} → m < n → m ≤ n
  <-weaken p = ≤-trans (n≤1+n _) p

-- The text after the raw body is a suffix of the input.
rawSplit-≤ : ∀ cs b tl → rawSplit cs ≡ just (b , tl) → length tl ≤ length cs
rawSplit-≤ []       b tl ()
rawSplit-≤ (c ∷ cs) b tl h with is '<' c ∧ slashNext cs
rawSplit-≤ (c ∷ cs) .[] .(c ∷ cs) refl | true = ≤-refl
... | false with rawSplit cs in eq
rawSplit-≤ (c ∷ cs) b tl () | false | nothing
rawSplit-≤ (c ∷ cs) .(c ∷ b′) tl refl | false | just (b′ , tl′) = ≤-step (rawSplit-≤ cs b′ tl eq)

-- The rest after a token is strictly shorter than the input.
lexToken-progress : ∀ L t rest → lexToken L ≡ just (t , rest) → length rest < length L
lexToken-progress L t rest h with X.lexToken L in eq
lexToken-progress L t rest () | nothing
lexToken-progress L t rest h | just (openT n as , r) with isRawTag n
lexToken-progress L .(tok (openT n as)) rest refl | just (openT n as , r) | false = xmlProgress L _ _ eq
lexToken-progress L t rest h | just (openT n as , r) | true with rawSplit r in eq₂
lexToken-progress L t rest () | just (openT n as , r) | true | nothing
lexToken-progress L t rest h | just (openT n as , r) | true | just (b , tl) with X.lexToken tl in eq₃
lexToken-progress L t rest () | just (openT n as , r) | true | just (b , tl) | nothing
lexToken-progress L t rest () | just (openT n as , r) | true | just (b , tl) | just (openT _ _ , _)
lexToken-progress L t rest () | just (openT n as , r) | true | just (b , tl) | just (selfT _ _ , _)
lexToken-progress L t rest () | just (openT n as , r) | true | just (b , tl) | just (textT _ , _)
lexToken-progress L t rest h | just (openT n as , r) | true | just (b , tl) | just (closeT m , r₂)
  with eqName n m
lexToken-progress L t rest () | just (openT n as , r) | true | just (b , tl) | just (closeT m , r₂) | false
lexToken-progress L .(rawT n as b) .r₂ refl | just (openT n as , r) | true | just (b , tl) | just (closeT m , r₂) | true =
  ≤-trans (≤-trans (xmlProgress tl _ _ eq₃) (rawSplit-≤ r b tl eq₂)) (<-weaken (xmlProgress L _ _ eq))
lexToken-progress L .(tok (selfT n as)) rest refl | just (selfT n as , r) = xmlProgress L _ _ eq
lexToken-progress L .(tok (closeT n)) rest refl | just (closeT n , r) = xmlProgress L _ _ eq
lexToken-progress L .(tok (textT x)) rest refl | just (textT x , r) = xmlProgress L _ _ eq
