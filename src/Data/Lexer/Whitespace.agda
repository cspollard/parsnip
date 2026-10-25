{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- White space
--
-- `skipWS` drops leading white space (space, line feed, tab, carriage
-- return).  JSON tokenizes by skipping it before every token; XML skips
-- it between the attributes of a tag.  `skipWS-nonWS` is the fact the
-- tokenizer proofs use: text that starts with something else is left alone.
------------------------------------------------------------------------

module Data.Lexer.Whitespace where

open import Data.Char using (Char)
open import Data.Char.Fast using (_∈?_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (_≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

whitespace : List Char
whitespace = ' ' ∷ '\n' ∷ '\t' ∷ '\r' ∷ []

-- Drops leading white space; `skipWS′` takes the decision as an argument
-- so that proofs can rewrite exactly that call.
skipWS : List Char → List Char
skipWS′ : (c : Char) → List Char → Dec (c ∈ whitespace) → List Char

skipWS []       = []
skipWS (c ∷ cs) = skipWS′ c cs (c ∈? whitespace)

skipWS′ c cs (yes _) = skipWS cs
skipWS′ c cs (no  _) = c ∷ cs

NonWS : Char → Set
NonWS c = c ∈ whitespace → ⊥

skipWS-nonWS : ∀ c cs → NonWS c → skipWS (c ∷ cs) ≡ c ∷ cs
skipWS-nonWS c cs nw with c ∈? whitespace
... | yes p = ⊥-elim (nw p)
... | no  _ = refl

-- Skipping never lengthens the text.
skipWS-≤ : ∀ cs → length (skipWS cs) ≤ length cs
skipWS-≤ []       = z≤n
skipWS-≤ (c ∷ cs) with c ∈? whitespace
... | yes _ = ≤-trans (skipWS-≤ cs) (n≤1+n _)
... | no  _ = ≤-refl
