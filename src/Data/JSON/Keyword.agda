{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- JSON literal names (RFC 8259 §3): `null`, `true`, `false`
--
-- `keywordStage` is a stdlib `RightInverse` between keywords and their
-- spelling; `lexKeyword-print` is the prefix round trip it is built from.
------------------------------------------------------------------------

module Data.JSON.Keyword where

open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (toList)
open import Function.Bundles using (RightInverse)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; subst; setoid)

open import Data.JSON.Stage using (Chars; mkStage)

data Keyword : Set where
  nullK trueK falseK : Keyword

keywordText : Keyword → List Char
keywordText nullK  = toList "null"
keywordText trueK  = toList "true"
keywordText falseK = toList "false"

allKeywords : List Keyword
allKeywords = nullK ∷ trueK ∷ falseK ∷ []

------------------------------------------------------------------------
-- Lexing
------------------------------------------------------------------------

-- `stripPrefix xs ys` is `just zs` when `ys ≡ xs ++ zs`.
stripPrefix : List Char → List Char → Maybe (List Char)
stripPrefix []       ys       = just ys
stripPrefix (x ∷ xs) []       = nothing
stripPrefix (x ∷ xs) (y ∷ ys) with x ≟ y
... | yes _ = stripPrefix xs ys
... | no  _ = nothing

-- The first keyword that is a prefix of the input, and the remainder.
lexKeywordFrom : List Keyword → List Char → Maybe (Keyword × List Char)
lexKeywordFrom []       cs = nothing
lexKeywordFrom (k ∷ ks) cs with stripPrefix (keywordText k) cs
... | just rest = just (k , rest)
... | nothing   = lexKeywordFrom ks cs

lexKeyword : List Char → Maybe (Keyword × List Char)
lexKeyword = lexKeywordFrom allKeywords

------------------------------------------------------------------------
-- Round trip
------------------------------------------------------------------------

stripPrefix-++ : ∀ xs rest → stripPrefix xs (xs ++ rest) ≡ just rest
stripPrefix-++ []       rest = refl
stripPrefix-++ (x ∷ xs) rest with x ≟ x
... | yes _  = stripPrefix-++ xs rest
... | no  ¬p = ⊥-elim (¬p refl)

private
  found : ∀ k ks cs r → stripPrefix (keywordText k) cs ≡ just r →
          lexKeywordFrom (k ∷ ks) cs ≡ just (k , r)
  found k ks cs r eq rewrite eq = refl

  skip : ∀ k ks cs → stripPrefix (keywordText k) cs ≡ nothing →
         lexKeywordFrom (k ∷ ks) cs ≡ lexKeywordFrom ks cs
  skip k ks cs eq rewrite eq = refl

lexKeyword-print : ∀ k rest → lexKeyword (keywordText k ++ rest) ≡ just (k , rest)
lexKeyword-print nullK  rest =
  found nullK (trueK ∷ falseK ∷ []) cs rest (stripPrefix-++ (keywordText nullK) rest)
  where cs = keywordText nullK ++ rest
lexKeyword-print trueK  rest =
  trans (skip nullK (trueK ∷ falseK ∷ []) cs refl)
        (found trueK (falseK ∷ []) cs rest (stripPrefix-++ (keywordText trueK) rest))
  where cs = keywordText trueK ++ rest
lexKeyword-print falseK rest =
  trans (skip nullK (trueK ∷ falseK ∷ []) cs refl)
        (trans (skip trueK (falseK ∷ []) cs refl)
               (found falseK [] cs rest (stripPrefix-++ (keywordText falseK) rest)))
  where cs = keywordText falseK ++ rest

parseKeyword : List Char → Maybe Keyword
parseKeyword cs = Maybe.map proj₁ (lexKeyword cs)

-- `keywordStage` (see `Data.JSON.Goals`).
keywordStage : RightInverse (setoid Keyword) Chars
keywordStage = mkStage (setoid Keyword) keywordText parseKeyword nullK
  (cong keywordText)
  (λ k → k , parseKeyword-print k , refl)
  where
  parseKeyword-print : ∀ k → parseKeyword (keywordText k) ≡ just k
  parseKeyword-print k =
    subst (λ cs → parseKeyword cs ≡ just k) (++-identityʳ (keywordText k))
          (cong (Maybe.map proj₁) (lexKeyword-print k []))
