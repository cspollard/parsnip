{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Style sheets as lists of rules, from and to text
--
-- `printRules` (`Data.CSS.Rule`) followed by `printCSS` prints a list of
-- rules, and the parser reads it back:
--
--   parseStylesheet (printStylesheet rs) ≡ just rs.
------------------------------------------------------------------------

module Data.CSS.Stylesheet where

open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Data.CSS.Print using (printCSS)
open import Data.CSS.Rule
open import Data.CSS.RoundTrip using (parseCSSText; parseCSSText-printCSS)

printStylesheet : List Rule → List Char
printStylesheet rs = printCSS (printRules rs)

parseStylesheet : List Char → Maybe (List Rule)
parseStylesheet cs = Maybe.maybe parseRuleList nothing (parseCSSText cs)

parseStylesheet-printStylesheet : ∀ rs → parseStylesheet (printStylesheet rs) ≡ just rs
parseStylesheet-printStylesheet rs =
  trans (cong (Maybe.maybe parseRuleList nothing) (parseCSSText-printCSS (printRules rs)))
        (parseRuleList-printRules rs)
