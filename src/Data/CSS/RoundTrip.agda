{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The headline theorem: parsing inverts printing, lexing included
--
-- `cssStage` is the composite of `parser` and `lexer`, two stdlib
-- `RightInverse`s (`Function.Construct.Composition.rightInverse`):
--
--   to        = printCSS
--   from      = total parser (tokenize, drop comments, parse; `defaultCSS`
--               on failure)
--   inverseʳ  = from (printCSS v) ≡ v
--
-- `parseCSSText` is the partial `Maybe` parser used at runtime, and
-- `parseCSSText-printCSS` is the same law stated for it.
------------------------------------------------------------------------

module Data.CSS.RoundTrip where

open import Data.Char using (Char)
open import Data.List using (List; [])
open import Data.Maybe as Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Product using (_,_; proj₁)
open import Function.Bundles using (RightInverse)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; setoid)
import Function.Construct.Composition as Composition

open import Data.Stage using (Chars)
open import Data.CSS.AST using (CSS)
open import Data.CSS.Lexer using (ValidTokens; lexer; tokenize; tokenize-printList)
open import Data.CSS.Parser using (parseCSS; parseCSS-printTokens)
open import Data.CSS.Print using (printCSS)
open import Data.CSS.Tokens using (printTokens; printTokens-valid)

CSSSetoid = setoid CSS

-- The parser: the token stream of a tree, with the proof it is valid, and
-- back.  Where parsing fails, the empty style sheet.
parser : RightInverse CSSSetoid ValidTokens
parser = record
  { to        = λ v → printTokens v , printTokens-valid v
  ; from      = λ x → fromMaybe [] (parseCSS (proj₁ x))
  ; to-cong   = cong printTokens
  ; from-cong = λ { refl → refl }
  ; inverseʳ  = λ { {v} refl → inv v }
  }
  where
  inv : ∀ v → fromMaybe [] (parseCSS (printTokens v)) ≡ v
  inv v = cong (fromMaybe []) (parseCSS-printTokens v)

cssStage : RightInverse CSSSetoid Chars
cssStage = Composition.rightInverse parser lexer

-- The printer of `cssStage` is `printCSS`.
to-printCSS : ∀ v → RightInverse.to cssStage v ≡ printCSS v
to-printCSS v = refl

-- The partial parser: tokenize, then parse the whole stream.
parseCSSText : List Char → Maybe CSS
parseCSSText cs = Maybe.maybe parseCSS nothing (tokenize cs)

parseCSSText-printCSS : ∀ v → parseCSSText (printCSS v) ≡ just v
parseCSSText-printCSS v =
  Eq.trans (cong (Maybe.maybe parseCSS nothing)
                 (tokenize-printList (printTokens v) (printTokens-valid v)))
           (parseCSS-printTokens v)
