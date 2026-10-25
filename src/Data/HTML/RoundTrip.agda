{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The headline theorem: parsing inverts printing, lexing included
--
-- `htmlStage` is the composite of `parser` and `lexer`, two stdlib
-- `RightInverse`s (`Function.Construct.Composition.rightInverse`), for
-- the element itself:
--
--   to        = printBody
--   from      = total parser (tokenize, parse; `defaultElem` on failure)
--   inverseʳ  = from (printBody e) ≡ e
--
-- `parseHTML` is the partial parser for whole documents: it strips the
-- `<!DOCTYPE html>` that `printHTML` writes, and `parseHTML-printHTML`
-- is the round-trip law.
------------------------------------------------------------------------

module Data.HTML.RoundTrip where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe as Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat.Properties using (≡⇒≡ᵇ)
open import Data.Product using (_,_; proj₁)
open import Data.String using (toList)
open import Function.Bundles using (RightInverse)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; setoid)
import Function.Construct.Composition as Composition

open import Data.Char.Class using (is)
open import Data.Stage using (Chars)
open import Data.HTML.Valid using (toEq)
open import Data.HTML.AST
open import Data.HTML.Lexer using (ValidTokens; lexer; tokenize; tokenize-printTokenList; valid-run)
open import Data.HTML.Parser using (parseTokens; parseTokens-tokensElem)
open import Data.HTML.Print
open import Data.HTML.Tokens using (tokensElem; elem-run)

ElemSetoid = setoid Elem

-- Where parsing fails: an empty `<br />`.
defaultElem : Elem
defaultElem = void (toList "br") [] _

-- The parser: the token stream of an element, with the proof it is valid,
-- and back.
parser : RightInverse ElemSetoid ValidTokens
parser = record
  { to        = λ e → tokensElem e , valid-run (elem-run e false)
  ; from      = λ x → fromMaybe defaultElem (parseTokens (proj₁ x))
  ; to-cong   = cong tokensElem
  ; from-cong = λ { refl → refl }
  ; inverseʳ  = λ { {e} refl → cong (fromMaybe defaultElem) (parseTokens-tokensElem e) }
  }

htmlStage : RightInverse ElemSetoid Chars
htmlStage = Composition.rightInverse parser lexer

-- The printer of `htmlStage` is `printBody`.
to-printBody : ∀ e → RightInverse.to htmlStage e ≡ printBody e
to-printBody e = refl

-- The partial parser: tokenize, then parse the whole stream.
parseBody : List Char → Maybe Elem
parseBody cs = Maybe.maybe parseTokens nothing (tokenize cs)

parseBody-printBody : ∀ e → parseBody (printBody e) ≡ just e
parseBody-printBody e =
  Eq.trans (cong (Maybe.maybe parseTokens nothing)
                 (tokenize-printTokenList (tokensElem e) (valid-run (elem-run e false))))
           (parseTokens-tokensElem e)

------------------------------------------------------------------------
-- Documents
------------------------------------------------------------------------

stripPrefix : List Char → List Char → Maybe (List Char)
stripStep : List Char → List Char → Bool → Maybe (List Char)

stripPrefix []       ys       = just ys
stripPrefix (x ∷ xs) []       = nothing
stripPrefix (x ∷ xs) (y ∷ ys) = stripStep xs ys (is x y)

stripStep xs ys true  = stripPrefix xs ys
stripStep xs ys false = nothing

is-refl : ∀ c → is c c ≡ true
is-refl c = toEq (≡⇒≡ᵇ (toℕ c) (toℕ c) refl)

stripPrefix-++ : ∀ xs ys → stripPrefix xs (xs ++ ys) ≡ just ys
stripPrefix-++ []       ys = refl
stripPrefix-++ (x ∷ xs) ys =
  Eq.trans (cong (stripStep xs (xs ++ ys)) (is-refl x)) (stripPrefix-++ xs ys)

-- A document: `<!DOCTYPE html>` and then the root element.
parseHTML : List Char → Maybe Elem
parseHTML cs = Maybe.maybe parseBody nothing (stripPrefix doctype cs)

parseHTML-printHTML : ∀ e → parseHTML (printHTML e) ≡ just e
parseHTML-printHTML e =
  Eq.trans (cong (Maybe.maybe parseBody nothing) (stripPrefix-++ doctype (printBody e)))
           (parseBody-printBody e)
