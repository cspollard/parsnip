{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The tokenizer, and `lexer`: a stdlib RightInverse from valid token
-- streams to text
--
-- An instance of the generic `Data.Lexer`: `tokenize` skips white space
-- and lexes tokens one at a time with `lexToken` (`Data.JSON.Token`).
-- `lexer` is a `RightInverse` out of `ValidTokens`, the token streams with
-- no two adjacent numbers (the only streams whose printed form re-lexes
-- to themselves).  Its `from` is total by checking validity of the
-- tokenizer's output, which is decidable, and falling back to the empty
-- stream.
------------------------------------------------------------------------

module Data.JSON.Lexer where

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Char.Fast using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Char.Fast using (_∈?_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Linked as Linked using (Linked; []; [-]; _∷_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤?_; z≤n; z<s; s<s; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Data.List.Properties using (length-++)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≰⇒>; m≤n+m; n≤1+n; n<1+n)
open import Function.Bundles using (RightInverse)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; setoid)

open import Data.JSON.Number
  using (JSONNumber; jsonNumber; NoLeadingNumCont; printNat-head; printFraction; printExponent)
open import Data.Sign as Sign using ()
open import Data.JSON.Token
open import Data.Lexer using (TokenLang; module Lexing)
open import Data.JSON.Progress using (lexToken-progress)
open import Data.Lexer.Whitespace public
open import Data.Invertible.Char using (parseDigit; printDigit; parsePrintDigit)

------------------------------------------------------------------------
-- Valid token streams
------------------------------------------------------------------------

IsNumber : JSONToken → Set
IsNumber (numberT _) = ⊤
IsNumber _           = ⊥

-- Two adjacent number tokens would print as one number.
NotAdjacent : JSONToken → JSONToken → Set
NotAdjacent x y = IsNumber x → IsNumber y → ⊥

ValidTokenSeq : List JSONToken → Set
ValidTokenSeq = Linked NotAdjacent

isNumber? : ∀ t → Dec (IsNumber t)
isNumber? lbraceT     = no (λ ())
isNumber? lbracketT   = no (λ ())
isNumber? rbraceT     = no (λ ())
isNumber? rbracketT   = no (λ ())
isNumber? colonT      = no (λ ())
isNumber? commaT      = no (λ ())
isNumber? nullT       = no (λ ())
isNumber? (boolT _)   = no (λ ())
isNumber? (numberT _) = yes tt
isNumber? (stringT _) = no (λ ())

notAdjacent? : ∀ x y → Dec (NotAdjacent x y)
notAdjacent? x y with isNumber? x | isNumber? y
... | yes px | yes py = no (λ f → f px py)
... | yes px | no ¬py = yes (λ _ py → ¬py py)
... | no ¬px | _      = yes (λ px _ → ¬px px)

validTokenSeq? : ∀ ts → Dec (ValidTokenSeq ts)
validTokenSeq? = Linked.linked? notAdjacent?

------------------------------------------------------------------------
-- Facts about printed tokens
------------------------------------------------------------------------

private
  nonWS-literal : ∀ {c} → False (c ∈? whitespace) → NonWS c
  nonWS-literal f = toWitnessFalse f

  -- A digit is not white space (`parseDigit` rejects all four).
  nonWS-digit : ∀ c d → parseDigit c ≡ just d → NonWS c
  nonWS-digit .' '  d () (here refl)
  nonWS-digit .'\n' d () (there (here refl))
  nonWS-digit .'\t' d () (there (there (here refl)))
  nonWS-digit .'\r' d () (there (there (there (here refl))))

-- Every printed token starts with a character that is not white space.
printToken-cons : ∀ t → ∃ λ c → ∃ λ cs → printToken t ≡ c ∷ cs × NonWS c
printToken-cons lbraceT   = '{' , _ , refl , nonWS-literal tt
printToken-cons rbraceT   = '}' , _ , refl , nonWS-literal tt
printToken-cons lbracketT = '[' , _ , refl , nonWS-literal tt
printToken-cons rbracketT = ']' , _ , refl , nonWS-literal tt
printToken-cons colonT    = ':' , _ , refl , nonWS-literal tt
printToken-cons commaT    = ',' , _ , refl , nonWS-literal tt
printToken-cons nullT         = 'n' , _ , refl , nonWS-literal tt
printToken-cons (boolT true)  = 't' , _ , refl , nonWS-literal tt
printToken-cons (boolT false) = 'f' , _ , refl , nonWS-literal tt
printToken-cons (stringT s)   = '"' , _ , refl , nonWS-literal tt
printToken-cons (numberT (jsonNumber Sign.- i f e)) = '-' , _ , refl , nonWS-literal tt
printToken-cons (numberT (jsonNumber Sign.+ i f e)) with printNat-head i (printFraction f ++ printExponent e)
... | d , cs , eq = printDigit d , cs , eq , nonWS-digit (printDigit d) d (parsePrintDigit d)

-- After a non-number token, nothing continues a number.
follow-nonNumber : ∀ t rest → ¬ IsNumber t → NoLeadingNumCont (printToken t ++ rest)
follow-nonNumber lbraceT   rest _ = refl , tt , tt
follow-nonNumber rbraceT   rest _ = refl , tt , tt
follow-nonNumber lbracketT rest _ = refl , tt , tt
follow-nonNumber rbracketT rest _ = refl , tt , tt
follow-nonNumber colonT    rest _ = refl , tt , tt
follow-nonNumber commaT    rest _ = refl , tt , tt
follow-nonNumber nullT         rest _ = refl , tt , tt
follow-nonNumber (boolT true)  rest _ = refl , tt , tt
follow-nonNumber (boolT false) rest _ = refl , tt , tt
follow-nonNumber (stringT _)   rest _ = refl , tt , tt
follow-nonNumber (numberT _)   rest n = ⊥-elim (n tt)

-- In a valid stream, the text after a token may follow it.
tokenFollow : ∀ t ts → ValidTokenSeq (t ∷ ts) → TokenFollow t (printTokenList ts)
tokenFollow (numberT _) []        _ = tt , tt , tt
tokenFollow (numberT _) (t′ ∷ ts) v = follow-nonNumber t′ (printTokenList ts) (λ n → Linked.head v tt n)
tokenFollow lbraceT   ts _ = tt
tokenFollow rbraceT   ts _ = tt
tokenFollow lbracketT ts _ = tt
tokenFollow rbracketT ts _ = tt
tokenFollow colonT    ts _ = tt
tokenFollow commaT    ts _ = tt
tokenFollow nullT     ts _ = tt
tokenFollow (boolT _) ts _ = tt
tokenFollow (stringT _) ts _ = tt

------------------------------------------------------------------------
-- The token language
------------------------------------------------------------------------

private
  skip-printToken : ∀ t R → skipWS (printToken t ++ R) ≡ printToken t ++ R
  skip-printToken t R with printToken-cons t
  ... | c , cs , eq , nw =
    trans (cong skipWS (cong (_++ R) eq))
    (trans (skipWS-nonWS c (cs ++ R) nw)
           (sym (cong (_++ R) eq)))

jsonLang : TokenLang
jsonLang = record
  { Token      = JSONToken
  ; print      = printToken
  ; lex        = lexToken
  ; skip       = skipWS
  ; skip-nil   = refl
  ; Valid      = ValidTokenSeq
  ; valid?     = validTokenSeq?
  ; valid-nil  = []
  ; valid-tail = Linked.tail
  ; print-cons = λ {t} _ → let c , cs , eq , _ = printToken-cons t in c , cs , eq
  ; skip-print = λ {t} {ts} _ → skip-printToken t (printTokenList ts)
  ; lex-print  = λ {t} {ts} v → lexToken-printToken t (printTokenList ts) (tokenFollow t ts v)
  }

open Lexing jsonLang public
  using (ValidTokens; tokenize; tokenizeLoop; lexValid; lexer)
  renaming (tokenize-printList to tokenize-printTokenList)

open Lexing.Fuel jsonLang skipWS-≤ lexToken-progress public
  using (tokenizeLoop-fuel; tokenizeLoop-mono; tokenizeLoop-sound)
