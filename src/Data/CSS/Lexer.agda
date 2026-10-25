{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The CSS tokenizer, and `lexer`: a stdlib RightInverse from valid token
-- streams to text
--
-- An instance of the generic `Data.Lexer`.  A stream is valid when every
-- token is well formed (`tokenWF`) and every token may be followed by the
-- first character of the next (`okFollow`): these are the streams whose
-- printed form lexes back to themselves.  White space is a token, so
-- nothing is skipped.
------------------------------------------------------------------------

module Data.CSS.Lexer where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.XML.Valid using (∧-split)
open import Data.Lexer
open import Data.CSS.Valid
open import Data.CSS.Token

------------------------------------------------------------------------
-- Valid token streams
------------------------------------------------------------------------

-- `validSeq′ t ts`: `t ∷ ts` is valid.
validSeq′ : CToken → List CToken → Bool
validSeq′ t []       = tokenWF t
validSeq′ t (u ∷ us) = tokenWF t ∧ okFollow t (firstCls u) ∧ validSeq′ u us

validSeq : List CToken → Bool
validSeq []       = true
validSeq (t ∷ ts) = validSeq′ t ts

ValidSeq : List CToken → Set
ValidSeq ts = validSeq ts ≡ true

private
  validSeq-wf : ∀ t ts → validSeq′ t ts ≡ true → tokenWF t ≡ true
  validSeq-wf t []       h = h
  validSeq-wf t (u ∷ us) h = proj₁ (∧-split {tokenWF t} {okFollow t (firstCls u) ∧ validSeq′ u us} h)

  validSeq-tail : ∀ t ts → validSeq′ t ts ≡ true → validSeq ts ≡ true
  validSeq-tail t []       h = refl
  validSeq-tail t (u ∷ us) h =
    proj₂ (∧-split {okFollow t (firstCls u)} {validSeq′ u us}
             (proj₂ (∧-split {tokenWF t} {okFollow t (firstCls u) ∧ validSeq′ u us} h)))

  -- What follows the printed token `t`, in a valid stream.
  follow : ∀ t ts → validSeq′ t ts ≡ true →
           okFollow t (headCls (concatMap printToken ts)) ≡ true
  follow t []       h = okFollow-other t
  follow t (u ∷ us) h with ∧-split {tokenWF t} {okFollow t (firstCls u) ∧ validSeq′ u us} h
  ... | _ , h₁ with ∧-split {okFollow t (firstCls u)} {validSeq′ u us} h₁
  ... | hf , h₂ with headCls-printToken u (concatMap printToken us) (validSeq-wf u us h₂)
  ... | eq = trans′ eq hf
    where
    trans′ : ∀ {k} → headCls (printToken u ++ concatMap printToken us) ≡ k →
             okFollow t k ≡ true → okFollow t (headCls (printToken u ++ concatMap printToken us)) ≡ true
    trans′ refl h = h

cssLang : TokenLang
cssLang = record
  { Token      = CToken
  ; print      = printToken
  ; lex        = lexToken
  ; skip       = λ cs → cs
  ; skip-nil   = refl
  ; Valid      = ValidSeq
  ; valid?     = λ ts → validSeq ts ≟ᵇ true
  ; valid-nil  = refl
  ; valid-tail = λ {t} {ts} → validSeq-tail t ts
  ; print-cons = λ {t} {ts} v → printToken-cons t (validSeq-wf t ts v)
  ; skip-print = λ _ → refl
  ; lex-print  = λ {t} {ts} v → lexToken-printToken t (concatMap printToken ts) (validSeq-wf t ts v) (follow t ts v)
  }

open Lexing cssLang public
