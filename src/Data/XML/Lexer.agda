{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The tokenizer, and `lexer`: a stdlib RightInverse from valid token
-- streams to text
--
-- An instance of the generic `Data.Lexer`: `tokenize` lexes tokens one at
-- a time with `lexToken` (`Data.XML.Token`); white space is significant,
-- so nothing is skipped.  `lexer` is a `RightInverse` out of
-- `ValidTokens`, the token streams that print and lex back to themselves:
-- every token is well formed (`tokenWF`), no two character-data tokens are
-- adjacent (they would print as one), and the stream does not end in
-- character data (which needs a following `<`).  Its `from` is total by
-- checking validity of the tokenizer's output, which is decidable, and
-- falling back to the empty stream.
--
-- The validity of a stream is stated by `Run p q`, a small state machine
-- (the state is "the previous token was text"); `ValidSeq` is "valid from
-- some state", which is closed under tails as `Data.Lexer` needs.
------------------------------------------------------------------------

module Data.XML.Lexer where

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Data.Bool using (Bool; true; false; _∧_; not; T)
open import Data.Bool.Properties using (T?) renaming (_≟_ to _≟ᵇ_)
open import Data.Char using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n+m; n<1+n)
open import Data.List.Properties using (length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (RightInverse)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; setoid)

open import Data.XML.Escape using (escapeText-head)
open import Data.Lexer using (TokenLang; module Lexing)
open import Data.XML.Token
open import Data.XML.Progress using (lexToken-progress)
open import Data.Stage using (Chars; Subtype)

------------------------------------------------------------------------
-- Valid token streams
------------------------------------------------------------------------

isText : XMLToken → Bool
isText (textT _) = true
isText _         = false

-- `Run p q ts`: reading `ts` from state `p` ("the previous token was
-- text") every token is well formed and follows no text token with
-- another, ending in state `q`.
data Run : Bool → Bool → List XMLToken → Set where
  done : ∀ {p} → Run p p []
  step : ∀ {p q t ts} → tokenWF t ≡ true → T (not (p ∧ isText t)) →
         Run (isText t) q ts → Run p q (t ∷ ts)

ValidTokenSeq : List XMLToken → Set
ValidTokenSeq = Run false false

run++ : ∀ {p q r xs ys} → Run p q xs → Run q r ys → Run p r (xs ++ ys)
run++ done           ys = ys
run++ (step wf nt xs) ys = step wf nt (run++ xs ys)

run? : ∀ p q ts → Dec (Run p q ts)
run? p q [] with p ≟ᵇ q
... | yes refl = yes done
... | no  p≢q  = no (λ { done → p≢q refl })
run? p q (t ∷ ts) with tokenWF t ≟ᵇ true | T? (not (p ∧ isText t)) | run? (isText t) q ts
... | yes a | yes b | yes c = yes (step a b c)
... | no ¬a | _     | _     = no (λ { (step a _ _) → ¬a a })
... | _     | no ¬b | _     = no (λ { (step _ b _) → ¬b b })
... | _     | _     | no ¬c = no (λ { (step _ _ c) → ¬c c })

validTokenSeq? : ∀ ts → Dec (ValidTokenSeq ts)
validTokenSeq? = run? false false

------------------------------------------------------------------------
-- Facts about printed tokens
------------------------------------------------------------------------

-- Every well-formed token prints to something non-empty.
printToken-cons : ∀ t → tokenWF t ≡ true → ∃ λ c → ∃ λ cs → printToken t ≡ c ∷ cs
printToken-cons (openT n as)   _  = '<' , _ , refl
printToken-cons (selfT n as)   _  = '<' , _ , refl
printToken-cons (closeT n)     _  = '<' , _ , refl
printToken-cons (textT [])     ()
printToken-cons (textT (c ∷ cs)) _ with escapeText-head c cs
... | d , ds , eq , _ = d , ds , eq

-- A tag starts with `<`.
tag-startsLt : ∀ t → T (not (isText t)) → ∃ λ r → printToken t ≡ '<' ∷ r
tag-startsLt (openT n as) _ = _ , refl
tag-startsLt (selfT n as) _ = _ , refl
tag-startsLt (closeT n)   _ = _ , refl
tag-startsLt (textT _)    ()

-- In a valid stream, the text after a token may follow it.
tokenFollow : ∀ {p t ts} → Run p false (t ∷ ts) → TokenFollow t (printTokenList ts)
tokenFollow {t = openT _ _}  _ = tt
tokenFollow {t = selfT _ _}  _ = tt
tokenFollow {t = closeT _}   _ = tt
tokenFollow {t = textT _} {ts = []} (step _ _ ())
tokenFollow {t = textT _} {ts = t′ ∷ ts} (step _ _ (step _ nt _)) with tag-startsLt t′ nt
... | r , eq = (r ++ printTokenList ts) , cong (_++ printTokenList ts) eq

------------------------------------------------------------------------
-- The token language
------------------------------------------------------------------------

-- A stream is valid if it is, from some state.
ValidSeq : List XMLToken → Set
ValidSeq ts = ∃ λ p → Run p false ts

private
  -- Starting from `false` is the weakest requirement.
  weaken : ∀ {p ts} → Run p false ts → ValidTokenSeq ts
  weaken done           = done
  weaken (step wf _ r)  = step wf tt r

  validSeq? : ∀ ts → Dec (ValidSeq ts)
  validSeq? ts with validTokenSeq? ts
  ... | yes r  = yes (false , r)
  ... | no  ¬r = no (λ { (p , r) → ¬r (weaken r) })

  run-tail : ∀ {p t ts} → Run p false (t ∷ ts) → ValidSeq ts
  run-tail (step _ _ r) = _ , r

  run-wf : ∀ {p t ts} → Run p false (t ∷ ts) → tokenWF t ≡ true
  run-wf (step wf _ _) = wf

xmlLang : TokenLang
xmlLang = record
  { Token      = XMLToken
  ; print      = printToken
  ; lex        = lexToken
  ; skip       = λ cs → cs
  ; skip-nil   = refl
  ; Valid      = ValidSeq
  ; valid?     = validSeq?
  ; valid-nil  = false , done
  ; valid-tail = λ { (_ , r) → run-tail r }
  ; print-cons = λ { {t} {ts} (_ , r) → printToken-cons t (run-wf {t = t} {ts = ts} r) }
  ; skip-print = λ _ → refl
  ; lex-print  = λ { {t} {ts} (_ , r) → lexToken-printToken t (printTokenList ts) (run-wf {t = t} {ts = ts} r) (tokenFollow r) }
  }

open Lexing xmlLang public
  using (ValidTokens; tokenize; tokenizeLoop; lexValid; lexer)
  renaming (tokenize-printList to tokenize-printTokenList)

open Lexing.Fuel xmlLang (λ _ → ≤-refl) lexToken-progress public
  using (tokenizeLoop-fuel; tokenizeLoop-mono; tokenizeLoop-sound; tokenizeFast; tokenizeFast-sound; tokenizeString; tokenizeString-sound)

-- A stream valid from the start is valid.
valid-run : ∀ {ts} → Run false false ts → ValidSeq ts
valid-run r = false , r
