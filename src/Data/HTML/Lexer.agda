{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The tokenizer, and `lexer`: a stdlib RightInverse from valid token
-- streams to text
--
-- An instance of the generic `Data.Lexer`, exactly as for XML
-- (`Data.XML.Lexer`): a stream is valid when every token is well formed
-- and no two character-data tokens are adjacent, and it does not end in
-- character data.
------------------------------------------------------------------------

module Data.HTML.Lexer where

open import Data.Bool using (Bool; true; false; _∧_; not; T)
open import Data.Bool.Properties using (T?) renaming (_≟_ to _≟ᵇ_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.XML.Token using (openT; selfT; closeT; textT)
import Data.XML.Token as X
open import Data.XML.Escape using (escapeText-head)
open import Data.Lexer using (TokenLang; module Lexing)
open import Data.HTML.Token

------------------------------------------------------------------------
-- Valid token streams
------------------------------------------------------------------------

isText : HToken → Bool
isText (tok (textT _)) = true
isText _               = false

-- `Run p q ts`: reading `ts` from state `p` ("the previous token was
-- text") every token is well formed and follows no text token with
-- another, ending in state `q`.
data Run : Bool → Bool → List HToken → Set where
  done : ∀ {p} → Run p p []
  step : ∀ {p q t ts} → tokenWF t ≡ true → T (not (p ∧ isText t)) →
         Run (isText t) q ts → Run p q (t ∷ ts)

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

------------------------------------------------------------------------
-- Facts about printed tokens
------------------------------------------------------------------------

printToken-cons : ∀ t → tokenWF t ≡ true → ∃ λ c → ∃ λ cs → printToken t ≡ c ∷ cs
printToken-cons (tok (openT n as))      _  = '<' , _ , refl
printToken-cons (tok (selfT n as))      _  = '<' , _ , refl
printToken-cons (tok (closeT n))        _  = '<' , _ , refl
printToken-cons (tok (textT []))        ()
printToken-cons (tok (textT (c ∷ cs))) wf with escapeText-head c cs
... | d , ds , eq , _ = d , ds , eq
printToken-cons (rawT n as b)           _  = '<' , _ , refl

-- A tag starts with `<`.
tag-startsLt : ∀ t → T (not (isText t)) → ∃ λ r → printToken t ≡ '<' ∷ r
tag-startsLt (tok (openT n as)) _ = _ , refl
tag-startsLt (tok (selfT n as)) _ = _ , refl
tag-startsLt (tok (closeT n))   _ = _ , refl
tag-startsLt (tok (textT _))    ()
tag-startsLt (rawT n as b)      _ = _ , refl

-- In a valid stream, the text after a token may follow it.
tokenFollow : ∀ {p t ts} → Run p false (t ∷ ts) → TokenFollow t (printTokenList ts)
tokenFollow {t = tok (openT _ _)} _ = tt
tokenFollow {t = tok (selfT _ _)} _ = tt
tokenFollow {t = tok (closeT _)}  _ = tt
tokenFollow {t = rawT _ _ _}      _ = tt
tokenFollow {t = tok (textT _)} {ts = []} (step _ _ ())
tokenFollow {t = tok (textT _)} {ts = t′ ∷ ts} (step _ _ (step _ nt _)) with tag-startsLt t′ nt
... | r , eq = (r ++ printTokenList ts) , cong (_++ printTokenList ts) eq

------------------------------------------------------------------------
-- The token language
------------------------------------------------------------------------

-- A stream is valid if it is, from some state.
ValidSeq : List HToken → Set
ValidSeq ts = ∃ λ p → Run p false ts

private
  weaken : ∀ {p ts} → Run p false ts → Run false false ts
  weaken done           = done
  weaken (step wf _ r)  = step wf tt r

  validSeq? : ∀ ts → Dec (ValidSeq ts)
  validSeq? ts with run? false false ts
  ... | yes r  = yes (false , r)
  ... | no  ¬r = no (λ { (p , r) → ¬r (weaken r) })

  run-tail : ∀ {p t ts} → Run p false (t ∷ ts) → ValidSeq ts
  run-tail (step _ _ r) = _ , r

  run-wf : ∀ {p t ts} → Run p false (t ∷ ts) → tokenWF t ≡ true
  run-wf (step wf _ _) = wf

htmlLang : TokenLang
htmlLang = record
  { Token      = HToken
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

open Lexing htmlLang public
  using (ValidTokens; tokenize; tokenizeLoop; lexValid; lexer)
  renaming (tokenize-printList to tokenize-printTokenList)

-- A stream valid from the start is valid.
valid-run : ∀ {ts} → Run false false ts → ValidSeq ts
valid-run r = false , r
