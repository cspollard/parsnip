{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- HTML tokens: printing, and the prefix lexer for one token
--
-- An HTML token is an XML token (`Data.XML.Token`: tags with their
-- attributes, and escaped character data), or `rawT n as b`, a whole
-- raw-text element `<n a="v" …>b</n>` whose body `b` is not escaped.  The
-- lexer is the XML lexer, except that after the start tag of a raw-text
-- tag (`isRawTag`) it reads the body up to the first `</`, which must be
-- the matching end tag.  Void elements print as the XML self-closing tag
-- `<br />`, which HTML accepts.
--
-- `lexToken-printToken` is the prefix round trip: a well-formed token is
-- read back from its printed form, whatever follows (text must be
-- followed by `<`).
------------------------------------------------------------------------

module Data.HTML.Token where

open import Data.Bool using (Bool; true; false; _∧_; not; T)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; map₁; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Data.Char.Class using (is)
open import Data.XML.Valid using (Name; Text; Attributes; isValidName; eqName; ∧-join; ∧-split)
open import Data.XML.Token using (XMLToken; openT; selfT; closeT; textT; attrNamesValid)
import Data.XML.Token as X
open import Data.HTML.Valid

------------------------------------------------------------------------
-- Tokens and their spelling
------------------------------------------------------------------------

data HToken : Set where
  tok  : XMLToken → HToken
  rawT : Name → Attributes → Text → HToken

printToken : HToken → List Char
printToken (tok t)       = X.printToken t
printToken (rawT n as b) = X.printToken (openT n as) ++ b ++ X.printToken (closeT n)

printTokenList : List HToken → List Char
printTokenList = concatMap printToken

-- Tokens that print and lex back.  A start tag of a raw-text element
-- would be lexed as `rawT`, so it is not well formed as a plain tag.
tokenWF : HToken → Bool
tokenWF (tok (openT n as)) = X.tokenWF (openT n as) ∧ not (isRawTag n)
tokenWF (tok t)            = X.tokenWF t
tokenWF (rawT n as b)      = X.tokenWF (openT n as) ∧ isRawTag n ∧ noEndTag b

TokenFollow : HToken → List Char → Set
TokenFollow (tok t)      rest = X.TokenFollow t rest
TokenFollow (rawT _ _ _) _    = ⊤

------------------------------------------------------------------------
-- Lexing
------------------------------------------------------------------------

-- The text before the first `</`, and the text from there.
rawSplit : List Char → Maybe (Text × List Char)
rawSplit₁ : Char → List Char → Bool → Maybe (Text × List Char)

slashNext : List Char → Bool
slashNext []      = false
slashNext (d ∷ _) = is '/' d

rawSplit []       = nothing
rawSplit (c ∷ cs) = rawSplit₁ c cs (is '<' c ∧ slashNext cs)

rawSplit₁ c cs true  = just ([] , c ∷ cs)
rawSplit₁ c cs false = Maybe.map (map₁ (c ∷_)) (rawSplit cs)

-- The body of a raw-text element, read after its start tag.
rawClose₂ : Name → Attributes → Text → List Char → Bool → Maybe (HToken × List Char)
rawClose₂ n as b rest true  = just (rawT n as b , rest)
rawClose₂ n as b rest false = nothing

rawClose : Name → Attributes → Text → Maybe (XMLToken × List Char) → Maybe (HToken × List Char)
rawClose n as b (just (closeT m , rest)) = rawClose₂ n as b rest (eqName n m)
rawClose n as b _                        = nothing

rawFinish : Name → Attributes → Maybe (Text × List Char) → Maybe (HToken × List Char)
rawFinish n as nothing           = nothing
rawFinish n as (just (b , tl))   = rawClose n as b (X.lexToken tl)

lexOpen : Bool → Name → Attributes → List Char → Maybe (HToken × List Char)
lexOpen false n as rest = just (tok (openT n as) , rest)
lexOpen true  n as rest = rawFinish n as (rawSplit rest)

lexStep : Maybe (XMLToken × List Char) → Maybe (HToken × List Char)
lexStep nothing                      = nothing
lexStep (just (openT n as , rest))   = lexOpen (isRawTag n) n as rest
lexStep (just (t , rest))            = just (tok t , rest)

lexToken : List Char → Maybe (HToken × List Char)
lexToken cs = lexStep (X.lexToken cs)

------------------------------------------------------------------------
-- Round trip
------------------------------------------------------------------------

private
  eq-false : ∀ {b} → not b ≡ true → b ≡ false
  eq-false {false} _ = refl

  not-and : ∀ a b → not (a ∧ b) ≡ true → a ∧ b ≡ false
  not-and a b h = eq-false h

  -- No `</` in `b` means `rawSplit` finds the one after it.
  rawSplit-++ : ∀ b Y → noEndTag b ≡ true →
                rawSplit (b ++ '<' ∷ '/' ∷ Y) ≡ just (b , '<' ∷ '/' ∷ Y)
  rawSplit-++ []       Y _  = refl
  rawSplit-++ (c ∷ []) Y _  = cong (rawSplit₁ c ('<' ∷ '/' ∷ Y)) (andFalse (is '<' c))
    where
    andFalse : ∀ x → x ∧ false ≡ false
    andFalse true  = refl
    andFalse false = refl
  rawSplit-++ (c ∷ d ∷ cs) Y h =
    rawSplit-step c d cs Y (proj₁ (∧-split {not (is '<' c ∧ is '/' d)} {noEndTag (d ∷ cs)} h))
                  (rawSplit-++ (d ∷ cs) Y (proj₂ (∧-split {not (is '<' c ∧ is '/' d)} {noEndTag (d ∷ cs)} h)))
    where
    rawSplit-step : ∀ c d cs Y → not (is '<' c ∧ is '/' d) ≡ true →
      rawSplit (d ∷ cs ++ '<' ∷ '/' ∷ Y) ≡ just (d ∷ cs , '<' ∷ '/' ∷ Y) →
      rawSplit ((c ∷ d ∷ cs) ++ '<' ∷ '/' ∷ Y) ≡ just (c ∷ d ∷ cs , '<' ∷ '/' ∷ Y)
    rawSplit-step c d cs Y hn ih =
      trans (cong (rawSplit₁ c (d ∷ cs ++ '<' ∷ '/' ∷ Y)) (not-and (is '<' c) (is '/' d) hn))
            (cong (Maybe.map (map₁ (c ∷_))) ih)

lexToken-printToken : ∀ t rest → tokenWF t ≡ true → TokenFollow t rest →
                      lexToken (printToken t ++ rest) ≡ just (t , rest)
lexToken-printToken (tok (openT n as)) rest wf fol with ∧-split wf
... | hx , hr =
  trans (cong lexStep (X.lexToken-printToken (openT n as) rest hx fol))
        (cong (λ b → lexOpen b n as rest) (eq-false hr))
lexToken-printToken (tok (selfT n as)) rest wf fol =
  cong lexStep (X.lexToken-printToken (selfT n as) rest wf fol)
lexToken-printToken (tok (closeT n)) rest wf fol =
  cong lexStep (X.lexToken-printToken (closeT n) rest wf fol)
lexToken-printToken (tok (textT x)) rest wf fol =
  cong lexStep (X.lexToken-printToken (textT x) rest wf fol)
lexToken-printToken (rawT n as b) rest wf _ with ∧-split wf
... | hx , hrest with ∧-split hrest
... | hraw , hb =
  trans (cong lexToken (trans (++-assoc (X.printToken (openT n as)) (b ++ X.printToken (closeT n)) rest)
                              (cong (X.printToken (openT n as) ++_) (++-assoc b (X.printToken (closeT n)) rest))))
  (trans (cong lexStep (X.lexToken-printToken (openT n as) (b ++ X.printToken (closeT n) ++ rest) hx tt))
  (trans (cong (λ x → lexOpen x n as (b ++ X.printToken (closeT n) ++ rest)) hraw)
  (trans (cong (rawFinish n as) (rawSplit-++ b ((n ++ '>' ∷ []) ++ rest) hb))
  (trans (cong (rawClose n as b) (X.lexToken-printToken (closeT n) rest (proj₁ (∧-split hx)) tt))
         (cong (rawClose₂ n as b rest) (eqName-refl n))))))
