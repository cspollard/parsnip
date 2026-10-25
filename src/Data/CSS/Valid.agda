{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Character classes of CSS, and what counts as a well-formed token
--
-- The lexer (`Data.CSS.Token`) dispatches on the *class* of the first
-- character, `classOf`.  Every other character predicate is defined on
-- classes, so that the facts the proofs need ("a character that starts
-- an identifier has class `identStartC`", "a digit is not an identifier
-- start") hold by definition or by computation on literal characters,
-- never by arithmetic on code points.
--
-- The classes follow CSS Syntax Level 3 §4, with these restrictions
-- (the *strict* subset that the printer produces and the proofs cover):
--
-- * identifiers have no escapes; an identifier is
--   `-? [A-Za-z_ or non-ASCII] [A-Za-z0-9_- or non-ASCII]*` or starts `--`;
-- * delimiters are the ASCII punctuation that is not a token of its own;
-- * text in strings uses XML-legal characters (`Data.XML.Valid`), so a
--   style sheet can always be embedded in HTML, XML or SVG.
------------------------------------------------------------------------

module Data.CSS.Valid where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_; T)
open import Data.Bool.ListAction using (all)
open import Data.Char using (Char; toℕ)
open import Data.Char.Class using (inRange; is; range)
open import Data.Char.Properties using (_≟_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Data.Invertible.Char using (parseDigit)
open import Data.XML.Valid using (isValidChar)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Name Text : Set
Name = List Char
Text = List Char

------------------------------------------------------------------------
-- Classes
------------------------------------------------------------------------

data Cls : Set where
  wsC identStartC digitC minusC plusC dotC hashC atC slashC starC percentC : Cls
  dquoteC squoteC backslashC : Cls
  lparenC rparenC lbrackC rbrackC lbraceC rbraceC commaC colonC semiC : Cls
  delimC otherC : Cls

-- Letters, `_`, and the non-ASCII characters that XML allows.
isIdentStartRaw : Char → Bool
isIdentStartRaw c =
    range 'a' 'z' c ∨ range 'A' 'Z' c ∨ is '_' c
  ∨ inRange 0x80 0xD7FF c ∨ inRange 0xE000 0xFFFD c ∨ inRange 0x10000 0x10FFFF c

isWsRaw : Char → Bool
isWsRaw c = is c ' ' ∨ is c '\t' ∨ is c '\n' ∨ is c '\r' ∨ is c '\f'

-- The remaining ASCII punctuation, which is a delimiter on its own.
isOtherDelim : Char → Bool
isOtherDelim c =
    is c '!' ∨ is c '$' ∨ is c '&' ∨ is c '<' ∨ is c '=' ∨ is c '>'
  ∨ is c '?' ∨ is c '^' ∨ is c '`' ∨ is c '|' ∨ is c '~'

-- `classOfL` classifies the characters that are neither digits nor
-- identifier starts.  The digit decision comes first and is an argument of
-- `classOfD`, so that proofs can rewrite exactly that call: a character of
-- any class but `digitC` is not a digit (`parseDigit c ≡ nothing`).
classOfL : Char → Cls
classOfL c =
  if isWsRaw c then wsC else
  if is c '-' then minusC else
  if is c '+' then plusC else
  if is c '.' then dotC else
  if is c '#' then hashC else
  if is c '@' then atC else
  if is c '/' then slashC else
  if is c '*' then starC else
  if is c '%' then percentC else
  if is c '"' then dquoteC else
  if is c '\'' then squoteC else
  if is c '\\' then backslashC else
  if is c '(' then lparenC else
  if is c ')' then rparenC else
  if is c '[' then lbrackC else
  if is c ']' then rbrackC else
  if is c '{' then lbraceC else
  if is c '}' then rbraceC else
  if is c ',' then commaC else
  if is c ':' then colonC else
  if is c ';' then semiC else
  if isOtherDelim c then delimC else otherC

classOfD : Char → Maybe (Fin 10) → Cls
classOfD c (just _) = digitC
classOfD c nothing  = if isIdentStartRaw c then identStartC else classOfL c

classOf : Char → Cls
classOf c = classOfD c (parseDigit c)

-- The class of the first character of a text (`otherC` for none).
headCls : List Char → Cls
headCls []      = otherC
headCls (c ∷ _) = classOf c

------------------------------------------------------------------------
-- Predicates on classes
------------------------------------------------------------------------

identStartK digitK minusK plusK dotK percentK starK wsK lparenK : Cls → Bool
identStartK identStartC = true
identStartK _           = false
digitK digitC = true
digitK _      = false
minusK minusC = true
minusK _      = false
plusK plusC = true
plusK _     = false
dotK dotC = true
dotK _    = false
percentK percentC = true
percentK _        = false
starK starC = true
starK _     = false
wsK wsC = true
wsK _   = false
lparenK lparenC = true
lparenK _       = false

-- Characters that continue an identifier-like run.
identContK : Cls → Bool
identContK k = identStartK k ∨ digitK k ∨ minusK k

isIdentChar : Char → Bool
isIdentChar c = identContK (classOf c)

isIdentStart : Char → Bool
isIdentStart c = identStartK (classOf c)

isWs : Char → Bool
isWs c = wsK (classOf c)

------------------------------------------------------------------------
-- Identifiers
------------------------------------------------------------------------

-- Would these characters start an identifier?
startsIdent′ : Cls → List Char → Bool
startsIdent′ identStartC _        = true
startsIdent′ minusC      (d ∷ _)  = identStartK (classOf d) ∨ minusK (classOf d)
startsIdent′ _           _        = false

startsIdent : List Char → Bool
startsIdent []       = false
startsIdent (c ∷ cs) = startsIdent′ (classOf c) cs

isValidIdent : Name → Bool
isValidIdent n = startsIdent n ∧ all isIdentChar n

-- The name of a hash token: a non-empty run of identifier characters.
isValidHash : Name → Bool
isValidHash []       = false
isValidHash (c ∷ cs) = all isIdentChar (c ∷ cs)

-- Would these characters start a number: a digit, or `.` and a digit?
startsNumber′ : Cls → List Char → Bool
startsNumber′ digitC _        = true
startsNumber′ dotC   (d ∷ _)  = digitK (classOf d)
startsNumber′ _      _        = false

startsNumber : List Char → Bool
startsNumber []       = false
startsNumber (c ∷ cs) = startsNumber′ (classOf c) cs

------------------------------------------------------------------------
-- Delimiters and strings
------------------------------------------------------------------------

delimChars : List Char
delimChars =
  '!' ∷ '#' ∷ '$' ∷ '%' ∷ '&' ∷ '*' ∷ '+' ∷ '-' ∷ '.' ∷ '/' ∷ '<' ∷ '=' ∷ '>' ∷
  '?' ∷ '@' ∷ '^' ∷ '`' ∷ '|' ∷ '~' ∷ []

isDelimChar : Char → Bool
isDelimChar c = ⌊ c ∈? delimChars ⌋

isValidText : Text → Bool
isValidText = all isValidChar

------------------------------------------------------------------------
-- Facts about classes
------------------------------------------------------------------------

∨-false : ∀ {a b} → a ∨ b ≡ false → a ≡ false × b ≡ false
∨-false {false} {false} _ = refl , refl

not-true : ∀ {b} → not b ≡ true → b ≡ false
not-true {false} _ = refl

-- Facts proved by splitting on the 25 classes.
-- A text that starts an identifier starts with an identifier start or `-` and
-- another identifier start or `-`.
startsIdent′-true : ∀ k cs → startsIdent′ k cs ≡ true →
  (k ≡ identStartC) ⊎ (k ≡ minusC × ∃ λ d → ∃ λ ds → cs ≡ d ∷ ds × identStartK (classOf d) ∨ minusK (classOf d) ≡ true)
startsIdent′-true wsC cs ()
startsIdent′-true identStartC cs _ = inj₁ refl
startsIdent′-true digitC cs ()
startsIdent′-true minusC []       ()
startsIdent′-true minusC (d ∷ ds) h = inj₂ (refl , d , ds , refl , h)
startsIdent′-true plusC cs ()
startsIdent′-true dotC cs ()
startsIdent′-true hashC cs ()
startsIdent′-true atC cs ()
startsIdent′-true slashC cs ()
startsIdent′-true starC cs ()
startsIdent′-true percentC cs ()
startsIdent′-true dquoteC cs ()
startsIdent′-true squoteC cs ()
startsIdent′-true backslashC cs ()
startsIdent′-true lparenC cs ()
startsIdent′-true rparenC cs ()
startsIdent′-true lbrackC cs ()
startsIdent′-true rbrackC cs ()
startsIdent′-true lbraceC cs ()
startsIdent′-true rbraceC cs ()
startsIdent′-true commaC cs ()
startsIdent′-true colonC cs ()
startsIdent′-true semiC cs ()
startsIdent′-true delimC cs ()
startsIdent′-true otherC cs ()

-- Neither an identifier start nor `-` does not start an identifier.
startsIdent′-false : ∀ k cs → identStartK k ≡ false → minusK k ≡ false → startsIdent′ k cs ≡ false
startsIdent′-false wsC cs _ _ = refl
startsIdent′-false identStartC cs () _
startsIdent′-false digitC cs _ _ = refl
startsIdent′-false minusC cs _ ()
startsIdent′-false plusC cs _ _ = refl
startsIdent′-false dotC cs _ _ = refl
startsIdent′-false hashC cs _ _ = refl
startsIdent′-false atC cs _ _ = refl
startsIdent′-false slashC cs _ _ = refl
startsIdent′-false starC cs _ _ = refl
startsIdent′-false percentC cs _ _ = refl
startsIdent′-false dquoteC cs _ _ = refl
startsIdent′-false squoteC cs _ _ = refl
startsIdent′-false backslashC cs _ _ = refl
startsIdent′-false lparenC cs _ _ = refl
startsIdent′-false rparenC cs _ _ = refl
startsIdent′-false lbrackC cs _ _ = refl
startsIdent′-false rbrackC cs _ _ = refl
startsIdent′-false lbraceC cs _ _ = refl
startsIdent′-false rbraceC cs _ _ = refl
startsIdent′-false commaC cs _ _ = refl
startsIdent′-false colonC cs _ _ = refl
startsIdent′-false semiC cs _ _ = refl
startsIdent′-false delimC cs _ _ = refl
startsIdent′-false otherC cs _ _ = refl

-- Neither a digit nor `.` does not start a number.
startsNumber′-false : ∀ k cs → digitK k ≡ false → dotK k ≡ false → startsNumber′ k cs ≡ false
startsNumber′-false wsC cs _ _ = refl
startsNumber′-false identStartC cs _ _ = refl
startsNumber′-false digitC cs () _
startsNumber′-false minusC cs _ _ = refl
startsNumber′-false plusC cs _ _ = refl
startsNumber′-false dotC cs _ ()
startsNumber′-false hashC cs _ _ = refl
startsNumber′-false atC cs _ _ = refl
startsNumber′-false slashC cs _ _ = refl
startsNumber′-false starC cs _ _ = refl
startsNumber′-false percentC cs _ _ = refl
startsNumber′-false dquoteC cs _ _ = refl
startsNumber′-false squoteC cs _ _ = refl
startsNumber′-false backslashC cs _ _ = refl
startsNumber′-false lparenC cs _ _ = refl
startsNumber′-false rparenC cs _ _ = refl
startsNumber′-false lbrackC cs _ _ = refl
startsNumber′-false rbrackC cs _ _ = refl
startsNumber′-false lbraceC cs _ _ = refl
startsNumber′-false rbraceC cs _ _ = refl
startsNumber′-false commaC cs _ _ = refl
startsNumber′-false colonC cs _ _ = refl
startsNumber′-false semiC cs _ _ = refl
startsNumber′-false delimC cs _ _ = refl
startsNumber′-false otherC cs _ _ = refl

identStartK-true : ∀ k → identStartK k ≡ true → k ≡ identStartC
identStartK-true wsC ()
identStartK-true identStartC _ = refl
identStartK-true digitC ()
identStartK-true minusC ()
identStartK-true plusC ()
identStartK-true dotC ()
identStartK-true hashC ()
identStartK-true atC ()
identStartK-true slashC ()
identStartK-true starC ()
identStartK-true percentC ()
identStartK-true dquoteC ()
identStartK-true squoteC ()
identStartK-true backslashC ()
identStartK-true lparenC ()
identStartK-true rparenC ()
identStartK-true lbrackC ()
identStartK-true rbrackC ()
identStartK-true lbraceC ()
identStartK-true rbraceC ()
identStartK-true commaC ()
identStartK-true colonC ()
identStartK-true semiC ()
identStartK-true delimC ()
identStartK-true otherC ()

minusK-true : ∀ k → minusK k ≡ true → k ≡ minusC
minusK-true wsC ()
minusK-true identStartC ()
minusK-true digitC ()
minusK-true minusC _ = refl
minusK-true plusC ()
minusK-true dotC ()
minusK-true hashC ()
minusK-true atC ()
minusK-true slashC ()
minusK-true starC ()
minusK-true percentC ()
minusK-true dquoteC ()
minusK-true squoteC ()
minusK-true backslashC ()
minusK-true lparenC ()
minusK-true rparenC ()
minusK-true lbrackC ()
minusK-true rbrackC ()
minusK-true lbraceC ()
minusK-true rbraceC ()
minusK-true commaC ()
minusK-true colonC ()
minusK-true semiC ()
minusK-true delimC ()
minusK-true otherC ()
