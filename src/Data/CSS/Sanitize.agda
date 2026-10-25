{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Total CSS constructors for runtime data
--
-- The AST only holds well-formed tokens (`Data.CSS.Token.tokenWF`).
-- Data computed at runtime cannot be checked statically, so these
-- constructors repair it, in the manner of `Data.XML.Sanitize`:
--
-- * a character that is not legal XML becomes U+FFFD in strings;
-- * an identifier that is not valid is repaired character by character
--   (`_` for each character that cannot occur, and for a bad first
--   character), and the empty identifier becomes `_`;
-- * a delimiter that is not a legal delimiter becomes `*`.
--
-- Valid input is left unchanged, and each repair comes with the proof
-- that its output is valid.  Use the constructors of `Data.CSS.AST`
-- directly when the content is known to be valid.
------------------------------------------------------------------------

module Data.CSS.Sanitize where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; map)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Sanitize
open import Data.CSS.Valid
open import Data.CSS.Number using (CSSNumber)
open import Data.CSS.Token
open import Data.CSS.AST

------------------------------------------------------------------------
-- Identifiers
------------------------------------------------------------------------

private
  start-ok : ∀ c cs → isIdentStart c ≡ true → startsIdent′ (classOf c) cs ≡ true
  start-ok c cs h rewrite identStartK-true (classOf c) h = refl

  cont-ok : ∀ c → isIdentStart c ≡ true → isIdentChar c ≡ true
  cont-ok c h rewrite identStartK-true (classOf c) h = refl

  -- Each character that cannot occur becomes `_`.
  repairIdent : Name → Name
  repairIdent []       = '_' ∷ []
  repairIdent (c ∷ cs) = fixWith isIdentStart '_' c ∷ map (fixWith isIdentChar '_') cs

  repairIdent-valid : ∀ n → isValidIdent (repairIdent n) ≡ true
  repairIdent-valid []       = refl
  repairIdent-valid (c ∷ cs) =
    both (start-ok (fixWith isIdentStart '_' c) (map (fixWith isIdentChar '_') cs)
                   (fixWith-ok isIdentStart '_' refl c))
         (both (cont-ok (fixWith isIdentStart '_' c) (fixWith-ok isIdentStart '_' refl c))
               (all-map isIdentChar (fixWith isIdentChar '_') (fixWith-ok isIdentChar '_' refl) cs))

  fixIdentB : Bool → Name → Name
  fixIdentB true  n = n
  fixIdentB false n = repairIdent n

fixIdent : Name → Name
fixIdent n = fixIdentB (isValidIdent n) n

fixIdent-valid : ∀ n → isValidIdent (fixIdent n) ≡ true
fixIdent-valid n = go (isValidIdent n) refl
  where
  go : ∀ b → isValidIdent n ≡ b → isValidIdent (fixIdentB b n) ≡ true
  go true  eq = eq
  go false _  = repairIdent-valid n

-- A hash name: any run of identifier characters, not empty.
fixHash : Name → Name
fixHash []       = '_' ∷ []
fixHash (c ∷ cs) = map (fixWith isIdentChar '_') (c ∷ cs)

fixHash-valid : ∀ n → isValidHash (fixHash n) ≡ true
fixHash-valid []       = refl
fixHash-valid (c ∷ cs) =
  both (fixWith-ok isIdentChar '_' refl c)
       (all-map isIdentChar (fixWith isIdentChar '_') (fixWith-ok isIdentChar '_' refl) cs)

fixDelim : Char → Char
fixDelim = fixWith isDelimChar '*'

fixDelim-valid : ∀ c → isDelimChar (fixDelim c) ≡ true
fixDelim-valid = fixWith-ok isDelimChar '*' refl

------------------------------------------------------------------------
-- Leaves
------------------------------------------------------------------------

ident′ : Name → CV
ident′ n = leaf (identT (fixIdent n)) (fromEq (fixIdent-valid n))

atKeyword′ : Name → CV
atKeyword′ n = leaf (atT (fixIdent n)) (fromEq (fixIdent-valid n))

hash′ : Name → CV
hash′ n = leaf (hashT (fixHash n)) (fromEq (fixHash-valid n))

string′ : Text → CV
string′ s = leaf (stringT (fixText s)) (fromEq (fixText-valid s))

dimension′ : CSSNumber → Name → CV
dimension′ x u = leaf (dimT x (fixIdent u)) (fromEq (fixIdent-valid u))

delim : Char → CV
delim c = leaf (delimT (fixDelim c)) (fromEq (fixDelim-valid c))

function′ : Name → List CV → CV
function′ n vs = func (fixIdent n) (fromEq (fixIdent-valid n)) vs

number : CSSNumber → CV
number x = leaf (numberT x) _

percentage : CSSNumber → CV
percentage x = leaf (percentT x) _

whitespace colon semicolon comma : CV
whitespace = leaf wsT _
colon      = leaf colonT _
semicolon  = leaf semiT _
comma      = leaf commaT _

-- From strings.
ident atKeyword hash string : String → CV
ident     s = ident′ (toList s)
atKeyword s = atKeyword′ (toList s)
hash      s = hash′ (toList s)
string    s = string′ (toList s)

dimension : CSSNumber → String → CV
dimension x u = dimension′ x (toList u)

function : String → List CV → CV
function n vs = function′ (toList n) vs
