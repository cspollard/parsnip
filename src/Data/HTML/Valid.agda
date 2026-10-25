{-# OPTIONS --safe --cubical-compatible #-}

------------------------------------------------------------------------
-- What counts as well-formed HTML content
--
-- The strict, canonical subset that the printer writes and the parser
-- reads (see `Data.HTML.AST`):
--
-- * names are XML names (`Data.XML.Valid`) without capital letters, for
--   tags and attributes: HTML names are case-insensitive, and lower case
--   is the canonical spelling;
-- * the tags in `voidTags` have no content and no end tag (`<br />`);
-- * the tags in `rawTags` (`script`, `style`) have one text body, which
--   is not escaped, and so must not contain `</` (it would end the
--   element for any reader);
-- * after the start tag of a `pre`-like element a browser drops one
--   newline, so its content may not start with one.
------------------------------------------------------------------------

module Data.HTML.Valid where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; T)
open import Data.Bool.ListAction using (all; any)
open import Data.Char using (Char; toℕ)
open import Data.Nat.Properties using (≡⇒≡ᵇ)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Char.Class using (is; range)
open import Data.XML.Valid
  using (Name; Text; Attributes; isValidName; isValidAttrs; isValidText; eqName; ∧-join; ∧-split)

------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------

isLowerName : Name → Bool
isLowerName = all (λ c → not (range 'A' 'Z' c))

attrsLower : Attributes → Bool
attrsLower = all (λ a → isLowerName (proj₁ a))

-- A tag name and attributes that can be printed.
okTag : Name → Attributes → Bool
okTag n as = isValidName n ∧ isLowerName n ∧ isValidAttrs as ∧ attrsLower as

private
  names : List String → List Name
  names = map toList

voidTags rawTags preTags : List Name
voidTags = names ( "area" ∷ "base" ∷ "br" ∷ "col" ∷ "embed" ∷ "hr" ∷ "img" ∷ "input"
                 ∷ "link" ∷ "meta" ∷ "param" ∷ "source" ∷ "track" ∷ "wbr" ∷ [] )
rawTags  = names ( "script" ∷ "style" ∷ [] )
preTags  = names ( "listing" ∷ "pre" ∷ "textarea" ∷ [] )

isVoidTag isRawTag isPreTag : Name → Bool
isVoidTag n = any (eqName n) voidTags
isRawTag  n = any (eqName n) rawTags
isPreTag  n = any (eqName n) preTags

------------------------------------------------------------------------
-- Text
------------------------------------------------------------------------

-- No `</` anywhere: the body of a raw-text element ends at its end tag.
noEndTag : Text → Bool
noEndTag []           = true
noEndTag (c ∷ [])     = true
noEndTag (c ∷ d ∷ cs) = not (is '<' c ∧ is '/' d) ∧ noEndTag (d ∷ cs)

startsNewline : Text → Bool
startsNewline []      = false
startsNewline (c ∷ _) = is '\n' c

------------------------------------------------------------------------
-- Elements
------------------------------------------------------------------------

okVoid : Name → Attributes → Bool
okVoid n as = isVoidTag n ∧ okTag n as

okRaw : Name → Attributes → Text → Bool
okRaw n as b = isRawTag n ∧ okTag n as ∧ noEndTag b ∧ isValidText b

-- An element with content: neither void nor raw, and the content does
-- not start with a newline in a `pre`-like element.
okElem : Name → Attributes → Text → Bool
okElem n as t =
  not (isVoidTag n) ∧ not (isRawTag n) ∧ okTag n as ∧ isValidText t
  ∧ not (isPreTag n ∧ startsNewline t)

------------------------------------------------------------------------
-- Facts used by the lexer and parser
------------------------------------------------------------------------

toEq : ∀ {b} → T b → b ≡ true
toEq {true} _ = refl

eqName-refl : ∀ n → eqName n n ≡ true
eqName-refl []      = refl
eqName-refl (c ∷ n) = ∧-join (toEq (≡⇒≡ᵇ (toℕ c) (toℕ c) refl)) (eqName-refl n)
