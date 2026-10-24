{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Total XML constructors for runtime data
--
-- The AST only holds well-formed content (`Data.XML.Valid`).  Data that is
-- computed at runtime (feature names, projected coordinates, attribute
-- lists) cannot be checked statically, so these constructors repair it:
--
-- * a character that is not legal XML becomes U+FFFD in text and values;
-- * a character that is not legal in a name becomes `_`, and an empty
--   name becomes `_`;
-- * if an attribute name occurs more than once, the last occurrence wins.
--
-- Valid input is left unchanged (every repair is the identity there), and
-- each repair comes with the proof that its output is valid.  Use
-- `Data.XML.AST.node`, `leaf` and `parent` directly when the content is
-- known to be valid.
------------------------------------------------------------------------

module Data.XML.Sanitize where

open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_; T)
open import Data.Char using (Char)
open import Data.String using (String; toList)
open import Data.List using (List; []; _∷_; map; foldr)
open import Data.Bool.ListAction using (all)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂; map₁; map₂)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.XML.Valid
open import Data.XML.AST

private variable
  A : Set

fromEq : ∀ {b} → b ≡ true → T b
fromEq refl = tt

both : ∀ {x y} → x ≡ true → y ≡ true → x ∧ y ≡ true
both refl refl = refl

------------------------------------------------------------------------
-- Repairing characters
------------------------------------------------------------------------

-- `c` if it satisfies `ok`, and the replacement `d` otherwise.
fixWith : (Char → Bool) → Char → Char → Char
fixWith ok d c = if ok c then c else d

fixWith-ok : ∀ (ok : Char → Bool) (d : Char) → ok d ≡ true →
             ∀ (c : Char) → ok (fixWith ok d c) ≡ true
fixWith-ok ok d hd c = go (ok c) refl
  where
  go : ∀ (b : Bool) → ok c ≡ b → ok (if b then c else d) ≡ true
  go true  eq = eq
  go false eq = hd

all-map : ∀ (p : Char → Bool) (f : Char → Char) → (∀ c → p (f c) ≡ true) →
          ∀ (cs : List Char) → all p (map f cs) ≡ true
all-map p f h []       = refl
all-map p f h (c ∷ cs) rewrite h c = all-map p f h cs

------------------------------------------------------------------------
-- Text and names
------------------------------------------------------------------------

fixText : Text → Text
fixText = map (fixWith isValidChar '\xFFFD')

fixText-valid : ∀ t → isValidText (fixText t) ≡ true
fixText-valid = all-map isValidChar (fixWith isValidChar '\xFFFD') (fixWith-ok isValidChar '\xFFFD' refl)

fixStart-ok : ∀ c → isNameStart (fixWith isNameStart '_' c) ≡ true
fixStart-ok = fixWith-ok isNameStart '_' refl

fixNameChar-ok : ∀ c → isNameChar (fixWith isNameChar '_' c) ≡ true
fixNameChar-ok = fixWith-ok isNameChar '_' refl

fixName : Name → Name
fixName []       = '_' ∷ []
fixName (c ∷ cs) = fixWith isNameStart '_' c ∷ map (fixWith isNameChar '_') cs

fixName-valid : ∀ n → isValidName (fixName n) ≡ true
fixName-valid []       = refl
fixName-valid (c ∷ cs) =
  both (fixStart-ok c) (all-map isNameChar (fixWith isNameChar '_') fixNameChar-ok cs)

------------------------------------------------------------------------
-- Attributes
------------------------------------------------------------------------

fixAttribute : Attribute → Attribute
fixAttribute (k , v) = fixName k , fixText v

fixAttribute-valid : ∀ a → isValidAttribute (fixAttribute a) ≡ true
fixAttribute-valid (k , v) = both (fixName-valid k) (fixText-valid v)

-- Add `a` unless its name is already present.
insertAttr : Attribute → Attributes → Attributes
insertAttr a acc = if hasKey (proj₁ a) acc then acc else a ∷ acc

insertAttr-all : ∀ a acc → isValidAttribute a ≡ true → all isValidAttribute acc ≡ true →
                 all isValidAttribute (insertAttr a acc) ≡ true
insertAttr-all (k , v) acc ha hacc with hasKey k acc
... | true  = hacc
... | false = both ha hacc

insertAttr-unique : ∀ a acc → uniqueKeys acc ≡ true → uniqueKeys (insertAttr a acc) ≡ true
insertAttr-unique (k , v) acc u = go (hasKey k acc) refl
  where
  go : ∀ b → hasKey k acc ≡ b → uniqueKeys (if b then acc else (k , v) ∷ acc) ≡ true
  go true  eq = u
  go false eq = both (cong not eq) u

-- Each attribute is repaired, then later occurrences of a name replace
-- earlier ones.
fixAttrs : Attributes → Attributes
fixAttrs = foldr (insertAttr ∘ fixAttribute) []

fixAttrs-valid : ∀ as → isValidAttrs (fixAttrs as) ≡ true
fixAttrs-valid as with go as
  where
  go : ∀ as → all isValidAttribute (fixAttrs as) ≡ true × uniqueKeys (fixAttrs as) ≡ true
  go []       = refl , refl
  go (a ∷ as) =
    let (hall , huniq) = go as
    in insertAttr-all (fixAttribute a) (fixAttrs as) (fixAttribute-valid a) hall
     , insertAttr-unique (fixAttribute a) (fixAttrs as) huniq
... | hall , huniq = both hall huniq

------------------------------------------------------------------------
-- Constructors
------------------------------------------------------------------------

-- An element with only text, from characters.
textElement′ : Name → List (Name × Text) → Text → XMLM A
textElement′ tag attrs t =
  leaf (fixName tag) (fixAttrs attrs) (fixText t)
    {fromEq (fixName-valid tag)} {fromEq (fixAttrs-valid attrs)} {fromEq (fixText-valid t)}

-- An element with only element children, from characters.
element′ : Name → List (Name × Text) → List (XMLM A) → XMLM A
element′ tag attrs cs =
  parentList (fixName tag) (fixAttrs attrs) cs
    {fromEq (fixName-valid tag)} {fromEq (fixAttrs-valid attrs)}

private
  chars : List (String × String) → List (Name × Text)
  chars = map (λ { (k , v) → toList k , toList v })

textElement : String → List (String × String) → String → XMLM A
textElement tag attrs t = textElement′ (toList tag) (chars attrs) (toList t)

element : String → List (String × String) → List (XMLM A) → XMLM A
element tag attrs cs = element′ (toList tag) (chars attrs) cs
