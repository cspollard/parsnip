{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Total HTML constructors for runtime data
--
-- The AST only holds well-formed content (`Data.HTML.Valid`).  Data
-- computed at runtime cannot be checked statically, so `element` repairs
-- it, in the manner of `Data.XML.Sanitize`:
--
-- * a character that is not legal XML becomes U+FFFD in text;
-- * a character that cannot be in a name, or is a capital letter, becomes
--   `_` in tag and attribute names, and an empty name becomes `_`;
-- * if an attribute name occurs more than once, the last occurrence wins;
-- * a void tag (`br`, `img`, …) drops its content;
-- * a raw-text tag (`script`, `style`) keeps only the text of its content
--   and is empty if that text contains `</`;
-- * leading newlines are dropped from the content of a `pre`-like tag
--   (a browser would drop one);
-- * adjacent texts are merged, and empty ones vanish.
--
-- Valid input is left unchanged (except for the `pre` case), and the
-- result comes with the proof that it is valid.
------------------------------------------------------------------------

module Data.HTML.Sanitize where

open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_; T)
open import Data.Bool.ListAction using (all)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_; map; foldr)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.String using (String; toList)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.Char.Class using (is; range)
open import Data.Sanitize
open import Data.XML.Valid
open import Data.XML.Sanitize using (insertAttr; insertAttr-all; insertAttr-unique)
open import Data.HTML.Valid
open import Data.HTML.AST

------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------

private
  notUpper : Char → Bool
  notUpper c = not (range 'A' 'Z' c)

  okStart okChar : Char → Bool
  okStart c = isNameStart c ∧ notUpper c
  okChar  c = isNameChar c ∧ notUpper c

  and-elim : ∀ a b → a ∧ b ≡ true → a ≡ true × b ≡ true
  and-elim true b h = refl , h

  all-and : ∀ (p q : Char → Bool) xs → all (λ c → p c ∧ q c) xs ≡ true →
            all p xs ≡ true × all q xs ≡ true
  all-and p q []       _ = refl , refl
  all-and p q (x ∷ xs) h with and-elim (p x ∧ q x) _ h
  ... | hx , hxs with and-elim (p x) (q x) hx | all-and p q xs hxs
  ... | hp , hq | ap , aq = both hp ap , both hq aq

  start⇒char : ∀ c → isNameStart c ≡ true → isNameChar c ≡ true
  start⇒char c hs rewrite hs = refl

-- A name of lower-case name characters.
fixTag : Name → Name
fixTag []       = '_' ∷ []
fixTag (c ∷ cs) = fixWith okStart '_' c ∷ map (fixWith okChar '_') cs

private
  fixTag-parts : ∀ n → isValidName (fixTag n) ≡ true × isLowerName (fixTag n) ≡ true
  fixTag-parts []       = refl , refl
  fixTag-parts (c ∷ cs) with and-elim (isNameStart c′) (notUpper c′) (fixWith-ok okStart '_' refl c)
                           | all-and isNameChar notUpper (map (fixWith okChar '_') cs)
                                     (all-map okChar (fixWith okChar '_') (fixWith-ok okChar '_' refl) cs)
    where c′ = fixWith okStart '_' c
  ... | hs , hn | ac , an = both hs ac , both hn an

fixTag-valid : ∀ n → isValidName (fixTag n) ≡ true
fixTag-valid n = proj₁ (fixTag-parts n)

fixTag-lower : ∀ n → isLowerName (fixTag n) ≡ true
fixTag-lower n = proj₂ (fixTag-parts n)

------------------------------------------------------------------------
-- Attributes
------------------------------------------------------------------------

fixAttribute : Attribute → Attribute
fixAttribute (k , v) = fixTag k , fixText v

fixAttribute-valid : ∀ a → isValidAttribute (fixAttribute a) ≡ true
fixAttribute-valid (k , v) = both (fixTag-valid k) (fixText-valid v)

fixAttrs : Attributes → Attributes
fixAttrs = foldr (insertAttr ∘ fixAttribute) []

private
  lower-insert : ∀ a acc → isLowerName (proj₁ a) ≡ true → attrsLower acc ≡ true →
                 attrsLower (insertAttr a acc) ≡ true
  lower-insert (k , v) acc ha hacc with hasKey k acc
  ... | true  = hacc
  ... | false = both ha hacc

  goAttrs : ∀ as → (all isValidAttribute (fixAttrs as) ≡ true × uniqueKeys (fixAttrs as) ≡ true)
              × attrsLower (fixAttrs as) ≡ true
  goAttrs []       = (refl , refl) , refl
  goAttrs (a ∷ as) with goAttrs as
  ... | (hall , huniq) , hlow =
    ( insertAttr-all (fixAttribute a) (fixAttrs as) (fixAttribute-valid a) hall
    , insertAttr-unique (fixAttribute a) (fixAttrs as) huniq )
    , lower-insert (fixAttribute a) (fixAttrs as) (fixTag-lower (proj₁ a)) hlow

fixAttrs-valid : ∀ as → isValidAttrs (fixAttrs as) ≡ true
fixAttrs-valid as with goAttrs as
... | (hall , huniq) , _ = both hall huniq

fixAttrs-lower : ∀ as → attrsLower (fixAttrs as) ≡ true
fixAttrs-lower as = proj₂ (goAttrs as)

okTag-fix : ∀ n as → okTag (fixTag n) (fixAttrs as) ≡ true
okTag-fix n as =
  both (fixTag-valid n) (both (fixTag-lower n) (both (fixAttrs-valid as) (fixAttrs-lower as)))

------------------------------------------------------------------------
-- Content
------------------------------------------------------------------------

-- Text and elements, as given.
data Item : Set where
  txt : Text → Item
  el  : Elem → Item

private
  all-++ : ∀ (p : Char → Bool) xs ys → all p xs ≡ true → all p ys ≡ true → all p (xs ++ ys) ≡ true
  all-++ p []       ys _  hy = hy
  all-++ p (x ∷ xs) ys hx hy with and-elim (p x) (all p xs) hx
  ... | h₁ , h₂ = both h₁ (all-++ p xs ys h₂ hy)

-- The leading text and the children with trailing text, merged.
Content : Set
Content = Σ[ t ∈ Text ] isValidText t ≡ true × List Follow

content : List Item → Content
content []             = [] , refl , []
content (txt x ∷ is)   with content is
... | t , v , fs = fixText x ++ t , all-++ isValidChar (fixText x) t (fixText-valid x) v , fs
content (el e ∷ is)    with content is
... | t , v , fs = [] , refl , follow e t (fromEq v) ∷ fs

-- The text of the items, for a raw-text element.
rawText : List Item → Text
rawText []           = []
rawText (txt x ∷ is) = fixText x ++ rawText is
rawText (el _ ∷ is)  = rawText is

rawText-valid : ∀ is → isValidText (rawText is) ≡ true
rawText-valid []           = refl
rawText-valid (txt x ∷ is) = all-++ isValidChar (fixText x) (rawText is) (fixText-valid x) (rawText-valid is)
rawText-valid (el _ ∷ is)  = rawText-valid is

-- Leading newlines removed.
dropNewlines : Text → Text
dropNewlines₁ : Bool → Char → Text → Text

dropNewlines []       = []
dropNewlines (c ∷ cs) = dropNewlines₁ (is '\n' c) c cs

dropNewlines₁ true  c cs = dropNewlines cs
dropNewlines₁ false c cs = c ∷ cs

dropNewlines-start : ∀ t → startsNewline (dropNewlines t) ≡ false
dropNewlines₁-start : ∀ b c cs → is '\n' c ≡ b → startsNewline (dropNewlines₁ b c cs) ≡ false

dropNewlines-start []       = refl
dropNewlines-start (c ∷ cs) = dropNewlines₁-start (is '\n' c) c cs refl

dropNewlines₁-start true  c cs _  = dropNewlines-start cs
dropNewlines₁-start false c cs eq = eq

dropNewlines-valid : ∀ t → isValidText t ≡ true → isValidText (dropNewlines t) ≡ true
dropNewlines₁-valid : ∀ b c cs → isValidText (c ∷ cs) ≡ true → isValidText (dropNewlines₁ b c cs) ≡ true

dropNewlines-valid []       _ = refl
dropNewlines-valid (c ∷ cs) h = dropNewlines₁-valid (is '\n' c) c cs h

dropNewlines₁-valid true  c cs h = dropNewlines-valid cs (proj₂ (and-elim (isValidChar c) _ h))
dropNewlines₁-valid false c cs h = h

------------------------------------------------------------------------
-- Elements
------------------------------------------------------------------------

private
  void-ok : ∀ n as → isVoidTag n ≡ true → okTag n as ≡ true → T (okVoid n as)
  void-ok n as hv ht = fromEq (both hv ht)

  raw-ok : ∀ n as b → isRawTag n ≡ true → okTag n as ≡ true → noEndTag b ≡ true →
           isValidText b ≡ true → T (okRaw n as b)
  raw-ok n as b hr ht hb hv = fromEq (both hr (both ht (both hb hv)))

  not-true : ∀ b → b ≡ false → not b ≡ true
  not-true .false refl = refl

  elem-ok : ∀ n as t → isVoidTag n ≡ false → isRawTag n ≡ false → okTag n as ≡ true →
            isValidText t ≡ true → not (isPreTag n ∧ startsNewline t) ≡ true →
            T (okElem n as t)
  elem-ok n as t hv hr ht hvt hp =
    fromEq (both (not-true _ hv) (both (not-true _ hr) (both ht (both hvt hp))))

  -- Dispatch on the kind of tag, with the evidence.
  buildRaw : (n : Name) (as : Attributes) (b : Text) → isRawTag n ≡ true → okTag n as ≡ true →
             isValidText b ≡ true → (bb : Bool) → noEndTag b ≡ bb → Elem
  buildRaw n as b hr ht hv true  hb = raw n as b (raw-ok n as b hr ht hb hv)
  buildRaw n as b hr ht hv false hb = raw n as [] (raw-ok n as [] hr ht refl refl)

-- Leading newlines are dropped in `pre`-like elements.
fixPreB : Bool → Text → Text
fixPreB true  t = dropNewlines t
fixPreB false t = t

fixPre : Name → Text → Text
fixPre n = fixPreB (isPreTag n)

private
  fixPre-ok : ∀ n t → isValidText t ≡ true →
              isValidText (fixPre n t) ≡ true × not (isPreTag n ∧ startsNewline (fixPre n t)) ≡ true
  fixPre-ok n t h = go (isPreTag n) refl
    where
    go : ∀ b → isPreTag n ≡ b →
         isValidText (fixPreB b t) ≡ true × not (isPreTag n ∧ startsNewline (fixPreB b t)) ≡ true
    go true  eq rewrite eq | dropNewlines-start t = dropNewlines-valid t h , refl
    go false eq rewrite eq = h , refl

  -- Elements with content: neither void nor raw.
  buildElem : (n : Name) (as : Attributes) → isVoidTag n ≡ false → isRawTag n ≡ false →
              okTag n as ≡ true → List Item → Elem
  buildElem n as hv hr ht is with content is
  ... | t , v , fs with fixPre-ok n t v
  ... | hv′ , hp = elem n as (fixPre n t) fs (elem-ok n as (fixPre n t) hv hr ht hv′ hp)

  buildR : (n : Name) (as : Attributes) → isVoidTag n ≡ false → okTag n as ≡ true → List Item →
           (br : Bool) → isRawTag n ≡ br → Elem
  buildR n as hv ht is true  eq = buildRaw n as (rawText is) eq ht (rawText-valid is) (noEndTag (rawText is)) refl
  buildR n as hv ht is false eq = buildElem n as hv eq ht is

  buildV : (n : Name) (as : Attributes) → okTag n as ≡ true → List Item →
           (bv : Bool) → isVoidTag n ≡ bv → Elem
  buildV n as ht is true  eq = void n as (void-ok n as eq ht)
  buildV n as ht is false eq = buildR n as eq ht is (isRawTag n) refl

-- An element, from characters.
element′ : Name → List (Name × Text) → List Item → Elem
element′ n as is =
  buildV (fixTag n) (fixAttrs as) (okTag-fix n as) is (isVoidTag (fixTag n)) refl

private
  chars : List (String × String) → List (Name × Text)
  chars = map (λ { (k , v) → toList k , toList v })

-- An element, from strings.
element : String → List (String × String) → List Item → Elem
element n as is = element′ (toList n) (chars as) is

-- Text, from a string.
text : String → Item
text s = txt (toList s)
