{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The token stream of an HTML tree
--
-- `tokensElem` gives an element's tokens from its content's, and
-- `tokensElem-valid` says the stream is a valid input to `lexer`
-- (`Data.HTML.Lexer`).
--
-- * `void` is one self-closing tag, `raw` is one `rawT`;
-- * `elem` is a start tag, its content, and the end tag: the leading
--   text (a token unless it is empty), then each child followed by its
--   trailing text.
------------------------------------------------------------------------

module Data.HTML.Tokens where

open import Data.Bool using (Bool; true; false; _∧_; not; T)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.XML.Valid using (Name; Text; Attributes; isValidName; isValidAttrs; isValidAttribute; isValidText; ∧-join; ∧-split)
open import Data.XML.Token using (openT; selfT; closeT; textT; attrNamesValid)
import Data.XML.Token as X
open import Data.HTML.Valid
open import Data.HTML.AST
open import Data.HTML.Token
open import Data.HTML.Lexer using (Run; done; step; run++)

------------------------------------------------------------------------
-- Printing
------------------------------------------------------------------------

-- Character data: a token unless the text is empty.
textTokens : Text → List HToken
textTokens []       = []
textTokens (c ∷ cs) = tok (textT (c ∷ cs)) ∷ []

mutual
  tokensElem : Elem → List HToken
  tokensElem (void n as _)     = tok (selfT n as) ∷ []
  tokensElem (raw n as b _)    = rawT n as b ∷ []
  tokensElem (elem n as t cs _) =
    tok (openT n as) ∷ textTokens t ++ tokensFollows cs ++ tok (closeT n) ∷ []

  tokensFollows : List Follow → List HToken
  tokensFollows []                    = []
  tokensFollows (follow e t _ ∷ fs)  = tokensElem e ++ textTokens t ++ tokensFollows fs

------------------------------------------------------------------------
-- The stream is valid
------------------------------------------------------------------------

private
  notText : ∀ p → T (not (p ∧ false))
  notText true  = tt
  notText false = tt

  names : ∀ as → isValidAttrs as ≡ true → attrNamesValid as ≡ true
  names as h with ∧-split h
  ... | hall , _ = go as hall
    where
    go : ∀ as → all isValidAttribute as ≡ true → attrNamesValid as ≡ true
    go []             _ = refl
    go ((k , v) ∷ as) h with ∧-split h
    ... | hk , hs with ∧-split hk
    ... | hname , _ = ∧-join hname (go as hs)

  and₁ : ∀ a b → a ∧ b ≡ true → a ≡ true
  and₁ a b h = proj₁ (∧-split {a} {b} h)

  and₂ : ∀ a b → a ∧ b ≡ true → b ≡ true
  and₂ a b h = proj₂ (∧-split {a} {b} h)

  -- A tag that can be printed has a valid XML start tag.
  startWF : ∀ n as → okTag n as ≡ true → X.tokenWF (openT n as) ≡ true
  startWF n as h =
    ∧-join (and₁ (isValidName n) _ h)
           (names as (and₁ (isValidAttrs as) _ (and₂ (isLowerName n) _ (and₂ (isValidName n) _ h))))

  -- The state after the text `t`.
  slot : Text → Bool
  slot []      = false
  slot (_ ∷ _) = true

  endState : Bool → List Follow → Bool
  endState p []                   = p
  endState p (follow _ t _ ∷ fs) = endState (slot t) fs

  text-run : ∀ t → Run false (slot t) (textTokens t)
  text-run []       = done
  text-run (x ∷ xs) = step refl tt done

  void-wf : ∀ n as → okVoid n as ≡ true → tokenWF (tok (selfT n as)) ≡ true
  void-wf n as h = startWF n as (and₂ (isVoidTag n) (okTag n as) h)

  raw-wf : ∀ n as b → okRaw n as b ≡ true → tokenWF (rawT n as b) ≡ true
  raw-wf n as b h =
    ∧-join (startWF n as (and₁ (okTag n as) _ h₂))
           (∧-join (and₁ (isRawTag n) _ h) (and₁ (noEndTag b) _ (and₂ (okTag n as) _ h₂)))
    where
    h₂ : okTag n as ∧ noEndTag b ∧ isValidText b ≡ true
    h₂ = and₂ (isRawTag n) _ h

  elem-wf : ∀ n as t → okElem n as t ≡ true →
            tokenWF (tok (openT n as)) ≡ true × isValidName n ≡ true
  elem-wf n as t h = ∧-join sw (and₁ (not (isRawTag n)) _ h₁) , and₁ (isValidName n) _ (startWF n as ht)
    where
    h₁ : not (isRawTag n) ∧ okTag n as ∧ isValidText t ∧ not (isPreTag n ∧ startsNewline t) ≡ true
    h₁ = and₂ (not (isVoidTag n)) _ h
    ht : okTag n as ≡ true
    ht = and₁ (okTag n as) _ (and₂ (not (isRawTag n)) _ h₁)
    sw : X.tokenWF (openT n as) ≡ true
    sw = startWF n as ht

mutual
  elem-run : ∀ e p → Run p false (tokensElem e)
  elem-run (void n as h) p = step (void-wf n as (toEq h)) (notText p) done
  elem-run (raw n as b h) p = step (raw-wf n as b (toEq h)) (notText p) done
  elem-run (elem n as t cs h) p with elem-wf n as t (toEq h)
  ... | wo , wn =
    step wo (notText p)
         (run++ (text-run t)
           (run++ (follows-run (slot t) cs) (step wn (notText _) done)))

  follows-run : ∀ p cs → Run p (endState p cs) (tokensFollows cs)
  follows-run p []                   = done
  follows-run p (follow e t _ ∷ fs) =
    run++ (elem-run e p) (run++ (text-run t) (follows-run (slot t) fs))
