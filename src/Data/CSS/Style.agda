{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Typed vocabulary: rules from selectors, and a few typed declarations
--
-- * `selectorRule sel block` is the qualified rule whose prelude is the
--   printed selector list (`Data.CSS.Selector`); the evidence the rule
--   needs (no top-level `{}` block, not starting with an at-keyword) is
--   proved for every selector.
-- * `declaration name values` is a declaration from runtime data, `nothing`
--   if a value is a `;` leaf (which would end the declaration); the typed
--   constructors (`color`, `display`, `margin`, …) are total.
------------------------------------------------------------------------

module Data.CSS.Style where

open import Data.Bool using (Bool; true; false; not; _∧_; T)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sign using (Sign)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Sanitize using (fromEq)
open import Data.CSS.Number using (cssNumber)
open import Data.CSS.AST
open import Data.CSS.Sanitize
open import Data.CSS.Rule
open import Data.CSS.Declaration
open import Data.CSS.Selector

------------------------------------------------------------------------
-- Rules from selectors
------------------------------------------------------------------------

private
  NB : List CV → Bool
  NB = all (λ v → not (isBraceCV v))

  all-++ : ∀ xs ys → NB xs ≡ true → NB ys ≡ true → NB (xs ++ ys) ≡ true
  all-++ []       ys _  hy = hy
  all-++ (x ∷ xs) ys hx hy = go (isBraceCV x) hx
    where
    go : ∀ b → (not b ∧ NB xs) ≡ true → (not b ∧ NB (xs ++ ys)) ≡ true
    go false h = all-++ xs ys h hy

  nb-simple : ∀ s → NB (printSimple s) ≡ true
  nb-simple (classS n h)        = refl
  nb-simple (idS n h)           = refl
  nb-simple (attrP n h)         = refl
  nb-simple (attrV n h op v hv) = refl
  nb-simple (pseudoC n h)       = refl
  nb-simple (pseudoE n h)       = refl
  nb-simple (pseudoF n h as)    = refl

  nb-tails : ∀ ts → NB (printTails ts) ≡ true
  nb-tails []       = refl
  nb-tails (s ∷ ts) = all-++ (printSimple s) (printTails ts) (nb-simple s) (nb-tails ts)

  nb-compound : ∀ c → NB (printCompound c) ≡ true
  nb-compound (withHead (typeH n h) ts) = nb-tails ts
  nb-compound (withHead universalH ts)  = nb-tails ts
  nb-compound (tailsOnly s ts) = all-++ (printSimple s) (printTails ts) (nb-simple s) (nb-tails ts)

  nb-combs : ∀ kcs → NB (printCombs kcs) ≡ true
  nb-combs []                    = refl
  nb-combs ((k , c) ∷ kcs) =
    nb-cons k {printCompound c ++ printCombs kcs} (all-++ (printCompound c) (printCombs kcs) (nb-compound c) (nb-combs kcs))
    where
    nb-cons : ∀ k {r} → NB r ≡ true → NB (printComb k ∷ r) ≡ true
    nb-cons descendant  h = h
    nb-cons child       h = h
    nb-cons nextSibling h = h
    nb-cons subsequent  h = h

  nb-complex : ∀ cx → NB (printComplex cx) ≡ true
  nb-complex (c , kcs) = all-++ (printCompound c) (printCombs kcs) (nb-compound c) (nb-combs kcs)

  nb-more : ∀ cxs → NB (printMore cxs) ≡ true
  nb-more []         = refl
  nb-more (cx ∷ cxs) = all-++ (printComplex cx) (printMore cxs) (nb-complex cx) (nb-more cxs)

  nb-selectors : ∀ s → NB (printSelectorList s) ≡ true
  nb-selectors (cx , cxs) = all-++ (printComplex cx) (printMore cxs) (nb-complex cx) (nb-more cxs)

  -- The first value is never an at-keyword.
  head-compound : ∀ c K M → headAt ((printCompound c ++ K) ++ M) ≡ false
  head-compound (withHead (typeH n h) ts) K M = refl
  head-compound (withHead universalH ts)  K M = refl
  head-compound (tailsOnly (classS n h) ts)        K M = refl
  head-compound (tailsOnly (idS n h) ts)           K M = refl
  head-compound (tailsOnly (attrP n h) ts)         K M = refl
  head-compound (tailsOnly (attrV n h op v hv) ts) K M = refl
  head-compound (tailsOnly (pseudoC n h) ts)       K M = refl
  head-compound (tailsOnly (pseudoE n h) ts)       K M = refl
  head-compound (tailsOnly (pseudoF n h as) ts)    K M = refl

  okQ-selectors : ∀ s → okQ (printSelectorList s) ≡ true
  okQ-selectors s@((c , kcs) , cxs) = go (nb-selectors s)
    where
    go : NB (printSelectorList s) ≡ true → okQ (printSelectorList s) ≡ true
    go h rewrite h | head-compound c (printCombs kcs) (printMore cxs) = refl

-- A rule with the given selectors and block contents.
selectorRule : SelectorList → List CV → Rule
selectorRule s block = qualified (printSelectorList s) (fromEq (okQ-selectors s)) block

------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------

-- A declaration from runtime data: the name is repaired, and a value
-- that is a `;` leaf is rejected.
declaration : String → List CV → Maybe Decl
declaration n vs = go (okV vs) refl
  where
  go : (b : Bool) → okV vs ≡ b → Maybe Decl
  go true  eq = just (decl (fixIdent (toList n)) (fromEq (fixIdent-valid (toList n))) vs (fromEq eq))
  go false _  = nothing

-- Typed declarations: a keyword or a length in pixels.
color backgroundColor display position : String → Decl
color           v = decl (toList "color") _ (ident v ∷ []) _
backgroundColor v = decl (toList "background-color") _ (ident v ∷ []) _
display         v = decl (toList "display") _ (ident v ∷ []) _
position        v = decl (toList "position") _ (ident v ∷ []) _

px : ℕ → CV
px n = dimension (cssNumber Sign.+ n []) "px"

margin padding fontSize width height : ℕ → Decl
margin   n = decl (toList "margin") _ (px n ∷ []) _
padding  n = decl (toList "padding") _ (px n ∷ []) _
fontSize n = decl (toList "font-size") _ (px n ∷ []) _
width    n = decl (toList "width") _ (px n ∷ []) _
height   n = decl (toList "height") _ (px n ∷ []) _
