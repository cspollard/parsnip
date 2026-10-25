{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Style sheets in HTML: the body of a `<style>` element
--
-- `styleElement rs` is the `<style>` element holding the printed style
-- sheet `rs` (`Data.CSS.Stylesheet`).  A raw-text body may not contain
-- `</`, which printed CSS can (as two delimiters), so the constructor
-- is partial: it fails exactly then.  `styleRules` reads the rules back
-- from a `<style>` element, and
--
--   styleElement rs ≡ just e  →  styleRules e ≡ just rs.
------------------------------------------------------------------------

module Data.HTML.Style where

open import Data.Bool using (Bool; true; false; T)
open import Data.List using (List; []; _∷_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Data.XML.Valid using (Name)
open import Data.HTML.Valid
open import Data.HTML.AST
open import Data.CSS.Rule using (Rule)
open import Data.CSS.Stylesheet

styleName : Name
styleName = toList "style"

private
  toT : ∀ {b} → b ≡ true → T b
  toT refl = _

styleGo : ∀ rs (b : Bool) → okRaw styleName [] (printStylesheet rs) ≡ b → Maybe Elem
styleGo rs true  eq = just (raw styleName [] (printStylesheet rs) (toT eq))
styleGo rs false _  = nothing

-- The element, if the printed sheet is a legal raw-text body.
styleElement : List Rule → Maybe Elem
styleElement rs = styleGo rs (okRaw styleName [] (printStylesheet rs)) refl

-- The rules in the body of a `<style>` element.
styleRules : Elem → Maybe (List Rule)
styleRules (raw _ _ b _) = parseStylesheet b
styleRules _             = nothing

private
  go : ∀ rs e b (h : okRaw styleName [] (printStylesheet rs) ≡ b) →
       styleGo rs b h ≡ just e → styleRules e ≡ just rs
  go rs .(raw styleName [] (printStylesheet rs) (toT h)) true h refl =
    parseStylesheet-printStylesheet rs
  go rs e false h ()

styleElement-styleRules : ∀ rs e → styleElement rs ≡ just e → styleRules e ≡ just rs
styleElement-styleRules rs e eq = go rs e _ refl eq
