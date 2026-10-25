{-# OPTIONS --safe --cubical-compatible #-}

------------------------------------------------------------------------
-- Maximal runs of characters
--
-- `spanBy p cs` splits `cs` into its longest prefix of characters
-- satisfying `p` and the rest.  Lexing a name, a run of white space or
-- a run of digits is a `spanBy`; `spanBy-++` is the prefix round trip
-- they all rely on: a run followed by a character that is not in the
-- run (or by nothing) is read back exactly.
------------------------------------------------------------------------

module Data.Lexer.Span where

open import Data.Bool using (Bool; true; false; _∧_; T)
open import Data.Bool.ListAction using (all)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; map₁; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

spanBy : (Char → Bool) → List Char → List Char × List Char
spanBy′ : (Char → Bool) → Char → List Char → Bool → List Char × List Char

spanBy p []       = [] , []
spanBy p (c ∷ cs) = spanBy′ p c cs (p c)

spanBy′ p c cs true  = map₁ (c ∷_) (spanBy p cs)
spanBy′ p c cs false = [] , c ∷ cs

-- The text after a run does not continue it.
Stops : (Char → Bool) → List Char → Set
Stops p []      = T true
Stops p (c ∷ _) = p c ≡ false

private
  ∧-split : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
  ∧-split {true}  h = refl , h
  ∧-split {false} ()

spanBy-++ : ∀ p xs ys → all p xs ≡ true → Stops p ys → spanBy p (xs ++ ys) ≡ (xs , ys)
spanBy-++ p []       []       _  _  = refl
spanBy-++ p []       (y ∷ ys) _  st = cong (spanBy′ p y ys) st
spanBy-++ p (x ∷ xs) ys       ax st with ∧-split ax
... | hx , hxs =
  trans (cong (spanBy′ p x (xs ++ ys)) hx)
        (cong (map₁ (x ∷_)) (spanBy-++ p xs ys hxs st))
