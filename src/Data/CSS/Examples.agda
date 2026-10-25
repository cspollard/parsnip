{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Concrete examples: `a { color: red; margin: 0 }` as rules and
-- declarations, printed and read back
------------------------------------------------------------------------

module Data.CSS.Examples where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.CSS.Sanitize
open import Data.CSS.Rule
open import Data.CSS.Declaration
open import Data.CSS.Stylesheet

decls : List Decl
decls = decl (toList "color") _ (ident "red" ∷ []) _
      ∷ decl (toList "margin") _ (whitespace ∷ ident "auto" ∷ []) _
      ∷ []

sheet : List Rule
sheet = qualified (ident "a" ∷ []) _ (printDecls decls) ∷ []

-- Declarations print without extra white space.
printed : printStylesheet sheet ≡ toList "a{color:red;margin: auto;}"
printed = refl

-- ... and read back as the same rules.
read : parseStylesheet (toList "a{color:red;margin: auto;}") ≡ just sheet
read = refl

------------------------------------------------------------------------
-- Lexing: `.5`, `+3px` and `-2` are numbers
------------------------------------------------------------------------

open import Data.Fin using (#_)
open import Data.Sign using (Sign)
open import Data.CSS.Number using (cssNumber)
open import Data.CSS.Token using (numberT; dimT; wsT)
open import Data.CSS.Lexer using (tokenize)

numbers : tokenize (toList ".5 +3px -2")
  ≡ just ( numberT (cssNumber Sign.+ 0 (# 5 ∷ []))
         ∷ wsT
         ∷ dimT (cssNumber Sign.+ 3 []) (toList "px")
         ∷ wsT
         ∷ numberT (cssNumber Sign.- 2 [])
         ∷ [] )
numbers = refl
