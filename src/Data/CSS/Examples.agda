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

------------------------------------------------------------------------
-- Selectors: `a.x>b:hover, *` from text
------------------------------------------------------------------------

open import Data.Product using (_×_; _,_)
open import Data.CSS.Selector
open import Data.CSS.RoundTrip using (parseCSSText)

sel : SelectorList
sel = ( withHead (typeH (toList "a") _) (classS (toList "x") _ ∷ [])
      , (child , withHead (typeH (toList "b") _) (pseudoC (toList "hover") _ ∷ [])) ∷ [] )
    , (withHead universalH [] , []) ∷ []

selectors : parseCSSText (toList "a.x>b:hover,*") ≡ just (printSelectorList sel)
selectors = refl

selectors′ : parseSelectorList (printSelectorList sel) ≡ just sel
selectors′ = parseSelectorList-print sel

------------------------------------------------------------------------
-- A rule from a selector and typed declarations
------------------------------------------------------------------------

open import Data.CSS.Style using (selectorRule; color; margin)

styled : List Rule
styled = selectorRule sel (printDecls (color "red" ∷ margin 4 ∷ [])) ∷ []

styled-printed : printStylesheet styled ≡ toList "a.x>b:hover,*{color:red;margin:4px;}"
styled-printed = refl

styled-read : parseStylesheet (toList "a.x>b:hover,*{color:red;margin:4px;}") ≡ just styled
styled-read = refl
