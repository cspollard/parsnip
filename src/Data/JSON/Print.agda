{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

module Data.JSON.Print where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.String as String using (String; toList; fromList)
open import Data.String.Properties using () renaming (≡-decSetoid to stringDecSetoid)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Sign using (Sign; +; -)
open import Data.Fin using (Fin; zero; suc)
open import Data.List as List
  using (List; []; _∷_; _++_; concat; map; length; intercalate)
open import Data.List.Membership.DecPropositional (_≟_)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; _$_)
open import Relation.Nullary.Decidable using (yes; no; does)
open import Data.Container as C
open import Data.Empty

open import Data.JSON.AST
open import Data.JSON.ObjectC stringDecSetoid
open JSONCont
open import GeoAgda.Parsing.Invertible.Number public
  using (printSign; printNat; printFraction; printExponent; printNumber)

------------------------------------------------------------------------
-- String Escaping & Formatting
------------------------------------------------------------------------

escapeList : List Char
escapeList = '"' ∷ '\\' ∷ '\n' ∷ '\r' ∷ '\t' ∷ []

-- Escape special JSON string characters using decidable equality
escapeString : List Char → List Char
escapeString = List.concat ∘ List.map go
  where
    go : Char → List Char
    go c with does (c ∈? escapeList)
    ... | true = '\\' ∷ c ∷ []
    ... | false = c ∷ []

printStringLiteral : String → List Char
printStringLiteral s = '"' ∷ escapeString (toList s) ++ ('"' ∷ [])

------------------------------------------------------------------------
-- JSON Pretty-Printing
------------------------------------------------------------------------

-- Pretty print a closed JSON value to a List Char
print⊤ : ⊤ → List Char
print⊤ _ = String.toList "null"

printPrim : (t : PrimJSONType) → (RetType t) → List Char
printPrim PrimJSONType.primstring = toList
printPrim PrimJSONType.primnumber = printNumber
printPrim PrimJSONType.primbool = toList ∘ show
  where open import Data.Bool.Show
printPrim PrimJSONType.primnull = print⊤

printJSON : JSON → List Char
printArrayBody : ⟦ ListC ⟧ (List Char) → List Char
printObjectBody : ⟦ StringObjectC ⟧ (List Char) → List Char

printArrayBody = intercalate (',' ∷  ' ' ∷ []) ∘ listCToList

printObjectBody = intercalate (',' ∷ ' ' ∷ []) ∘ List.map go ∘ objectToList
  where
    go : (String × List Char) → List Char
    go (k , x) = toList k ++ ':' ∷ ' ' ∷ x

printJSON = foldJSONM (λ ()) go
  where
    go : (t : JSONType) (x : ⟦ JSON→ t ⟧ (List Char)) → List Char
    go object x = '{' ∷ printObjectBody x ++ '}' ∷ []
    go array x  = '[' ∷ printArrayBody x ++ ']' ∷ []
    go (prim t) (x , _) = printPrim t x

-- Render to standard Agda String
renderJSON : JSON → String
renderJSON = fromList ∘ printJSON
