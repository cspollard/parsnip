{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Compact JSON printing
--
-- `printJSON` is the free-monad catamorphism (`foldJSONM`) printing each
-- node from its printed children.  It is the `to` of `jsonStage` (see
-- `Data.JSON.Goals`): the parser is proved to be its right inverse.
-- Literals, numbers and string literals come from `Data.JSON.Keyword`,
-- `Data.JSON.Number` and `Data.JSON.String`, so there is a single
-- definition of each spelling.
------------------------------------------------------------------------

module Data.JSON.Print where

open import Data.Bool using (true; false)
open import Data.Char using (Char)
open import Data.List as List
  using (List; []; _∷_; _++_; intercalate)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; fromList)
open import Function using (_∘_)
open import Data.Container using (⟦_⟧)

open import Data.JSON.AST
open JSONCont
open import Data.JSON.Number using (printNumber) public
open import Data.JSON.String using (printStringLiteral) public
open import Data.JSON.Keyword using (keywordText; nullK; trueK; falseK)

printPrim : (t : PrimJSONType) → RetType t → List Char
printPrim primstring = printStringLiteral
printPrim primnumber = printNumber
printPrim primbool true  = keywordText trueK
printPrim primbool false = keywordText falseK
printPrim primnull _     = keywordText nullK

printArrayBody : List (List Char) → List Char
printArrayBody = intercalate (',' ∷ [])

printObjectBody : List (Key × List Char) → List Char
printObjectBody = intercalate (',' ∷ []) ∘ List.map entry
  where
  entry : Key × List Char → List Char
  entry (k , x) = printStringLiteral k ++ ':' ∷ x

printJSON : JSON → List Char
printJSON = foldJSONM (λ ()) go
  where
  go : (t : JSONType) (x : ⟦ JSON→ t ⟧ (List Char)) → List Char
  go object x = '{' ∷ printObjectBody (objectCToEntries x) ++ '}' ∷ []
  go array x  = '[' ∷ printArrayBody (listCToList x) ++ ']' ∷ []
  go (prim t) (x , _) = printPrim t x

-- Render to standard Agda String
renderJSON : JSON → String
renderJSON = fromList ∘ printJSON
