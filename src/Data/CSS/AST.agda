{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The CSS syntax tree: component values
--
-- CSS Syntax Level 3 parses a style sheet into a tree of *component
-- values*: preserved tokens, and `( )`, `[ ]`, `{ }` blocks and
-- `name( )` functions that contain more component values.  Everything
-- else (rules, declarations, selectors, values) is a grammar applied on
-- top of that tree (`Data.CSS.Rule`, `Data.CSS.Selector`); this module
-- is the layer they share.
--
-- * Leaves are tokens, so white space, commas, colons and semicolons are
--   leaves; the tree has the structure of the brackets and nothing else.
-- * A leaf carries evidence (`isLeaf`) that its token is well formed
--   (`Data.CSS.Token.tokenWF`) and is not a bracket, a function start or a
--   comment, and a function carries evidence that its name is a legal
--   identifier: ill-formed trees are unrepresentable.  The evidence is
--   `T b`, definitionally irrelevant for concrete data; for runtime data
--   see `Data.CSS.Sanitize` for total constructors.
-- * Children are plain lists, so equality of trees is propositional
--   equality, and the round trip is `≡` (cf. `Data.XML.Equality`, where
--   children are indexed by `Fin` and the strongest equality is
--   bisimilarity).
-- * Adjacent leaves are unconstrained: the printer inserts a comment
--   between tokens that would otherwise run together (`Data.CSS.Tokens`).
------------------------------------------------------------------------

module Data.CSS.AST where

open import Data.Bool using (Bool; true; false; T)
open import Data.List using (List; []; _∷_; _++_)

open import Data.CSS.Valid using (Name; isValidIdent)
open import Data.CSS.Token

-- A leaf token: well formed, and not structural.
isLeaf : CToken → Bool
isLeaf (functionT _) = false
isLeaf lparenT       = false
isLeaf rparenT       = false
isLeaf lbrackT       = false
isLeaf rbrackT       = false
isLeaf lbraceT       = false
isLeaf rbraceT       = false
isLeaf commentT      = false
isLeaf t             = tokenWF t

data CV : Set where
  leaf    : (t : CToken) → T (isLeaf t) → CV
  paren   : List CV → CV
  bracket : List CV → CV
  brace   : List CV → CV
  func    : (n : Name) → T (isValidIdent n) → List CV → CV

-- A style sheet, as far as the syntax layer is concerned.
CSS : Set
CSS = List CV

------------------------------------------------------------------------
-- The tokens of a tree
------------------------------------------------------------------------

mutual
  tokensCV : CV → List CToken
  tokensCV (leaf t _)    = t ∷ []
  tokensCV (paren vs)    = lparenT ∷ tokensList vs ++ rparenT ∷ []
  tokensCV (bracket vs)  = lbrackT ∷ tokensList vs ++ rbrackT ∷ []
  tokensCV (brace vs)    = lbraceT ∷ tokensList vs ++ rbraceT ∷ []
  tokensCV (func n _ vs) = functionT n ∷ tokensList vs ++ rparenT ∷ []

  tokensList : List CV → List CToken
  tokensList []       = []
  tokensList (v ∷ vs) = tokensCV v ++ tokensList vs
