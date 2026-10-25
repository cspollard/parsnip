{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The HTML syntax tree
--
-- An `Elem` is one of three kinds of element, each with the evidence
-- (`T b`, see `Data.HTML.Valid`) that it can be printed and read back:
--
-- * `void`:  an element with no content and no end tag (`br`, `img`, …),
--            printed `<br />`;
-- * `raw`:   `script` or `style`, with one unescaped text body;
-- * `elem`:  any other element, with *mixed content*: the text `t`
--            before the first child, and each child followed by its
--            trailing text.  This is the layout of `Data.XML.AST`: two
--            adjacent text nodes (which would print as one) cannot be
--            written down, and an empty text is no node.
--
-- Children are plain lists, so equality of trees is propositional
-- equality.  Comments, doctypes other than `<!DOCTYPE html>`, named
-- entities and the HTML5 tree-construction rules are out of scope
-- (see `plans/HTMLPlan.md`); the round trip is for this strict subset.
------------------------------------------------------------------------

module Data.HTML.AST where

open import Data.Bool using (T)
open import Data.List using (List; []; _∷_; _++_)

open import Data.XML.Valid using (Name; Text; Attributes; isValidText)
open import Data.HTML.Valid

mutual
  data Elem : Set where
    void : (n : Name) (as : Attributes) → T (okVoid n as) → Elem
    raw  : (n : Name) (as : Attributes) (b : Text) → T (okRaw n as b) → Elem
    elem : (n : Name) (as : Attributes) (t : Text) (cs : List Follow) →
           T (okElem n as t) → Elem

  -- A child and the text after it.
  data Follow : Set where
    follow : Elem → (t : Text) → T (isValidText t) → Follow
