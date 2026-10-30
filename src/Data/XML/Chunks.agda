{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Printing an XML document in pieces
--
-- `printXML` builds the whole document's token list and text in one go; for a
-- document with hundreds of megabytes of text that is the dominant memory cost
-- (`plans/PathPlan.md`, "Output memory").  `xmlChunks d` splits the printed text
-- of the root element at its children: the start tag with the leading text, then
-- each child (with the text after it), then the end tag.  Written one after the
-- other the chunks are exactly `printXML d`:
-- `concat (xmlChunks d) ≡ printXML d` (checked on examples in
-- `GeoAgda.Tests.Chunks`; the general statement is not proved yet).
-- Each chunk is printed on demand, so a consumer that writes a chunk out
-- before asking for the next one never holds the whole document.
------------------------------------------------------------------------

module Data.XML.Chunks where

open import Data.Char using (Char)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; fromList)

open import Data.XML.AST
open import Data.XML.Escape using (escapeText)
open import Data.XML.Print using (printXML)
open import Data.XML.Token using (openT; closeT; printToken)

private
  childChunks : List (XMLDoc × Text) → List (List Char)
  childChunks []             = []
  childChunks ((c , t) ∷ cs) = (printXML c ++ escapeText t) ∷ childChunks cs

  split : XMLDoc → XMLShape → Content XMLDoc → List (List Char)
  split whole s (t , [])        = printXML whole ∷ []
  split whole s (t , c ∷ cs)    =
    (printToken (openT (XMLShape.tag s) (XMLShape.attrs s)) ++ escapeText t)
      ∷ childChunks (c ∷ cs) ++ printToken (closeT (XMLShape.tag s)) ∷ []

-- The printed document, one chunk per child of the root.
xmlCharChunks : XMLDoc → List (List Char)
xmlCharChunks (pure ())
xmlCharChunks whole@(impure (s , f)) =
  split whole s (mixed (XMLShape.arity s) (XMLShape.texts s) f)

xmlChunks : XMLDoc → List String
xmlChunks d = map fromList (xmlCharChunks d)
