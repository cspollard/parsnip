{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Concrete examples: a small page, printed and read back
------------------------------------------------------------------------

module Data.HTML.Examples where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.HTML.AST using (Elem)
open import Data.HTML.Sanitize using (text)
open import Data.HTML.Elements
open import Data.HTML.Print using (printHTML)
open import Data.HTML.RoundTrip using (parseHTML)

page : Elem
page = html (("lang" , "en") ∷ [])
  ( head [] (title [] (text "Hi & bye" ∷ []) ∷ [])
  ∷ body []
      ( h1 [] (text "Hello" ∷ [])
      ∷ p [] (text "a < b, " ∷ a (("href" , "/x?a=1&b=2") ∷ []) (text "link" ∷ []) ∷ text "." ∷ [])
      ∷ br []
      ∷ script [] "if (a < b && c) { go(); }"
      ∷ [] )
  ∷ [] )

printed : printHTML page ≡ toList
  "<!DOCTYPE html><html lang=\"en\"><head><title>Hi &amp; bye</title></head><body><h1>Hello</h1><p>a &lt; b, <a href=\"/x?a=1&amp;b=2\">link</a>.</p><br /><script>if (a < b && c) { go(); }</script></body></html>"
printed = refl

read : parseHTML (toList
  "<!DOCTYPE html><html lang=\"en\"><head><title>Hi &amp; bye</title></head><body><h1>Hello</h1><p>a &lt; b, <a href=\"/x?a=1&amp;b=2\">link</a>.</p><br /><script>if (a < b && c) { go(); }</script></body></html>")
  ≡ just page
read = refl
