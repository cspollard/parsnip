{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

module Data.XML.AST where

open import Level using (0ℓ; Level) renaming (suc to lsuc)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; length; lookup)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Function using (_∘_)
open import Data.Container hiding (refl)
import Data.Container.Combinator as CC
open import Data.Container.FreeMonad as FM

private variable
  a b : Level
  A : Set a
  B : Set b

------------------------------------------------------------------------
-- XML Attributes
------------------------------------------------------------------------

-- XML attributes as key-value pairs
Attribute : Set
Attribute = String × String

Attributes : Set
Attributes = List Attribute

------------------------------------------------------------------------
-- Container & Free Monad Formulations
------------------------------------------------------------------------

module XMLCont where

  open import Data.Container.List public

  data XMLShape : Set where
    textₛ    : String → XMLShape
    elementₛ : (tag : String) (attrs : Attributes) (arity : ℕ) → XMLShape

  XMLPosition : XMLShape → Set
  XMLPosition (textₛ _)            = ⊥
  XMLPosition (elementₛ _ _ arity) = Fin arity

  XMLC : Container 0ℓ 0ℓ
  XMLC = XMLShape ▷ XMLPosition

  XMLContainer : Container 0ℓ 0ℓ
  XMLContainer = XMLC

  XMLM : Set a → Set a
  XMLM A = XMLC ⋆ A

  XML : Set a → Set a
  XML = XMLM

  XMLDoc : Set
  XMLDoc = XMLM ⊥

  foldXMLC : (String → B) → (String → Attributes → List B → B) → ⟦ XMLC ⟧ B → B
  foldXMLC fText fElem (textₛ s , _) = fText s
  foldXMLC fText fElem (elementₛ tag attrs n , pos) = fElem tag attrs (listCToList (n , pos))

  foldXMLM : (A → B) → (String → B) → (String → Attributes → List B → B) → XMLM A → B
  foldXMLM f g h = FM.foldr f (foldXMLC g h)

  text : String → XMLM A
  text s = FM.impure (textₛ s , λ ())

  elementList : (tag : String) → (attrs : Attributes) → (children : List (XMLM A)) → XMLM A
  elementList tag attrs children =
    let (n , pos) = listToListC children
    in FM.impure (elementₛ tag attrs n , pos)

  elementC : (tag : String) → (attrs : Attributes) → ⟦ ListC ⟧ (XMLM A) → XMLM A
  elementC tag attrs (n , pos) = FM.impure (elementₛ tag attrs n , pos)

  leafElement : (tag : String) (attrs : Attributes) → XMLM A
  leafElement tag attrs = elementList tag attrs []

  svg : Attributes → List (XMLM A) → XMLM A
  svg attrs children = elementList "svg" (("xmlns" , "http://www.w3.org/2000/svg") ∷ attrs) children

  g : Attributes → List (XMLM A) → XMLM A
  g attrs children = elementList "g" attrs children

  path : (d : String) → Attributes → XMLM A
  path d attrs = leafElement "path" (("d" , d) ∷ attrs)

  circle : (cx cy r : String) → Attributes → XMLM A
  circle cx cy r attrs = leafElement "circle" (("cx" , cx) ∷ ("cy" , cy) ∷ ("r" , r) ∷ attrs)

  rect : (x y width height : String) → Attributes → XMLM A
  rect x y w h attrs = leafElement "rect" (("x" , x) ∷ ("y" , y) ∷ ("width" , w) ∷ ("height" , h) ∷ attrs)

  polygon : (points : String) → Attributes → XMLM A
  polygon pts attrs = leafElement "polygon" (("points" , pts) ∷ attrs)

  polyline : (points : String) → Attributes → XMLM A
  polyline pts attrs = leafElement "polyline" (("points" , pts) ∷ attrs)

open XMLCont public using
  ( ListC; listCToList; listToListC
  ; XMLShape; textₛ; elementₛ; XMLPosition; XMLC; XMLContainer
  ; XMLM; XML; XMLDoc
  ; foldXMLC; foldXMLM
  ; text; elementList; elementC; leafElement
  ; svg; g; path; circle; rect; polygon; polyline
  )

open FM public using (pure; impure)
