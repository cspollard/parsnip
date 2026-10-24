{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The token stream of an XML document
--
-- `printTokens` is the free-monad catamorphism giving each element's
-- tokens from its children's.  `printTokens-valid` says its output is a
-- valid stream (so it is a valid input to `lexer`), `printTokens-head`
-- that it starts with a start tag, and `printTokens-cong` that printing
-- respects bisimilarity.
------------------------------------------------------------------------

module Data.XML.Tokens where

open import Data.Bool using (Bool; true; false; _∧_; not; T)
open import Data.Bool.ListAction using (all)
open import Data.Fin using (Fin; zero; suc)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Data.XML.AST
open import Data.XML.Valid
open import Data.XML.Equality using (_≈ₓ_; ≈element)
open import Data.XML.Token
open import Data.XML.Lexer using (Run; done; step; run++; isText)

------------------------------------------------------------------------
-- Printing
------------------------------------------------------------------------

-- Character data: a token unless the slot is empty.
textTokens : Text → List XMLToken
textTokens []       = []
textTokens (c ∷ cs) = textT (c ∷ cs) ∷ []

-- Each child's tokens followed by the text after it.
childTokens : List (List XMLToken × Text) → List XMLToken
childTokens []              = []
childTokens ((ts , t) ∷ cs) = ts ++ textTokens t ++ childTokens cs

contentTokens : Content (List XMLToken) → List XMLToken
contentTokens (t , cs) = textTokens t ++ childTokens cs

-- An element with no content is one `selfT`; otherwise it is wrapped in
-- `openT` and `closeT`.  (The children are matched first, so that the
-- definition reduces when only they are known.)
elementTokens : Name → Attributes → Content (List XMLToken) → List XMLToken
elementTokens₁ : Name → Attributes → Text → List XMLToken

elementTokens tag attrs (t , [])        = elementTokens₁ tag attrs t
elementTokens tag attrs (t , c ∷ cs)   = openT tag attrs ∷ contentTokens (t , c ∷ cs) ++ closeT tag ∷ []

elementTokens₁ tag attrs []           = selfT tag attrs ∷ []
elementTokens₁ tag attrs (x ∷ xs)     = openT tag attrs ∷ contentTokens (x ∷ xs , []) ++ closeT tag ∷ []

printTokens : XMLDoc → List XMLToken
printTokens = foldXMLM (λ ()) elementTokens

-- `printTokens` at a node.
printTokens-node : ∀ tag attrs n ts pt pa px (f : Fin n → XMLDoc) →
  printTokens (impure (shape tag attrs n ts pt pa px , f))
    ≡ elementTokens tag attrs (mixed n ts (printTokens ∘ f))
printTokens-node tag attrs n ts pt pa px f = refl

------------------------------------------------------------------------
-- `mixed` commutes with mapping the children
------------------------------------------------------------------------

mapChildren : ∀ {A B : Set} → (A → B) → List (A × Text) → List (B × Text)
mapChildren h = List.map (λ { (x , t) → h x , t })

mapContent : ∀ {A B : Set} → (A → B) → Content A → Content B
mapContent h (t , cs) = t , mapChildren h cs

mixed-map : ∀ {A B : Set} n (ts : Vec Text (suc n)) (g : Fin n → A) (h : A → B) →
            mixed n ts (h ∘ g) ≡ mapContent h (mixed n ts g)
mixed-map zero    (t ∷ [])  g h = refl
mixed-map (suc n) (t ∷ ts) g h =
  cong (λ m → t , (h (g zero) , proj₁ m) ∷ proj₂ m) (mixed-map n ts (g ∘ suc) h)

mixed-cong : ∀ {B : Set} n (ts : Vec Text (suc n)) (F G : Fin n → B) → (∀ i → F i ≡ G i) →
             mixed n ts F ≡ mixed n ts G
mixed-cong zero    (t ∷ [])  F G p = refl
mixed-cong (suc n) (t ∷ ts) F G p =
  cong₂ (λ x m → t , (x , proj₁ m) ∷ proj₂ m) (p zero) (mixed-cong n ts (F ∘ suc) (G ∘ suc) (p ∘ suc))

------------------------------------------------------------------------
-- The first token
------------------------------------------------------------------------

-- Tokens an element can start with.
data ElemStart : XMLToken → Set where
  openS : ∀ {n as} → ElemStart (openT n as)
  selfS : ∀ {n as} → ElemStart (selfT n as)

printTokens-head : ∀ v → ∃ λ t → ∃ λ ts → printTokens v ≡ t ∷ ts × ElemStart t
printTokens-head (pure ())
printTokens-head (impure (shape tag attrs zero ([] ∷ []) pt pa px , f))        = selfT tag attrs , [] , refl , selfS
printTokens-head (impure (shape tag attrs zero ((x ∷ xs) ∷ []) pt pa px , f)) = openT tag attrs , _ , refl , openS
printTokens-head (impure (shape tag attrs (suc n) (t ∷ ts) pt pa px , f))     = openT tag attrs , _ , refl , openS

------------------------------------------------------------------------
-- The stream is valid
------------------------------------------------------------------------

private
  toEq : ∀ {b} → T b → b ≡ true
  toEq {true} _ = refl

  notText : ∀ p → T (not (p ∧ false))
  notText true  = tt
  notText false = tt

  names : ∀ as → isValidAttrs as ≡ true → attrNamesValid as ≡ true
  names as h with ∧-split h
  ... | hall , _ = go as hall
    where
    go : ∀ as → all isValidAttribute as ≡ true → attrNamesValid as ≡ true
    go []             _ = refl
    go ((k , v) ∷ as) h with ∧-split h
    ... | hk , hs with ∧-split hk
    ... | hname , _ = ∧-join hname (go as hs)

  -- The state after the text slot `t`.
  slot : Text → Bool
  slot []      = false
  slot (_ ∷ _) = true

  text-run : ∀ t → Run false (slot t) (textTokens t)
  text-run []       = done
  text-run (x ∷ xs) = step refl tt done

  -- The tokens of a content, started after a start tag.
  content-run : ∀ n (ts : Vec Text (suc n)) (g : Fin n → List XMLToken) →
                (∀ i p → Run p false (g i)) →
                ∃ λ q → Run false q (contentTokens (mixed n ts g))
  content-run zero    ([] ∷ [])        g _ = false , done
  content-run zero    ((x ∷ xs) ∷ [])  g _ = true , step refl tt done
  content-run (suc n) (t ∷ ts)         g r with content-run n ts (g ∘ suc) (r ∘ suc)
  ... | q , rest = q , run++ (text-run t) (run++ (r zero (slot t)) rest)

  -- A start tag, the tokens of its content, and the end tag.
  open′ : ∀ {p c} tag attrs → T (isValidName tag) → T (isValidAttrs attrs) →
          (∃ λ q → Run false q (contentTokens c)) →
          Run p false (openT tag attrs ∷ contentTokens c ++ closeT tag ∷ [])
  open′ {p} tag attrs pt pa (q , r) =
    step (∧-join (toEq pt) (names attrs (toEq pa))) (notText p)
         (run++ r (step (toEq pt) (notText q) done))

  elem-run : ∀ v p → Run p false (printTokens v)
  elem-run (pure ()) p
  elem-run (impure (shape tag attrs zero ([] ∷ []) pt pa px , f)) p =
    step (∧-join (toEq pt) (names attrs (toEq pa))) (notText p) done
  elem-run (impure (shape tag attrs zero ((x ∷ xs) ∷ []) pt pa px , f)) p =
    open′ {c = mixed zero ((x ∷ xs) ∷ []) (printTokens ∘ f)} tag attrs pt pa
      (content-run zero ((x ∷ xs) ∷ []) (printTokens ∘ f) (λ ()))
  elem-run (impure (shape tag attrs (suc n) (t ∷ ts) pt pa px , f)) p =
    open′ {c = mixed (suc n) (t ∷ ts) (printTokens ∘ f)} tag attrs pt pa
      (content-run (suc n) (t ∷ ts) (printTokens ∘ f) (λ i q → elem-run (f i) q))

printTokens-valid : ∀ v → Run false false (printTokens v)
printTokens-valid v = elem-run v false

------------------------------------------------------------------------
-- Printing respects bisimilarity
------------------------------------------------------------------------

printTokens-cong : ∀ {v w} → v ≈ₓ w → printTokens v ≡ printTokens w
printTokens-cong (≈element {tag} {attrs} {n} {ts = ts} {f = f} {g = g} refl refl h) =
  cong (elementTokens tag attrs)
       (mixed-cong n ts (printTokens ∘ f) (printTokens ∘ g) (λ i → printTokens-cong (h i)))
