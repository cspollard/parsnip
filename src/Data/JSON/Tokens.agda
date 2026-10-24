{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The token stream of a JSON value
--
-- `printTokens` is the free-monad catamorphism giving each node's tokens
-- from its children's.  `printTokens-valid` says its output never has
-- two adjacent numbers (so it is a valid input to `lexer`), and
-- `printTokens-head` that it never starts with a closing token (what
-- the parser's case split needs).
------------------------------------------------------------------------

module Data.JSON.Tokens where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List as List using (List; []; _∷_; _++_; intercalate; last; head)
open import Data.List.Relation.Unary.Linked as Linked using (Linked; []; [-]; _∷_; _∷′_)
open import Data.List.Relation.Unary.Linked.Properties using (++⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Nullary using (¬_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Binary.Connected as Connected using (Connected)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; ∃)
open import Data.Container using (⟦_⟧)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.JSON.AST
open JSONCont
open import Data.JSON.Token
open import Data.JSON.Lexer using (IsNumber; NotAdjacent; ValidTokenSeq)

------------------------------------------------------------------------
-- Printing
------------------------------------------------------------------------

-- Children's tokens joined by commas.
elems : List (List JSONToken) → List JSONToken
elems = intercalate (commaT ∷ [])

entry : Key × List JSONToken → List JSONToken
entry (k , ts) = stringT k ∷ colonT ∷ ts

printTokens : JSON → List JSONToken
printTokens = foldJSONM (λ ()) go
  where
  go : (t : JSONType) → ⟦ JSON→ t ⟧ (List JSONToken) → List JSONToken
  go object x = lbraceT ∷ elems (List.map entry (objectCToEntries x)) ++ rbraceT ∷ []
  go array x  = lbracketT ∷ elems (listCToList x) ++ rbracketT ∷ []
  go (prim primstring) (s , _) = stringT s ∷ []
  go (prim primnumber) (n , _) = numberT n ∷ []
  go (prim primbool)   (b , _) = boolT b ∷ []
  go (prim primnull)   _       = nullT ∷ []

------------------------------------------------------------------------
-- Unfolding `printTokens` at arrays and objects
------------------------------------------------------------------------

listCToList-map : ∀ {A B : Set} n (f : Fin n → A) (g : A → B) →
                  listCToList (n , g ∘ f) ≡ List.map g (listCToList (n , f))
listCToList-map zero    f g = refl
listCToList-map (suc n) f g = cong (g (f zero) ∷_) (listCToList-map n (f ∘ suc) g)

objectCToEntries-map : ∀ {A B : Set} ks (f : Fin (List.length ks) → A) (g : A → B) →
                       objectCToEntries (ks , g ∘ f)
                         ≡ List.map (λ p → proj₁ p , g (Data.Product.proj₂ p)) (objectCToEntries (ks , f))
objectCToEntries-map []       f g = refl
objectCToEntries-map (k ∷ ks) f g =
  cong ((k , g (f zero)) ∷_) (objectCToEntries-map ks (f ∘ suc) g)

printTokens-array : ∀ n (f : Fin n → JSON) →
  printTokens (impure ((array , n) , f))
    ≡ lbracketT ∷ elems (List.map printTokens (listCToList (n , f))) ++ rbracketT ∷ []
printTokens-array n f = cong (λ l → lbracketT ∷ elems l ++ rbracketT ∷ []) (listCToList-map n f printTokens)

printTokens-object : ∀ ks (f : Fin (List.length ks) → JSON) →
  printTokens (impure ((object , ks) , f))
    ≡ lbraceT ∷ elems (List.map entry (objectCToEntries (ks , printTokens ∘ f))) ++ rbraceT ∷ []
printTokens-object ks f = refl

------------------------------------------------------------------------
-- The first token
------------------------------------------------------------------------

-- Tokens a value can start with.
data ValueStart : JSONToken → Set where
  lbrace   : ValueStart lbraceT
  lbracket : ValueStart lbracketT
  null     : ValueStart nullT
  bool     : ∀ {b} → ValueStart (boolT b)
  number   : ∀ {n} → ValueStart (numberT n)
  string   : ∀ {s} → ValueStart (stringT s)

printTokens-head : ∀ v → ∃ λ t → ∃ λ ts → printTokens v ≡ t ∷ ts × ValueStart t
printTokens-head (pure ())
printTokens-head (impure ((object , ks) , f)) = lbraceT , _ , refl , lbrace
printTokens-head (impure ((array , n) , f))   = lbracketT , _ , refl , lbracket
printTokens-head (impure ((prim primstring , s) , f)) = stringT s , _ , refl , string
printTokens-head (impure ((prim primnumber , n) , f)) = numberT n , _ , refl , number
printTokens-head (impure ((prim primbool , b) , f))   = boolT b , _ , refl , bool
printTokens-head (impure ((prim primnull , u) , f))   = nullT , _ , refl , null

------------------------------------------------------------------------
-- No two adjacent numbers
------------------------------------------------------------------------

private
  Valid : List JSONToken → Set
  Valid = ValidTokenSeq

  connected-sep-r : ∀ m s → ¬ IsNumber s → Connected NotAdjacent m (just s)
  connected-sep-r nothing  s ns = Connected.nothing-just
  connected-sep-r (just x) s ns = Connected.just (λ _ n → ns n)

  connected-sep-l : ∀ s → ¬ IsNumber s → ∀ m → Connected NotAdjacent (just s) m
  connected-sep-l s ns nothing  = Connected.just-nothing
  connected-sep-l s ns (just y) = Connected.just (λ n _ → ns n)

  -- A non-number separator never creates an adjacent pair.
  valid-sep : ∀ {xs ys} s → ¬ IsNumber s → Valid xs → Valid ys → Valid (xs ++ s ∷ ys)
  valid-sep {xs} {ys} s ns vxs vys =
    ++⁺ vxs (connected-sep-r (last xs) s ns) (connected-sep-l s ns (head ys) ∷′ vys)

  valid-wrap : ∀ {ys} o c → ¬ IsNumber o → ¬ IsNumber c → Valid ys → Valid (o ∷ ys ++ c ∷ [])
  valid-wrap {ys} o c no nc vys =
    connected-sep-l o no (head (ys ++ c ∷ [])) ∷′ valid-sep c nc vys []

  valid-elems : ∀ ls → All Valid ls → Valid (elems ls)
  valid-elems []           _             = []
  valid-elems (x ∷ [])     (vx ∷ _)      = vx
  valid-elems (x ∷ y ∷ ls) (vx ∷ vyls)   = valid-sep commaT (λ ()) vx (valid-elems (y ∷ ls) vyls)

  valid-entry : ∀ k {ts} → Valid ts → Valid (entry (k , ts))
  valid-entry k {ts} vts =
    connected-sep-l (stringT k) (λ ()) (just colonT)
      ∷′ (connected-sep-l colonT (λ ()) (head ts) ∷′ vts)

  all-listC : ∀ {A : Set} {P : A → Set} n (g : Fin n → A) → (∀ i → P (g i)) →
              All P (listCToList (n , g))
  all-listC zero    g p = []
  all-listC (suc n) g p = p zero ∷ all-listC n (g ∘ suc) (p ∘ suc)

  all-entries : ∀ ks (g : Fin (List.length ks) → List JSONToken) → (∀ i → Valid (g i)) →
                All Valid (List.map entry (objectCToEntries (ks , g)))
  all-entries []       g p = []
  all-entries (k ∷ ks) g p = valid-entry k (p zero) ∷ all-entries ks (g ∘ suc) (p ∘ suc)

printTokens-valid : ∀ v → ValidTokenSeq (printTokens v)
printTokens-valid (pure ())
printTokens-valid (impure ((object , ks) , f)) =
  valid-wrap lbraceT rbraceT (λ ()) (λ ())
    (valid-elems _ (all-entries ks (printTokens ∘ f) (λ i → printTokens-valid (f i))))
printTokens-valid (impure ((array , n) , f)) =
  valid-wrap lbracketT rbracketT (λ ()) (λ ())
    (valid-elems _ (all-listC n (printTokens ∘ f) (λ i → printTokens-valid (f i))))
printTokens-valid (impure ((prim primstring , s) , f)) = [-]
printTokens-valid (impure ((prim primnumber , n) , f)) = [-]
printTokens-valid (impure ((prim primbool , b) , f))   = [-]
printTokens-valid (impure ((prim primnull , u) , f))   = [-]

------------------------------------------------------------------------
-- Printing respects bisimilarity
------------------------------------------------------------------------

open import Data.JSON.Equality using (_≈ⱼ_; ≈prim; ≈array; ≈object)

private
  listCToList-cong : ∀ {A : Set} n (F G : Fin n → A) → (∀ i → F i ≡ G i) →
                     listCToList (n , F) ≡ listCToList (n , G)
  listCToList-cong zero    F G p = refl
  listCToList-cong (suc n) F G p =
    Relation.Binary.PropositionalEquality.cong₂ _∷_ (p zero)
      (listCToList-cong n (F ∘ suc) (G ∘ suc) (p ∘ suc))

  objectCToEntries-cong : ∀ {A : Set} ks (F G : Fin (List.length ks) → A) → (∀ i → F i ≡ G i) →
                          objectCToEntries (ks , F) ≡ objectCToEntries (ks , G)
  objectCToEntries-cong []       F G p = refl
  objectCToEntries-cong (k ∷ ks) F G p =
    Relation.Binary.PropositionalEquality.cong₂ _∷_
      (cong (k ,_) (p zero))
      (objectCToEntries-cong ks (F ∘ suc) (G ∘ suc) (p ∘ suc))

printTokens-cong : ∀ {v w} → v ≈ⱼ w → printTokens v ≡ printTokens w
printTokens-cong (≈prim {primstring}) = refl
printTokens-cong (≈prim {primnumber}) = refl
printTokens-cong (≈prim {primbool})   = refl
printTokens-cong (≈prim {primnull})   = refl
printTokens-cong (≈array {n} {_} {f} {g} refl h) =
  cong (λ l → lbracketT ∷ elems l ++ rbracketT ∷ [])
       (listCToList-cong n (printTokens ∘ f) (printTokens ∘ g) (λ i → printTokens-cong (h i)))
printTokens-cong (≈object {ks} {_} {f} {g} refl h) =
  cong (λ l → lbraceT ∷ elems (List.map entry l) ++ rbraceT ∷ [])
       (objectCToEntries-cong ks (printTokens ∘ f) (printTokens ∘ g) (λ i → printTokens-cong (h i)))
