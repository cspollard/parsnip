{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The recursive-descent parser, and `parser`: a stdlib RightInverse
-- from JSON values to valid token streams
--
-- `parseValue` is fuel-bounded recursive descent.  The fuel invariant is
-- "fuel ≥ number of tokens consumed": every call consumes at least one
-- token, and a call's children consume strictly fewer than the call.
-- `parseValue-print` shows the parser inverts `printTokens` up to `_≈ⱼ_`,
-- whatever tokens follow.
------------------------------------------------------------------------

module Data.JSON.Parser where

open import Level using (0ℓ)
open import Data.Char using (Char)
open import Data.Fin using (Fin; zero; suc)
open import Data.List as List using (List; []; _∷_; _++_; length)
open import Data.Maybe as Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m; +-comm; n≤1+n)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++; map-∘; map-cong)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; map₁; ∃; Σ-syntax)
open import Function using (_∘_)
open import Function.Bundles using (RightInverse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.JSON.AST
open JSONCont using (Key)
open import Data.JSON.Token
open import Data.JSON.Lexer using (ValidTokens; ValidTokenSeq)
open import Data.JSON.Tokens
open import Data.Container.FreeMonad using (pure; impure)
open import Data.JSON.Equality
open import Data.Stage using (Subtype)

------------------------------------------------------------------------
-- The parser
------------------------------------------------------------------------

mutual
  parseValue : ℕ → List JSONToken → Maybe (JSON × List JSONToken)
  parseValue zero    _ = nothing
  parseValue (suc f) (nullT ∷ ts)     = just (nullⱼ , ts)
  parseValue (suc f) (boolT b ∷ ts)   = just (boolⱼ b , ts)
  parseValue (suc f) (numberT n ∷ ts) = just (numberⱼ n , ts)
  parseValue (suc f) (stringT s ∷ ts) = just (stringⱼ′ s , ts)
  parseValue (suc f) (lbracketT ∷ ts) = Maybe.map (map₁ arrayⱼ) (parseArrayElements f ts)
  parseValue (suc f) (lbraceT ∷ ts)   = Maybe.map (map₁ objectFromList′) (parseObjectEntries f ts)
  parseValue (suc f) _                = nothing

  -- After a value: `]` ends the array, `,` continues it.
  continueArray : ℕ → JSON → List JSONToken → Maybe (List JSON × List JSONToken)
  continueArray f v (rbracketT ∷ ts) = just (v ∷ [] , ts)
  continueArray f v (commaT ∷ ts)    = Maybe.map (map₁ (v ∷_)) (parseArrayElements f ts)
  continueArray _ _ _                = nothing

  parseArrayElements : ℕ → List JSONToken → Maybe (List JSON × List JSONToken)
  parseArrayElements zero    _             = nothing
  parseArrayElements (suc f) []            = nothing
  parseArrayElements (suc f) (rbracketT ∷ ts) = just ([] , ts)
  parseArrayElements (suc f) ts            = continueArray′ f (parseValue f ts)

  continueArray′ : ℕ → Maybe (JSON × List JSONToken) → Maybe (List JSON × List JSONToken)
  continueArray′ f nothing         = nothing
  continueArray′ f (just (v , ts)) = continueArray f v ts

  continueObject : ℕ → Key → JSON → List JSONToken → Maybe (List (Key × JSON) × List JSONToken)
  continueObject f k v (rbraceT ∷ ts) = just ((k , v) ∷ [] , ts)
  continueObject f k v (commaT ∷ ts)  = Maybe.map (map₁ ((k , v) ∷_)) (parseObjectEntries f ts)
  continueObject _ _ _ _              = nothing

  parseObjectEntries : ℕ → List JSONToken → Maybe (List (Key × JSON) × List JSONToken)
  parseObjectEntries zero    _ = nothing
  parseObjectEntries (suc f) (rbraceT ∷ ts) = just ([] , ts)
  parseObjectEntries (suc f) (stringT k ∷ colonT ∷ ts) = continueObject′ f k (parseValue f ts)
  parseObjectEntries (suc f) _ = nothing

  continueObject′ : ℕ → Key → Maybe (JSON × List JSONToken) →
                    Maybe (List (Key × JSON) × List JSONToken)
  continueObject′ f k nothing         = nothing
  continueObject′ f k (just (v , ts)) = continueObject f k v ts

-- A complete token stream is one value.
parseWhole : Maybe (JSON × List JSONToken) → Maybe JSON
parseWhole (just (v , [])) = just v
parseWhole _               = nothing

parseTokens : List JSONToken → Maybe JSON
parseTokens ts = parseWhole (parseValue (suc (length ts)) ts)

------------------------------------------------------------------------
-- The parser inverts `printTokens`
------------------------------------------------------------------------

-- What the induction proves about each value.
Print-ok : JSON → Set
Print-ok v = ∀ rest fuel → length (printTokens v) ≤ fuel →
             ∃ λ v′ → parseValue fuel (printTokens v ++ rest) ≡ just (v′ , rest) × v′ ≈ⱼ v

private
  -- The array/object loops case-split on the first token; a value never
  -- starts with a closing token, so they continue with a value.
  parseArrayElements-value : ∀ g L → (∃ λ t → ∃ λ ts → L ≡ t ∷ ts × ValueStart t) →
                             parseArrayElements (suc g) L ≡ continueArray′ g (parseValue g L)
  parseArrayElements-value g .(t ∷ ts) (t , ts , refl , lbrace)   = refl
  parseArrayElements-value g .(t ∷ ts) (t , ts , refl , lbracket) = refl
  parseArrayElements-value g .(t ∷ ts) (t , ts , refl , null)     = refl
  parseArrayElements-value g .(t ∷ ts) (t , ts , refl , bool)     = refl
  parseArrayElements-value g .(t ∷ ts) (t , ts , refl , number)   = refl
  parseArrayElements-value g .(t ∷ ts) (t , ts , refl , string)   = refl

  -- A value's tokens, followed by anything, still start with a value.
  head-++ : ∀ v rest → ∃ λ t → ∃ λ ts → printTokens v ++ rest ≡ t ∷ ts × ValueStart t
  head-++ v rest with printTokens-head v
  ... | t , ts , eq , vs = t , ts ++ rest , cong (_++ rest) eq , vs

private
  arrayLoop-print : ∀ (xs : List JSON) → All Print-ok xs → ∀ rest fuel →
    length (elems (List.map printTokens xs)) < fuel →
    ∃ λ xs′ → parseArrayElements fuel (elems (List.map printTokens xs) ++ rbracketT ∷ rest)
                ≡ just (xs′ , rest)
            × Pointwise _≈ⱼ_ xs′ xs
  arrayLoop-print [] [] rest zero ()
  arrayLoop-print [] [] rest (suc g) _ = [] , refl , []
  arrayLoop-print (x ∷ []) (px ∷ []) rest zero ()
  arrayLoop-print (x ∷ []) (px ∷ []) rest (suc g) (s≤s le)
    with px (rbracketT ∷ rest) g le
  ... | v′ , eqp , ≈v =
    v′ ∷ [] ,
    trans (parseArrayElements-value g _ (head-++ x (rbracketT ∷ rest)))
          (cong (continueArray′ g) eqp) ,
    ≈v ∷ []
  arrayLoop-print (x ∷ y ∷ ys) (px ∷ pys) rest zero ()
  arrayLoop-print (x ∷ y ∷ ys) (px ∷ pys) rest (suc g) lt
    with subst (_< suc g) (length-++ (printTokens x)) lt
  ... | s≤s le
    with px (commaT ∷ (E ++ rbracketT ∷ rest)) g
            (≤-trans (m≤m+n (length (printTokens x)) (suc (length E))) le)
    where E = elems (List.map printTokens (y ∷ ys))
  ... | v′ , eqp , ≈v
    with arrayLoop-print (y ∷ ys) pys rest g
            (≤-trans (m≤n+m (suc (length (elems (List.map printTokens (y ∷ ys))))) (length (printTokens x))) le)
  ... | xs″ , eqI , pw =
    v′ ∷ xs″ ,
    trans (cong (parseArrayElements (suc g))
                (++-assoc (printTokens x) (commaT ∷ elems (List.map printTokens (y ∷ ys)))
                          (rbracketT ∷ rest)))
    (trans (parseArrayElements-value g _
              (head-++ x (commaT ∷ (elems (List.map printTokens (y ∷ ys)) ++ rbracketT ∷ rest))))
    (trans (cong (continueArray′ g) eqp)
           (cong (Maybe.map (map₁ (v′ ∷_))) eqI))) ,
    ≈v ∷ pw

-- The tokens of one keyed child.
entryOf : Key × JSON → List JSONToken
entryOf (k , x) = stringT k ∷ colonT ∷ printTokens x

private
  objectLoop-print : ∀ (kvs : List (Key × JSON)) → All (λ p → Print-ok (proj₂ p)) kvs → ∀ rest fuel →
    length (elems (List.map entryOf kvs)) < fuel →
    ∃ λ kvs′ → parseObjectEntries fuel (elems (List.map entryOf kvs) ++ rbraceT ∷ rest)
                 ≡ just (kvs′ , rest)
             × Pointwise EntryRel kvs′ kvs
  objectLoop-print [] [] rest zero ()
  objectLoop-print [] [] rest (suc g) _ = [] , refl , []
  objectLoop-print ((k , x) ∷ []) (px ∷ []) rest zero ()
  objectLoop-print ((k , x) ∷ []) (px ∷ []) rest (suc g) (s≤s le)
    with px (rbraceT ∷ rest) g (≤-trans (m≤n+m (length (printTokens x)) 2) le)
  ... | v′ , eqp , ≈v =
    (k , v′) ∷ [] , cong (continueObject′ g k) eqp , (refl , ≈v) ∷ []
  objectLoop-print ((k , x) ∷ (k₂ , y) ∷ kvs) (px ∷ pkvs) rest zero ()
  objectLoop-print ((k , x) ∷ (k₂ , y) ∷ kvs) (px ∷ pkvs) rest (suc g) lt
    with subst (_< suc g) (length-++ (entryOf (k , x))) lt
  ... | s≤s le
    with px (commaT ∷ (E ++ rbraceT ∷ rest)) g
            (≤-trans (≤-trans (m≤n+m (length (printTokens x)) 2)
                              (m≤m+n (length (entryOf (k , x))) (suc (length E)))) le)
    where E = elems (List.map entryOf ((k₂ , y) ∷ kvs))
  ... | v′ , eqp , ≈v
    with objectLoop-print ((k₂ , y) ∷ kvs) pkvs rest g
            (≤-trans (m≤n+m (suc (length (elems (List.map entryOf ((k₂ , y) ∷ kvs)))))
                            (length (entryOf (k , x)))) le)
  ... | kvs″ , eqI , pw =
    (k , v′) ∷ kvs″ ,
    trans (cong (parseObjectEntries (suc g))
                (++-assoc (entryOf (k , x))
                          (commaT ∷ elems (List.map entryOf ((k₂ , y) ∷ kvs)))
                          (rbraceT ∷ rest)))
    (trans (cong (continueObject′ g k) eqp)
           (cong (Maybe.map (map₁ ((k , v′) ∷_))) eqI)) ,
    (refl , ≈v) ∷ pw

private
  all-listC : ∀ {P : JSON → Set} n (g : Fin n → JSON) → (∀ i → P (g i)) →
              All P (JSONCont.listCToList (n , g))
  all-listC zero    g p = []
  all-listC (suc n) g p = p zero ∷ all-listC n (g ∘ suc) (p ∘ suc)

  all-entries : ∀ {P : JSON → Set} ks (g : Fin (length ks) → JSON) → (∀ i → P (g i)) →
                All (λ p → P (proj₂ p)) (JSONCont.objectCToEntries (ks , g))
  all-entries []       g p = []
  all-entries (k ∷ ks) g p = p zero ∷ all-entries ks (g ∘ suc) (p ∘ suc)

  printTokens-object′ : ∀ ks (f : Fin (length ks) → JSON) →
    printTokens (impure ((JSONCont.object , ks) , f))
      ≡ lbraceT ∷ elems (List.map entryOf (JSONCont.objectCToEntries (ks , f))) ++ rbraceT ∷ []
  printTokens-object′ ks f =
    cong (λ l → lbraceT ∷ elems l ++ rbraceT ∷ [])
      (trans (cong (List.map entry) (objectCToEntries-map ks f printTokens))
             (trans (sym (map-∘ (JSONCont.objectCToEntries (ks , f))))
                    (map-cong (λ { (k , x) → refl }) (JSONCont.objectCToEntries (ks , f)))))

private
  -- Print-ok is invariant under rewriting the token list of the value.
  print-ok-via : ∀ v T → printTokens v ≡ T →
                 (∀ rest fuel → length T ≤ fuel →
                    ∃ λ v′ → parseValue fuel (T ++ rest) ≡ just (v′ , rest) × v′ ≈ⱼ v) →
                 Print-ok v
  print-ok-via v T eq core rest fuel le with core rest fuel (subst (λ X → length X ≤ fuel) eq le)
  ... | v′ , p , ≈v = v′ , subst (λ X → parseValue fuel (X ++ rest) ≡ just (v′ , rest)) (sym eq) p , ≈v

  arrayCase : ∀ n (f : Fin n → JSON) → (∀ i → Print-ok (f i)) →
              Print-ok (impure ((JSONCont.array , n) , f))
  arrayCase n f ih = print-ok-via _ _ (printTokens-array n f) core
    where
    xs = JSONCont.listCToList (n , f)
    E  = elems (List.map printTokens xs)

    core : ∀ rest fuel → length (lbracketT ∷ E ++ rbracketT ∷ []) ≤ fuel →
           ∃ λ v′ → parseValue fuel ((lbracketT ∷ E ++ rbracketT ∷ []) ++ rest) ≡ just (v′ , rest)
                  × v′ ≈ⱼ impure ((JSONCont.array , n) , f)
    core rest zero ()
    core rest (suc g) (s≤s le) with arrayLoop-print xs (all-listC n f ih) rest g
                              (subst (_≤ g) (trans (length-++ E) (+-comm (length E) 1)) le)
    ... | xs′ , eqL , pw =
      arrayⱼ xs′ ,
      trans (cong (λ T → Maybe.map (map₁ arrayⱼ) (parseArrayElements g T))
                  (++-assoc E (rbracketT ∷ []) rest))
            (cong (Maybe.map (map₁ arrayⱼ)) eqL) ,
      arrayⱼ-go n f xs′ pw

  objectCase : ∀ ks (f : Fin (length ks) → JSON) → (∀ i → Print-ok (f i)) →
               Print-ok (impure ((JSONCont.object , ks) , f))
  objectCase ks f ih = print-ok-via _ _ (printTokens-object′ ks f) core
    where
    kvs = JSONCont.objectCToEntries (ks , f)
    E   = elems (List.map entryOf kvs)

    core : ∀ rest fuel → length (lbraceT ∷ E ++ rbraceT ∷ []) ≤ fuel →
           ∃ λ v′ → parseValue fuel ((lbraceT ∷ E ++ rbraceT ∷ []) ++ rest) ≡ just (v′ , rest)
                  × v′ ≈ⱼ impure ((JSONCont.object , ks) , f)
    core rest zero ()
    core rest (suc g) (s≤s le) with objectLoop-print kvs (all-entries ks f ih) rest g
                              (subst (_≤ g) (trans (length-++ E) (+-comm (length E) 1)) le)
    ... | kvs′ , eqL , pw =
      objectFromList′ kvs′ ,
      trans (cong (λ T → Maybe.map (map₁ objectFromList′) (parseObjectEntries g T))
                  (++-assoc E (rbraceT ∷ []) rest))
            (cong (Maybe.map (map₁ objectFromList′)) eqL) ,
      objectFromList′-go ks f kvs′ pw

parseValue-print : ∀ v → Print-ok v
parseValue-print (pure ())
parseValue-print (impure ((JSONCont.prim JSONCont.primstring , s) , f)) rest (suc g) (s≤s _) =
  stringⱼ′ s , refl , ≈prim
parseValue-print (impure ((JSONCont.prim JSONCont.primnumber , n) , f)) rest (suc g) (s≤s _) =
  numberⱼ n , refl , ≈prim
parseValue-print (impure ((JSONCont.prim JSONCont.primbool , b) , f)) rest (suc g) (s≤s _) =
  boolⱼ b , refl , ≈prim
parseValue-print (impure ((JSONCont.prim JSONCont.primnull , u) , f)) rest (suc g) (s≤s _) =
  nullⱼ , refl , ≈prim
parseValue-print (impure ((JSONCont.array , n) , f)) = arrayCase n f (λ i → parseValue-print (f i))
parseValue-print (impure ((JSONCont.object , ks) , f)) = objectCase ks f (λ i → parseValue-print (f i))

------------------------------------------------------------------------
-- `parser`
------------------------------------------------------------------------

parseTokens-printTokens : ∀ v → ∃ λ v′ → parseTokens (printTokens v) ≡ just v′ × v′ ≈ⱼ v
parseTokens-printTokens v with parseValue-print v [] (suc (length (printTokens v))) (n≤1+n _)
... | v′ , p , ≈v =
  v′ ,
  cong parseWhole
    (subst (λ X → parseValue (suc (length (printTokens v))) X ≡ just (v′ , []))
           (++-identityʳ (printTokens v)) p) ,
  ≈v

-- `parser` (see `Data.JSON.Goals`).  `to` pairs the tokens with the proof that
-- they are valid; `from` parses, with `nullⱼ` where parsing fails.
parser : RightInverse JSONSetoid ValidTokens
parser = record
  { to        = λ v → printTokens v , printTokens-valid v
  ; from      = λ x → fromMaybe nullⱼ (parseTokens (proj₁ x))
  ; to-cong   = printTokens-cong
  ; from-cong = λ { refl → ≈ⱼ-refl }
  ; inverseʳ  = λ { {v} {ts , _} refl → inv v }
  }
  where
  inv : ∀ v → fromMaybe nullⱼ (parseTokens (printTokens v)) ≈ⱼ v
  inv v with parseTokens-printTokens v
  ... | v′ , eq , ≈v = subst (_≈ⱼ v) (sym (cong (fromMaybe nullⱼ) eq)) ≈v
