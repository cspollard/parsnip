{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Projections out of a JSON value
--
-- Total `Maybe` views (`asNull` … `asObject`) and first-match field
-- lookup.  The schema language and its evidence relation live in
-- `Data.JSON.Conformance`.
------------------------------------------------------------------------

module Data.JSON.Schema where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.String as String using (String; fromList)
open import Data.String.Properties using (_≟_) renaming (≡-decSetoid to stringDecSetoid)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List as List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂; map₁)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.JSON.AST
open JSONCont
  using (listCToList; objectCToEntries; pstring; pnumber; pbool; pnull; object; array; primnull; primbool; primnumber; primstring; prim)

------------------------------------------------------------------------
-- JSON Unpacking / Projections
------------------------------------------------------------------------

asNull : JSON → Maybe ⊤
asNull (impure ((pnull , _) , _)) = just tt
asNull _                          = nothing

asBool : JSON → Maybe Bool
asBool (impure ((pbool , b) , _)) = just b
asBool _                          = nothing

asNumber : JSON → Maybe JSONNumber
asNumber (impure ((pnumber , n) , _)) = just n
asNumber _                            = nothing

asString : JSON → Maybe String
asString (impure ((pstring , s) , _)) = just (fromList s)
asString _                            = nothing

asArray : JSON → Maybe (List JSON)
asArray (impure ((array , shp) , pos)) = just (listCToList (shp , pos))
asArray _                              = nothing

asObject : JSON → Maybe (List (String × JSON))
asObject (impure ((object , shp) , pos)) = just (List.map (map₁ fromList) (objectCToEntries (shp , pos)))
asObject _                               = nothing

------------------------------------------------------------------------
-- Field Lookup in Association Lists
------------------------------------------------------------------------

lookupField : String → List (String × JSON) → Maybe JSON
lookupField _ [] = nothing
lookupField key ((k , v) ∷ kvs) with key ≟ k
... | yes _ = just v
... | no  _ = lookupField key kvs
