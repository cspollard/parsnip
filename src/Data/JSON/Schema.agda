{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

module Data.JSON.Schema where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.String as String using (String)
open import Data.String.Properties using (_≟_) renaming (≡-decSetoid to stringDecSetoid)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List as List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.JSON.AST
open JSONCont
  using (listCToList; pstring; pnumber; pbool; pnull; object; array; primnull; primbool; primnumber; primstring; prim)
open import Data.JSON.ObjectC stringDecSetoid using (objectToList)

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
asString (impure ((pstring , s) , _)) = just s
asString _                            = nothing

asArray : JSON → Maybe (List JSON)
asArray (impure ((array , shp) , pos)) = just (listCToList (shp , pos))
asArray _                              = nothing

asObject : JSON → Maybe (List (String × JSON))
asObject (impure ((object , shp) , pos)) = just (objectToList (shp , pos))
asObject _                               = nothing

------------------------------------------------------------------------
-- Field Lookup in Association Lists
------------------------------------------------------------------------

lookupField : String → List (String × JSON) → Maybe JSON
lookupField _ [] = nothing
lookupField key ((k , v) ∷ kvs) with key ≟ k
... | yes _ = just v
... | no  _ = lookupField key kvs

------------------------------------------------------------------------
-- Lightweight Schema Definitions
------------------------------------------------------------------------

data Schema : Set where
  sAny    : Schema
  sNull   : Schema
  sBool   : Schema
  sNumber : Schema
  sString : Schema
  sArray  : Schema → Schema
  sObject : List (String × Schema) → Schema

-- Decidable schema check procedure
mutual
  checkSchema : JSON → Schema → Bool
  checkSchema _ sAny    = true
  checkSchema v sNull   with asNull v
  ... | just _  = true
  ... | nothing = false
  checkSchema v sBool   with asBool v
  ... | just _  = true
  ... | nothing = false
  checkSchema v sNumber with asNumber v
  ... | just _  = true
  ... | nothing = false
  checkSchema v sString with asString v
  ... | just _  = true
  ... | nothing = false
  checkSchema v (sArray elemS) with asArray v
  ... | nothing    = false
  ... | just elems = checkArrayElements elems elemS
  checkSchema v (sObject reqs) with asObject v
  ... | nothing  = false
  ... | just kvs = checkObjectFields kvs reqs

  checkArrayElements : List JSON → Schema → Bool
  checkArrayElements [] _ = true
  checkArrayElements (x ∷ xs) s with checkSchema x s
  ... | true  = checkArrayElements xs s
  ... | false = false

  checkObjectFields : List (String × JSON) → List (String × Schema) → Bool
  checkObjectFields _ [] = true
  checkObjectFields kvs ((k , s) ∷ reqs) with lookupField k kvs
  ... | nothing = false
  ... | just v  with checkSchema v s
  ...   | true  = checkObjectFields kvs reqs
  ...   | false = false
