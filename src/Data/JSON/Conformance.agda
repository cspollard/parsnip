{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Schemas, constructive conformance evidence, and its decision procedure
--
-- `v ⊨ s` is evidence that `v` conforms to `s`, stated through the
-- projections of `Data.JSON.Schema` (`asNumber v ≡ just n`, …) rather
-- than equations on `JSON`, which would need funext.  Every schema has a
-- decision procedure and a type `⟦ s ⟧` of decoded values, and evidence
-- decodes to it (`decodeFromEvidence`).
------------------------------------------------------------------------

module Data.JSON.Conformance where

open import Data.Bool using (Bool)
open import Data.String as String using (String)
open import Data.String.Properties using (_≟_)
open import Data.List as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Data.JSON.AST using (JSON; JSONNumber)
open import Data.JSON.Schema
  using (asNull; asBool; asNumber; asString; asArray; asObject; lookupField)

------------------------------------------------------------------------
-- Schemas
------------------------------------------------------------------------

data Schema : Set where
  sAny         : Schema
  sNull        : Schema
  sBool        : Schema
  sNumber      : Schema
  sString      : Schema
  sExactString : String → Schema
  sList        : Schema → Schema
  sTuple2      : Schema → Schema → Schema
  sObjectReq   : List (String × Schema) → Schema

------------------------------------------------------------------------
-- Evidence
------------------------------------------------------------------------

mutual
  data _⊨_ : JSON → Schema → Set where
    evAny         : ∀ {v} → v ⊨ sAny
    evNull        : ∀ {v} → asNull v ≡ just tt → v ⊨ sNull
    evBool        : ∀ {v} (b : Bool) → asBool v ≡ just b → v ⊨ sBool
    evNumber      : ∀ {v} (n : JSONNumber) → asNumber v ≡ just n → v ⊨ sNumber
    evString      : ∀ {v} (s : String) → asString v ≡ just s → v ⊨ sString
    evExactString : ∀ {v expected} → asString v ≡ just expected → v ⊨ sExactString expected
    evList        : ∀ {v xs elemS} → asArray v ≡ just xs → All (_⊨ elemS) xs → v ⊨ sList elemS
    evTuple2      : ∀ {v x₁ x₂ s₁ s₂} →
                    asArray v ≡ just (x₁ ∷ x₂ ∷ []) → x₁ ⊨ s₁ → x₂ ⊨ s₂ → v ⊨ sTuple2 s₁ s₂
    evObject      : ∀ {v kvs reqs} →
                    asObject v ≡ just kvs → AllFieldsEvidence kvs reqs → v ⊨ sObjectReq reqs

  data FieldEvidence (kvs : List (String × JSON)) (k : String) (s : Schema) : Set where
    fieldEv : (val : JSON) → lookupField k kvs ≡ just val → val ⊨ s → FieldEvidence kvs k s

  data AllFieldsEvidence (kvs : List (String × JSON)) : List (String × Schema) → Set where
    nilFields  : AllFieldsEvidence kvs []
    consFields : ∀ {k s reqs} →
                 FieldEvidence kvs k s → AllFieldsEvidence kvs reqs →
                 AllFieldsEvidence kvs ((k , s) ∷ reqs)

------------------------------------------------------------------------
-- Decision procedures
------------------------------------------------------------------------

private
  just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
  just≢nothing ()

decNumber : (v : JSON) → Dec (v ⊨ sNumber)
decNumber v with asNumber v in eq
... | just n  = yes (evNumber n eq)
... | nothing = no λ { (evNumber n eq′) → just≢nothing (trans (sym eq′) eq) }

decString : (v : JSON) → Dec (v ⊨ sString)
decString v with asString v in eq
... | just s  = yes (evString s eq)
... | nothing = no λ { (evString s eq′) → just≢nothing (trans (sym eq′) eq) }

decExactString : (expected : String) (v : JSON) → Dec (v ⊨ sExactString expected)
decExactString expected v with asString v in eq
... | nothing = no λ { (evExactString eq′) → just≢nothing (trans (sym eq′) eq) }
... | just s with s ≟ expected
...   | yes refl = yes (evExactString eq)
...   | no  ¬p   = no λ { (evExactString eq′) → ¬p (just-injective (trans (sym eq) eq′)) }

private
  tuple-injective : ∀ {a b c d : JSON} → _≡_ {A = List JSON} (a ∷ b ∷ []) (c ∷ d ∷ []) → a ≡ c × b ≡ d
  tuple-injective refl = refl , refl

decTuple2 : ∀ {s₁ s₂} → ((v : JSON) → Dec (v ⊨ s₁)) → ((v : JSON) → Dec (v ⊨ s₂)) →
            (v : JSON) → Dec (v ⊨ sTuple2 s₁ s₂)
decTuple2 {s₁} {s₂} check₁ check₂ v with asArray v in eq
... | nothing = no λ { (evTuple2 eq′ _ _) → just≢nothing (trans (sym eq′) eq) }
... | just [] = no λ { (evTuple2 eq′ _ _) → contradiction (just-injective (trans (sym eq) eq′)) (λ ()) }
... | just (_ ∷ []) = no λ { (evTuple2 eq′ _ _) → contradiction (just-injective (trans (sym eq) eq′)) (λ ()) }
... | just (_ ∷ _ ∷ _ ∷ _) = no λ { (evTuple2 eq′ _ _) → contradiction (just-injective (trans (sym eq) eq′)) (λ ()) }
... | just (x₁ ∷ x₂ ∷ []) with check₁ x₁ | check₂ x₂
...   | no ¬p₁ | _ = no λ { (evTuple2 eq′ p₁ _) →
          ¬p₁ (subst (_⊨ s₁) (proj₁ (tuple-injective (just-injective (trans (sym eq′) eq)))) p₁) }
...   | yes _ | no ¬p₂ = no λ { (evTuple2 eq′ _ p₂) →
          ¬p₂ (subst (_⊨ s₂) (proj₂ (tuple-injective (just-injective (trans (sym eq′) eq)))) p₂) }
...   | yes p₁ | yes p₂ = yes (evTuple2 eq p₁ p₂)

decField : ∀ {s} → ((v : JSON) → Dec (v ⊨ s)) → (k : String) (kvs : List (String × JSON)) →
           Dec (FieldEvidence kvs k s)
decField {s} check k kvs with lookupField k kvs in eq
... | nothing = no λ { (fieldEv _ eq′ _) → just≢nothing (trans (sym eq′) eq) }
... | just val with check val
...   | yes p = yes (fieldEv val eq p)
...   | no ¬p = no λ { (fieldEv val′ eq′ p′) →
          ¬p (subst (_⊨ s) (just-injective (trans (sym eq′) eq)) p′) }

decList : ∀ {elemS} → ((v : JSON) → Dec (v ⊨ elemS)) → (v : JSON) → Dec (v ⊨ sList elemS)
decList {elemS} check v with asArray v in eq
... | nothing = no λ { (evList eq′ _) → just≢nothing (trans (sym eq′) eq) }
... | just xs with All.all? check xs
...   | yes allP = yes (evList eq allP)
...   | no ¬all  = no λ { (evList eq′ allP′) →
          ¬all (subst (All (_⊨ elemS)) (just-injective (trans (sym eq′) eq)) allP′) }

------------------------------------------------------------------------
-- Decoding evidence
------------------------------------------------------------------------

-- The type of values a schema describes.
⟦_⟧ : Schema → Set
⟦ sAny ⟧                        = JSON
⟦ sNull ⟧                       = ⊤
⟦ sBool ⟧                       = Bool
⟦ sNumber ⟧                     = JSONNumber
⟦ sString ⟧                     = String
⟦ sExactString _ ⟧              = ⊤
⟦ sList s ⟧                     = List ⟦ s ⟧
⟦ sTuple2 s₁ s₂ ⟧               = ⟦ s₁ ⟧ × ⟦ s₂ ⟧
⟦ sObjectReq [] ⟧               = ⊤
⟦ sObjectReq ((k , s) ∷ reqs) ⟧ = ⟦ s ⟧ × ⟦ sObjectReq reqs ⟧

mutual
  decodeFromEvidence : ∀ {v s} → v ⊨ s → ⟦ s ⟧
  decodeFromEvidence (evAny {v})          = v
  decodeFromEvidence (evNull _)           = tt
  decodeFromEvidence (evBool b _)         = b
  decodeFromEvidence (evNumber n _)       = n
  decodeFromEvidence (evString s _)       = s
  decodeFromEvidence (evExactString _)    = tt
  decodeFromEvidence (evList _ allP)      = decodeList allP
  decodeFromEvidence (evTuple2 _ p₁ p₂)   = decodeFromEvidence p₁ , decodeFromEvidence p₂
  decodeFromEvidence (evObject _ flds)    = decodeFields flds

  decodeList : ∀ {elemS xs} → All (_⊨ elemS) xs → List ⟦ elemS ⟧
  decodeList []         = []
  decodeList (px ∷ pxs) = decodeFromEvidence px ∷ decodeList pxs

  decodeFields : ∀ {kvs reqs} → AllFieldsEvidence kvs reqs → ⟦ sObjectReq reqs ⟧
  decodeFields nilFields                         = tt
  decodeFields (consFields (fieldEv _ _ p) rest) = decodeFromEvidence p , decodeFields rest
