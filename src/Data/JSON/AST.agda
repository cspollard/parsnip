{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The JSON AST as a free monad over a container
--
-- A JSON value is `JSONC ⋆ ⊥` (`Data.Container.FreeMonad`): a node has a
-- shape (its type, plus the payload of a leaf or the length of an array,
-- or the keys of an object) and one child per position.
--
-- * Arrays are `ListC = ℕ ▷ Fin` (`Data.Container.List`).
-- * Objects are `ObjectC = List (List Char) ▷ (Fin ∘ length)`: keys in order,
--   one child per key.  RFC 8259 §4 only says that names SHOULD be
--   unique, so duplicate keys are representable (and round-trip).
-- * String payloads are `List Char`: the `String ↔ List Char` round trip
--   is not provable under `--safe` (see plans/JSONPlan.md).  `stringⱼ` accepts
--   a `String` for convenience.
------------------------------------------------------------------------

module Data.JSON.AST where

open import Level using (0ℓ; Level)
open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String; toList)
open import Data.List using (List; []; _∷_; length)
import Data.List as L
open import Data.Product using (_×_; _,_; proj₁; proj₂; map₁)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Function using (_∘_)
open import Data.Container hiding (refl)
import Data.Container.Combinator as CC
open import Data.Container.FreeMonad as FM
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.JSON.Number using (JSONNumber; jsonNumber) public

private variable
  a b : Level
  A : Set a
  B : Set b

-- put in module to avoid clashes
module JSONCont where

  ----------------------------------------------------------------------
  -- Arrays and objects as containers
  ----------------------------------------------------------------------

  open import Data.Container.List public

  -- Keys are `List Char`, like string payloads.
  Key : Set
  Key = List Char

  ObjectC : Container 0ℓ 0ℓ
  ObjectC = List Key ▷ (Fin ∘ length)

  -- The keyed children, in key order.
  objectCToEntries : ⟦ ObjectC ⟧ A → List (Key × A)
  objectCToEntries (ks , f) = go ks f
    where
    go : ∀ ks → (Fin (length ks) → _) → List (Key × _)
    go []       _ = []
    go (k ∷ ks) f = (k , f zero) ∷ go ks (f ∘ suc)

  entriesToObjectC : List (Key × A) → ⟦ ObjectC ⟧ A
  entriesToObjectC = L.foldr add ([] , λ ())
    where
    add : _ → ⟦ ObjectC ⟧ _ → ⟦ ObjectC ⟧ _
    add (k , x) p = k ∷ proj₁ p , λ { zero → x; (suc i) → proj₂ p i }

  ----------------------------------------------------------------------
  -- The signature of JSON values
  ----------------------------------------------------------------------

  data PrimJSONType : Set where
    primstring primnumber primbool primnull : PrimJSONType

  data JSONType : Set where
    object array : JSONType
    prim : PrimJSONType → JSONType

  pattern pstring = prim primstring
  pattern pnumber = prim primnumber
  pattern pbool = prim primbool
  pattern pnull = prim primnull

  RetType : (t : PrimJSONType) → Set
  RetType primstring = List Char
  RetType primnumber = JSONNumber
  RetType primbool = Bool
  RetType primnull = ⊤

  JSON→ : JSONType → Container 0ℓ 0ℓ
  JSON→ object = ObjectC
  JSON→ array = ListC
  JSON→ (prim t) = CC.const (RetType t)

  JSONC : Container 0ℓ 0ℓ
  JSONC = CC.Σ _ JSON→

  foldJSONC : (∀ t → ⟦ JSON→ t ⟧ A → B) → ⟦ JSONC ⟧ A → B
  foldJSONC f (shp , pos) = f (shp .proj₁) (shp .proj₂ , pos)

  injC : ∀ t → RetType t → ∀ {A : Set a} → ⟦ JSONC ⟧ A
  injC primstring x = (pstring , x) , λ ()
  injC primnumber x = (pnumber , x) , λ ()
  injC primbool x = (pbool , x) , λ ()
  injC primnull _ = (pnull , _) , λ ()

  JSONM : Set a → Set a
  JSONM A = JSONC ⋆ A

  -- it's better to use JSONM ⊥ rather than ∀ {a} {A : Set a} → JSONM A
  -- they are isomorphic, but the latter has poor compilation properties
  JSON : Set
  JSON = JSONM ⊥

  foldJSONM : (A → B) → (∀ t → ⟦ JSON→ t ⟧ B → B) → JSONM A → B
  foldJSONM f g = foldr f (foldJSONC g)

  lift : (t : JSONType) → (xs : ⟦ JSON→ t ⟧ (JSONM A)) → JSONM A
  lift t (fst , snd) = impure ((t , fst) , snd)

  json↑ : (t : JSONType) → (xs : ⟦ JSON→ t ⟧ A) → JSONM A
  json↑ t (s , go) = impure ((t , s) , pure ∘ go)

  jsoninj : (t : PrimJSONType) → RetType t → JSON
  jsoninj t x = json↑ (prim t) (x , λ ())

  nullⱼ : JSON
  nullⱼ = jsoninj primnull _

  boolⱼ : Bool → JSON
  boolⱼ = jsoninj primbool

  trueⱼ falseⱼ : JSON
  trueⱼ = boolⱼ true
  falseⱼ = boolⱼ false

  -- A string given as its characters.
  stringⱼ′ : List Char → JSON
  stringⱼ′ = jsoninj primstring

  stringⱼ : String → JSON
  stringⱼ = stringⱼ′ ∘ toList

  numberⱼ : JSONNumber → JSON
  numberⱼ = jsoninj primnumber

  arrayⱼ : List (JSONM A) → JSONM A
  arrayⱼ = lift array ∘ listToListC

  objectⱼ : ⟦ ObjectC ⟧ (JSONM A) → JSONM A
  objectⱼ = lift object

  -- An object given as its keyed children, with keys as characters.
  objectFromList′ : List (List Char × JSONM A) → JSONM A
  objectFromList′ = objectⱼ ∘ entriesToObjectC

  objectFromList : List (String × JSONM A) → JSONM A
  objectFromList = objectFromList′ ∘ L.map (map₁ toList)

open JSONCont public using
  ( JSONM; JSON; nullⱼ; boolⱼ; trueⱼ; falseⱼ; stringⱼ; stringⱼ′; numberⱼ; arrayⱼ; objectⱼ
  ; objectFromList; objectFromList′
  )
