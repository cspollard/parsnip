{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

module Data.JSON.AST where

open import Level using (0ℓ; Level) renaming (suc to lsuc)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ)
open import Data.Sign using (Sign; +; -)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; length; lookup)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin; zero; suc)
open import Function using (_∘_)
open import Data.Container hiding (refl)
import Data.Container.Combinator as CC
open import Data.Container.FreeMonad as FM
open import Relation.Binary.PropositionalEquality
open import Data.Float
open import Relation.Binary
open import Relation.Nullary
open import Data.JSON.ObjectC
open import Data.JSON.Number using (JSONNumber; jsonNumber) public
open import Data.String.Properties using () renaming (≡-decSetoid to stringDecSetoid)
open import Data.Sum
open import Data.Empty
open import Function using (flip)

private variable
  a b : Level
  A : Set a
  B : Set b

------------------------------------------------------------------------
-- The Inductive JSON AST Type
------------------------------------------------------------------------

-- put in module to avoid clashes
module JSONCont where

  ListC : Container 0ℓ 0ℓ
  ListC = ℕ ▷ Fin

  foldListC : (A → B → B) → B → ⟦ ListC ⟧ A → B
  foldListC f b (n , lookup) = go n lookup
    where
    go : ∀ n → (Fin n → _) → _
    go zero _ = b
    go (suc k) pos = f (pos zero) (go k (pos ∘ suc))

  module SO = Data.JSON.ObjectC stringDecSetoid
  StringObjectC : Container 0ℓ 0ℓ
  StringObjectC = SO.ObjectC

  listCToList : ⟦ ListC ⟧ A → List A
  listCToList = foldListC _∷_ []

  listToListC : List A → ⟦ ListC ⟧ A
  listToListC = L.foldr add (zero , λ ())
    where
      import Data.List as L
      add : A → ⟦ ListC ⟧ A → ⟦ ListC ⟧ A
      add x (fst , snd) = suc fst , λ { zero → x; (suc i) → snd i }

  data PrimJSONType : Set where
    primstring primnumber primbool primnull : PrimJSONType

  data JSONType : Set where
    object array : JSONType
    prim : PrimJSONType → JSONType

  prim-injective : ∀ {t t'} → prim t ≡ prim t' → t ≡ t'
  prim-injective refl = refl

  pattern pstring = prim primstring
  pattern pnumber = prim primnumber
  pattern pbool = prim primbool
  pattern pnull = prim primnull

  RetType : (t : PrimJSONType) → Set
  RetType primstring = String
  RetType primnumber = JSONNumber
  RetType primbool = Bool
  RetType primnull = ⊤

  PrimJSONType≟ : DecidableEquality PrimJSONType
  PrimJSONType≟ primstring primstring = yes refl
  PrimJSONType≟ primnumber primnumber = yes refl
  PrimJSONType≟ primbool primbool = yes refl
  PrimJSONType≟ primnull primnull = yes refl
  PrimJSONType≟ primstring primnumber = no λ ()
  PrimJSONType≟ primstring primbool = no λ ()
  PrimJSONType≟ primstring primnull = no λ ()
  PrimJSONType≟ primnumber primstring = no λ ()
  PrimJSONType≟ primnumber primbool = no λ ()
  PrimJSONType≟ primnumber primnull = no λ ()
  PrimJSONType≟ primbool primstring = no λ ()
  PrimJSONType≟ primbool primnumber = no λ ()
  PrimJSONType≟ primbool primnull = no λ ()
  PrimJSONType≟ primnull primstring = no λ ()
  PrimJSONType≟ primnull primnumber = no λ ()
  PrimJSONType≟ primnull primbool = no λ ()

  JSONType≟ : DecidableEquality JSONType
  JSONType≟ object object = yes refl
  JSONType≟ array array = yes refl
  JSONType≟ object array = no λ ()
  JSONType≟ array object = no λ ()
  JSONType≟ object (prim _) = no λ ()
  JSONType≟ array (prim _) = no λ ()
  JSONType≟ (prim _) object = no λ ()
  JSONType≟ (prim _) array = no λ ()
  JSONType≟ (prim t) (prim t') with PrimJSONType≟ t t'
  ... | yes p = yes (cong prim p)
  ... | no ¬p = no λ p → ¬p (prim-injective p)

  JSON→ : JSONType → Container 0ℓ 0ℓ
  JSON→ object = StringObjectC
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

  stringⱼ : String → JSON
  stringⱼ = jsoninj primstring

  numberⱼ : JSONNumber → JSON
  numberⱼ = jsoninj primnumber

  arrayⱼ : List (JSONM A) → JSONM A
  arrayⱼ = lift array ∘ listToListC

  objectⱼ : ⟦ StringObjectC ⟧ (JSONM A) → JSONM A
  objectⱼ = lift object

  objectFromList : List (String × JSONM A) → JSONM A
  objectFromList = objectⱼ ∘ SO.toObjectC

open JSONCont public using
  ( JSONM; JSON; nullⱼ; boolⱼ; trueⱼ; falseⱼ; stringⱼ; numberⱼ; arrayⱼ; objectⱼ
  ; objectFromList
  )
