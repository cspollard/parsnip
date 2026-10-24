{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The XML AST as a free monad over a container
--
-- A document is `XMLC ⋆ ⊥` (`Data.Container.FreeMonad`).  Every node is an
-- element; its shape is the tag, the attributes, and the text around its
-- `n` children, and it has one child per position (`Fin n`).
--
-- * Text uses XML's mixed-content layout: an element with `n` children
--   carries `n + 1` text slots, `t₀ e₁ t₁ … eₙ tₙ`, where an empty slot
--   means "no text".  There are no text nodes, so adjacent text nodes
--   cannot be written down and every content has a unique representation.
-- * The shape also carries evidence (`Data.XML.Valid`) that names and
--   characters are legal XML and that attribute names are unique, so
--   ill-formed documents are unrepresentable.  The evidence is `T b`,
--   definitionally irrelevant; for literals Agda fills it in, otherwise
--   see `Data.XML.Sanitize` for total constructors.
-- * Payloads are `List Char`: the `String ↔ List Char` round trip is not
--   provable under `--safe` (see plans/JSONPlan.md).
-- * Attributes are an ordered list, kept in source order.
------------------------------------------------------------------------

module Data.XML.AST where

open import Level using (0ℓ; Level)
open import Data.Bool using (Bool; true; false; _∧_; T)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Function using (_∘_)
open import Data.Container using (Container; ⟦_⟧; _▷_)
open import Data.Container.FreeMonad as FM using (_⋆_)

open import Data.Container.List
open import Data.XML.Valid
open import Data.XML.Valid public using (Name; Text; Attribute; Attributes)

private variable
  a b : Level
  A : Set a
  B : Set b

-- put in module to avoid clashes
module XMLCont where

  ----------------------------------------------------------------------
  -- The signature of XML elements
  ----------------------------------------------------------------------

  record XMLShape : Set where
    constructor shape
    field
      tag        : Name
      attrs      : Attributes
      arity      : ℕ
      texts      : Vec Text (suc arity)
      validTag   : T (isValidName tag)
      validAttrs : T (isValidAttrs attrs)
      validTexts : T (isValidTexts texts)

  XMLC : Container 0ℓ 0ℓ
  XMLC = XMLShape ▷ (Fin ∘ XMLShape.arity)

  XMLM : Set a → Set a
  XMLM A = XMLC ⋆ A

  -- it's better to use XMLM ⊥ rather than ∀ {a} {A : Set a} → XMLM A
  -- they are isomorphic, but the latter has poor compilation properties
  XMLDoc : Set
  XMLDoc = XMLM ⊥

  ----------------------------------------------------------------------
  -- Folds
  ----------------------------------------------------------------------

  -- The content of an element: the text before the first child, then each
  -- child followed by the text after it.
  Content : Set b → Set b
  Content B = Text × List (B × Text)

  mixed : ∀ n → Vec Text (suc n) → (Fin n → B) → Content B
  mixed zero    (t ∷ [])  f = t , []
  mixed (suc n) (t ∷ ts) f =
    let m = mixed n ts (f ∘ suc) in t , (f zero , proj₁ m) ∷ proj₂ m

  -- The data of an element's content: its arity, text slots and children.
  NodeData : Set b → Set b
  NodeData B = Σ ℕ (λ n → Vec Text (suc n) × (Fin n → B))

  consNode : Text → B → NodeData B → NodeData B
  consNode t b (n , ts , f) = suc n , t ∷ ts , λ { zero → b; (suc i) → f i }

  -- The inverse of `mixed`.
  fromContent′ : Text → List (B × Text) → NodeData B
  fromContent′ t []             = zero , (t ∷ []) , λ ()
  fromContent′ t ((b , t′) ∷ cs) = consNode t b (fromContent′ t′ cs)

  fromContent : Content B → NodeData B
  fromContent (t , cs) = fromContent′ t cs

  foldXMLC : (Name → Attributes → Content B → B) → ⟦ XMLC ⟧ B → B
  foldXMLC alg (s , f) = alg tag attrs (mixed arity texts f)
    where open XMLShape s

  foldXMLM : (A → B) → (Name → Attributes → Content B → B) → XMLM A → B
  foldXMLM f alg = FM.foldr f (foldXMLC alg)

  ----------------------------------------------------------------------
  -- Constructors
  ----------------------------------------------------------------------

  -- An element given as its shape components: `n + 1` text slots and `n`
  -- children.
  node : (tag : Name) (attrs : Attributes) {n : ℕ}
         (texts : Vec Text (suc n)) (cs : Fin n → XMLM A)
         {pt : T (isValidName tag)} {pa : T (isValidAttrs attrs)}
         {px : T (isValidTexts texts)} → XMLM A
  node tag attrs texts cs {pt} {pa} {px} = FM.impure (shape tag attrs _ texts pt pa px , cs)

  private
    leafOK : ∀ {b} → T b → T (b ∧ true)
    leafOK {true} _ = tt

    replicate-valid : ∀ n → T (isValidTexts (replicate n []))
    replicate-valid zero    = tt
    replicate-valid (suc n) = replicate-valid n

  -- An element with only text.
  leaf : (tag : Name) (attrs : Attributes) (t : Text)
         {pt : T (isValidName tag)} {pa : T (isValidAttrs attrs)} {px : T (isValidText t)} → XMLM A
  leaf tag attrs t {pt} {pa} {px} = node tag attrs (t ∷ []) (λ ()) {pt} {pa} {leafOK px}

  -- An element with only element children.
  parent : (tag : Name) (attrs : Attributes) → ⟦ ListC ⟧ (XMLM A) →
           {pt : T (isValidName tag)} {pa : T (isValidAttrs attrs)} → XMLM A
  parent tag attrs (n , cs) {pt} {pa} = node tag attrs (replicate (suc n) []) cs {pt} {pa} {replicate-valid (suc n)}

  parentList : (tag : Name) (attrs : Attributes) → List (XMLM A) →
               {pt : T (isValidName tag)} {pa : T (isValidAttrs attrs)} → XMLM A
  parentList tag attrs cs {pt} {pa} = parent tag attrs (listToListC cs) {pt} {pa}

open XMLCont public using
  ( XMLShape; shape; XMLC; XMLM; XMLDoc; Content; mixed; NodeData; consNode; fromContent′; fromContent
  ; foldXMLC; foldXMLM; node; leaf; parent; parentList
  )
