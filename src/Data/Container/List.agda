{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Lists as a container
--
-- `ListC = ℕ ▷ Pos`: a list is its length together with one element per
-- position (`Data.Container.Pos`).  Shared by the JSON and XML ASTs,
-- where it describes the children of an array / element.
--
-- Both directions are linear (up to a `log` for random access):
-- `listToListC` backs the positions by a balanced tree
-- (`Data.Container.Table`) and `listCToList` reads the positions in
-- order (`tabulate`).  `tabulate-suc` is the equation the proofs unfold.
------------------------------------------------------------------------

module Data.Container.List where

open import Level using (Level; 0ℓ)
open import Data.Bool using (Bool; true; false; T)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.List using (List; []; _∷_; length; map; foldr)
open import Data.List.Properties using (map-cong)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Binary.Pointwise using (Pointwise; Pointwise-length; []; _∷_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Data.Container using (Container; ⟦_⟧; _▷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Data.Container.Pos public
open import Data.Container.Table public using (table; table-nth; nth)

private variable
  a b : Level
  A : Set a
  B : Set b

ListC : Container 0ℓ 0ℓ
ListC = ℕ ▷ Pos

------------------------------------------------------------------------
-- Reading positions in order
------------------------------------------------------------------------

-- The elements at the positions `k, k+1, …` below `n`, at most `fuel` of
-- them.  (The decision `k <ᵇ n` is an argument of `tabStep` so that proofs
-- can abstract it.)
tabulate′ : ∀ n → (Pos n → A) → ℕ → ℕ → List A
tabStep   : ∀ n → (Pos n → A) → ℕ → (k : ℕ) → (b : Bool) → (k <ᵇ n) ≡ b → List A

tabulate′ n f zero       k = []
tabulate′ n f (suc fuel) k = tabStep n f fuel k (k <ᵇ n) refl

tabStep n f fuel k true  eq = f (mkPos k (subst T (sym eq) tt)) ∷ tabulate′ n f fuel (suc k)
tabStep n f fuel k false eq = []

tabulate : ∀ n → (Pos n → A) → List A
tabulate n f = tabulate′ n f n zero

-- Starting one position later is reading the shifted function.
tabulate′-shift : ∀ n (f : Pos (suc n) → A) fuel k →
                  tabulate′ (suc n) f fuel (suc k) ≡ tabulate′ n (f ∘ sucP) fuel k
tabStep-shift   : ∀ n (f : Pos (suc n) → A) fuel k b (eq : (k <ᵇ n) ≡ b) →
                  tabStep (suc n) f fuel (suc k) b eq ≡ tabStep n (f ∘ sucP) fuel k b eq

tabulate′-shift n f zero       k = refl
tabulate′-shift n f (suc fuel) k = tabStep-shift n f fuel k (k <ᵇ n) refl

tabStep-shift n f fuel k true  eq = cong (_ ∷_) (tabulate′-shift n f fuel (suc k))
tabStep-shift n f fuel k false eq = refl

tabulate-zero : ∀ (f : Pos zero → A) → tabulate zero f ≡ []
tabulate-zero f = refl

tabulate-suc : ∀ n (f : Pos (suc n) → A) → tabulate (suc n) f ≡ f zeroP ∷ tabulate n (f ∘ sucP)
tabulate-suc n f = cong (f zeroP ∷_) (tabulate′-shift n f n zero)

tabulate-cong : ∀ n (f g : Pos n → A) → (∀ p → f p ≡ g p) → tabulate n f ≡ tabulate n g
tabulate-cong zero    f g h = refl
tabulate-cong (suc n) f g h =
  trans (tabulate-suc n f)
    (trans (cong₂ _∷_ (h zeroP) (tabulate-cong n (f ∘ sucP) (g ∘ sucP) (h ∘ sucP)))
           (sym (tabulate-suc n g)))

tabulate-map : ∀ n (f : Pos n → A) (g : A → B) → tabulate n (g ∘ f) ≡ map g (tabulate n f)
tabulate-map zero    f g = refl
tabulate-map (suc n) f g =
  trans (tabulate-suc n (g ∘ f))
    (trans (cong (g (f zeroP) ∷_) (tabulate-map n (f ∘ sucP) g))
           (cong (map g) (sym (tabulate-suc n f))))

length-tabulate : ∀ n (f : Pos n → A) → length (tabulate n f) ≡ n
length-tabulate zero    f = refl
length-tabulate (suc n) f =
  trans (cong length (tabulate-suc n f)) (cong suc (length-tabulate n (f ∘ sucP)))

------------------------------------------------------------------------
-- Lists and `ListC`
------------------------------------------------------------------------

listCToList : ⟦ ListC ⟧ A → List A
listCToList (n , f) = tabulate n f

listToListC : List A → ⟦ ListC ⟧ A
listToListC xs = length xs , table xs

foldListC : (A → B → B) → B → ⟦ ListC ⟧ A → B
foldListC f b = foldr f b ∘ listCToList

tabulate-table : ∀ (xs : List A) → tabulate (length xs) (table xs) ≡ xs
tabulate-table []       = refl
tabulate-table (x ∷ xs) =
  trans (tabulate-suc (length xs) (table (x ∷ xs)))
    (cong₂ _∷_ (table-nth (x ∷ xs) zeroP)
      (trans (tabulate-cong (length xs) _ (table xs) (λ p → trans (table-nth (x ∷ xs) (sucP p)) (sym (table-nth xs p))))
             (tabulate-table xs)))

------------------------------------------------------------------------
-- Rebuilding a node from related children
------------------------------------------------------------------------

-- If `xs` is pointwise related to the children `tabulate n f`, then each
-- element of the table of `xs` is related to the child at its position.
pointwise-nth : ∀ {R : A → B → Set} (xs : List A) n (f : Pos n → B) (e : length xs ≡ n) →
                Pointwise R xs (tabulate n f) → ∀ i → R (nth xs i) (f (castP e i))
pointwise-nth []       n                f e    pw i = noPos i
pointwise-nth (x ∷ xs) .(suc (length xs)) f refl pw i
  with subst (Pointwise _ (x ∷ xs)) (tabulate-suc (length xs) f) pw
... | rx ∷ rest with view i
...   | isZero  = rx
...   | isSuc q = pointwise-nth xs (length xs) (f ∘ sucP) refl rest q

pointwise-table : ∀ {R : A → B → Set} (xs : List A) n (f : Pos n → B) →
                  Pointwise R xs (tabulate n f) →
                  Σ[ e ∈ length xs ≡ n ] ∀ i → R (table xs i) (f (castP e i))
pointwise-table {R = R} xs n f pw = e , λ i → subst (λ a → R a (f (castP e i))) (sym (table-nth xs i)) (pointwise-nth xs n f e pw i)
  where
  e : length xs ≡ n
  e = trans (Pointwise-length pw) (length-tabulate n f)

-- A property of every child is a property of the list of children.
all-tabulate : ∀ {P : A → Set} n (g : Pos n → A) → (∀ i → P (g i)) → All P (tabulate n g)
all-tabulate zero    g p = All.[]
all-tabulate (suc n) g p =
  subst (All _) (sym (tabulate-suc n g)) (p zeroP All.∷ all-tabulate n (g ∘ sucP) (p ∘ sucP))
