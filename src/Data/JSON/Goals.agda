{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- JSON round-trip goals (temporary; see JSONPlan.md, Phase 1)
--
-- The top-level contract of the JSON pipeline, with every implementation
-- left as a hole.  Each hole is a work item; once filled, the definition
-- moves to its home module and this file shrinks.  Deleted in Phase 9.
--
-- Every stage is a stdlib `Function.Bundles.RightInverse`:
--
--   RightInverse A B   has   to : A → B     (our `print`)
--                            from : B → A   (our `parse`, total, with a
--                                            default witness on failure)
--                            inverseʳ :  from (to x) ≈ x
--
-- so stages compose with `Function.Construct.Composition.rightInverse`,
-- products with `Data.Product.Function.NonDependent.Setoid._×-rightInverse_`
-- (dependent: `Data.Product.Function.Dependent.Setoid.rightInverse`), and no
-- hand-written "tokenize (print ts) ≡ …" statements are needed.
------------------------------------------------------------------------

module Data.JSON.Goals where

open import Level using (0ℓ)
open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Unit using (⊤)
open import Function.Bundles using (RightInverse)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality using (setoid)

open import Data.JSON.AST using (JSON; JSONNumber)

------------------------------------------------------------------------
-- Setoids (stubs; real definitions arrive with the phase noted)
------------------------------------------------------------------------

-- Phase 5: bisimilarity on the free monad, built on stdlib `Pointwise`
-- (`Data.Container.Relation.Binary.Pointwise`), and its setoid.
_≈ⱼ_ : Rel JSON 0ℓ
_≈ⱼ_ = ?

JSONSetoid : Setoid 0ℓ 0ℓ
JSONSetoid = ?

-- Phase 4/6: lexical tokens.
data JSONToken : Set where

-- Phase 4: `null`, `true`, `false`.
data Keyword : Set where

-- Phase 3: what may not follow a number (digit, `.`, `e`, `E`).
NoLeadingNumCont : List Char → Set
NoLeadingNumCont = ?

-- Phase 4: what may follow a token.
TokenFollow : JSONToken → List Char → Set
TokenFollow = ?

-- Phase 6: no two adjacent number tokens.
ValidTokenSeq : List JSONToken → Set
ValidTokenSeq = ?

-- Phase 6: token streams satisfying `ValidTokenSeq`, as a setoid
-- (a subtype of `setoid (List JSONToken)`).
ValidTokens : Setoid 0ℓ 0ℓ
ValidTokens = ?

Chars : Setoid 0ℓ 0ℓ
Chars = setoid (List Char)

-- Phase 2: a value together with a continuation allowed to follow it,
-- i.e. `Σ[ (y , rest) ∈ Y × List I ] Follow y rest`, compared pointwise.
PrefixSetoid : ∀ {I : Set} (S : Setoid 0ℓ 0ℓ) →
               (Setoid.Carrier S → List I → Set) → Setoid 0ℓ 0ℓ
PrefixSetoid = ?

------------------------------------------------------------------------
-- Stage types
------------------------------------------------------------------------

-- A prefix stage over symbols `I`: `to (y , rest) = print y ++ rest` and
-- `from` is the prefix parser returning `(value , remaining input)`.
-- `inverseʳ` is the round-trip law (analogue of a partial isomorphism in
-- Rendel & Ostermann, with an explicit follow-condition).
Prefix : ∀ {I : Set} (S : Setoid 0ℓ 0ℓ) →
         (Setoid.Carrier S → List I → Set) → Set
Prefix {I} S Follow = RightInverse (PrefixSetoid S Follow) (setoid (List I))

------------------------------------------------------------------------
-- Lexical stages (Chars → tokens)
------------------------------------------------------------------------

numberStage : Prefix {Char} (setoid JSONNumber) (λ _ rest → NoLeadingNumCont rest)
numberStage = ?

stringStage : Prefix {Char} (setoid (List Char)) (λ _ _ → ⊤)
stringStage = ?

keywordStage : Prefix {Char} (setoid Keyword) (λ _ _ → ⊤)
keywordStage = ?

tokenStage : Prefix {Char} (setoid JSONToken) TokenFollow
tokenStage = ?

-- Whole input: `to` concatenates the printed tokens; `from` is the tokenizer.
lexer : RightInverse ValidTokens Chars
lexer = ?

------------------------------------------------------------------------
-- Syntactic stage (tokens → JSON)
------------------------------------------------------------------------

-- `to` is the token printer; that its output satisfies `ValidTokenSeq`
-- (no two adjacent number tokens) is part of its type, so there is no
-- separate compatibility lemma.  `to-cong` is "printing respects `_≈ⱼ_`".
parser : RightInverse JSONSetoid ValidTokens
parser = ?

------------------------------------------------------------------------
-- The whole pipeline
------------------------------------------------------------------------

open import Function.Construct.Composition using ()
  renaming (rightInverse to _∘-rightInverse_)

-- Headline theorem: `parseJSON (printJSON v) ≈ⱼ v`, lexing included.
jsonStage : RightInverse JSONSetoid Chars
jsonStage = ?
-- target: jsonStage = parser ∘-rightInverse lexer   (stdlib composition)
