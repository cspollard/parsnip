{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The tokenizer, and `lexer`: a stdlib RightInverse from valid token
-- streams to text
--
-- `tokenize` skips white space and lexes tokens one at a time with
-- `lexToken` (`Data.JSON.Token`).  `lexer` is a `RightInverse` out of
-- `ValidTokens`, the token streams with no two adjacent numbers (the
-- only streams whose printed form re-lexes to themselves).  Its `from`
-- is total by checking validity of the tokenizer's output, which is
-- decidable, and falling back to the empty stream.
------------------------------------------------------------------------

module Data.JSON.Lexer where

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Linked as Linked using (Linked; []; [-]; _∷_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z<s; s<s; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Data.List.Properties using (length-++)
open import Data.Nat.Properties using (≤-trans; m≤n+m; n<1+n)
open import Function.Bundles using (RightInverse)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; setoid)

open import Data.JSON.Number
  using (JSONNumber; jsonNumber; NoLeadingNumCont; printNat-head; printFraction; printExponent)
open import Data.Sign as Sign using ()
open import Data.JSON.Token
open import Data.Stage using (Chars; Subtype)
open import Data.Invertible.Char using (parseDigit; printDigit; parsePrintDigit)

------------------------------------------------------------------------
-- White space
------------------------------------------------------------------------

whitespace : List Char
whitespace = ' ' ∷ '\n' ∷ '\t' ∷ '\r' ∷ []

-- Drops leading white space; `skipWS′` takes the decision as an argument
-- so that proofs can rewrite exactly that call.
skipWS : List Char → List Char
skipWS′ : (c : Char) → List Char → Dec (c ∈ whitespace) → List Char

skipWS []       = []
skipWS (c ∷ cs) = skipWS′ c cs (c ∈? whitespace)

skipWS′ c cs (yes _) = skipWS cs
skipWS′ c cs (no  _) = c ∷ cs

NonWS : Char → Set
NonWS c = c ∈ whitespace → ⊥

skipWS-nonWS : ∀ c cs → NonWS c → skipWS (c ∷ cs) ≡ c ∷ cs
skipWS-nonWS c cs nw with c ∈? whitespace
... | yes p = ⊥-elim (nw p)
... | no  _ = refl

------------------------------------------------------------------------
-- The tokenizer
------------------------------------------------------------------------

tokenizeLoop : ℕ → List Char → Maybe (List JSONToken)
tokenizeStep : ℕ → List Char → Maybe (List JSONToken)
tokenizeCons : ℕ → Maybe (JSONToken × List Char) → Maybe (List JSONToken)

tokenizeLoop zero    _  = nothing
tokenizeLoop (suc f) cs = tokenizeStep f (skipWS cs)

tokenizeStep f []       = just []
tokenizeStep f (c ∷ cs) = tokenizeCons f (lexToken (c ∷ cs))

tokenizeCons f nothing           = nothing
tokenizeCons f (just (t , rest)) = Maybe.map (t ∷_) (tokenizeLoop f rest)

tokenize : List Char → Maybe (List JSONToken)
tokenize cs = tokenizeLoop (suc (length cs)) cs

------------------------------------------------------------------------
-- Valid token streams
------------------------------------------------------------------------

IsNumber : JSONToken → Set
IsNumber (numberT _) = ⊤
IsNumber _           = ⊥

-- Two adjacent number tokens would print as one number.
NotAdjacent : JSONToken → JSONToken → Set
NotAdjacent x y = IsNumber x → IsNumber y → ⊥

ValidTokenSeq : List JSONToken → Set
ValidTokenSeq = Linked NotAdjacent

isNumber? : ∀ t → Dec (IsNumber t)
isNumber? lbraceT     = no (λ ())
isNumber? lbracketT   = no (λ ())
isNumber? rbraceT     = no (λ ())
isNumber? rbracketT   = no (λ ())
isNumber? colonT      = no (λ ())
isNumber? commaT      = no (λ ())
isNumber? nullT       = no (λ ())
isNumber? (boolT _)   = no (λ ())
isNumber? (numberT _) = yes tt
isNumber? (stringT _) = no (λ ())

notAdjacent? : ∀ x y → Dec (NotAdjacent x y)
notAdjacent? x y with isNumber? x | isNumber? y
... | yes px | yes py = no (λ f → f px py)
... | yes px | no ¬py = yes (λ _ py → ¬py py)
... | no ¬px | _      = yes (λ px _ → ¬px px)

validTokenSeq? : ∀ ts → Dec (ValidTokenSeq ts)
validTokenSeq? = Linked.linked? notAdjacent?

-- Token streams with no two adjacent numbers (`Data.JSON.Goals.ValidTokens`).
ValidTokens : Setoid 0ℓ 0ℓ
ValidTokens = Subtype (setoid (List JSONToken)) ValidTokenSeq

------------------------------------------------------------------------
-- Facts about printed tokens
------------------------------------------------------------------------

private
  nonWS-literal : ∀ {c} → False (c ∈? whitespace) → NonWS c
  nonWS-literal f = toWitnessFalse f

  -- A digit is not white space (`parseDigit` rejects all four).
  nonWS-digit : ∀ c d → parseDigit c ≡ just d → NonWS c
  nonWS-digit .' '  d () (here refl)
  nonWS-digit .'\n' d () (there (here refl))
  nonWS-digit .'\t' d () (there (there (here refl)))
  nonWS-digit .'\r' d () (there (there (there (here refl))))

-- Every printed token starts with a character that is not white space.
printToken-cons : ∀ t → ∃ λ c → ∃ λ cs → printToken t ≡ c ∷ cs × NonWS c
printToken-cons lbraceT   = '{' , _ , refl , nonWS-literal tt
printToken-cons rbraceT   = '}' , _ , refl , nonWS-literal tt
printToken-cons lbracketT = '[' , _ , refl , nonWS-literal tt
printToken-cons rbracketT = ']' , _ , refl , nonWS-literal tt
printToken-cons colonT    = ':' , _ , refl , nonWS-literal tt
printToken-cons commaT    = ',' , _ , refl , nonWS-literal tt
printToken-cons nullT         = 'n' , _ , refl , nonWS-literal tt
printToken-cons (boolT true)  = 't' , _ , refl , nonWS-literal tt
printToken-cons (boolT false) = 'f' , _ , refl , nonWS-literal tt
printToken-cons (stringT s)   = '"' , _ , refl , nonWS-literal tt
printToken-cons (numberT (jsonNumber Sign.- i f e)) = '-' , _ , refl , nonWS-literal tt
printToken-cons (numberT (jsonNumber Sign.+ i f e)) with printNat-head i (printFraction f ++ printExponent e)
... | d , cs , eq = printDigit d , cs , eq , nonWS-digit (printDigit d) d (parsePrintDigit d)

-- After a non-number token, nothing continues a number.
follow-nonNumber : ∀ t rest → ¬ IsNumber t → NoLeadingNumCont (printToken t ++ rest)
follow-nonNumber lbraceT   rest _ = refl , tt , tt
follow-nonNumber rbraceT   rest _ = refl , tt , tt
follow-nonNumber lbracketT rest _ = refl , tt , tt
follow-nonNumber rbracketT rest _ = refl , tt , tt
follow-nonNumber colonT    rest _ = refl , tt , tt
follow-nonNumber commaT    rest _ = refl , tt , tt
follow-nonNumber nullT         rest _ = refl , tt , tt
follow-nonNumber (boolT true)  rest _ = refl , tt , tt
follow-nonNumber (boolT false) rest _ = refl , tt , tt
follow-nonNumber (stringT _)   rest _ = refl , tt , tt
follow-nonNumber (numberT _)   rest n = ⊥-elim (n tt)

-- In a valid stream, the text after a token may follow it.
tokenFollow : ∀ t ts → ValidTokenSeq (t ∷ ts) → TokenFollow t (printTokenList ts)
tokenFollow (numberT _) []        _ = tt , tt , tt
tokenFollow (numberT _) (t′ ∷ ts) v = follow-nonNumber t′ (printTokenList ts) (λ n → Linked.head v tt n)
tokenFollow lbraceT   ts _ = tt
tokenFollow rbraceT   ts _ = tt
tokenFollow lbracketT ts _ = tt
tokenFollow rbracketT ts _ = tt
tokenFollow colonT    ts _ = tt
tokenFollow commaT    ts _ = tt
tokenFollow nullT     ts _ = tt
tokenFollow (boolT _) ts _ = tt
tokenFollow (stringT _) ts _ = tt

------------------------------------------------------------------------
-- The tokenizer inverts the printer on valid streams
------------------------------------------------------------------------

private
  -- One iteration, given the shape of the input and the token it starts with.
  tokenize-step : ∀ f L c cs t rest → L ≡ c ∷ cs → NonWS c →
                  lexToken L ≡ just (t , rest) →
                  tokenizeLoop (suc f) L ≡ Maybe.map (t ∷_) (tokenizeLoop f rest)
  tokenize-step f .(c ∷ cs) c cs t rest refl nw lt =
    trans (cong (tokenizeStep f) (skipWS-nonWS c cs nw))
          (cong (tokenizeCons f) lt)

  -- The fuel left after one token still exceeds the length of the rest.
  fuel-rest : ∀ (x : List Char) (c : Char) (cs R : List Char) f → x ≡ c ∷ cs → length (x ++ R) < suc f → length R < f
  fuel-rest .(c ∷ cs) c cs R f refl (s≤s lt′) =
    ≤-trans (s≤s (subst (length R ≤_) (sym (length-++ cs)) (m≤n+m (length R) (length cs)))) lt′

tokenize-print : ∀ ts → ValidTokenSeq ts → ∀ fuel →
                 length (printTokenList ts) < fuel →
                 tokenizeLoop fuel (printTokenList ts) ≡ just ts
tokenize-print ts v zero ()
tokenize-print [] v (suc f) _ = refl
tokenize-print (t ∷ ts) v (suc f) lt with printToken-cons t
... | c , cs₀ , eq , nw =
  trans (tokenize-step f (printToken t ++ printTokenList ts) c (cs₀ ++ printTokenList ts) t
                       (printTokenList ts) (cong (_++ printTokenList ts) eq) nw
                       (lexToken-printToken t (printTokenList ts) (tokenFollow t ts v)))
        (cong (Maybe.map (t ∷_))
              (tokenize-print ts (Linked.tail v) f
                              (fuel-rest (printToken t) c cs₀ (printTokenList ts) f eq lt)))

tokenize-printTokenList : ∀ ts → ValidTokenSeq ts →
                          tokenize (printTokenList ts) ≡ just ts
tokenize-printTokenList ts v =
  tokenize-print ts v (suc (length (printTokenList ts))) (n<1+n (length (printTokenList ts)))

------------------------------------------------------------------------
-- `lexer`
------------------------------------------------------------------------

-- The tokens of a text, or the empty stream when the text does not lex
-- to a valid stream.
lexValid′ : ∀ ts → Dec (ValidTokenSeq ts) → Σ[ ts′ ∈ List JSONToken ] ValidTokenSeq ts′
lexValid′ ts (yes v) = ts , v
lexValid′ ts (no  _) = [] , []

lexValidMaybe : Maybe (List JSONToken) → Σ[ ts ∈ List JSONToken ] ValidTokenSeq ts
lexValidMaybe nothing   = [] , []
lexValidMaybe (just ts) = lexValid′ ts (validTokenSeq? ts)

lexValid : List Char → Σ[ ts ∈ List JSONToken ] ValidTokenSeq ts
lexValid cs = lexValidMaybe (tokenize cs)

private
  lexValid′-valid : ∀ ts (d : Dec (ValidTokenSeq ts)) → ValidTokenSeq ts →
                    proj₁ (lexValid′ ts d) ≡ ts
  lexValid′-valid ts (yes _) _ = refl
  lexValid′-valid ts (no ¬v) v = ⊥-elim (¬v v)

  lexValid-print : ∀ ts → ValidTokenSeq ts → proj₁ (lexValid (printTokenList ts)) ≡ ts
  lexValid-print ts v =
    trans (cong (λ m → proj₁ (lexValidMaybe m)) (tokenize-printTokenList ts v))
          (lexValid′-valid ts (validTokenSeq? ts) v)

-- `lexer` (see `Data.JSON.Goals`).
lexer : RightInverse ValidTokens Chars
lexer = record
  { to        = λ x → printTokenList (proj₁ x)
  ; from      = lexValid
  ; to-cong   = cong (λ x → printTokenList x)
  ; from-cong = λ { refl → refl }
  ; inverseʳ  = λ { {x} refl → lexValid-print (proj₁ x) (proj₂ x) }
  }
