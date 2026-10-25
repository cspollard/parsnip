{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- A generic tokenizer, and `lexer`: a stdlib RightInverse from valid
-- token streams to text
--
-- Every token-based format (XML, CSS, ...) has the same shape of lexer:
-- a function `lex` reading one token off the front of the text, a
-- printer `print` for one token, and a notion of *valid* token stream
-- (the streams whose printed form lexes back to themselves: tokens are
-- well formed, and no two adjacent tokens would run together).  Given
--
--   * `lex-print`:  lexing a printed token followed by the printed rest
--                   of a valid stream gives the token and that rest, and
--   * `print-cons`: a token of a valid stream prints to something
--                   non-empty (so the tokenizer's fuel decreases),
--
-- this module provides the fuel-bounded `tokenize`, its inverse theorem
-- `tokenize-printList`, and the stage `lexer`.
--
-- Formats where white space is insignificant give a `skip` that drops it
-- before each token (JSON); formats where it is a token, or significant
-- in the text, use the identity (XML, CSS), and `skip-print` is `refl`.
------------------------------------------------------------------------

module Data.Lexer where

open import Level using (0ℓ; Level)
open import Relation.Binary using (Setoid)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; concatMap)
open import Data.List.Properties using (length-++)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤?_; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≰⇒>; m≤n+m; n≤1+n; n<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ-syntax)
open import Data.String using (String; toList)
open import Function.Bundles using (RightInverse)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; setoid)

open import Data.Stage using (Chars; Subtype)

------------------------------------------------------------------------
-- The data of a token language
------------------------------------------------------------------------

record TokenLang : Set₁ where
  field
    Token      : Set
    print      : Token → List Char
    lex        : List Char → Maybe (Token × List Char)
    skip       : List Char → List Char
    skip-nil   : skip [] ≡ []
    -- the streams that print and lex back to themselves
    Valid      : List Token → Set
    valid?     : ∀ ts → Dec (Valid ts)
    valid-nil  : Valid []
    valid-tail : ∀ {t ts} → Valid (t ∷ ts) → Valid ts
    -- every token of a valid stream prints to something non-empty
    print-cons : ∀ {t ts} → Valid (t ∷ ts) → ∃ λ c → ∃ λ cs → print t ≡ c ∷ cs
    -- a printed token is not skipped
    skip-print : ∀ {t ts} → Valid (t ∷ ts) →
                 skip (print t ++ concatMap print ts) ≡ print t ++ concatMap print ts
    -- the prefix round trip, for a token with the rest of its stream after it
    lex-print  : ∀ {t ts} → Valid (t ∷ ts) →
                 lex (print t ++ concatMap print ts) ≡ just (t , concatMap print ts)

-- The fuel `tokenizeString` gives the loop: more tokens than any input
-- that fits in memory can hold.
maxTokens : ℕ
maxTokens = 1000000000000000000

module Lexing (L : TokenLang) where
  open TokenLang L

  printList : List Token → List Char
  printList = concatMap print

  ----------------------------------------------------------------------
  -- The tokenizer
  ----------------------------------------------------------------------

  -- The first argument is fuel: each token consumes at least one character.
  tokenizeLoop : ℕ → List Char → Maybe (List Token)
  tokenizeStep : ℕ → List Char → Maybe (List Token)
  tokenizeCons : ℕ → Maybe (Token × List Char) → Maybe (List Token)

  tokenizeLoop zero    _  = nothing
  tokenizeLoop (suc f) cs = tokenizeStep f (skip cs)

  tokenizeStep f []       = just []
  tokenizeStep f (c ∷ cs) = tokenizeCons f (lex (c ∷ cs))

  tokenizeCons f nothing           = nothing
  tokenizeCons f (just (t , rest)) = Maybe.map (t ∷_) (tokenizeLoop f rest)

  tokenize : List Char → Maybe (List Token)
  tokenize cs = tokenizeLoop (suc (length cs)) cs

  ----------------------------------------------------------------------
  -- The tokenizer inverts the printer on valid streams
  ----------------------------------------------------------------------

  private
    -- The fuel left after one token still exceeds the length of the rest.
    fuel-rest : ∀ (x : List Char) (c : Char) (cs R : List Char) f →
                x ≡ c ∷ cs → length (x ++ R) < suc f → length R < f
    fuel-rest .(c ∷ cs) c cs R f refl (s≤s lt′) =
      ≤-trans (s≤s (subst (length R ≤_) (sym (length-++ cs)) (m≤n+m (length R) (length cs)))) lt′

    step-eq : ∀ f (t : Token) (R L : List Char) c cs → L ≡ c ∷ cs → skip L ≡ L →
              lex L ≡ just (t , R) →
              tokenizeLoop (suc f) L ≡ Maybe.map (t ∷_) (tokenizeLoop f R)
    step-eq f t R .(c ∷ cs) c cs refl sk lt′ =
      trans (cong (tokenizeStep f) sk) (cong (tokenizeCons f) lt′)

  tokenize-print : ∀ ts → Valid ts → ∀ fuel →
                   length (printList ts) < fuel →
                   tokenizeLoop fuel (printList ts) ≡ just ts
  tokenize-print ts v zero ()
  tokenize-print [] v (suc f) _ = cong (tokenizeStep f) skip-nil
  tokenize-print (t ∷ ts) v (suc f) lt with print-cons v
  ... | c , cs₀ , eq =
    trans (step-eq f t (printList ts) (print t ++ printList ts) c (cs₀ ++ printList ts)
                   (cong (_++ printList ts) eq) (skip-print v) (lex-print v))
          (cong (Maybe.map (t ∷_))
                (tokenize-print ts (valid-tail v) f
                                (fuel-rest (print t) c cs₀ (printList ts) f eq lt)))

  tokenize-printList : ∀ ts → Valid ts → tokenize (printList ts) ≡ just ts
  tokenize-printList ts v =
    tokenize-print ts v (suc (length (printList ts))) (n<1+n (length (printList ts)))

  ----------------------------------------------------------------------
  -- Fuel
  --
  -- `tokenize` gives the loop one unit of fuel per input character (plus
  -- one), which forces the whole input list before lexing starts.  Given
  -- that skipping never lengthens the text and every token consumes
  -- input, any other fuel gives the same answer when it succeeds, so a
  -- caller that knows the length without building the list (a `String`'s)
  -- can let the input stream.
  ----------------------------------------------------------------------

  module Fuel
    (skip-≤   : ∀ cs → length (skip cs) ≤ length cs)
    (progress : ∀ cs t rest → lex cs ≡ just (t , rest) → length rest < length cs)
    where

    -- Fuel never matters once it exceeds the input length.
    tokenizeLoop-fuel : ∀ f g cs → length cs < f → length cs < g →
                        tokenizeLoop f cs ≡ tokenizeLoop g cs
    tokenizeLoop-fuel zero    g       cs ()
    tokenizeLoop-fuel (suc f) zero    cs _ ()
    tokenizeLoop-fuel (suc f) (suc g) cs (s≤s lf) (s≤s lg) = step (skip cs) (skip-≤ cs)
      where
      step : ∀ w → length w ≤ length cs → tokenizeStep f w ≡ tokenizeStep g w
      step []       _ = refl
      step (c ∷ w′) w≤ with lex (c ∷ w′) in eq
      ... | nothing         = refl
      ... | just (t , rest) =
        cong (Maybe.map (t ∷_))
             (tokenizeLoop-fuel f g rest
                (≤-trans (progress (c ∷ w′) t rest eq) (≤-trans w≤ lf))
                (≤-trans (progress (c ∷ w′) t rest eq) (≤-trans w≤ lg)))

    -- More fuel keeps a successful result.
    tokenizeLoop-mono : ∀ g h cs ts → g ≤ h →
                        tokenizeLoop g cs ≡ just ts → tokenizeLoop h cs ≡ just ts
    tokenizeLoop-mono zero    h       cs ts _       ()
    tokenizeLoop-mono (suc g) zero    cs ts ()
    tokenizeLoop-mono (suc g) (suc h) cs ts (s≤s g≤h) eq = step (skip cs) eq
      where
      step : ∀ w → tokenizeStep g w ≡ just ts → tokenizeStep h w ≡ just ts
      step []       e = e
      step (c ∷ w′) e with lex (c ∷ w′)
      ... | nothing         = e
      ... | just (t , rest) with tokenizeLoop g rest in eq′
      step (c ∷ w′) () | just (t , rest) | nothing
      step (c ∷ w′) refl | just (t , rest) | just ts′ =
        cong (Maybe.map (t ∷_)) (tokenizeLoop-mono g h rest ts′ g≤h eq′)

    -- Whatever fuel produced a token stream, `tokenize` produces it too.
    tokenizeLoop-sound : ∀ g cs ts → tokenizeLoop g cs ≡ just ts → tokenize cs ≡ just ts
    tokenizeLoop-sound g cs ts eq with suc (length cs) ≤? g
    ... | yes le = trans (tokenizeLoop-fuel (suc (length cs)) g cs (s≤s ≤-refl) le) eq
    ... | no ¬le = tokenizeLoop-mono g (suc (length cs)) cs ts (≤-trans (n≤1+n g) (≰⇒> ¬le)) eq

    -- Tokenizing with a fixed fuel, so that the input list streams as it
    -- is produced (by `toList`, say) instead of being measured first.  It
    -- agrees with `tokenize` whenever it succeeds.
    tokenizeFast : List Char → Maybe (List Token)
    tokenizeFast = tokenizeLoop maxTokens

    tokenizeFast-sound : ∀ cs ts → tokenizeFast cs ≡ just ts → tokenize cs ≡ just ts
    tokenizeFast-sound cs = tokenizeLoop-sound maxTokens cs

    tokenizeString : String → Maybe (List Token)
    tokenizeString s = tokenizeFast (toList s)

    tokenizeString-sound : ∀ s ts → tokenizeString s ≡ just ts → tokenize (toList s) ≡ just ts
    tokenizeString-sound s = tokenizeFast-sound (toList s)

  ----------------------------------------------------------------------
  -- `lexer`
  ----------------------------------------------------------------------

  -- Valid token streams, as a setoid.
  ValidTokens : Setoid 0ℓ 0ℓ
  ValidTokens = Subtype (setoid (List Token)) Valid

  -- The tokens of a text, or the empty stream when the text does not lex
  -- to a valid stream.
  lexValid′ : ∀ ts → Dec (Valid ts) → Σ[ ts′ ∈ List Token ] Valid ts′
  lexValid′ ts (yes v) = ts , v
  lexValid′ ts (no  _) = [] , valid-nil

  lexValidMaybe : Maybe (List Token) → Σ[ ts ∈ List Token ] Valid ts
  lexValidMaybe nothing   = [] , valid-nil
  lexValidMaybe (just ts) = lexValid′ ts (valid? ts)

  lexValid : List Char → Σ[ ts ∈ List Token ] Valid ts
  lexValid cs = lexValidMaybe (tokenize cs)

  private
    lexValid′-valid : ∀ ts (d : Dec (Valid ts)) → Valid ts → proj₁ (lexValid′ ts d) ≡ ts
    lexValid′-valid ts (yes _) _ = refl
    lexValid′-valid ts (no ¬v) v = ⊥-elim (¬v v)

    lexValid-print : ∀ ts → Valid ts → proj₁ (lexValid (printList ts)) ≡ ts
    lexValid-print ts v =
      trans (cong (λ m → proj₁ (lexValidMaybe m)) (tokenize-printList ts v))
            (lexValid′-valid ts (valid? ts) v)

  lexer : RightInverse ValidTokens Chars
  lexer = record
    { to        = λ x → printList (proj₁ x)
    ; from      = lexValid
    ; to-cong   = cong (λ x → printList x)
    ; from-cong = λ { refl → refl }
    ; inverseʳ  = λ { {x} refl → lexValid-print (proj₁ x) (proj₂ x) }
    }
