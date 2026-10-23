{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- JSON string literals (RFC 8259 §7): escaping and lexing
--
-- Strings are `List Char` (a `String` round trip is not provable under
-- `--safe`).  Escapes are table driven: `escapes` pairs each character
-- that must be escaped with the letter after the backslash.
--
-- `stringStage` is a stdlib `RightInverse` between string contents and
-- the quoted literal; `lexBody-printBody` is the prefix round trip it
-- is built from (any continuation may follow the closing quote).
------------------------------------------------------------------------

module Data.JSON.String where

open import Data.Bool using (true; false)
open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; map₁; swap)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function.Bundles using (RightInverse)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; setoid)

open import Data.JSON.Stage using (Chars; mkStage)

------------------------------------------------------------------------
-- The escape table
------------------------------------------------------------------------

-- (character , letter after the backslash)
escapes : List (Char × Char)
escapes =
  ('"' , '"') ∷ ('\\' , '\\') ∷ ('\n' , 'n') ∷ ('\r' , 'r') ∷
  ('\t' , 't') ∷ ('\b' , 'b') ∷ ('\f' , 'f') ∷ []

-- Letters accepted when reading: the table, and also `\/`.
unescapes : List (Char × Char)
unescapes = Data.List.map swap escapes ++ ('/' , '/') ∷ []
  where import Data.List

lookupBy : List (Char × Char) → Char → Maybe Char
lookupBy []              c = nothing
lookupBy ((k , v) ∷ tbl) c with c ≟ k
... | yes _ = just v
... | no  _ = lookupBy tbl c

------------------------------------------------------------------------
-- Printing
------------------------------------------------------------------------

escapeChar : Char → List Char
escapeChar c with lookupBy escapes c
... | just l  = '\\' ∷ l ∷ []
... | nothing = c ∷ []

printBody : List Char → List Char
printBody = concatMap escapeChar

printStringLiteral : List Char → List Char
printStringLiteral cs = '"' ∷ printBody cs ++ '"' ∷ []

------------------------------------------------------------------------
-- Lexing
------------------------------------------------------------------------

-- The characters of a string body up to the closing quote, and the rest.
lexBody : List Char → Maybe (List Char × List Char)
lexBody []       = nothing
lexBody (c ∷ cs) with c ≟ '"' | c ≟ '\\'
lexBody (c ∷ cs)     | yes _ | _     = just ([] , cs)
lexBody (c ∷ cs)     | no  _ | no  _ = Maybe.map (map₁ (c ∷_)) (lexBody cs)
lexBody (c ∷ [])     | no  _ | yes _ = nothing
lexBody (c ∷ d ∷ cs) | no  _ | yes _ with lookupBy unescapes d
... | nothing = nothing
... | just x  = Maybe.map (map₁ (x ∷_)) (lexBody cs)

-- A complete literal (the closing quote ends it; the rest is ignored).
lexStringLiteral : List Char → Maybe (List Char × List Char)
lexStringLiteral ('"' ∷ cs) = lexBody cs
lexStringLiteral _          = nothing

------------------------------------------------------------------------
-- Round trip
------------------------------------------------------------------------

private
  -- Every table entry is read back.
  table-inverse : All (λ p → lookupBy unescapes (proj₂ p) ≡ just (proj₁ p)) escapes
  table-inverse = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []

  lookupBy-∈ : ∀ tbl c l → lookupBy tbl c ≡ just l → (c , l) ∈ tbl
  lookupBy-∈ []              c l ()
  lookupBy-∈ ((k , v) ∷ tbl) c l eq with c ≟ k
  ... | yes refl with eq
  ...   | refl = here refl
  lookupBy-∈ ((k , v) ∷ tbl) c l eq | no _ = there (lookupBy-∈ tbl c l eq)

  -- A printed escape is read back as the character it came from.
  unescape-escape : ∀ c l → lookupBy escapes c ≡ just l → lookupBy unescapes l ≡ just c
  unescape-escape c l eq = All.lookup table-inverse (lookupBy-∈ escapes c l eq)

  -- `"` and `\` are in the table, so unescaped characters are neither.
  unescaped-not-quote : ∀ c → lookupBy escapes c ≡ nothing → c ≡ '"' → ⊥
  unescaped-not-quote c eq refl with eq
  ... | ()

  unescaped-not-backslash : ∀ c → lookupBy escapes c ≡ nothing → c ≡ '\\' → ⊥
  unescaped-not-backslash c eq refl with eq
  ... | ()

  escapeChar-just : ∀ c l → lookupBy escapes c ≡ just l → escapeChar c ≡ '\\' ∷ l ∷ []
  escapeChar-just c l eq rewrite eq = refl

  escapeChar-nothing : ∀ c → lookupBy escapes c ≡ nothing → escapeChar c ≡ c ∷ []
  escapeChar-nothing c eq rewrite eq = refl

lexBody-printBody : ∀ cs rest →
  lexBody (printBody cs ++ '"' ∷ rest) ≡ just (cs , rest)
lexBody-printBody []       rest = refl
lexBody-printBody (c ∷ cs) rest =
  trans (cong lexBody (++-assoc (escapeChar c) (printBody cs) ('"' ∷ rest)))
        (step c cs rest (lexBody-printBody cs rest))
  where
  step : ∀ c cs rest → lexBody (printBody cs ++ '"' ∷ rest) ≡ just (cs , rest) →
         lexBody (escapeChar c ++ printBody cs ++ '"' ∷ rest) ≡ just (c ∷ cs , rest)
  step c cs rest ih = dispatch (lookupBy escapes c) refl
    where
    Goal : Set
    Goal = lexBody (escapeChar c ++ printBody cs ++ '"' ∷ rest) ≡ just (c ∷ cs , rest)

    dispatch : ∀ r → lookupBy escapes c ≡ r → Goal
    dispatch (just l) eq
      rewrite escapeChar-just c l eq
            | unescape-escape c l eq
            | ih
      = refl
    dispatch nothing eq = plain (unescaped-not-quote c eq)
                                (unescaped-not-backslash c eq) (escapeChar-nothing c eq)
      where
      plain : (c ≡ '"' → ⊥) → (c ≡ '\\' → ⊥) → escapeChar c ≡ c ∷ [] → Goal
      plain nq nb ec rewrite ec with c ≟ '"' | c ≟ '\\'
      ... | yes q | _     = ⊥-elim (nq q)
      ... | no  _ | yes b = ⊥-elim (nb b)
      ... | no  _ | no  _ rewrite ih = refl

-- The contents of a complete literal.
parseStringLiteral : List Char → Maybe (List Char)
parseStringLiteral cs = Maybe.map proj₁ (lexStringLiteral cs)

parseStringLiteral-print : ∀ cs → parseStringLiteral (printStringLiteral cs) ≡ just cs
parseStringLiteral-print cs rewrite lexBody-printBody cs [] = refl

-- `stringStage` (see `Data.JSON.Goals`).
stringStage : RightInverse (setoid (List Char)) Chars
stringStage = mkStage (setoid (List Char)) printStringLiteral parseStringLiteral []
  (cong printStringLiteral)
  (λ cs → cs , parseStringLiteral-print cs , refl)
