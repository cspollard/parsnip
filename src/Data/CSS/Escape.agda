{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- CSS strings: escaping and decoding
--
-- A string body is printed with the escape table `stringTable`: the
-- quote and the backslash by a backslash and the character, and the
-- line breaks by a hex escape (`\a `, `\d `), because a raw line break
-- would end the string.  Decoding (`lexBody`) reads characters up to a
-- terminator it does not consume.  It accepts every escape CSS Syntax
-- Level 3 §4.3.7 defines except the line continuation (a backslash and
-- a line break): a backslash and a hex digit starts up to six hex
-- digits and an optional white space character; a backslash and any
-- other character stands for that character.  A raw line break is an
-- error.  Code points must be legal XML characters.
--
-- The round trip `lexBody-escapeString` is an instance of the generic
-- `Data.Escape.RoundTrip`.
------------------------------------------------------------------------

module Data.CSS.Escape where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (Char; fromℕ)
open import Data.Char.Fast using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<ᵇ_)
open import Data.Product using (_×_; _,_; map₁)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Data.Invertible.Char using (parseDigit)
open import Data.Fin using (toℕ)
open import Data.XML.Valid using (isValidChar)
open import Data.CSS.Valid using (Text; isWs)
open import Data.Escape

------------------------------------------------------------------------
-- Printing
------------------------------------------------------------------------

stringTable : Table
stringTable =
  ('"'  , '\\' ∷ '"' ∷ []) ∷
  ('\\' , '\\' ∷ '\\' ∷ []) ∷
  ('\n' , '\\' ∷ 'a' ∷ ' ' ∷ []) ∷
  ('\r' , '\\' ∷ 'd' ∷ ' ' ∷ []) ∷ []

escapeString : Text → List Char
escapeString = escapeWith stringTable

------------------------------------------------------------------------
-- Decoding
------------------------------------------------------------------------

hexLetter : Char → Maybe ℕ
hexLetter 'a' = just 10
hexLetter 'b' = just 11
hexLetter 'c' = just 12
hexLetter 'd' = just 13
hexLetter 'e' = just 14
hexLetter 'f' = just 15
hexLetter 'A' = just 10
hexLetter 'B' = just 11
hexLetter 'C' = just 12
hexLetter 'D' = just 13
hexLetter 'E' = just 14
hexLetter 'F' = just 15
hexLetter _   = nothing

hexVal′ : Maybe (Data.Fin.Fin 10) → Char → Maybe ℕ
hexVal′ (just d) c = just (toℕ d)
hexVal′ nothing  c = hexLetter c

hexVal : Char → Maybe ℕ
hexVal c = hexVal′ (parseDigit c) c

-- A numeric escape must name a legal XML character.
fromCode : ℕ → Maybe Char
fromCode n = if n <ᵇ 0x110000 then check (fromℕ n) else nothing
  where
  check : Char → Maybe Char
  check c = if isValidChar c then just c else nothing

-- The characters up to the first unescaped `stop`, and the rest (which
-- starts with `stop`).  The functions are mutually structural: each
-- call is on the tail of the text.
--
--   lexBodyHead stop c cs        the body `c ∷ cs`
--   lexEsc stop cs               after a backslash
--   lexHex stop k acc cs         after hex digits, at most `k` more
--   lexHexEnd stop x w ws        after the hex digits; the next character
--                                `w` is skipped if it is white space
mutual
  lexBody : Char → List Char → Maybe (List Char × List Char)
  lexBody stop []       = nothing
  lexBody stop (c ∷ cs) = lexBodyHead stop c cs

  lexBodyHead : Char → Char → List Char → Maybe (List Char × List Char)
  lexBodyHead stop c cs with c ≟ stop
  ... | yes _ = just ([] , c ∷ cs)
  ... | no  _ with c ≟ '\\'
  ...   | yes _ = lexEsc stop cs
  ...   | no  _ with c ≟ '\n'
  ...     | yes _ = nothing
  ...     | no  _ = Maybe.map (map₁ (c ∷_)) (lexBody stop cs)

  lexEsc : Char → List Char → Maybe (List Char × List Char)
  lexEsc stop []       = nothing
  lexEsc stop (d ∷ ds) = lexEsc′ stop d ds (hexVal d)

  lexEsc′ : Char → Char → List Char → Maybe ℕ → Maybe (List Char × List Char)
  lexEsc′ stop d ds (just v) = lexHex stop 5 v ds
  lexEsc′ stop d ds nothing with d ≟ '\n'
  ... | yes _ = nothing
  ... | no  _ = Maybe.map (map₁ (d ∷_)) (lexBody stop ds)

  lexHex : Char → ℕ → ℕ → List Char → Maybe (List Char × List Char)
  lexHex stop k       acc []       = nothing
  lexHex stop zero    acc (w ∷ ws) = lexHexEnd stop (fromCode acc) w ws
  lexHex stop (suc k) acc (d ∷ ds) = lexHex′ stop k acc d ds (hexVal d)

  lexHex′ : Char → ℕ → ℕ → Char → List Char → Maybe ℕ → Maybe (List Char × List Char)
  lexHex′ stop k acc d ds (just v) = lexHex stop k (acc * 16 + v) ds
  lexHex′ stop k acc d ds nothing  = lexHexEnd stop (fromCode acc) d ds

  lexHexEnd : Char → Maybe Char → Char → List Char → Maybe (List Char × List Char)
  lexHexEnd stop nothing  w ws = nothing
  lexHexEnd stop (just x) w ws = lexHexEnd′ stop x w ws (isWs w)

  lexHexEnd′ : Char → Char → Char → List Char → Bool → Maybe (List Char × List Char)
  lexHexEnd′ stop x w ws true  = Maybe.map (map₁ (x ∷_)) (lexBody stop ws)
  lexHexEnd′ stop x w ws false = Maybe.map (map₁ (x ∷_)) (lexBodyHead stop w ws)

------------------------------------------------------------------------
-- Round trip
------------------------------------------------------------------------

private
  lexBodyHead-plain : ∀ stop c X → (c ≡ stop → ⊥) → (c ≡ '\\' → ⊥) → (c ≡ '\n' → ⊥) →
    lexBody stop (c ∷ X) ≡ Maybe.map (map₁ (c ∷_)) (lexBody stop X)
  lexBodyHead-plain stop c X n1 n2 n3 with c ≟ stop
  ... | yes e = ⊥-elim (n1 e)
  ... | no  _ with c ≟ '\\'
  ...   | yes e = ⊥-elim (n2 e)
  ...   | no  _ with c ≟ '\n'
  ...     | yes e = ⊥-elim (n3 e)
  ...     | no  _ = refl

  subst′ : ∀ {k c} {tbl : Table} → HasKey k tbl → c ≡ k → HasKey c tbl
  subst′ h refl = h

open RoundTrip (lexBody '"') '"' stringTable

private
  stops : Stops
  stops X = refl

  plain : Plain
  plain c X eq =
    lexBodyHead-plain '"' c X
      (λ e → lookupEntry-¬key stringTable c eq (subst′ (here refl) e))
      (λ e → lookupEntry-¬key stringTable c eq (subst′ (there (here refl)) e))
      (λ e → lookupEntry-¬key stringTable c eq (subst′ (there (there (here refl))) e))

  entries : Entries
  entries c out (here refl) rest = refl
  entries c out (there (here refl)) rest = refl
  entries c out (there (there (here refl))) rest = refl
  entries c out (there (there (there (here refl)))) rest = refl
  entries c out (there (there (there (there ()))))

-- Escaping a string body and reading it up to its closing quote.
lexBody-escapeString : ∀ cs rest →
  lexBody '"' (escapeString cs ++ '"' ∷ rest) ≡ just (cs , '"' ∷ rest)
lexBody-escapeString = lex-escapeWith stops plain entries
