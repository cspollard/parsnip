{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- Table-driven escaping, and its round trip, for any decoder
--
-- Text formats embed arbitrary characters in delimited bodies (XML
-- character data and attribute values, CSS strings, ...) by *escaping*
-- the characters that would end the body or start an escape.  An
-- escape table pairs each such character with the text printed for it
-- (`&amp;`, `\"`, `\a `, ...).  The decoder differs between formats, so
-- it is a parameter: a function reading a body up to (not including) the
-- terminator `stop`.  The module
-- proves, once, that escaping with a table and reading back gives the
-- original text, whenever the decoder stops at the terminator, passes
-- characters with no entry through, and reads back every entry.
-- It is shared by `Data.XML.Escape` and `Data.CSS.Escape`.
------------------------------------------------------------------------

module Data.Escape where

open import Data.Char using (Char)
open import Data.Char.Fast using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; map₁; ∃)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Tables and printing
------------------------------------------------------------------------

-- (character , the text printed for it)
Entry : Set
Entry = Char × List Char

Table : Set
Table = List Entry

lookupEntry : Table → Char → Maybe (List Char)
lookupEntry []              c = nothing
lookupEntry ((k , v) ∷ tbl) c with c ≟ k
... | yes _ = just v
... | no  _ = lookupEntry tbl c

escapeChar : Table → Char → List Char
escapeChar tbl c with lookupEntry tbl c
... | just n  = n
... | nothing = c ∷ []

escapeWith : Table → List Char → List Char
escapeWith tbl = concatMap (escapeChar tbl)

------------------------------------------------------------------------
-- Facts about tables
------------------------------------------------------------------------

-- The table has an entry for `k`.
HasKey : Char → Table → Set
HasKey k = Any (λ e → proj₁ e ≡ k)

lookupEntry-∈ : ∀ tbl c n → lookupEntry tbl c ≡ just n → (c , n) ∈ tbl
lookupEntry-∈ []              c n ()
lookupEntry-∈ ((k , v) ∷ tbl) c n eq with c ≟ k
... | yes refl with eq
...   | refl = here refl
lookupEntry-∈ ((k , v) ∷ tbl) c n eq | no _ = there (lookupEntry-∈ tbl c n eq)

-- A character with no entry is not a key.
lookupEntry-¬key : ∀ tbl c → lookupEntry tbl c ≡ nothing → HasKey c tbl → ⊥
lookupEntry-¬key []              c eq ()
lookupEntry-¬key ((k , v) ∷ tbl) c eq h with c ≟ k
lookupEntry-¬key ((k , v) ∷ tbl) c () h             | yes _
lookupEntry-¬key ((k , v) ∷ tbl) c eq (here e)      | no c≢k = c≢k (sym e)
lookupEntry-¬key ((k , v) ∷ tbl) c eq (there h)     | no _   = lookupEntry-¬key tbl c eq h

escapeChar-just : ∀ tbl c n → lookupEntry tbl c ≡ just n → escapeChar tbl c ≡ n
escapeChar-just tbl c n eq rewrite eq = refl

escapeChar-nothing : ∀ tbl c → lookupEntry tbl c ≡ nothing → escapeChar tbl c ≡ c ∷ []
escapeChar-nothing tbl c eq rewrite eq = refl

------------------------------------------------------------------------
-- The round trip
------------------------------------------------------------------------

-- `lex` reads a body up to (not including) a fixed terminator `stop`.
-- Escaping a text with `tbl` and reading it back (followed by `stop` and
-- anything) gives the text, provided that the decoder
--
--   * stops at the terminator              (`stops`),
--   * passes a character with no entry through   (`plain`), and
--   * reads back the text printed for every entry (`entries`).
--
-- The hypotheses say nothing about `tbl` beyond its entries, so the
-- instance proves `stops` and `plain` using that the table escapes the
-- terminator and the escape introducer.
module RoundTrip
  (lex  : List Char → Maybe (List Char × List Char))
  (stop : Char)
  (tbl  : Table)
  where

  Stops : Set
  Stops = ∀ X → lex (stop ∷ X) ≡ just ([] , stop ∷ X)

  Plain : Set
  Plain = ∀ c X → lookupEntry tbl c ≡ nothing →
          lex (c ∷ X) ≡ Maybe.map (map₁ (c ∷_)) (lex X)

  -- Reading back the text printed for an entry yields its character.
  Entries : Set
  Entries = ∀ c out → (c , out) ∈ tbl → ∀ rest →
            lex (out ++ rest) ≡ Maybe.map (map₁ (c ∷_)) (lex rest)

  lex-escapeWith : Stops → Plain → Entries →
    ∀ cs rest → lex (escapeWith tbl cs ++ stop ∷ rest) ≡ just (cs , stop ∷ rest)
  lex-escapeWith stops plain entries [] rest = stops rest
  lex-escapeWith stops plain entries (c ∷ cs) rest =
    trans (cong lex (++-assoc (escapeChar tbl c) (escapeWith tbl cs) (stop ∷ rest)))
          (step (lookupEntry tbl c) refl)
    where
    X : List Char
    X = escapeWith tbl cs ++ stop ∷ rest

    ih : lex X ≡ just (cs , stop ∷ rest)
    ih = lex-escapeWith stops plain entries cs rest

    step : ∀ r → lookupEntry tbl c ≡ r →
           lex (escapeChar tbl c ++ X) ≡ just (c ∷ cs , stop ∷ rest)
    step (just n) eq =
      trans (cong (λ l → lex (l ++ X)) (escapeChar-just tbl c n eq))
      (trans (entries c n (lookupEntry-∈ tbl c n eq) X)
             (cong (Maybe.map (map₁ (c ∷_))) ih))
    step nothing eq =
      trans (cong (λ l → lex (l ++ X)) (escapeChar-nothing tbl c eq))
      (trans (plain c X eq)
             (cong (Maybe.map (map₁ (c ∷_))) ih))
