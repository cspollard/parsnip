{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- XML character data: entity escaping and decoding
--
-- Text and attribute values are `List Char`.  Escaping is table driven
-- (`Data.Escape`, shared with CSS strings): a table pairs each character
-- that must be written as an entity with the text of that entity.
--
-- * text:   `& < >` and `\r`            (`textTable`)
-- * values: those, `"`, tab and newline  (`valueTable`)
--
-- `\r` (everywhere) and tab/newline (in values) are written as numeric
-- references because parsers normalise the literal characters.
--
-- Decoding (`lexBody`) reads characters up to a terminator that it does
-- not consume, turning entities back into characters.  It accepts the
-- five predefined entities, the numeric references the printer emits, and
-- any other numeric reference (`&#N;`, `&#xH;`) that is a legal XML
-- character.  It does not normalise raw whitespace.
--
-- `lexBody-escapeText` and `lexBody-escapeValue` are the prefix round
-- trips, instances of `Data.Escape.RoundTrip`: any continuation may
-- follow the terminator.
------------------------------------------------------------------------

module Data.XML.Escape where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (Char; fromℕ)
open import Data.Char.Fast using (_≟_)
open import Data.Nat using (ℕ; _<ᵇ_)
open import Data.Nat.Show using (readMaybe)
open import Data.String using (String; toList; fromList)
open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; map₁; ∃)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.XML.Valid using (Name; Text; isValidChar; eqName)
open import Data.Escape public

------------------------------------------------------------------------
-- The escape tables
------------------------------------------------------------------------

-- The text of the entity `&name;`.
entity : String → List Char
entity n = '&' ∷ toList n ++ ';' ∷ []

textTable : Table
textTable =
  ('&' , entity "amp") ∷ ('<' , entity "lt") ∷ ('>' , entity "gt") ∷ ('\r' , entity "#13") ∷ []

valueTable : Table
valueTable =
  ('&' , entity "amp") ∷ ('<' , entity "lt") ∷ ('>' , entity "gt") ∷ ('\r' , entity "#13") ∷
  ('"' , entity "quot") ∷ ('\t' , entity "#9") ∷ ('\n' , entity "#10") ∷ []

------------------------------------------------------------------------
-- Printing
------------------------------------------------------------------------

escapeText : Text → List Char
escapeText = escapeWith textTable

escapeValue : Text → List Char
escapeValue = escapeWith valueTable

------------------------------------------------------------------------
-- Entities
------------------------------------------------------------------------

namedEntities : List (String × Char)
namedEntities =
  ("amp" , '&') ∷ ("lt" , '<') ∷ ("gt" , '>') ∷ ("quot" , '"') ∷ ("apos" , '\'') ∷
  ("#9" , '\t') ∷ ("#10" , '\n') ∷ ("#13" , '\r') ∷ []

lookupNamed : Name → List (String × Char) → Maybe Char
lookupNamed name []              = nothing
lookupNamed name ((n , c) ∷ tbl) = if eqName name (toList n) then just c else lookupNamed name tbl

-- A numeric reference that is a legal XML character.
fromCode : Maybe ℕ → Maybe Char
fromCode nothing  = nothing
fromCode (just n) = if n <ᵇ 0x110000 then check (fromℕ n) else nothing
  where
  check : Char → Maybe Char
  check c = if isValidChar c then just c else nothing

numeric : Name → Maybe Char
numeric ('#' ∷ 'x' ∷ ds) = fromCode (readMaybe 16 (fromList ds))
numeric ('#' ∷ ds)       = fromCode (readMaybe 10 (fromList ds))
numeric _                = nothing

-- The character an entity name (between `&` and `;`) stands for.
resolve : Name → Maybe Char
resolve name with lookupNamed name namedEntities
... | just c  = just c
... | nothing = numeric name

------------------------------------------------------------------------
-- Decoding
------------------------------------------------------------------------

-- The characters up to the first unescaped `stop`, and the rest (which
-- starts with `stop`).  `lexEntity` reads an entity name, kept reversed.
mutual
  lexBody : Char → List Char → Maybe (List Char × List Char)
  lexBody stop []       = nothing
  lexBody stop (c ∷ cs) with c ≟ '&'
  ... | yes _ = lexEntity stop [] cs
  ... | no  _ = lexChar stop c cs (c ≟ stop)

  lexChar : (stop c : Char) → List Char → Dec (c ≡ stop) → Maybe (List Char × List Char)
  lexChar stop c cs (yes _) = just ([] , c ∷ cs)
  lexChar stop c cs (no  _) = Maybe.map (map₁ (c ∷_)) (lexBody stop cs)

  lexEntity : Char → List Char → List Char → Maybe (List Char × List Char)
  lexEntity stop acc []       = nothing
  lexEntity stop acc (c ∷ cs) with c ≟ ';'
  ... | no  _ = lexEntity stop (c ∷ acc) cs
  ... | yes _ with resolve (reverse acc)
  ...   | nothing = nothing
  ...   | just x  = Maybe.map (map₁ (x ∷_)) (lexBody stop cs)

------------------------------------------------------------------------
-- Round trip
------------------------------------------------------------------------

-- An ordinary character is passed through.
lexBody-plain : ∀ stop c X → (c ≡ '&' → ⊥) → (c ≡ stop → ⊥) →
                lexBody stop (c ∷ X) ≡ Maybe.map (map₁ (c ∷_)) (lexBody stop X)
lexBody-plain stop c X n1 n2 with c ≟ '&'
... | yes e = ⊥-elim (n1 e)
... | no  _ with c ≟ stop
...   | yes e = ⊥-elim (n2 e)
...   | no  _ = refl

private
  subst′ : ∀ {tbl k c} → HasKey k tbl → c ≡ k → HasKey c tbl
  subst′ h refl = h

  -- `Plain` for a table that escapes `&` and the terminator.
  plain-for : ∀ tbl stop → HasKey '&' tbl → HasKey stop tbl → RoundTrip.Plain (lexBody stop) stop tbl
  plain-for tbl stop hamp hstop c X eq =
    lexBody-plain stop c X (λ e → lookupEntry-¬key tbl c eq (subst′ hamp e))
                           (λ e → lookupEntry-¬key tbl c eq (subst′ hstop e))

  -- The text printed for an entry is read back (every entity here is
  -- decoded by computation).
  textEntries : RoundTrip.Entries (lexBody '<') '<' textTable
  textEntries c out (here refl)                             rest = refl
  textEntries c out (there (here refl))                     rest = refl
  textEntries c out (there (there (here refl)))             rest = refl
  textEntries c out (there (there (there (here refl))))     rest = refl
  textEntries c out (there (there (there (there ()))))

  valueEntries : RoundTrip.Entries (lexBody '"') '"' valueTable
  valueEntries c out (here refl)                                                 rest = refl
  valueEntries c out (there (here refl))                                         rest = refl
  valueEntries c out (there (there (here refl)))                                 rest = refl
  valueEntries c out (there (there (there (here refl))))                         rest = refl
  valueEntries c out (there (there (there (there (here refl)))))                 rest = refl
  valueEntries c out (there (there (there (there (there (here refl))))))         rest = refl
  valueEntries c out (there (there (there (there (there (there (here refl))))))) rest = refl
  valueEntries c out (there (there (there (there (there (there (there ())))))))

lexBody-escapeText : ∀ cs rest →
  lexBody '<' (escapeText cs ++ '<' ∷ rest) ≡ just (cs , '<' ∷ rest)
lexBody-escapeText =
  RoundTrip.lex-escapeWith (lexBody '<') '<' textTable (λ X → refl)
    (plain-for textTable '<' (here refl) (there (here refl))) textEntries

lexBody-escapeValue : ∀ cs rest →
  lexBody '"' (escapeValue cs ++ '"' ∷ rest) ≡ just (cs , '"' ∷ rest)
lexBody-escapeValue =
  RoundTrip.lex-escapeWith (lexBody '"') '"' valueTable (λ X → refl)
    (plain-for valueTable '"' (here refl) (there (there (there (there (here refl)))))) valueEntries

-- Escaped text starts with `&`, or with the (non-`<`) character itself.
private
  textTable-amp : ∀ c n → lookupEntry textTable c ≡ just n → ∃ λ r → n ≡ '&' ∷ r
  textTable-amp c n eq with lookupEntry-∈ textTable c n eq
  ... | here refl                                         = _ , refl
  ... | there (here refl)                                 = _ , refl
  ... | there (there (here refl))                         = _ , refl
  ... | there (there (there (here refl)))                 = _ , refl
  ... | there (there (there (there ())))

-- Escaped text never starts with `<`.
escapeText-head : ∀ c cs → ∃ λ d → ∃ λ ds → escapeText (c ∷ cs) ≡ d ∷ ds × (d ≡ '<' → ⊥)
escapeText-head c cs = go (lookupEntry textTable c) refl
  where
  go : ∀ r → lookupEntry textTable c ≡ r →
       ∃ λ d → ∃ λ ds → escapeText (c ∷ cs) ≡ d ∷ ds × (d ≡ '<' → ⊥)
  go (just n) eq with textTable-amp c n eq
  ... | r , refl =
    '&' , r ++ escapeText cs , cong (_++ escapeText cs) (escapeChar-just textTable c _ eq) , (λ ())
  go nothing eq =
    c , escapeText cs , cong (_++ escapeText cs) (escapeChar-nothing textTable c eq)
      , (λ e → lookupEntry-¬key textTable c eq (subst (λ k → HasKey k textTable) (sym e) (there (here refl))))
