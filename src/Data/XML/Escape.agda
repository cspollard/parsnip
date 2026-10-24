{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- XML character data: entity escaping and decoding
--
-- Text and attribute values are `List Char`.  Escaping is table driven
-- (as in `Data.JSON.String`): a table pairs each character that must be
-- written as an entity with the entity's name.
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
-- trips: any continuation may follow the terminator.
------------------------------------------------------------------------

module Data.XML.Escape where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (Char; fromℕ)
open import Data.Char.Properties using (_≟_)
open import Data.Nat using (ℕ; _<ᵇ_)
open import Data.Nat.Show using (readMaybe)
open import Data.String using (String; toList; fromList)
open import Data.List using (List; []; _∷_; _++_; concatMap; reverse)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; map₁; ∃)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.XML.Valid using (Name; Text; isValidChar; eqName)

------------------------------------------------------------------------
-- The escape tables
------------------------------------------------------------------------

-- (character , entity name)
Entry : Set
Entry = Char × String

textTable : List Entry
textTable = ('&' , "amp") ∷ ('<' , "lt") ∷ ('>' , "gt") ∷ ('\r' , "#13") ∷ []

valueTable : List Entry
valueTable =
  ('&' , "amp") ∷ ('<' , "lt") ∷ ('>' , "gt") ∷ ('\r' , "#13") ∷
  ('"' , "quot") ∷ ('\t' , "#9") ∷ ('\n' , "#10") ∷ []

lookupEntry : List Entry → Char → Maybe String
lookupEntry []              c = nothing
lookupEntry ((k , v) ∷ tbl) c with c ≟ k
... | yes _ = just v
... | no  _ = lookupEntry tbl c

------------------------------------------------------------------------
-- Printing
------------------------------------------------------------------------

escapeChar : List Entry → Char → List Char
escapeChar tbl c with lookupEntry tbl c
... | just n  = '&' ∷ toList n ++ ';' ∷ []
... | nothing = c ∷ []

escapeWith : List Entry → Text → List Char
escapeWith tbl = concatMap (escapeChar tbl)

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

-- The table has an entry for `k`.
HasKey : Char → List Entry → Set
HasKey k = Any (λ e → proj₁ e ≡ k)

-- Reading back the entity printed for an entry yields its character,
-- whatever the terminator and continuation.
EntryOK : Entry → Set
EntryOK (c , n) = ∀ stop rest →
  lexBody stop ('&' ∷ toList n ++ ';' ∷ rest) ≡ Maybe.map (map₁ (c ∷_)) (lexBody stop rest)

textTable-ok : All EntryOK textTable
textTable-ok = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []

valueTable-ok : All EntryOK valueTable
valueTable-ok =
  (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
  (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []

private
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

  escapeChar-just : ∀ tbl c n → lookupEntry tbl c ≡ just n →
                    escapeChar tbl c ≡ '&' ∷ toList n ++ ';' ∷ []
  escapeChar-just tbl c n eq rewrite eq = refl

  escapeChar-nothing : ∀ tbl c → lookupEntry tbl c ≡ nothing → escapeChar tbl c ≡ c ∷ []
  escapeChar-nothing tbl c eq rewrite eq = refl

-- An ordinary character is passed through.
lexBody-plain : ∀ stop c X → (c ≡ '&' → ⊥) → (c ≡ stop → ⊥) →
                lexBody stop (c ∷ X) ≡ Maybe.map (map₁ (c ∷_)) (lexBody stop X)
lexBody-plain stop c X n1 n2 with c ≟ '&'
... | yes e = ⊥-elim (n1 e)
... | no  _ with c ≟ stop
...   | yes e = ⊥-elim (n2 e)
...   | no  _ = refl

-- Escaping with `tbl` and then reading up to `stop` gives the text back,
-- provided every entry decodes (`All EntryOK`), `&` and `stop` are
-- themselves escaped, and `stop` is not `&`.
lexBody-escapeWith :
  ∀ tbl → All EntryOK tbl → HasKey '&' tbl → ∀ stop → HasKey stop tbl → (stop ≡ '&' → ⊥) →
  ∀ cs rest → lexBody stop (escapeWith tbl cs ++ stop ∷ rest) ≡ just (cs , stop ∷ rest)
lexBody-escapeWith tbl ok amp stop hstop stop≢& [] rest with stop ≟ '&'
... | yes e = ⊥-elim (stop≢& e)
... | no  _ with stop ≟ stop
...   | yes _  = refl
...   | no  ne = ⊥-elim (ne refl)
lexBody-escapeWith tbl ok amp stop hstop stop≢& (c ∷ cs) rest =
  trans (cong (lexBody stop) (++-assoc (escapeChar tbl c) (escapeWith tbl cs) (stop ∷ rest)))
        (step (lookupEntry tbl c) refl)
  where
  X : List Char
  X = escapeWith tbl cs ++ stop ∷ rest

  ih : lexBody stop X ≡ just (cs , stop ∷ rest)
  ih = lexBody-escapeWith tbl ok amp stop hstop stop≢& cs rest

  step : ∀ r → lookupEntry tbl c ≡ r →
         lexBody stop (escapeChar tbl c ++ X) ≡ just (c ∷ cs , stop ∷ rest)
  step (just n) eq =
    trans (cong (λ l → lexBody stop (l ++ X)) (escapeChar-just tbl c n eq))
    (trans (cong (λ l → lexBody stop ('&' ∷ l)) (++-assoc (toList n) (';' ∷ []) X))
    (trans (All.lookup ok (lookupEntry-∈ tbl c n eq) stop X)
           (cong (Maybe.map (map₁ (c ∷_))) ih)))
  step nothing eq =
    trans (cong (λ l → lexBody stop (l ++ X)) (escapeChar-nothing tbl c eq))
          (plain (λ e → lookupEntry-¬key tbl c eq (subst′ amp e))
                 (λ e → lookupEntry-¬key tbl c eq (subst′ hstop e)))
    where
    subst′ : ∀ {k} → HasKey k tbl → c ≡ k → HasKey c tbl
    subst′ h refl = h

    plain : (c ≡ '&' → ⊥) → (c ≡ stop → ⊥) →
            lexBody stop (c ∷ X) ≡ just (c ∷ cs , stop ∷ rest)
    plain n1 n2 = trans (lexBody-plain stop c X n1 n2) (cong (Maybe.map (map₁ (c ∷_))) ih)

lexBody-escapeText : ∀ cs rest →
  lexBody '<' (escapeText cs ++ '<' ∷ rest) ≡ just (cs , '<' ∷ rest)
lexBody-escapeText =
  lexBody-escapeWith textTable textTable-ok (here refl) '<' (there (here refl)) (λ ())

lexBody-escapeValue : ∀ cs rest →
  lexBody '"' (escapeValue cs ++ '"' ∷ rest) ≡ just (cs , '"' ∷ rest)
lexBody-escapeValue =
  lexBody-escapeWith valueTable valueTable-ok (here refl) '"'
    (there (there (there (there (here refl))))) (λ ())

-- Escaped text never starts with `<`.
escapeText-head : ∀ c cs → ∃ λ d → ∃ λ ds → escapeText (c ∷ cs) ≡ d ∷ ds × (d ≡ '<' → ⊥)
escapeText-head c cs = go (lookupEntry textTable c) refl
  where
  go : ∀ r → lookupEntry textTable c ≡ r →
       ∃ λ d → ∃ λ ds → escapeText (c ∷ cs) ≡ d ∷ ds × (d ≡ '<' → ⊥)
  go (just n) eq =
    '&' , _ , cong (_++ escapeText cs) (escapeChar-just textTable c n eq) , (λ ())
  go nothing eq =
    c , escapeText cs , cong (_++ escapeText cs) (escapeChar-nothing textTable c eq)
      , (λ e → lookupEntry-¬key textTable c eq (subst (λ k → HasKey k textTable) (sym e) (there (here refl))))
