{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- XML tokens: printing, and the prefix lexer for one token
--
-- A tag is one token, attributes included:
--
--   openT n as   <n a="v" …>          selfT n as   <n a="v" … />
--   closeT n     </n>                 textT t      character data
--
-- `lexToken-printToken` is the prefix round trip used by the tokenizer
-- (`Data.XML.Lexer`): printing a token and lexing it back, whatever text
-- follows, as long as the token is well formed (`tokenWF`) and a text
-- token is followed by `<`.
--
-- The lexer is purely structural.  Names are maximal runs of name
-- characters; between attributes it skips white space (but not around
-- `=`); character data is read by `Data.XML.Escape.lexBody`.  Whether
-- names and values are legal XML is checked by the parser.
------------------------------------------------------------------------

module Data.XML.Token where

open import Data.Bool using (Bool; true; false; _∧_; T)
open import Data.Bool.ListAction using (all)
open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; concatMap; length)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤n+m; n<1+n)
open import Data.Product using (_×_; _,_; proj₁; map₁; ∃)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Data.XML.Valid
open import Data.XML.Escape

------------------------------------------------------------------------
-- Tokens and their spelling
------------------------------------------------------------------------

data XMLToken : Set where
  openT selfT : Name → Attributes → XMLToken
  closeT      : Name → XMLToken
  textT       : Text → XMLToken

printAttribute : Attribute → List Char
printAttribute (k , v) = ' ' ∷ k ++ '=' ∷ '"' ∷ escapeValue v ++ '"' ∷ []

printAttributes : Attributes → List Char
printAttributes = concatMap printAttribute

-- How a start tag ends: `>`, or ` />` for an empty element.
closer : Bool → List Char
closer false = '>' ∷ []
closer true  = ' ' ∷ '/' ∷ '>' ∷ []

-- The start tag token with the given ending.
startT : Bool → Name → Attributes → XMLToken
startT false = openT
startT true  = selfT

printToken : XMLToken → List Char
printToken (openT n as) = '<' ∷ n ++ printAttributes as ++ closer false
printToken (selfT n as) = '<' ∷ n ++ printAttributes as ++ closer true
printToken (closeT n)   = '<' ∷ '/' ∷ n ++ '>' ∷ []
printToken (textT t)    = escapeText t

printTokenList : List XMLToken → List Char
printTokenList []       = []
printTokenList (t ∷ ts) = printToken t ++ printTokenList ts

------------------------------------------------------------------------
-- Well-formed tokens
------------------------------------------------------------------------

attrNamesValid : Attributes → Bool
attrNamesValid = all (λ a → isValidName (proj₁ a))

-- Tokens that print and lex back: valid names, and non-empty text.
tokenWF : XMLToken → Bool
tokenWF (openT n as) = isValidName n ∧ attrNamesValid as
tokenWF (selfT n as) = isValidName n ∧ attrNamesValid as
tokenWF (closeT n)   = isValidName n
tokenWF (textT [])   = false
tokenWF (textT _)    = true

-- What may follow a printed token: character data must be ended by `<`
-- (it cannot run to the end of the input); anything may follow a tag.
TokenFollow : XMLToken → List Char → Set
TokenFollow (textT _) rest = ∃ λ r → rest ≡ '<' ∷ r
TokenFollow _         _    = ⊤

------------------------------------------------------------------------
-- Lexing
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

-- The longest prefix of name characters, and the rest.
lexName : List Char → Name × List Char
lexName′ : Char → List Char → Bool → Name × List Char

lexName []       = [] , []
lexName (c ∷ cs) = lexName′ c cs (isNameChar c)

lexName′ c cs true  = map₁ (c ∷_) (lexName cs)
lexName′ c cs false = [] , c ∷ cs

-- One attribute: `name="value"`.
lexAttr : List Char → Maybe (Attribute × List Char)
lexAttr₁ : Name × List Char → Maybe (Attribute × List Char)
lexAttr₂ : Name → Maybe (Text × List Char) → Maybe (Attribute × List Char)

lexAttr cs = lexAttr₁ (lexName cs)

lexAttr₁ (k@(_ ∷ _) , '=' ∷ '"' ∷ cs) = lexAttr₂ k (lexBody '"' cs)
lexAttr₁ _                             = nothing

lexAttr₂ k (just (v , '"' ∷ rest)) = just ((k , v) , rest)
lexAttr₂ k _                       = nothing

consAttr : Attribute → Attributes × Bool × List Char → Attributes × Bool × List Char
consAttr a (as , b , r) = a ∷ as , b , r

-- The attributes of a start tag, up to and including its ending
-- (`false` for `>`, `true` for `/>`).  The first argument is fuel: each
-- attribute consumes at least one character.
mutual
  lexAttrs : ℕ → List Char → Maybe (Attributes × Bool × List Char)
  lexAttrs zero    _  = nothing
  lexAttrs (suc f) cs = lexAttrs₁ f (skipWS cs)

  lexAttrs₁ : ℕ → List Char → Maybe (Attributes × Bool × List Char)
  lexAttrs₁ f []       = nothing
  lexAttrs₁ f (c ∷ cs) = lexAttrs₃ f c cs (isNameChar c)

  lexAttrs₃ : ℕ → Char → List Char → Bool → Maybe (Attributes × Bool × List Char)
  lexAttrs₃ f c   cs        true  = lexAttrs₂ f (lexAttr (c ∷ cs))
  lexAttrs₃ f '>' cs        false = just ([] , false , cs)
  lexAttrs₃ f '/' ('>' ∷ cs) false = just ([] , true , cs)
  lexAttrs₃ f _   _         false = nothing

  lexAttrs₂ : ℕ → Maybe (Attribute × List Char) → Maybe (Attributes × Bool × List Char)
  lexAttrs₂ f nothing         = nothing
  lexAttrs₂ f (just (a , cs)) = Maybe.map (consAttr a) (lexAttrs f cs)

-- A start tag, after the `<`.
lexOpen : List Char → Maybe (XMLToken × List Char)
lexOpen₁ : Name × List Char → Maybe (XMLToken × List Char)
lexOpen₂ : Name → Maybe (Attributes × Bool × List Char) → Maybe (XMLToken × List Char)

lexOpen cs = lexOpen₁ (lexName cs)

lexOpen₁ ([]          , _)    = nothing
lexOpen₁ (n@(_ ∷ _)   , rest) = lexOpen₂ n (lexAttrs (suc (length rest)) rest)

lexOpen₂ n nothing                 = nothing
lexOpen₂ n (just (as , b , rest))  = just (startT b n as , rest)

-- An end tag, after the `</`.
lexClose : List Char → Maybe (XMLToken × List Char)
lexClose₁ : Name × List Char → Maybe (XMLToken × List Char)

lexClose cs = lexClose₁ (lexName cs)

lexClose₁ (n@(_ ∷ _) , '>' ∷ rest) = just (closeT n , rest)
lexClose₁ _                        = nothing

-- A tag, after the `<`.
lexTag : List Char → Maybe (XMLToken × List Char)
lexTag′ : Char → List Char → Bool → Maybe (XMLToken × List Char)

lexTag []       = nothing
lexTag (c ∷ cs) = lexTag′ c cs (isNameChar c)

lexTag′ c   cs true  = lexOpen (c ∷ cs)
lexTag′ '/' cs false = lexClose cs
lexTag′ _   _  false = nothing

-- Character data, up to (not including) the next `<`.
lexText : List Char → Maybe (XMLToken × List Char)
lexText cs = Maybe.map (map₁ textT) (lexBody '<' cs)

lexToken : List Char → Maybe (XMLToken × List Char)
lexToken′ : (c : Char) → List Char → Dec (c ≡ '<') → Maybe (XMLToken × List Char)

lexToken []       = nothing
lexToken (c ∷ cs) = lexToken′ c cs (c ≟ '<')

lexToken′ c cs (yes _) = lexTag cs
lexToken′ c cs (no  _) = lexText (c ∷ cs)

------------------------------------------------------------------------
-- Round trip
------------------------------------------------------------------------

NameChars : Name → Set
NameChars n = all isNameChar n ≡ true

-- Name characters are consumed up to a character that is not one.
lexName-span : ∀ n rest → NameChars n → lexName rest ≡ ([] , rest) →
               lexName (n ++ rest) ≡ (n , rest)
lexName-span []      rest _  stop = stop
lexName-span (c ∷ n) rest nc stop with ∧-split nc
... | hc , hn =
  trans (cong (lexName′ c (n ++ rest)) hc)
        (cong (map₁ (c ∷_)) (lexName-span n rest hn stop))

-- After the name of a start tag comes a space, or the ending `>`.
stop-printAttributes : ∀ as b rest →
  lexName (printAttributes as ++ closer b ++ rest) ≡ ([] , printAttributes as ++ closer b ++ rest)
stop-printAttributes []            false rest = refl
stop-printAttributes []            true  rest = refl
stop-printAttributes ((k , v) ∷ as) b    rest = refl

printAttribute-++ : ∀ k v R →
  printAttribute (k , v) ++ R ≡ ' ' ∷ k ++ '=' ∷ '"' ∷ escapeValue v ++ '"' ∷ R
printAttribute-++ k v R =
  cong (' ' ∷_) (trans (++-assoc k _ R)
    (cong (k ++_) (cong ('=' ∷_) (cong ('"' ∷_) (++-assoc (escapeValue v) ('"' ∷ []) R)))))

lexAttr-print : ∀ c k v rest → NameChars (c ∷ k) →
  lexAttr ((c ∷ k) ++ '=' ∷ '"' ∷ escapeValue v ++ '"' ∷ rest) ≡ just (((c ∷ k) , v) , rest)
lexAttr-print c k v rest nc =
  trans (cong lexAttr₁ (lexName-span (c ∷ k) _ nc refl))
        (cong (lexAttr₂ (c ∷ k)) (lexBody-escapeValue v rest))

NonWS : Char → Set
NonWS c = c ∈ whitespace → ⊥

skipWS-nonWS : ∀ c cs → NonWS c → skipWS (c ∷ cs) ≡ c ∷ cs
skipWS-nonWS c cs nw with c ∈? whitespace
... | yes p = ⊥-elim (nw p)
... | no  _ = refl

-- Name characters are not white space.
nonWS-name : ∀ c → isNameChar c ≡ true → NonWS c
nonWS-name .' '  () (here refl)
nonWS-name .'\n' () (there (here refl))
nonWS-name .'\t' () (there (there (here refl)))
nonWS-name .'\r' () (there (there (there (here refl))))

-- Fuel: after consuming a non-empty prefix, the rest still fits.
fuel-step : ∀ (p : Char) (P R : List Char) (f : ℕ) → length ((p ∷ P) ++ R) < suc f → length R < f
fuel-step p P R f (s≤s lt) =
  ≤-trans (s≤s (subst (length R ≤_) (sym (length-++ P)) (m≤n+m (length R) (length P)))) lt

-- The attributes of a start tag and its ending are read back.
lexAttrs-print : ∀ as b rest f → attrNamesValid as ≡ true →
  length (printAttributes as ++ closer b ++ rest) < f →
  lexAttrs f (printAttributes as ++ closer b ++ rest) ≡ just (as , b , rest)
lexAttrs-print as b rest zero _ ()
lexAttrs-print [] false rest (suc g) _ _ = refl
lexAttrs-print [] true  rest (suc g) _ _ = refl
lexAttrs-print ((k , v) ∷ as) b rest (suc g) nv lt with ∧-split nv
... | hk , has with validName-chars k hk
... | c , k′ , refl , hc , hk′ =
  subst (λ l → lexAttrs (suc g) l ≡ just ((((c ∷ k′) , v) ∷ as) , b , rest))
        (sym eqI) main
  where
  R : List Char
  R = printAttributes as ++ closer b ++ rest

  eqI : printAttributes (((c ∷ k′) , v) ∷ as) ++ closer b ++ rest
        ≡ ' ' ∷ (c ∷ k′) ++ '=' ∷ '"' ∷ escapeValue v ++ '"' ∷ R
  eqI = trans (++-assoc (printAttribute ((c ∷ k′) , v)) (printAttributes as) (closer b ++ rest))
              (printAttribute-++ (c ∷ k′) v R)

  lt′ : length R < g
  lt′ = fuel-step ' ' ((c ∷ k′) ++ '=' ∷ '"' ∷ escapeValue v ++ '"' ∷ []) R g
          (subst (λ l → length l < suc g)
                 (++-assoc (printAttribute ((c ∷ k′) , v)) (printAttributes as) (closer b ++ rest)) lt)

  nc : NameChars (c ∷ k′)
  nc = ∧-join hc hk′

  main : lexAttrs (suc g) (' ' ∷ (c ∷ k′) ++ '=' ∷ '"' ∷ escapeValue v ++ '"' ∷ R)
         ≡ just ((((c ∷ k′) , v) ∷ as) , b , rest)
  main =
    trans (cong (lexAttrs₁ g) (skipWS-nonWS c _ (nonWS-name c hc)))
    (trans (cong (lexAttrs₃ g c _) hc)
    (trans (cong (lexAttrs₂ g) (lexAttr-print c k′ v R nc))
           (cong (Maybe.map (consAttr ((c ∷ k′) , v))) (lexAttrs-print as b rest g has lt′))))

------------------------------------------------------------------------
-- Tags
------------------------------------------------------------------------

tag-assoc : ∀ (n PA C rest : List Char) → (n ++ PA ++ C) ++ rest ≡ n ++ PA ++ C ++ rest
tag-assoc n PA C rest = trans (++-assoc n (PA ++ C) rest) (cong (n ++_) (++-assoc PA C rest))

lexTag-start : ∀ b n as rest → isValidName n ≡ true → attrNamesValid as ≡ true →
  lexTag (n ++ printAttributes as ++ closer b ++ rest) ≡ just (startT b n as , rest)
lexTag-start b n as rest hn ha with validName-chars n hn
... | c , n′ , refl , hc , hn′ =
  trans (cong (lexTag′ c (n′ ++ R)) hc)
  (trans (cong lexOpen₁ (lexName-span (c ∷ n′) R (∧-join hc hn′) (stop-printAttributes as b rest)))
         (cong (lexOpen₂ (c ∷ n′)) (lexAttrs-print as b rest (suc (length R)) ha (n<1+n (length R)))))
  where
  R : List Char
  R = printAttributes as ++ closer b ++ rest

lexTag-close : ∀ n rest → isValidName n ≡ true →
  lexTag ('/' ∷ n ++ '>' ∷ rest) ≡ just (closeT n , rest)
lexTag-close n rest hn with validName-chars n hn
... | c , n′ , refl , hc , hn′ =
  cong lexClose₁ (lexName-span (c ∷ n′) ('>' ∷ rest) (∧-join hc hn′) refl)

------------------------------------------------------------------------
-- One token
------------------------------------------------------------------------

lexToken-notlt : ∀ d X → (d ≡ '<' → ⊥) → lexToken (d ∷ X) ≡ lexText (d ∷ X)
lexToken-notlt d X nd = go (d ≟ '<')
  where
  go : (dec : Dec (d ≡ '<')) → lexToken′ d X dec ≡ lexText (d ∷ X)
  go (yes e) = ⊥-elim (nd e)
  go (no  _) = refl

lexToken-printToken : ∀ t rest → tokenWF t ≡ true → TokenFollow t rest →
  lexToken (printToken t ++ rest) ≡ just (t , rest)
lexToken-printToken (openT n as) rest wf _ with ∧-split wf
... | hn , ha =
  trans (cong (λ l → lexToken ('<' ∷ l)) (tag-assoc n (printAttributes as) (closer false) rest))
        (lexTag-start false n as rest hn ha)
lexToken-printToken (selfT n as) rest wf _ with ∧-split wf
... | hn , ha =
  trans (cong (λ l → lexToken ('<' ∷ l)) (tag-assoc n (printAttributes as) (closer true) rest))
        (lexTag-start true n as rest hn ha)
lexToken-printToken (closeT n) rest wf _ =
  trans (cong (λ l → lexToken ('<' ∷ '/' ∷ l)) (++-assoc n ('>' ∷ []) rest))
        (lexTag-close n rest wf)
lexToken-printToken (textT [])      rest () _
lexToken-printToken (textT (c ∷ cs)) .('<' ∷ r) _ (r , refl) with escapeText-head c cs
... | d , ds , eq , nd =
  trans (cong (λ l → lexToken (l ++ '<' ∷ r)) eq)
  (trans (lexToken-notlt d (ds ++ '<' ∷ r) nd)
  (trans (cong (λ l → lexText (l ++ '<' ∷ r)) (sym eq))
         (cong (Maybe.map (map₁ textT)) (lexBody-escapeText (c ∷ cs) r))))
