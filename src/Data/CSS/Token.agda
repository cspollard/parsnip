{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- CSS tokens: printing, and the prefix lexer for one token
--
-- The tokens are those of CSS Syntax Level 3 §4 (except `url(...)`,
-- which is the function token `url(` and a string, `<!--`/`-->`, bad
-- strings and unicode ranges), plus `commentT`, which stands for the
-- comment `/**/`: the printer writes it between two tokens that would
-- otherwise run together, and the parser drops it.
--
--   identT n        n            functionT n     n(
--   atT n           @n           hashT n         #n
--   stringT s       "s"          numberT x       x
--   percentT x      x%           dimT x u        xu
--   wsT             one space    delimT c        c
--   colonT semiT commaT lparenT rparenT lbrackT rbrackT lbraceT rbraceT
--   commentT        /**/
--
-- `lexToken-printToken` is the prefix round trip used by the tokenizer
-- (`Data.CSS.Lexer`): printing a token and lexing it back, whatever text
-- follows, as long as the token is well formed (`tokenWF`) and the text
-- does not continue it (`okFollow`).  `okFollow` is a table on the class
-- of the next character (`Data.CSS.Valid.Cls`); it is conservative: it
-- forbids some continuations that would in fact lex correctly, which only
-- means that the printer inserts a comment where none is needed.
------------------------------------------------------------------------

module Data.CSS.Token where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; T)
open import Data.Bool.ListAction using (all)
open import Data.Char using (Char)
open import Data.Char.Fast using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; map₁)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F; 8F; 9F)
open import Data.Sign as Sign using (Sign)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Char.Fast using (_∈?_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Data.Invertible.Char using (parseDigit; printDigit; parsePrintDigit)
open import Data.XML.Valid using (∧-split; ∧-join)
open import Data.Number.Digits using (printNat; printNat-head; printSign; printFraction; NoLeadingDigit; NoLeadingDot)
open import Data.Lexer.Span
open import Data.CSS.Valid
open import Data.CSS.Number
open import Data.CSS.Escape

------------------------------------------------------------------------
-- Tokens and their spelling
------------------------------------------------------------------------

data CToken : Set where
  identT functionT atT hashT : Name → CToken
  stringT                    : Text → CToken
  numberT percentT           : CSSNumber → CToken
  dimT                       : CSSNumber → Name → CToken
  wsT commentT               : CToken
  delimT                     : Char → CToken
  colonT semiT commaT lparenT rparenT lbrackT rbrackT lbraceT rbraceT : CToken

printToken : CToken → List Char
printToken (identT n)      = n
printToken (functionT n)   = n ++ '(' ∷ []
printToken (atT n)         = '@' ∷ n
printToken (hashT n)       = '#' ∷ n
printToken (stringT s)     = '"' ∷ escapeString s ++ '"' ∷ []
printToken (numberT x)     = printNumber x
printToken (percentT x)    = printNumber x ++ '%' ∷ []
printToken (dimT x u)      = printNumber x ++ u
printToken wsT             = ' ' ∷ []
printToken commentT        = '/' ∷ '*' ∷ '*' ∷ '/' ∷ []
printToken (delimT c)      = c ∷ []
printToken colonT          = ':' ∷ []
printToken semiT           = ';' ∷ []
printToken commaT          = ',' ∷ []
printToken lparenT         = '(' ∷ []
printToken rparenT         = ')' ∷ []
printToken lbrackT         = '[' ∷ []
printToken rbrackT         = ']' ∷ []
printToken lbraceT         = '{' ∷ []
printToken rbraceT         = '}' ∷ []

------------------------------------------------------------------------
-- Well-formed tokens, and what may follow them
------------------------------------------------------------------------

tokenWF : CToken → Bool
tokenWF (identT n)    = isValidIdent n
tokenWF (functionT n) = isValidIdent n
tokenWF (atT n)       = isValidIdent n
tokenWF (hashT n)     = isValidHash n
tokenWF (stringT s)   = isValidText s
tokenWF (dimT x u)    = isValidIdent u
tokenWF (delimT c)    = isDelimChar c
tokenWF _             = true

-- The class of the first character of a printed token.
numClass : CSSNumber → Cls
numClass (cssNumber Sign.- _ _) = minusC
numClass (cssNumber Sign.+ _ _) = digitC

firstCls : CToken → Cls
firstCls (identT [])      = otherC
firstCls (identT (c ∷ _)) = classOf c
firstCls (functionT [])      = otherC
firstCls (functionT (c ∷ _)) = classOf c
firstCls (atT _)          = atC
firstCls (hashT _)        = hashC
firstCls (stringT _)      = dquoteC
firstCls (numberT x)      = numClass x
firstCls (percentT x)     = numClass x
firstCls (dimT x _)       = numClass x
firstCls wsT              = wsC
firstCls commentT         = slashC
firstCls (delimT c)       = classOf c
firstCls colonT           = colonC
firstCls semiT            = semiC
firstCls commaT           = commaC
firstCls lparenT          = lparenC
firstCls rparenT          = rparenC
firstCls lbrackT          = lbrackC
firstCls rbrackT          = rbrackC
firstCls lbraceT          = lbraceC
firstCls rbraceT          = rbraceC

-- A delimiter, by its class, may not be followed by what would turn it
-- into a longer token.
okDelim : Cls → Cls → Bool
okDelim hashC  k = not (identContK k)
okDelim atC    k = not (identStartK k ∨ minusK k)
okDelim plusC  k = not (digitK k ∨ dotK k)
okDelim minusC k = not (digitK k ∨ dotK k ∨ identStartK k ∨ minusK k)
okDelim dotC   k = not (digitK k)
okDelim slashC k = not (starK k)
okDelim _      k = true

-- May a token whose printed form is followed by text starting with a
-- character of class `k`?
okFollow : CToken → Cls → Bool
okFollow (identT _)    k = not (identContK k ∨ lparenK k)
okFollow (atT _)       k = not (identContK k)
okFollow (hashT _)     k = not (identContK k)
okFollow (numberT _)   k = not (identContK k ∨ dotK k ∨ percentK k)
okFollow (dimT _ _)    k = not (identContK k ∨ plusK k)
okFollow wsT           k = not (wsK k)
okFollow (delimT c)    k = okDelim (classOf c) k
okFollow _             k = true

------------------------------------------------------------------------
-- Lexing
------------------------------------------------------------------------

drop₁ : List Char → List Char
drop₁ []       = []
drop₁ (_ ∷ cs) = cs

-- A number, and what follows it: `%`, a unit, or neither.
lexNumTok : Sign → List Char → Maybe (CToken × List Char)
lexNumTok₁ : Maybe (CSSNumber × List Char) → Maybe (CToken × List Char)
lexNumTok₂ : CSSNumber → List Char → Bool → Bool → Maybe (CToken × List Char)

lexNumTok s cs = lexNumTok₁ (lexNumber s cs)

lexNumTok₁ nothing          = nothing
lexNumTok₁ (just (x , rest)) = lexNumTok₂ x rest (percentK (headCls rest)) (startsIdent rest)

lexNumTok₂ x rest true  _     = just (percentT x , drop₁ rest)
lexNumTok₂ x rest false true  = just (map₁ (dimT x) (spanBy isIdentChar rest))
lexNumTok₂ x rest false false = just (numberT x , rest)

-- An identifier or function, from text that starts an identifier.
lexIdent : List Char → Maybe (CToken × List Char)
lexIdent₁ : List Char × List Char → Maybe (CToken × List Char)
lexIdent₂ : Name → List Char → Bool → Maybe (CToken × List Char)

lexIdent cs = lexIdent₁ (spanBy isIdentChar cs)

lexIdent₁ (n , rest) = lexIdent₂ n rest (lparenK (headCls rest))

lexIdent₂ n rest false = just (identT n , rest)
lexIdent₂ n []       true = nothing
lexIdent₂ n (_ ∷ cs) true = just (functionT n , cs)

-- A `#` is a hash token if a name character follows.
lexHash₁ : Char → List Char → Bool → Maybe (CToken × List Char)
lexHash₁ c cs true  = just (map₁ hashT (spanBy isIdentChar cs))
lexHash₁ c cs false = just (delimT c , cs)

lexHash : Char → List Char → Maybe (CToken × List Char)
lexHash c cs = lexHash₁ c cs (identContK (headCls cs))

-- An `@` is an at-keyword if an identifier follows.
lexAt₁ : Char → List Char → Bool → Maybe (CToken × List Char)
lexAt₁ c cs true  = just (map₁ atT (spanBy isIdentChar cs))
lexAt₁ c cs false = just (delimT c , cs)

lexAt : Char → List Char → Maybe (CToken × List Char)
lexAt c cs = lexAt₁ c cs (startsIdent cs)

-- A comment, after the `/*`: up to and including the first `*/`.
lexComment : List Char → Maybe (CToken × List Char)
lexComment []                = nothing
lexComment ('*' ∷ '/' ∷ cs)  = just (commentT , cs)
lexComment (_ ∷ cs)          = lexComment cs

-- A `/` is a delimiter, unless a `*` follows.
lexSlash₁ : Bool → Char → List Char → Maybe (CToken × List Char)
lexSlash₁ false c cs       = just (delimT c , cs)
lexSlash₁ true  c []       = nothing
lexSlash₁ true  c (_ ∷ cs) = lexComment cs

lexSlash : Char → List Char → Maybe (CToken × List Char)
lexSlash c cs = lexSlash₁ (starK (headCls cs)) c cs

-- A string, after its opening quote `q`.
lexString : Char → List Char → Maybe (CToken × List Char)
lexString₁ : Maybe (List Char × List Char) → Maybe (CToken × List Char)

lexString q cs = lexString₁ (lexBody q cs)

lexString₁ nothing              = nothing
lexString₁ (just (t , []))      = nothing
lexString₁ (just (t , _ ∷ rest)) = just (stringT t , rest)

-- A `-` starts a number, an identifier, or is a delimiter.
lexMinus₁ : Char → List Char → Bool → Bool → Maybe (CToken × List Char)
lexMinus₁ c cs true  _     = lexNumTok Sign.- cs
lexMinus₁ c cs false true  = lexIdent (c ∷ cs)
lexMinus₁ c cs false false = just (delimT c , cs)

lexMinus : Char → List Char → Maybe (CToken × List Char)
lexMinus c cs = lexMinus₁ c cs (startsNumber cs) (startsIdent (c ∷ cs))

-- A `+` starts a number or is a delimiter.
lexPlus₁ : Char → List Char → Bool → Maybe (CToken × List Char)
lexPlus₁ c cs true  = lexNumTok Sign.+ cs
lexPlus₁ c cs false = just (delimT c , cs)

lexPlus : Char → List Char → Maybe (CToken × List Char)
lexPlus c cs = lexPlus₁ c cs (startsNumber cs)

-- A `.` starts a number or is a delimiter.
lexDot₁ : Char → List Char → Bool → Maybe (CToken × List Char)
lexDot₁ c cs true  = lexNumTok Sign.+ (c ∷ cs)
lexDot₁ c cs false = just (delimT c , cs)

lexDot : Char → List Char → Maybe (CToken × List Char)
lexDot c cs = lexDot₁ c cs (startsNumber (c ∷ cs))

-- One token, by the class of its first character.
lexTok : Char → List Char → Cls → Maybe (CToken × List Char)
lexTok c cs wsC         = just (wsT , proj₂ (spanBy isWs cs))
lexTok c cs identStartC = lexIdent (c ∷ cs)
lexTok c cs digitC      = lexNumTok Sign.+ (c ∷ cs)
lexTok c cs minusC      = lexMinus c cs
lexTok c cs plusC       = lexPlus c cs
lexTok c cs dotC        = lexDot c cs
lexTok c cs hashC       = lexHash c cs
lexTok c cs atC         = lexAt c cs
lexTok c cs slashC      = lexSlash c cs
lexTok c cs starC       = just (delimT c , cs)
lexTok c cs percentC    = just (delimT c , cs)
lexTok c cs dquoteC     = lexString c cs
lexTok c cs squoteC     = lexString c cs
lexTok c cs backslashC  = nothing
lexTok c cs lparenC     = just (lparenT , cs)
lexTok c cs rparenC     = just (rparenT , cs)
lexTok c cs lbrackC     = just (lbrackT , cs)
lexTok c cs rbrackC     = just (rbrackT , cs)
lexTok c cs lbraceC     = just (lbraceT , cs)
lexTok c cs rbraceC     = just (rbraceT , cs)
lexTok c cs commaC      = just (commaT , cs)
lexTok c cs colonC      = just (colonT , cs)
lexTok c cs semiC       = just (semiT , cs)
lexTok c cs delimC      = just (delimT c , cs)
lexTok c cs otherC      = nothing

lexToken : List Char → Maybe (CToken × List Char)
lexToken []       = nothing
lexToken (c ∷ cs) = lexTok c cs (classOf c)

------------------------------------------------------------------------
-- Round trip: facts about classes and the text that follows a token
------------------------------------------------------------------------

private
  absurd : true ≡ false → ∀ {a} {A : Set a} → A
  absurd ()

  -- Digits.
  classOf-printDigit : ∀ d → classOf (printDigit d) ≡ digitC
  classOf-printDigit 0F = refl
  classOf-printDigit 1F = refl
  classOf-printDigit 2F = refl
  classOf-printDigit 3F = refl
  classOf-printDigit 4F = refl
  classOf-printDigit 5F = refl
  classOf-printDigit 6F = refl
  classOf-printDigit 7F = refl
  classOf-printDigit 8F = refl
  classOf-printDigit 9F = refl

  -- A character whose class is not `digitC` is not a digit.
  notDigit : ∀ c → digitK (classOfD c (parseDigit c)) ≡ false → parseDigit c ≡ nothing
  notDigit c h with parseDigit c
  ... | nothing = refl
  ... | just d  = absurd h

  noDigit : ∀ rest → digitK (headCls rest) ≡ false → NoLeadingDigit rest
  noDigit []      _ = tt
  noDigit (c ∷ _) h = notDigit c h

  noDot : ∀ rest → dotK (headCls rest) ≡ false → NoLeadingDot rest
  noDot []      _ = tt
  noDot (c ∷ _) h with c ≟ '.'
  ... | yes refl = absurd h
  ... | no  _    = tt

  -- What follows does not continue a run of identifier characters.
  stops-ident : ∀ rest → identContK (headCls rest) ≡ false → Stops isIdentChar rest
  stops-ident []      _ = tt
  stops-ident (c ∷ _) h = h

  stops-ws : ∀ rest → wsK (headCls rest) ≡ false → Stops isWs rest
  stops-ws []      _ = tt
  stops-ws (c ∷ _) h = h

  startsIdent-false : ∀ rest → identStartK (headCls rest) ≡ false → minusK (headCls rest) ≡ false →
                      startsIdent rest ≡ false
  startsIdent-false []       _  _  = refl
  startsIdent-false (c ∷ cs) h1 h2 = startsIdent′-false (classOf c) cs h1 h2

  startsNumber-false : ∀ rest → digitK (headCls rest) ≡ false → dotK (headCls rest) ≡ false →
                       startsNumber rest ≡ false
  startsNumber-false []       _  _  = refl
  startsNumber-false (c ∷ cs) h1 h2 = startsNumber′-false (classOf c) cs h1 h2

  startsNumber-dot : ∀ rest → digitK (headCls rest) ≡ false → startsNumber′ dotC rest ≡ false
  startsNumber-dot []      _ = refl
  startsNumber-dot (c ∷ _) h = h

  -- A text that starts an identifier still does so with more text after it.
  startsIdent-++ : ∀ u R → startsIdent u ≡ true → startsIdent (u ++ R) ≡ true
  startsIdent-++ []       R ()
  startsIdent-++ (c ∷ cs) R h with startsIdent′-true (classOf c) cs h
  ... | inj₁ eq = cong (λ k → startsIdent′ k (cs ++ R)) eq
  ... | inj₂ (eq , d , ds , refl , hd) = trans (cong (λ k → startsIdent′ k (d ∷ ds ++ R)) eq) hd

  -- An identifier is `c ∷ cs` where `c` is an identifier start or `-`,
  -- followed (in the second case) by an identifier start or `-`.
  ident-head : ∀ u → startsIdent u ≡ true →
    ∃ λ c → ∃ λ cs → u ≡ c ∷ cs × (classOf c ≡ identStartC ⊎ classOf c ≡ minusC)
  ident-head []       ()
  ident-head (c ∷ cs) h with startsIdent′-true (classOf c) cs h
  ... | inj₁ eq          = c , cs , refl , inj₁ eq
  ... | inj₂ (eq , _)    = c , cs , refl , inj₂ eq

  all-head : ∀ c cs → all isIdentChar (c ∷ cs) ≡ true → isIdentChar c ≡ true × all isIdentChar cs ≡ true
  all-head c cs h with isIdentChar c
  ... | true  = refl , h
  all-head c cs () | false

  ∨-false₃ : ∀ {a b c} → a ∨ b ∨ c ≡ false → a ≡ false × b ≡ false × c ≡ false
  ∨-false₃ h with ∨-false h
  ... | ha , hbc with ∨-false hbc
  ... | hb , hc = ha , hb , hc

------------------------------------------------------------------------
-- Round trip: identifiers, functions, at-keywords and hashes
------------------------------------------------------------------------

private
  -- After a hyphen, an identifier continues with an identifier start or a
  -- hyphen, which is neither a digit nor a `.`.
  identOrMinus-notNum : ∀ k → identStartK k ∨ minusK k ≡ true → digitK k ≡ false × dotK k ≡ false
  identOrMinus-notNum k h with identStartK k in eq
  ... | true  rewrite identStartK-true k eq = refl , refl
  ... | false rewrite minusK-true k h       = refl , refl

  minus-ident : ∀ cs → startsIdent′ minusC cs ≡ true →
                ∃ λ d → ∃ λ ds → cs ≡ d ∷ ds × digitK (classOf d) ≡ false × dotK (classOf d) ≡ false
  minus-ident []       ()
  minus-ident (d ∷ ds) h with identOrMinus-notNum (classOf d) h
  ... | hd , hdot = d , ds , refl , hd , hdot

  -- A run of identifier characters is read back as a name.
  lexIdent-print : ∀ n R → all isIdentChar n ≡ true → Stops isIdentChar R →
    lexIdent (n ++ R) ≡ lexIdent₂ n R (lparenK (headCls R))
  lexIdent-print n R an st = cong lexIdent₁ (spanBy-++ isIdentChar n R an st)

  -- A text that starts with an identifier is lexed as one.
  lexToken-ident-start : ∀ n R → isValidIdent n ≡ true → lexToken (n ++ R) ≡ lexIdent (n ++ R)
  lexToken-ident-start n R hv with ∧-split hv
  ... | hs , ha with ident-head n hs
  ... | c , cs , refl , inj₁ eq = cong (lexTok c (cs ++ R)) eq
  ... | c , cs , refl , inj₂ eq with minus-ident cs (subst (λ k → startsIdent′ k cs ≡ true) eq hs)
  ... | d , ds , refl , hd , hdot =
    trans (cong (lexTok c ((d ∷ ds) ++ R)) eq)
          (cong₂ (lexMinus₁ c ((d ∷ ds) ++ R))
                 (startsNumber′-false (classOf d) (ds ++ R) hd hdot)
                 (startsIdent-++ (c ∷ d ∷ ds) R hs))

  lexToken-identT : ∀ n R → isValidIdent n ≡ true → okFollow (identT n) (headCls R) ≡ true →
                    lexToken (n ++ R) ≡ just (identT n , R)
  lexToken-identT n R hv hf with ∧-split hv | ∨-false (not-true hf)
  ... | hs , ha | hc , hl =
    trans (lexToken-ident-start n R hv)
    (trans (lexIdent-print n R ha (stops-ident R hc))
           (cong (lexIdent₂ n R) hl))

  lexToken-functionT : ∀ n R → isValidIdent n ≡ true →
                       lexToken ((n ++ '(' ∷ []) ++ R) ≡ just (functionT n , R)
  lexToken-functionT n R hv with ∧-split hv
  ... | hs , ha =
    trans (cong lexToken (++-assoc n ('(' ∷ []) R))
    (trans (lexToken-ident-start n ('(' ∷ R) hv)
           (lexIdent-print n ('(' ∷ R) ha refl))

  lexToken-atT : ∀ n R → isValidIdent n ≡ true → okFollow (atT n) (headCls R) ≡ true →
                 lexToken ('@' ∷ n ++ R) ≡ just (atT n , R)
  lexToken-atT n R hv hf with ∧-split hv
  ... | hs , ha =
    trans (cong (lexAt₁ '@' (n ++ R)) (startsIdent-++ n R hs))
          (cong (λ p → just (atT (proj₁ p) , proj₂ p))
                (spanBy-++ isIdentChar n R ha (stops-ident R (not-true hf))))

  lexToken-hashT : ∀ n R → isValidHash n ≡ true → okFollow (hashT n) (headCls R) ≡ true →
                   lexToken ('#' ∷ n ++ R) ≡ just (hashT n , R)
  lexToken-hashT []       R () _
  lexToken-hashT (c ∷ cs) R hv hf with all-head c cs hv
  ... | hc , _ =
    trans (cong (lexHash₁ '#' ((c ∷ cs) ++ R)) hc)
          (cong (λ p → just (hashT (proj₁ p) , proj₂ p))
                (spanBy-++ isIdentChar (c ∷ cs) R hv (stops-ident R (not-true hf))))

------------------------------------------------------------------------
-- Round trip: numbers
------------------------------------------------------------------------

private
  -- A printed natural number starts a number token.
  lexToken-digits : ∀ i X → lexToken (printNat i ++ X) ≡ lexNumTok Sign.+ (printNat i ++ X)
  lexToken-digits i X with printNat-head i X
  ... | d , cs , eq =
    trans (cong lexToken eq)
    (trans (cong (lexTok (printDigit d) cs) (classOf-printDigit d))
           (cong (lexNumTok Sign.+) (sym eq)))

  lexToken-minus : ∀ i X → lexToken ('-' ∷ printNat i ++ X) ≡ lexNumTok Sign.- (printNat i ++ X)
  lexToken-minus i X with printNat-head i X
  ... | d , cs , eq =
    trans (cong (λ Y → lexMinus₁ '-' Y (startsNumber Y) (startsIdent ('-' ∷ Y))) eq)
    (trans (cong (λ k → lexMinus₁ '-' (printDigit d ∷ cs) (startsNumber′ k cs) (startsIdent ('-' ∷ printDigit d ∷ cs)))
                 (classOf-printDigit d))
           (cong (lexNumTok Sign.-) (sym eq)))

  lexToken-number : ∀ s i f R →
    lexToken ((printSign s ++ printNat i ++ printFraction f) ++ R)
      ≡ lexNumTok s ((printNat i ++ printFraction f) ++ R)
  lexToken-number Sign.+ i f R =
    trans (cong lexToken (++-assoc (printNat i) (printFraction f) R))
    (trans (lexToken-digits i (printFraction f ++ R))
           (cong (lexNumTok Sign.+) (sym (++-assoc (printNat i) (printFraction f) R))))
  lexToken-number Sign.- i f R =
    trans (cong (λ L → lexToken ('-' ∷ L)) (++-assoc (printNat i) (printFraction f) R))
    (trans (lexToken-minus i (printFraction f ++ R))
           (cong (lexNumTok Sign.-) (sym (++-assoc (printNat i) (printFraction f) R))))

  -- The number, read back, before looking at what follows it.
  lexNumTok-print : ∀ s i f R → NoLeadingDigit R → NoLeadingDot R →
    lexToken ((printSign s ++ printNat i ++ printFraction f) ++ R)
      ≡ lexNumTok₂ (cssNumber s i f) R (percentK (headCls R)) (startsIdent R)
  lexNumTok-print s i f R nd ndot =
    trans (lexToken-number s i f R)
          (cong lexNumTok₁ (lexNumber-print s i f R nd ndot))

  lexToken-numberT : ∀ x R → okFollow (numberT x) (headCls R) ≡ true →
                     lexToken (printNumber x ++ R) ≡ just (numberT x , R)
  lexToken-numberT (cssNumber s i f) R hf with ∨-false₃ (not-true hf)
  ... | hcont , hdot , hpct with ∨-false₃ {identStartK (headCls R)} {digitK (headCls R)} {minusK (headCls R)} hcont
  ... | hstart , hdigit , hminus =
    trans (lexNumTok-print s i f R (noDigit R hdigit) (noDot R hdot))
          (cong₂ (lexNumTok₂ (cssNumber s i f) R) hpct (startsIdent-false R hstart hminus))

  lexToken-percentT : ∀ x R → lexToken ((printNumber x ++ '%' ∷ []) ++ R) ≡ just (percentT x , R)
  lexToken-percentT (cssNumber s i f) R =
    trans (cong lexToken (++-assoc (printSign s ++ printNat i ++ printFraction f) ('%' ∷ []) R))
          (lexNumTok-print s i f ('%' ∷ R) refl tt)

  -- Characters of an identifier-like text are not digits, `.` or `%`.
  head-identish : ∀ u R → startsIdent u ≡ true →
    digitK (headCls (u ++ R)) ≡ false × dotK (headCls (u ++ R)) ≡ false × percentK (headCls (u ++ R)) ≡ false
  head-identish u R h with ident-head u h
  ... | c , cs , refl , inj₁ eq = subst (λ k → digitK k ≡ false × dotK k ≡ false × percentK k ≡ false) (sym eq) (refl , refl , refl)
  ... | c , cs , refl , inj₂ eq = subst (λ k → digitK k ≡ false × dotK k ≡ false × percentK k ≡ false) (sym eq) (refl , refl , refl)

  lexToken-dimT : ∀ x u R → isValidIdent u ≡ true → okFollow (dimT x u) (headCls R) ≡ true →
                  lexToken ((printNumber x ++ u) ++ R) ≡ just (dimT x u , R)
  lexToken-dimT (cssNumber s i f) u R hv hf with ∧-split hv | head-identish u R (proj₁ (∧-split hv)) | ∨-false (not-true hf)
  ... | hs , ha | hdigit , hdot , hpct | hcont , _ =
    trans (cong lexToken (++-assoc (printSign s ++ printNat i ++ printFraction f) u R))
    (trans (lexNumTok-print s i f (u ++ R) (noDigit (u ++ R) hdigit) (noDot (u ++ R) hdot))
    (trans (cong₂ (lexNumTok₂ (cssNumber s i f) (u ++ R)) hpct (startsIdent-++ u R hs))
           (cong (λ p → just (dimT (cssNumber s i f) (proj₁ p) , proj₂ p))
                 (spanBy-++ isIdentChar u R ha (stops-ident R hcont)))))

------------------------------------------------------------------------
-- Round trip: delimiters, strings, and all tokens
------------------------------------------------------------------------

private
  startsIdent′-minus-false : ∀ R → identStartK (headCls R) ≡ false → minusK (headCls R) ≡ false →
                             startsIdent′ minusC R ≡ false
  startsIdent′-minus-false []      _  _  = refl
  startsIdent′-minus-false (d ∷ _) h1 h2 = cong₂ _∨_ h1 h2

  lexSlash₁-false : ∀ c R → lexSlash₁ false c R ≡ just (delimT c , R)
  lexSlash₁-false c R = refl

  absurd′ : false ≡ true → ∀ {a} {A : Set a} → A
  absurd′ ()

  DelimOK : Char → Set
  DelimOK d = ∀ R → okFollow (delimT d) (headCls R) ≡ true → lexToken (d ∷ R) ≡ just (delimT d , R)

  -- One proof for each character of `delimChars`.
  delimOK : All DelimOK delimChars
  delimOK =
    (λ R hf → refl) ∷
    (λ R hf → cong (lexHash₁ '#' R) (not-true hf)) ∷
    (λ R hf → refl) ∷
    (λ R hf → refl) ∷
    (λ R hf → refl) ∷
    (λ R hf → refl) ∷
    (λ R hf → cong (lexPlus₁ '+' R) (let (h1 , h2) = ∨-false (not-true hf) in startsNumber-false R h1 h2)) ∷
    (λ R hf → let (hd , hr) = ∨-false (not-true hf) ; (ho , hr′) = ∨-false hr ; (hi , hm) = ∨-false hr′ in cong₂ (lexMinus₁ '-' R) (startsNumber-false R hd ho) (startsIdent′-minus-false R hi hm)) ∷
    (λ R hf → cong (lexDot₁ '.' R) (startsNumber-dot R (not-true hf))) ∷
    (λ R hf → trans (cong (λ b → lexSlash₁ b '/' R) (not-true hf)) (lexSlash₁-false '/' R)) ∷
    (λ R hf → refl) ∷
    (λ R hf → refl) ∷
    (λ R hf → refl) ∷
    (λ R hf → refl) ∷
    (λ R hf → cong (lexAt₁ '@' R) (let (h1 , h2) = ∨-false (not-true hf) in startsIdent-false R h1 h2)) ∷
    (λ R hf → refl) ∷
    (λ R hf → refl) ∷
    (λ R hf → refl) ∷
    (λ R hf → refl) ∷ []

  lexToken-delim : ∀ d R → ⌊ d ∈? delimChars ⌋ ≡ true → okFollow (delimT d) (headCls R) ≡ true →
                   lexToken (d ∷ R) ≡ just (delimT d , R)
  lexToken-delim d R hd hf with d ∈? delimChars
  ... | no _    = absurd′ hd
  ... | yes mem = All.lookup delimOK mem R hf

lexToken-printToken : ∀ t rest → tokenWF t ≡ true → okFollow t (headCls rest) ≡ true →
                      lexToken (printToken t ++ rest) ≡ just (t , rest)
lexToken-printToken (identT n)    rest hv hf = lexToken-identT n rest hv hf
lexToken-printToken (functionT n) rest hv hf = lexToken-functionT n rest hv
lexToken-printToken (atT n)       rest hv hf = lexToken-atT n rest hv hf
lexToken-printToken (hashT n)     rest hv hf = lexToken-hashT n rest hv hf
lexToken-printToken (stringT s)   rest hv hf =
  trans (cong (λ L → lexToken ('"' ∷ L)) (++-assoc (escapeString s) ('"' ∷ []) rest))
        (cong lexString₁ (lexBody-escapeString s rest))
lexToken-printToken (numberT x)   rest hv hf = lexToken-numberT x rest hf
lexToken-printToken (percentT x)  rest hv hf = lexToken-percentT x rest
lexToken-printToken (dimT x u)    rest hv hf = lexToken-dimT x u rest hv hf
lexToken-printToken wsT           rest hv hf =
  cong (λ p → just (wsT , proj₂ p)) (spanBy-++ isWs [] rest refl (stops-ws rest (not-true hf)))
lexToken-printToken commentT      rest hv hf = refl
lexToken-printToken (delimT c)    rest hv hf = lexToken-delim c rest hv hf
lexToken-printToken colonT        rest hv hf = refl
lexToken-printToken semiT         rest hv hf = refl
lexToken-printToken commaT        rest hv hf = refl
lexToken-printToken lparenT       rest hv hf = refl
lexToken-printToken rparenT       rest hv hf = refl
lexToken-printToken lbrackT       rest hv hf = refl
lexToken-printToken rbrackT       rest hv hf = refl
lexToken-printToken lbraceT       rest hv hf = refl
lexToken-printToken rbraceT       rest hv hf = refl

------------------------------------------------------------------------
-- Facts used by the token streams
------------------------------------------------------------------------

-- Nothing follows (or, equally, a control character follows) any token.
okDelim-other : ∀ k → okDelim k otherC ≡ true
okDelim-other wsC = refl
okDelim-other identStartC = refl
okDelim-other digitC = refl
okDelim-other minusC = refl
okDelim-other plusC = refl
okDelim-other dotC = refl
okDelim-other hashC = refl
okDelim-other atC = refl
okDelim-other slashC = refl
okDelim-other starC = refl
okDelim-other percentC = refl
okDelim-other dquoteC = refl
okDelim-other squoteC = refl
okDelim-other backslashC = refl
okDelim-other lparenC = refl
okDelim-other rparenC = refl
okDelim-other lbrackC = refl
okDelim-other rbrackC = refl
okDelim-other lbraceC = refl
okDelim-other rbraceC = refl
okDelim-other commaC = refl
okDelim-other colonC = refl
okDelim-other semiC = refl
okDelim-other delimC = refl
okDelim-other otherC = refl

-- Any token may be followed by a comment `/**/`.
okDelim-slash : ∀ k → okDelim k slashC ≡ true
okDelim-slash wsC = refl
okDelim-slash identStartC = refl
okDelim-slash digitC = refl
okDelim-slash minusC = refl
okDelim-slash plusC = refl
okDelim-slash dotC = refl
okDelim-slash hashC = refl
okDelim-slash atC = refl
okDelim-slash slashC = refl
okDelim-slash starC = refl
okDelim-slash percentC = refl
okDelim-slash dquoteC = refl
okDelim-slash squoteC = refl
okDelim-slash backslashC = refl
okDelim-slash lparenC = refl
okDelim-slash rparenC = refl
okDelim-slash lbrackC = refl
okDelim-slash rbrackC = refl
okDelim-slash lbraceC = refl
okDelim-slash rbraceC = refl
okDelim-slash commaC = refl
okDelim-slash colonC = refl
okDelim-slash semiC = refl
okDelim-slash delimC = refl
okDelim-slash otherC = refl

okFollow-other : ∀ t → okFollow t otherC ≡ true
okFollow-other (identT _)    = refl
okFollow-other (functionT _) = refl
okFollow-other (atT _)       = refl
okFollow-other (hashT _)     = refl
okFollow-other (stringT _)   = refl
okFollow-other (numberT _)   = refl
okFollow-other (percentT _)  = refl
okFollow-other (dimT _ _)    = refl
okFollow-other wsT           = refl
okFollow-other commentT      = refl
okFollow-other (delimT c)    = okDelim-other (classOf c)
okFollow-other colonT        = refl
okFollow-other semiT         = refl
okFollow-other commaT        = refl
okFollow-other lparenT       = refl
okFollow-other rparenT       = refl
okFollow-other lbrackT       = refl
okFollow-other rbrackT       = refl
okFollow-other lbraceT       = refl
okFollow-other rbraceT       = refl

okFollow-slash : ∀ t → okFollow t slashC ≡ true
okFollow-slash (identT _)    = refl
okFollow-slash (functionT _) = refl
okFollow-slash (atT _)       = refl
okFollow-slash (hashT _)     = refl
okFollow-slash (stringT _)   = refl
okFollow-slash (numberT _)   = refl
okFollow-slash (percentT _)  = refl
okFollow-slash (dimT _ _)    = refl
okFollow-slash wsT           = refl
okFollow-slash commentT      = refl
okFollow-slash (delimT c)    = okDelim-slash (classOf c)
okFollow-slash colonT        = refl
okFollow-slash semiT         = refl
okFollow-slash commaT        = refl
okFollow-slash lparenT       = refl
okFollow-slash rparenT       = refl
okFollow-slash lbrackT       = refl
okFollow-slash rbrackT       = refl
okFollow-slash lbraceT       = refl
okFollow-slash rbraceT       = refl

private
  headCls-printNat : ∀ i X → headCls (printNat i ++ X) ≡ digitC
  headCls-printNat i X with printNat-head i X
  ... | d , cs , eq = trans (cong headCls eq) (classOf-printDigit d)

  headCls-number : ∀ x R → headCls (printNumber x ++ R) ≡ numClass x
  headCls-number (cssNumber Sign.- i f) R = refl
  headCls-number (cssNumber Sign.+ i f) R =
    trans (cong headCls (++-assoc (printNat i) (printFraction f) R))
          (headCls-printNat i (printFraction f ++ R))

  number-cons : ∀ x R → ∃ λ c → ∃ λ cs → printNumber x ++ R ≡ c ∷ cs
  number-cons (cssNumber Sign.- i f) R = '-' , _ , refl
  number-cons (cssNumber Sign.+ i f) R with printNat-head i (printFraction f ++ R)
  ... | d , cs , eq = printDigit d , cs , trans (++-assoc (printNat i) (printFraction f) R) eq

-- The first character of a well-formed token determines `firstCls`.
headCls-printToken : ∀ t R → tokenWF t ≡ true → headCls (printToken t ++ R) ≡ firstCls t
headCls-printToken (identT n) R hv with ident-head n (proj₁ (∧-split hv))
... | c , cs , refl , _ = refl
headCls-printToken (functionT n) R hv with ident-head n (proj₁ (∧-split hv))
... | c , cs , refl , _ = refl
headCls-printToken (atT _)       R _ = refl
headCls-printToken (hashT _)     R _ = refl
headCls-printToken (stringT _)   R _ = refl
headCls-printToken (numberT x)   R _ = headCls-number x R
headCls-printToken (percentT x)  R _ =
  trans (cong headCls (++-assoc (printNumber x) ('%' ∷ []) R)) (headCls-number x ('%' ∷ R))
headCls-printToken (dimT x u)    R _ =
  trans (cong headCls (++-assoc (printNumber x) u R)) (headCls-number x (u ++ R))
headCls-printToken wsT           R _ = refl
headCls-printToken commentT      R _ = refl
headCls-printToken (delimT c)    R _ = refl
headCls-printToken colonT        R _ = refl
headCls-printToken semiT         R _ = refl
headCls-printToken commaT        R _ = refl
headCls-printToken lparenT       R _ = refl
headCls-printToken rparenT       R _ = refl
headCls-printToken lbrackT       R _ = refl
headCls-printToken rbrackT       R _ = refl
headCls-printToken lbraceT       R _ = refl
headCls-printToken rbraceT       R _ = refl

-- A well-formed token prints to something non-empty.
printToken-cons : ∀ t → tokenWF t ≡ true → ∃ λ c → ∃ λ cs → printToken t ≡ c ∷ cs
printToken-cons (identT n) hv with ident-head n (proj₁ (∧-split hv))
... | c , cs , refl , _ = c , cs , refl
printToken-cons (functionT n) hv with ident-head n (proj₁ (∧-split hv))
... | c , cs , refl , _ = c , _ , refl
printToken-cons (atT _)      _ = '@' , _ , refl
printToken-cons (hashT _)    _ = '#' , _ , refl
printToken-cons (stringT _)  _ = '"' , _ , refl
printToken-cons (numberT x)  _ with number-cons x []
... | c , cs , eq = c , cs , trans (sym (++-identityʳ (printNumber x))) eq
printToken-cons (percentT x) _ with number-cons x ('%' ∷ [])
... | c , cs , eq = c , cs , eq
printToken-cons (dimT x u)   hv with number-cons x u
... | c , cs , eq = c , cs , eq
printToken-cons wsT          _ = ' ' , _ , refl
printToken-cons commentT     _ = '/' , _ , refl
printToken-cons (delimT c)   _ = c , _ , refl
printToken-cons colonT       _ = ':' , _ , refl
printToken-cons semiT        _ = ';' , _ , refl
printToken-cons commaT       _ = ',' , _ , refl
printToken-cons lparenT      _ = '(' , _ , refl
printToken-cons rparenT      _ = ')' , _ , refl
printToken-cons lbrackT      _ = '[' , _ , refl
printToken-cons rbrackT      _ = ']' , _ , refl
printToken-cons lbraceT      _ = '{' , _ , refl
printToken-cons rbraceT      _ = '}' , _ , refl
