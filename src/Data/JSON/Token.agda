{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- JSON tokens: printing, and the prefix lexer for one token
--
-- `lexToken-printToken` is the prefix round trip used by the tokenizer
-- (`Data.JSON.Lexer`): printing a token and lexing it back, whatever
-- text follows, as long as a number is not followed by more number.
-- `tokenStage` is its instance at an empty continuation, as a stdlib
-- `RightInverse`.
------------------------------------------------------------------------

module Data.JSON.Token where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; map₁)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin)
open import Data.Sign using (Sign)
import Data.Sign as Sign
open import Function.Bundles using (RightInverse)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; setoid)

open import Data.JSON.Number
open import Data.JSON.String using (printStringLiteral; printBody; lexBody; lexBody-printBody)
open import Data.JSON.Keyword
open import Data.Stage using (Chars; mkStage)
open import Data.Invertible.Char using (parseDigit; printDigit; parsePrintDigit)

------------------------------------------------------------------------
-- Tokens and their spelling
------------------------------------------------------------------------

data JSONToken : Set where
  lbraceT lbracketT rbraceT rbracketT colonT commaT : JSONToken
  nullT    : JSONToken
  boolT    : Bool → JSONToken
  numberT  : JSONNumber → JSONToken
  stringT  : List Char → JSONToken

printToken : JSONToken → List Char
printToken lbraceT       = '{' ∷ []
printToken rbraceT       = '}' ∷ []
printToken lbracketT     = '[' ∷ []
printToken rbracketT     = ']' ∷ []
printToken colonT        = ':' ∷ []
printToken commaT        = ',' ∷ []
printToken nullT         = keywordText nullK
printToken (boolT true)  = keywordText trueK
printToken (boolT false) = keywordText falseK
printToken (numberT n)   = printNumber n
printToken (stringT s)   = printStringLiteral s

printTokenList : List JSONToken → List Char
printTokenList []       = []
printTokenList (t ∷ ts) = printToken t ++ printTokenList ts

-- What may follow a printed token: a number must not be run into more
-- number (digit, `.`, `e`, `E`); anything else may follow anything.
TokenFollow : JSONToken → List Char → Set
TokenFollow (numberT _) rest = NoLeadingNumCont rest
TokenFollow _           _    = ⊤

------------------------------------------------------------------------
-- Lexing one token
------------------------------------------------------------------------

private
  numberToken : Sign → List Char → Maybe (JSONToken × List Char)
  numberToken s cs = Maybe.map (map₁ numberT) (lexNumber s cs)

  keywordToken : Keyword × List Char → JSONToken × List Char
  keywordToken (nullK  , rest) = nullT , rest
  keywordToken (trueK  , rest) = boolT true , rest
  keywordToken (falseK , rest) = boolT false , rest

-- Dispatch on the first character; the third argument is `parseDigit c`,
-- passed explicitly so that proofs can rewrite exactly that call.
lexToken′ : Char → List Char → Maybe (Fin 10) → Maybe (JSONToken × List Char)
lexToken′ c   cs (just _) = numberToken Sign.+ (c ∷ cs)
lexToken′ '{' cs nothing  = just (lbraceT , cs)
lexToken′ '}' cs nothing  = just (rbraceT , cs)
lexToken′ '[' cs nothing  = just (lbracketT , cs)
lexToken′ ']' cs nothing  = just (rbracketT , cs)
lexToken′ ':' cs nothing  = just (colonT , cs)
lexToken′ ',' cs nothing  = just (commaT , cs)
lexToken′ '-' cs nothing  = numberToken Sign.- cs
lexToken′ '"' cs nothing  = Maybe.map (map₁ stringT) (lexBody cs)
lexToken′ c   cs nothing  = Maybe.map keywordToken (lexKeyword (c ∷ cs))

lexToken : List Char → Maybe (JSONToken × List Char)
lexToken []       = nothing
lexToken (c ∷ cs) = lexToken′ c cs (parseDigit c)

------------------------------------------------------------------------
-- Round trip
------------------------------------------------------------------------

private
  lexToken-digit : ∀ c cs d → parseDigit c ≡ just d →
                   lexToken (c ∷ cs) ≡ numberToken Sign.+ (c ∷ cs)
  lexToken-digit c cs d eq = cong (lexToken′ c cs) eq

  -- A number whose printed form starts with a digit is lexed by `lexNumber +`.
  lexToken-positive : ∀ i f e rest → NoLeadingNumCont rest →
    lexToken (printNumber (jsonNumber Sign.+ i f e) ++ rest)
      ≡ just (numberT (jsonNumber Sign.+ i f e) , rest)
  lexToken-positive i f e rest nc with printNat-head i (printFraction f ++ printExponent e)
  ... | d , cs , eqN =
    trans (subst (λ w → lexToken (w ++ rest) ≡ numberToken Sign.+ (w ++ rest))
                 (sym eqN)
                 (lexToken-digit (printDigit d) (cs ++ rest) d (parsePrintDigit d)))
          (cong (Maybe.map (map₁ numberT)) (correctLexNumberSign Sign.+ i f e rest nc))

lexToken-printToken : ∀ t rest → TokenFollow t rest →
  lexToken (printToken t ++ rest) ≡ just (t , rest)
lexToken-printToken lbraceT   rest _ = refl
lexToken-printToken rbraceT   rest _ = refl
lexToken-printToken lbracketT rest _ = refl
lexToken-printToken rbracketT rest _ = refl
lexToken-printToken colonT    rest _ = refl
lexToken-printToken commaT    rest _ = refl
lexToken-printToken nullT         rest _ = cong (Maybe.map keywordToken) (lexKeyword-print nullK rest)
lexToken-printToken (boolT true)  rest _ = cong (Maybe.map keywordToken) (lexKeyword-print trueK rest)
lexToken-printToken (boolT false) rest _ = cong (Maybe.map keywordToken) (lexKeyword-print falseK rest)
lexToken-printToken (stringT s) rest _ =
  trans (cong (λ x → Maybe.map (map₁ stringT) (lexBody x))
              (++-assoc (printBody s) ('"' ∷ []) rest))
        (cong (Maybe.map (map₁ stringT)) (lexBody-printBody s rest))
lexToken-printToken (numberT (jsonNumber Sign.- i f e)) rest nc =
  cong (Maybe.map (map₁ numberT)) (correctLexNumberSign Sign.- i f e rest nc)
lexToken-printToken (numberT (jsonNumber Sign.+ i f e)) rest nc = lexToken-positive i f e rest nc

parseToken : List Char → Maybe JSONToken
parseToken cs = Maybe.map proj₁ (lexToken cs)

-- `tokenStage` (see `Data.JSON.Goals`).
tokenStage : RightInverse (setoid JSONToken) Chars
tokenStage = mkStage (setoid JSONToken) printToken parseToken nullT
  (cong printToken)
  (λ t → t , parseToken-print t , refl)
  where
  -- Every token's printed form is accepted with an empty continuation.
  -- A number followed by nothing satisfies `NoLeadingNumCont []`.
  follow-[] : ∀ t → TokenFollow t []
  follow-[] (numberT _) = tt , tt , tt
  follow-[] lbraceT     = tt
  follow-[] rbraceT     = tt
  follow-[] lbracketT   = tt
  follow-[] rbracketT   = tt
  follow-[] colonT      = tt
  follow-[] commaT      = tt
  follow-[] nullT       = tt
  follow-[] (boolT _)   = tt
  follow-[] (stringT _) = tt

  parseToken-print : ∀ t → parseToken (printToken t) ≡ just t
  parseToken-print t =
    subst (λ cs → parseToken cs ≡ just t) (++-identityʳ (printToken t))
          (cong (Maybe.map proj₁) (lexToken-printToken t [] (follow-[] t)))
