{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- CSS selectors (Level 2): a grammar on top of component values
--
-- A selector list is read from the prelude of a qualified rule
-- (`Data.CSS.Rule`), a list of component values (`Data.CSS.AST`):
--
--   selector list = complex (`,` complex)*
--   complex       = compound (combinator compound)*
--   compound      = [type | `*`] simple*        (not empty)
--   simple        = `.class` | `#id` | `[attr]` | `[attr op "value"]`
--                 | `:pseudo` | `::pseudo-element` | `:fn(args)`
--   combinator    = white space | `>` | `+` | `~`
--
-- This is the strict canonical form that the printer writes: no white
-- space around `>`, `+`, `~` or `,`, attribute values are strings, and
-- the arguments of functional pseudo-classes are kept as component
-- values.  `parseSelectorList (printSelectorList s) ≡ just s` is proved.
-- The tree needs no evidence beyond what the component values carry (the
-- parser reuses the evidence found in the input).
------------------------------------------------------------------------

module Data.CSS.Selector where

open import Data.Bool using (T)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_; length; concatMap)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; m≤n+m; m≤m+n; n≤1+n)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.CSS.Valid using (Name; Text; isValidIdent; isValidHash; isValidText; isDelimChar)
open import Data.CSS.Token
open import Data.CSS.AST

------------------------------------------------------------------------
-- The syntax tree
------------------------------------------------------------------------

-- Attribute operators: `=`, `~=`, `|=`, `^=`, `$=`, `*=`.
data Op : Set where
  eqO includesO dashO prefixO suffixO substringO : Op

data Simple : Set where
  classS  : (n : Name) → T (isValidIdent n) → Simple
  idS     : (n : Name) → T (isValidHash n) → Simple
  attrP   : (n : Name) → T (isValidIdent n) → Simple
  attrV   : (n : Name) → T (isValidIdent n) → Op → (v : Text) → T (isValidText v) → Simple
  pseudoC : (n : Name) → T (isValidIdent n) → Simple
  pseudoE : (n : Name) → T (isValidIdent n) → Simple
  pseudoF : (n : Name) → T (isValidIdent n) → List CV → Simple

data Head : Set where
  typeH      : (n : Name) → T (isValidIdent n) → Head
  universalH : Head

data Compound : Set where
  withHead  : Head → List Simple → Compound
  tailsOnly : Simple → List Simple → Compound

data Comb : Set where
  descendant child nextSibling subsequent : Comb

Complex : Set
Complex = Compound × List (Comb × Compound)

-- A non-empty list of complex selectors.
SelectorList : Set
SelectorList = Complex × List Complex

------------------------------------------------------------------------
-- Printing, to component values
------------------------------------------------------------------------

delimCV : (c : Char) {p : T (isDelimChar c)} → CV
delimCV c {p} = leaf (delimT c) p

colonCV commaCV wsCV : CV
colonCV = leaf colonT _
commaCV = leaf commaT _
wsCV    = leaf wsT _

opCVs : Op → List CV
opCVs eqO        = delimCV '=' ∷ []
opCVs includesO  = delimCV '~' ∷ delimCV '=' ∷ []
opCVs dashO      = delimCV '|' ∷ delimCV '=' ∷ []
opCVs prefixO    = delimCV '^' ∷ delimCV '=' ∷ []
opCVs suffixO    = delimCV '$' ∷ delimCV '=' ∷ []
opCVs substringO = delimCV '*' ∷ delimCV '=' ∷ []

printSimple : Simple → List CV
printSimple (classS n h)        = delimCV '.' ∷ leaf (identT n) h ∷ []
printSimple (idS n h)           = leaf (hashT n) h ∷ []
printSimple (attrP n h)         = bracket (leaf (identT n) h ∷ []) ∷ []
printSimple (attrV n h op v hv) =
  bracket (leaf (identT n) h ∷ opCVs op ++ leaf (stringT v) hv ∷ []) ∷ []
printSimple (pseudoC n h)       = colonCV ∷ leaf (identT n) h ∷ []
printSimple (pseudoE n h)       = colonCV ∷ colonCV ∷ leaf (identT n) h ∷ []
printSimple (pseudoF n h as)    = colonCV ∷ func n h as ∷ []

printTails : List Simple → List CV
printTails = concatMap printSimple

printHead : Head → List CV
printHead (typeH n h) = leaf (identT n) h ∷ []
printHead universalH  = delimCV '*' ∷ []

printCompound : Compound → List CV
printCompound (withHead h ts)  = printHead h ++ printTails ts
printCompound (tailsOnly s ts) = printSimple s ++ printTails ts

printComb : Comb → CV
printComb descendant  = wsCV
printComb child       = delimCV '>'
printComb nextSibling = delimCV '+'
printComb subsequent  = delimCV '~'

printCombs : List (Comb × Compound) → List CV
printCombs []              = []
printCombs ((k , c) ∷ kcs) = printComb k ∷ printCompound c ++ printCombs kcs

printComplex : Complex → List CV
printComplex (c , kcs) = printCompound c ++ printCombs kcs

printMore : List Complex → List CV
printMore []         = []
printMore (cx ∷ cxs) = commaCV ∷ printComplex cx ++ printMore cxs

printSelectorList : SelectorList → List CV
printSelectorList (cx , cxs) = printComplex cx ++ printMore cxs

------------------------------------------------------------------------
-- Parsing
------------------------------------------------------------------------

parseOp : List CV → Maybe (Op × List CV)
parseOp (leaf (delimT '=') _ ∷ r)                       = just (eqO , r)
parseOp (leaf (delimT '~') _ ∷ leaf (delimT '=') _ ∷ r) = just (includesO , r)
parseOp (leaf (delimT '|') _ ∷ leaf (delimT '=') _ ∷ r) = just (dashO , r)
parseOp (leaf (delimT '^') _ ∷ leaf (delimT '=') _ ∷ r) = just (prefixO , r)
parseOp (leaf (delimT '$') _ ∷ leaf (delimT '=') _ ∷ r) = just (suffixO , r)
parseOp (leaf (delimT '*') _ ∷ leaf (delimT '=') _ ∷ r) = just (substringO , r)
parseOp _                                               = nothing

parseAttrV : (n : Name) → T (isValidIdent n) → Maybe (Op × List CV) → Maybe Simple
parseAttrV n h (just (op , leaf (stringT v) hv ∷ [])) = just (attrV n h op v hv)
parseAttrV n h _                                      = nothing

-- The inside of `[ ]`.
parseAttr : List CV → Maybe Simple
parseAttr (leaf (identT n) h ∷ []) = just (attrP n h)
parseAttr (leaf (identT n) h ∷ r)  = parseAttrV n h (parseOp r)
parseAttr _                        = nothing

consS : Simple → List Simple × List CV → List Simple × List CV
consS s (ss , r) = s ∷ ss , r

mutual
  -- The simple selectors at the front, and the rest.
  parseTails : List CV → Maybe (List Simple × List CV)
  parseTails (leaf (delimT '.') _ ∷ leaf (identT n) h ∷ r) = parseTailsThen (classS n h) r
  parseTails (leaf (hashT n) h ∷ r)                        = parseTailsThen (idS n h) r
  parseTails (bracket vs ∷ r)                              = parseTailsAttr (parseAttr vs) r
  parseTails (leaf colonT _ ∷ leaf colonT _ ∷ leaf (identT n) h ∷ r) = parseTailsThen (pseudoE n h) r
  parseTails (leaf colonT _ ∷ leaf (identT n) h ∷ r)       = parseTailsThen (pseudoC n h) r
  parseTails (leaf colonT _ ∷ func n h as ∷ r)             = parseTailsThen (pseudoF n h as) r
  parseTails r                                             = just ([] , r)

  parseTailsThen : Simple → List CV → Maybe (List Simple × List CV)
  parseTailsThen s r = Maybe.map (consS s) (parseTails r)

  parseTailsAttr : Maybe Simple → List CV → Maybe (List Simple × List CV)
  parseTailsAttr (just s) r = parseTailsThen s r
  parseTailsAttr nothing  r = nothing

withHeadOf : Head → List Simple × List CV → Compound × List CV
withHeadOf h (ts , r) = withHead h ts , r

tailsOnlyOf : Maybe (List Simple × List CV) → Maybe (Compound × List CV)
tailsOnlyOf (just (s ∷ ts , r)) = just (tailsOnly s ts , r)
tailsOnlyOf _                   = nothing

parseCompound : List CV → Maybe (Compound × List CV)
parseCompound (leaf (identT n) h ∷ r)   = Maybe.map (withHeadOf (typeH n h)) (parseTails r)
parseCompound (leaf (delimT '*') _ ∷ r) = Maybe.map (withHeadOf universalH) (parseTails r)
parseCompound r                         = tailsOnlyOf (parseTails r)

combOf : CV → Maybe Comb
combOf (leaf wsT _)         = just descendant
combOf (leaf (delimT '>') _) = just child
combOf (leaf (delimT '+') _) = just nextSibling
combOf (leaf (delimT '~') _) = just subsequent
combOf _                    = nothing

consC : Comb × Compound → List (Comb × Compound) × List CV → List (Comb × Compound) × List CV
consC kc (kcs , r) = kc ∷ kcs , r

-- The first argument is fuel: each combinator consumes a value.
mutual
  parseCombs : ℕ → List CV → Maybe (List (Comb × Compound) × List CV)
  parseCombs zero    _        = nothing
  parseCombs (suc f) []       = just ([] , [])
  parseCombs (suc f) (c ∷ r)  = parseCombs₁ f c r (combOf c)

  parseCombs₁ : ℕ → CV → List CV → Maybe Comb → Maybe (List (Comb × Compound) × List CV)
  parseCombs₁ f c r (just k) = parseCombs₂ k f (parseCompound r)
  parseCombs₁ f c r nothing  = just ([] , c ∷ r)

  parseCombs₂ : Comb → ℕ → Maybe (Compound × List CV) → Maybe (List (Comb × Compound) × List CV)
  parseCombs₂ k f (just (cp , r)) = Maybe.map (consC (k , cp)) (parseCombs f r)
  parseCombs₂ k f nothing         = nothing

parseComplex₂ : Compound → Maybe (List (Comb × Compound) × List CV) → Maybe (Complex × List CV)
parseComplex₂ c (just (kcs , r)) = just ((c , kcs) , r)
parseComplex₂ c nothing          = nothing

parseComplex₁ : ℕ → Maybe (Compound × List CV) → Maybe (Complex × List CV)
parseComplex₁ f (just (c , r)) = parseComplex₂ c (parseCombs f r)
parseComplex₁ f nothing        = nothing

parseComplex : ℕ → List CV → Maybe (Complex × List CV)
parseComplex f ws = parseComplex₁ f (parseCompound ws)

consX : Complex → List Complex × List CV → List Complex × List CV
consX cx (cxs , r) = cx ∷ cxs , r

mutual
  parseMore : ℕ → List CV → Maybe (List Complex × List CV)
  parseMore zero    _                     = nothing
  parseMore (suc f) (leaf commaT _ ∷ r)   = parseMore₁ f (parseComplex f r)
  parseMore (suc f) r                     = just ([] , r)

  parseMore₁ : ℕ → Maybe (Complex × List CV) → Maybe (List Complex × List CV)
  parseMore₁ f (just (cx , r)) = Maybe.map (consX cx) (parseMore f r)
  parseMore₁ f nothing         = nothing

parseSel₁ : ℕ → Maybe (Complex × List CV) → Maybe (SelectorList × List CV)
parseSel₁ f (just (cx , r)) = Maybe.map (λ { (cxs , r′) → (cx , cxs) , r′ }) (parseMore f r)
parseSel₁ f nothing         = nothing

parseWhole : Maybe (SelectorList × List CV) → Maybe SelectorList
parseWhole (just (s , [])) = just s
parseWhole _               = nothing

parseSelectorList : List CV → Maybe SelectorList
parseSelectorList ws = parseWhole (parseSel₁ (suc (length ws)) (parseComplex (suc (length ws)) ws))

------------------------------------------------------------------------
-- Round trip
------------------------------------------------------------------------

-- What may follow a compound.
data Boundary : List CV → Set where
  endB   : Boundary []
  wsB    : ∀ {r} → Boundary (wsCV ∷ r)
  gtB    : ∀ {r} → Boundary (delimCV '>' ∷ r)
  plusB  : ∀ {r} → Boundary (delimCV '+' ∷ r)
  tildeB : ∀ {r} → Boundary (delimCV '~' ∷ r)
  commaB : ∀ {r} → Boundary (commaCV ∷ r)

-- What may follow a complex selector.
data ComplexEnd : List CV → Set where
  endE   : ComplexEnd []
  commaE : ∀ {r} → ComplexEnd (commaCV ∷ r)

private
  ce⇒b : ∀ {r} → ComplexEnd r → Boundary r
  ce⇒b endE   = endB
  ce⇒b commaE = commaB

  boundary-combs : ∀ kcs rest → ComplexEnd rest → Boundary (printCombs kcs ++ rest)
  boundary-combs []                    rest ce = ce⇒b ce
  boundary-combs ((descendant , c) ∷ _)  rest ce = wsB
  boundary-combs ((child , c) ∷ _)       rest ce = gtB
  boundary-combs ((nextSibling , c) ∷ _) rest ce = plusB
  boundary-combs ((subsequent , c) ∷ _)  rest ce = tildeB

  complexEnd-more : ∀ cxs → ComplexEnd (printMore cxs)
  complexEnd-more []        = endE
  complexEnd-more (_ ∷ _)   = commaE

  parseTails-stop : ∀ {r} → Boundary r → parseTails r ≡ just ([] , r)
  parseTails-stop endB    = refl
  parseTails-stop wsB     = refl
  parseTails-stop gtB     = refl
  parseTails-stop plusB   = refl
  parseTails-stop tildeB  = refl
  parseTails-stop commaB  = refl

  parseAttr-print : ∀ n h op v hv →
    parseAttr (leaf (identT n) h ∷ opCVs op ++ leaf (stringT v) hv ∷ []) ≡ just (attrV n h op v hv)
  parseAttr-print n h eqO        v hv = refl
  parseAttr-print n h includesO  v hv = refl
  parseAttr-print n h dashO      v hv = refl
  parseAttr-print n h prefixO    v hv = refl
  parseAttr-print n h suffixO    v hv = refl
  parseAttr-print n h substringO v hv = refl

  parseTails-print : ∀ ts rest → Boundary rest →
                     parseTails (printTails ts ++ rest) ≡ just (ts , rest)
  parseTails-print []        rest b = parseTails-stop b
  parseTails-print (classS n h ∷ ts) rest b =
    cong (Maybe.map (consS (classS n h))) (parseTails-print ts rest b)
  parseTails-print (idS n h ∷ ts) rest b =
    cong (Maybe.map (consS (idS n h))) (parseTails-print ts rest b)
  parseTails-print (attrP n h ∷ ts) rest b =
    cong (Maybe.map (consS (attrP n h))) (parseTails-print ts rest b)
  parseTails-print (attrV n h op v hv ∷ ts) rest b =
    trans (cong (λ x → parseTailsAttr x (printTails ts ++ rest)) (parseAttr-print n h op v hv))
          (cong (Maybe.map (consS (attrV n h op v hv))) (parseTails-print ts rest b))
  parseTails-print (pseudoC n h ∷ ts) rest b =
    cong (Maybe.map (consS (pseudoC n h))) (parseTails-print ts rest b)
  parseTails-print (pseudoE n h ∷ ts) rest b =
    cong (Maybe.map (consS (pseudoE n h))) (parseTails-print ts rest b)
  parseTails-print (pseudoF n h as ∷ ts) rest b =
    cong (Maybe.map (consS (pseudoF n h as))) (parseTails-print ts rest b)

  parseCompound-print : ∀ c rest → Boundary rest →
                        parseCompound (printCompound c ++ rest) ≡ just (c , rest)
  parseCompound-print (withHead (typeH n h) ts) rest b =
    cong (Maybe.map (withHeadOf (typeH n h))) (parseTails-print ts rest b)
  parseCompound-print (withHead universalH ts) rest b =
    cong (Maybe.map (withHeadOf universalH)) (parseTails-print ts rest b)
  parseCompound-print (tailsOnly (classS n h) ts) rest b =
    cong tailsOnlyOf (parseTails-print (classS n h ∷ ts) rest b)
  parseCompound-print (tailsOnly (idS n h) ts) rest b =
    cong tailsOnlyOf (parseTails-print (idS n h ∷ ts) rest b)
  parseCompound-print (tailsOnly (attrP n h) ts) rest b =
    cong tailsOnlyOf (parseTails-print (attrP n h ∷ ts) rest b)
  parseCompound-print (tailsOnly (attrV n h op v hv) ts) rest b =
    cong tailsOnlyOf (parseTails-print (attrV n h op v hv ∷ ts) rest b)
  parseCompound-print (tailsOnly (pseudoC n h) ts) rest b =
    cong tailsOnlyOf (parseTails-print (pseudoC n h ∷ ts) rest b)
  parseCompound-print (tailsOnly (pseudoE n h) ts) rest b =
    cong tailsOnlyOf (parseTails-print (pseudoE n h ∷ ts) rest b)
  parseCompound-print (tailsOnly (pseudoF n h as) ts) rest b =
    cong tailsOnlyOf (parseTails-print (pseudoF n h as ∷ ts) rest b)

  combOf-print : ∀ k → combOf (printComb k) ≡ just k
  combOf-print descendant  = refl
  combOf-print child       = refl
  combOf-print nextSibling = refl
  combOf-print subsequent  = refl

  -- Fuel for the rest of the combinators.
  fuel-tail : ∀ (C K : List CV) f → suc (length (C ++ K)) ≤ f → suc (length K) ≤ f
  fuel-tail C K f lt =
    ≤-trans (s≤s (subst (length K ≤_) (sym (length-++ C)) (m≤n+m (length K) (length C)))) lt

  parseCombs-print : ∀ kcs rest → ComplexEnd rest → ∀ fuel →
                     suc (length (printCombs kcs)) ≤ fuel →
                     parseCombs fuel (printCombs kcs ++ rest) ≡ just (kcs , rest)
  parseCombs-print kcs rest ce zero ()
  parseCombs-print [] .[] endE (suc f) _ = refl
  parseCombs-print [] .(commaCV ∷ _) commaE (suc f) _ = refl
  parseCombs-print ((k , c) ∷ kcs) rest ce (suc f) (s≤s lt) =
    subst (λ L → parseCombs (suc f) (printComb k ∷ L) ≡ just ((k , c) ∷ kcs , rest))
          (sym (++-assoc (printCompound c) (printCombs kcs) rest))
          (trans (cong (λ m → parseCombs₁ f (printComb k) _ m) (combOf-print k))
          (trans (cong (parseCombs₂ k f)
                       (parseCompound-print c (printCombs kcs ++ rest) (boundary-combs kcs rest ce)))
                 (cong (Maybe.map (consC (k , c)))
                       (parseCombs-print kcs rest ce f (fuel-tail (printCompound c) (printCombs kcs) f lt)))))

  parseComplex-print : ∀ cx rest → ComplexEnd rest → ∀ fuel →
                       suc (length (printComplex cx)) ≤ fuel →
                       parseComplex fuel (printComplex cx ++ rest) ≡ just (cx , rest)
  parseComplex-print (c , kcs) rest ce fuel lt =
    subst (λ L → parseComplex fuel L ≡ just ((c , kcs) , rest))
          (sym (++-assoc (printCompound c) (printCombs kcs) rest))
          (trans (cong (parseComplex₁ fuel)
                       (parseCompound-print c (printCombs kcs ++ rest) (boundary-combs kcs rest ce)))
                 (cong (parseComplex₂ c)
                       (parseCombs-print kcs rest ce fuel (fuel-tail (printCompound c) (printCombs kcs) fuel lt))))

  parseMore-print : ∀ cxs fuel → suc (length (printMore cxs)) ≤ fuel →
                    parseMore fuel (printMore cxs) ≡ just (cxs , [])
  parseMore-print cxs zero ()
  parseMore-print []        (suc f) _ = refl
  parseMore-print (cx ∷ cxs) (suc f) (s≤s lt) =
    trans (cong (parseMore₁ f)
                (parseComplex-print cx (printMore cxs) (complexEnd-more cxs) f
                   (≤-trans (s≤s (m≤m+n (length (printComplex cx)) (length (printMore cxs))))
                            (subst (λ n → suc n ≤ f) (length-++ (printComplex cx) {printMore cxs}) lt′))))
          (cong (Maybe.map (consX cx))
                (parseMore-print cxs f
                   (≤-trans (s≤s (m≤n+m (length (printMore cxs)) (length (printComplex cx))))
                            (subst (λ n → suc n ≤ f) (length-++ (printComplex cx) {printMore cxs}) lt′))))
    where
    lt′ : suc (length (printComplex cx ++ printMore cxs)) ≤ f
    lt′ = lt

parseSelectorList-print : ∀ s → parseSelectorList (printSelectorList s) ≡ just s
parseSelectorList-print (cx , cxs) =
  cong parseWhole
    (trans (cong (parseSel₁ F) (parseComplex-print cx (printMore cxs) (complexEnd-more cxs) F l₁))
           (cong (Maybe.map (λ { (cxs′ , r′) → (cx , cxs′) , r′ }))
                 (parseMore-print cxs F l₂)))
  where
  F : ℕ
  F = suc (length (printComplex cx ++ printMore cxs))

  l₁ : suc (length (printComplex cx)) ≤ F
  l₁ = s≤s (subst (length (printComplex cx) ≤_) (sym (length-++ (printComplex cx) {printMore cxs}))
                  (m≤m+n (length (printComplex cx)) (length (printMore cxs))))

  l₂ : suc (length (printMore cxs)) ≤ F
  l₂ = s≤s (subst (length (printMore cxs) ≤_) (sym (length-++ (printComplex cx) {printMore cxs}))
                  (m≤n+m (length (printMore cxs)) (length (printComplex cx))))
