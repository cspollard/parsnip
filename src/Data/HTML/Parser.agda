{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The recursive-descent parser from tokens to a tree
--
-- Fuel-bounded recursive descent over `HToken`s, in the style of
-- `Data.CSS.Parser`.  The fuel invariant is "fuel ≥ number of tokens
-- consumed" (and one more in the loop over children, for the call that
-- finds the end tag or the end of the stream).
--
-- * `parseFollows` reads children, each with its trailing text, up to an
--   end tag or the end (which it leaves);
-- * `parseElem` reads one element from its first token: a self-closing
--   tag is a void element, a `rawT` a raw one, and a start tag is the
--   leading text, the children and the matching end tag.
--
-- The parser checks what the AST needs (valid names and attributes, the
-- kind of element, valid text) when it builds a node, and fails
-- otherwise.  `parseTokens-tokensElem` shows it inverts `tokensElem`.
------------------------------------------------------------------------

module Data.HTML.Parser where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.XML.Valid using (Name; Text; Attributes; isValidText; eqName)
open import Data.XML.Token using (openT; selfT; closeT; textT)
open import Data.HTML.Valid
open import Data.HTML.AST
open import Data.HTML.Token
open import Data.HTML.Lexer using (isText)
open import Data.HTML.Tokens

------------------------------------------------------------------------
-- The parser
------------------------------------------------------------------------

-- Continue when a decidable check holds.
checked : ∀ {A : Set} (b : Bool) → (T b → Maybe A) → Maybe A
checked true  k = k tt
checked false _ = nothing

mkVoid : Name → Attributes → Maybe Elem
mkVoid n as = checked (okVoid n as) λ p → just (void n as p)

mkRaw : Name → Attributes → Text → Maybe Elem
mkRaw n as b = checked (okRaw n as b) λ p → just (raw n as b p)

mkElem : Name → Attributes → Text → List Follow → Maybe Elem
mkElem n as t cs = checked (okElem n as t) λ p → just (elem n as t cs p)

isCloser : HToken → Bool
isCloser (tok (closeT _)) = true
isCloser _                = false

-- Leading character data, which may be absent.
parseText : List HToken → Text × List HToken
parseText (tok (textT x) ∷ ts) = x , ts
parseText ts                   = [] , ts

consF : Follow → List Follow × List HToken → List Follow × List HToken
consF fo (fs , ts) = fo ∷ fs , ts

mutual
  -- Children, each with its trailing text, up to an end tag or the end.
  parseFollows : ℕ → List HToken → Maybe (List Follow × List HToken)
  parseFollows zero    _        = nothing
  parseFollows (suc f) []       = just ([] , [])
  parseFollows (suc f) (t ∷ ts) = parseFollows₁ f t ts (isCloser t)

  parseFollows₁ : ℕ → HToken → List HToken → Bool → Maybe (List Follow × List HToken)
  parseFollows₁ f t ts true  = just ([] , t ∷ ts)
  parseFollows₁ f t ts false = parseFollows₂ f (parseElem f t ts)

  parseFollows₂ : ℕ → Maybe (Elem × List HToken) → Maybe (List Follow × List HToken)
  parseFollows₂ f nothing          = nothing
  parseFollows₂ f (just (e , ts)) = parseFollows₃ f e (parseText ts)

  parseFollows₃ : ℕ → Elem → Text × List HToken → Maybe (List Follow × List HToken)
  parseFollows₃ f e (x , ts) =
    checked (isValidText x) λ p → Maybe.map (consF (follow e x p)) (parseFollows f ts)

  -- One element, the first token given separately.
  parseElem : ℕ → HToken → List HToken → Maybe (Elem × List HToken)
  parseElem f (tok (openT n as)) ts = parseOpen₁ n as (parseContent f ts)
  parseElem f (tok (selfT n as)) ts = Maybe.map (λ e → e , ts) (mkVoid n as)
  parseElem f (tok (closeT _))   ts = nothing
  parseElem f (tok (textT _))    ts = nothing
  parseElem f (rawT n as b)      ts = Maybe.map (λ e → e , ts) (mkRaw n as b)

  parseContent : ℕ → List HToken → Maybe (Text × List Follow × List HToken)
  parseContent f ts = parseContent₁ f (parseText ts)

  parseContent₁ : ℕ → Text × List HToken → Maybe (Text × List Follow × List HToken)
  parseContent₁ f (x , ts) = Maybe.map (λ r → x , r) (parseFollows f ts)

  parseOpen₁ : Name → Attributes → Maybe (Text × List Follow × List HToken) → Maybe (Elem × List HToken)
  parseOpen₁ n as (just (x , cs , tok (closeT m) ∷ ts)) = parseOpen₂ n as x cs ts (eqName n m)
  parseOpen₁ n as _                                     = nothing

  parseOpen₂ : Name → Attributes → Text → List Follow → List HToken → Bool → Maybe (Elem × List HToken)
  parseOpen₂ n as x cs ts true  = Maybe.map (λ e → e , ts) (mkElem n as x cs)
  parseOpen₂ n as x cs ts false = nothing

parseHead : ℕ → List HToken → Maybe (Elem × List HToken)
parseHead f []       = nothing
parseHead f (t ∷ ts) = parseElem f t ts

parseWhole : Maybe (Elem × List HToken) → Maybe Elem
parseWhole (just (e , [])) = just e
parseWhole _               = nothing

-- A complete token stream is one element.
parseTokens : List HToken → Maybe Elem
parseTokens ts = parseWhole (parseHead (suc (length ts)) ts)

------------------------------------------------------------------------
-- Facts about the tokens of a tree
------------------------------------------------------------------------

-- The stream is empty or starts with an end tag.
StopsAt : List HToken → Set
StopsAt []      = ⊤
StopsAt (t ∷ _) = isCloser t ≡ true

-- The stream does not start with character data.
NotText : List HToken → Set
NotText []      = ⊤
NotText (t ∷ _) = isText t ≡ false

private
  checked-T : ∀ {A : Set} b (p : T b) (k : T b → Maybe A) → checked b k ≡ k p
  checked-T true  p k = refl
  checked-T false () k

  -- The tokens of an element start with a token that is neither an end
  -- tag nor character data.
  head-tokensElem : ∀ e → ∃ λ t → ∃ λ ts → tokensElem e ≡ t ∷ ts × isCloser t ≡ false × isText t ≡ false
  head-tokensElem (void n as _)       = tok (selfT n as) , [] , refl , refl , refl
  head-tokensElem (raw n as b _)      = rawT n as b , [] , refl , refl , refl
  head-tokensElem (elem n as t cs _)  = tok (openT n as) , _ , refl , refl , refl

  len-pos : ∀ e → ∃ λ a → length (tokensElem e) ≡ suc a
  len-pos e with head-tokensElem e
  ... | t , ts , eq , _ = length ts , cong length eq

  stops⇒notText : ∀ rest → StopsAt rest → NotText rest
  stops⇒notText []       _ = tt
  stops⇒notText (tok (closeT _) ∷ _) _ = refl
  stops⇒notText (tok (openT _ _) ∷ _) ()
  stops⇒notText (tok (selfT _ _) ∷ _) ()
  stops⇒notText (tok (textT _) ∷ _)   ()
  stops⇒notText (rawT _ _ _ ∷ _)      ()

  -- Not starting with text, after any children.
  notText-follows : ∀ fs rest → StopsAt rest → NotText (tokensFollows fs ++ rest)
  notText-follows []                  rest st = stops⇒notText rest st
  notText-follows (follow e t _ ∷ fs) rest st with head-tokensElem e
  ... | t₀ , ts , eq , _ , nt = subst (λ L → NotText ((L ++ (textTokens t ++ tokensFollows fs)) ++ rest)) (sym eq) nt

  parseText-text : ∀ x xs rest → NotText rest →
                   parseText (textTokens (x ∷ xs) ++ rest) ≡ ((x ∷ xs) , rest)
  parseText-text x xs rest _ = refl

  parseText-none : ∀ rest → NotText rest → parseText rest ≡ ([] , rest)
  parseText-none []                    _ = refl
  parseText-none (tok (openT _ _) ∷ _) _ = refl
  parseText-none (tok (selfT _ _) ∷ _) _ = refl
  parseText-none (tok (closeT _)  ∷ _) _ = refl
  parseText-none (tok (textT _)   ∷ _) ()
  parseText-none (rawT _ _ _      ∷ _) _ = refl

  parseText-print : ∀ t rest → NotText rest → parseText (textTokens t ++ rest) ≡ (t , rest)
  parseText-print []       rest nt = parseText-none rest nt
  parseText-print (x ∷ xs) rest nt = refl

  parseFollows-nil : ∀ f rest → StopsAt rest → parseFollows (suc f) rest ≡ just ([] , rest)
  parseFollows-nil f []       _ = refl
  parseFollows-nil f (t ∷ ts) h = cong (parseFollows₁ f t ts) h

------------------------------------------------------------------------
-- The parser inverts `tokensElem`
------------------------------------------------------------------------

-- What the induction proves about each element.
Print-ok : Elem → Set
Print-ok e = ∀ rest fuel → length (tokensElem e) ≤ fuel →
             parseHead fuel (tokensElem e ++ rest) ≡ just (e , rest)

private
  -- The content of an element is read back, up to its end tag.
  parseContent-print : ∀ t cs n rest fuel →
    (∀ rest′ → StopsAt rest′ → ∀ fuel′ → suc (length (tokensFollows cs)) ≤ fuel′ →
       parseFollows fuel′ (tokensFollows cs ++ rest′) ≡ just (cs , rest′)) →
    suc (length (tokensFollows cs)) ≤ fuel →
    parseContent fuel (textTokens t ++ (tokensFollows cs ++ tok (closeT n) ∷ rest))
      ≡ just (t , cs , tok (closeT n) ∷ rest)
  parseContent-print t cs n rest fuel follows lt =
    trans (cong (parseContent₁ fuel) (parseText-print t (tokensFollows cs ++ tok (closeT n) ∷ rest)
                                        (notText-follows cs (tok (closeT n) ∷ rest) refl)))
          (cong (Maybe.map (λ r → t , r)) (follows (tok (closeT n) ∷ rest) refl fuel lt))

mutual
  parseElem-print : ∀ e → Print-ok e
  parseElem-print (void n as p) rest fuel _ =
    cong (Maybe.map (λ e → e , rest)) (checked-T _ p _)
  parseElem-print (raw n as b p) rest fuel _ =
    cong (Maybe.map (λ e → e , rest)) (checked-T _ p _)
  parseElem-print (elem n as t cs p) rest fuel le =
    trans (cong (λ L → parseOpen₁ n as (parseContent fuel L)) eqL)
    (trans (cong (parseOpen₁ n as) (parseContent-print t cs n rest fuel (parseFollows-print cs) fl))
    (trans (cong (λ b → parseOpen₂ n as t cs rest b) (eqName-refl n))
           (cong (Maybe.map (λ e → e , rest)) (checked-T _ p _))))
    where
    eqL : (textTokens t ++ tokensFollows cs ++ tok (closeT n) ∷ []) ++ rest
          ≡ textTokens t ++ (tokensFollows cs ++ tok (closeT n) ∷ rest)
    eqL = trans (++-assoc (textTokens t) (tokensFollows cs ++ tok (closeT n) ∷ []) rest)
                (cong (textTokens t ++_) (++-assoc (tokensFollows cs) (tok (closeT n) ∷ []) rest))

    l1 : length (tokensFollows cs) ≤ length (textTokens t ++ tokensFollows cs ++ tok (closeT n) ∷ [])
    l1 = subst (length (tokensFollows cs) ≤_)
               (sym (trans (length-++ (textTokens t)) (cong (length (textTokens t) +_) (length-++ (tokensFollows cs)))))
               (≤-trans (m≤m+n (length (tokensFollows cs)) 1)
                        (m≤n+m (length (tokensFollows cs) + 1) (length (textTokens t))))

    fl : suc (length (tokensFollows cs)) ≤ fuel
    fl = ≤-trans (s≤s l1) le

  -- A list of children, then an end tag or the end, is read back.
  parseFollows-print : ∀ cs rest → StopsAt rest → ∀ fuel → suc (length (tokensFollows cs)) ≤ fuel →
                       parseFollows fuel (tokensFollows cs ++ rest) ≡ just (cs , rest)
  parseFollows-print []       rest st zero    ()
  parseFollows-print []       rest st (suc f) _  = parseFollows-nil f rest st
  parseFollows-print (c ∷ cs) rest st zero    ()
  parseFollows-print (follow e t hv ∷ fs) rest st (suc f) (s≤s lt) with head-tokensElem e | len-pos e
  ... | t₀ , ts , eq , nc , nt | a , lenE =
    subst (λ L → parseFollows (suc f) L ≡ just (follow e t hv ∷ fs , rest)) (sym eqL) main
    where
    E T′ F : List HToken
    E  = tokensElem e
    T′ = textTokens t
    F  = tokensFollows fs

    R : List HToken
    R = T′ ++ (F ++ rest)

    eqL : (E ++ T′ ++ F) ++ rest ≡ t₀ ∷ (ts ++ R)
    eqL = trans (++-assoc E (T′ ++ F) rest)
                (trans (cong (E ++_) (++-assoc T′ F rest)) (cong (_++ R) eq))

    lt₁ : length E + (length T′ + length F) ≤ f
    lt₁ = subst (_≤ f) (cong (length E +_) (length-++ T′)) (subst (_≤ f) (length-++ E) lt′)
      where
      lt′ : length (E ++ T′ ++ F) ≤ f
      lt′ = lt

    fv : length E ≤ f
    fv = ≤-trans (m≤m+n (length E) (length T′ + length F)) lt₁

    fl : suc (length F) ≤ f
    fl = ≤-trans (s≤s (≤-trans (m≤n+m (length F) (length T′))
                               (m≤n+m (length T′ + length F) a)))
                 (subst (λ n → n + (length T′ + length F) ≤ f) lenE lt₁)

    pe : parseElem f t₀ (ts ++ R) ≡ just (e , R)
    pe = subst (λ L → parseHead f L ≡ just (e , R)) (cong (_++ R) eq) (parseElem-print e R f fv)

    pf : parseFollows f (F ++ rest) ≡ just (fs , rest)
    pf = parseFollows-print fs rest st f fl

    main : parseFollows (suc f) (t₀ ∷ (ts ++ R)) ≡ just (follow e t hv ∷ fs , rest)
    main =
      trans (cong (parseFollows₁ f t₀ (ts ++ R)) nc)
      (trans (cong (parseFollows₂ f) pe)
      (trans (cong (parseFollows₃ f e) (parseText-print t (F ++ rest) (notText-follows fs rest st)))
      (trans (checked-T _ hv _)
             (cong (Maybe.map (consF (follow e t hv))) pf))))

parseTokens-tokensElem : ∀ e → parseTokens (tokensElem e) ≡ just e
parseTokens-tokensElem e =
  cong parseWhole
    (subst (λ L → parseHead (suc (length (tokensElem e))) L ≡ just (e , []))
           (++-identityʳ (tokensElem e))
           (parseElem-print e [] (suc (length (tokensElem e))) (n≤1+n′ (length (tokensElem e)))))
  where
  n≤1+n′ : ∀ n → n ≤ suc n
  n≤1+n′ zero    = z≤n
  n≤1+n′ (suc n) = s≤s (n≤1+n′ n)
