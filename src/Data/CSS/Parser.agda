{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The recursive-descent parser from tokens to component values
--
-- `parseList` is fuel-bounded recursive descent over `CToken`s that are
-- not comments.  The fuel invariant is "fuel ≥ number of tokens consumed"
-- (and, in the loop over a list, one more, for the call that finds the
-- closing bracket or the end).  A list of component values runs up to a
-- closing bracket (which it leaves) or the end of the stream; a block or
-- function is its opening token, a list, and the matching closer.  The
-- parser checks what the AST needs (a well-formed leaf token, a legal
-- function name) when it builds a node, and fails otherwise.
--
-- `parseTokens-tokensList` shows the parser inverts `tokensList`, whatever
-- tokens follow (up to a closer), and `parseTokens-printTokens` that it
-- inverts `printTokens` once the comments are dropped.
------------------------------------------------------------------------

module Data.CSS.Parser where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++)
open import Data.Maybe as Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m; +-comm; +-monoˡ-≤; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.CSS.Valid using (Name; isValidIdent)
open import Data.CSS.Token
open import Data.CSS.AST
open import Data.CSS.Tokens

------------------------------------------------------------------------
-- The parser
------------------------------------------------------------------------

-- Continue when a decidable check holds.
checked : ∀ {A : Set} (b : Bool) → (T b → Maybe A) → Maybe A
checked true  k = k tt
checked false _ = nothing

mkLeaf : CToken → Maybe CV
mkLeaf t = checked (isLeaf t) λ p → just (leaf t p)

mkFunc : Name → List CV → Maybe CV
mkFunc n vs = checked (isValidIdent n) λ p → just (func n p vs)

isCloser : CToken → Bool
isCloser rparenT = true
isCloser rbrackT = true
isCloser rbraceT = true
isCloser _       = false

data Block : Set where
  parenB bracketB braceB : Block

mkBlock : Block → List CV → CV
mkBlock parenB   = paren
mkBlock bracketB = bracket
mkBlock braceB   = brace

closes : Block → CToken → Bool
closes parenB   rparenT = true
closes bracketB rbrackT = true
closes braceB   rbraceT = true
closes _        _       = false

consCV : CV → List CV × List CToken → List CV × List CToken
consCV v (vs , ts) = v ∷ vs , ts

mutual
  -- Component values up to a closing bracket or the end (which are left).
  parseList : ℕ → List CToken → Maybe (List CV × List CToken)
  parseList zero    _        = nothing
  parseList (suc f) []       = just ([] , [])
  parseList (suc f) (t ∷ ts) = parseList₁ f t ts (isCloser t)

  parseList₁ : ℕ → CToken → List CToken → Bool → Maybe (List CV × List CToken)
  parseList₁ f t ts true  = just ([] , t ∷ ts)
  parseList₁ f t ts false = parseCons f (parseCV f t ts)

  parseCons : ℕ → Maybe (CV × List CToken) → Maybe (List CV × List CToken)
  parseCons f nothing          = nothing
  parseCons f (just (v , ts)) = Maybe.map (consCV v) (parseList f ts)

  -- One component value, the first token given separately.
  parseCV : ℕ → CToken → List CToken → Maybe (CV × List CToken)
  parseCV f lparenT       ts = parseBlock f parenB ts
  parseCV f lbrackT       ts = parseBlock f bracketB ts
  parseCV f lbraceT       ts = parseBlock f braceB ts
  parseCV f (functionT n) ts = parseFunc f n ts
  parseCV f rparenT       ts = nothing
  parseCV f rbrackT       ts = nothing
  parseCV f rbraceT       ts = nothing
  parseCV f commentT      ts = nothing
  parseCV f t             ts = Maybe.map (λ v → v , ts) (mkLeaf t)

  parseBlock : ℕ → Block → List CToken → Maybe (CV × List CToken)
  parseBlock f b ts = parseBlock₁ b (parseList f ts)

  parseBlock₁ : Block → Maybe (List CV × List CToken) → Maybe (CV × List CToken)
  parseBlock₁ b (just (vs , c ∷ ts)) = parseBlock₂ b vs ts (closes b c)
  parseBlock₁ b _                    = nothing

  parseBlock₂ : Block → List CV → List CToken → Bool → Maybe (CV × List CToken)
  parseBlock₂ b vs ts true  = just (mkBlock b vs , ts)
  parseBlock₂ b vs ts false = nothing

  parseFunc : ℕ → Name → List CToken → Maybe (CV × List CToken)
  parseFunc f n ts = parseFunc₁ n (parseList f ts)

  parseFunc₁ : Name → Maybe (List CV × List CToken) → Maybe (CV × List CToken)
  parseFunc₁ n (just (vs , c ∷ ts)) = parseFunc₂ n vs ts (closes parenB c)
  parseFunc₁ n _                    = nothing

  parseFunc₂ : Name → List CV → List CToken → Bool → Maybe (CV × List CToken)
  parseFunc₂ n vs ts true  = Maybe.map (λ v → v , ts) (mkFunc n vs)
  parseFunc₂ n vs ts false = nothing

-- A complete token stream (without comments) is one list.
parseWhole : Maybe (List CV × List CToken) → Maybe CSS
parseWhole (just (vs , [])) = just vs
parseWhole _                = nothing

parseTokens : List CToken → Maybe CSS
parseTokens ts = parseWhole (parseList (suc (length ts)) ts)

-- The parser used on token streams that may contain comments.
parseCSS : List CToken → Maybe CSS
parseCSS ts = parseTokens (dropComments ts)

------------------------------------------------------------------------
-- Facts about the tokens of a tree
------------------------------------------------------------------------

-- The stream is empty or starts with a closer.
StopsAt : List CToken → Set
StopsAt []      = ⊤
StopsAt (t ∷ _) = isCloser t ≡ true

private
  toEq : ∀ {b} → T b → b ≡ true
  toEq {true} _ = refl

  checked-T : ∀ {A : Set} b (p : T b) (k : T b → Maybe A) → checked b k ≡ k p
  checked-T true  p k = refl
  checked-T false () k

  -- A leaf token is parsed back as itself.
  parseCV-leaf : ∀ f t ts (p : T (isLeaf t)) → parseCV f t ts ≡ just (leaf t p , ts)
  parseCV-leaf f (identT n)    ts p = cong (Maybe.map (λ v → v , ts)) (checked-T _ p _)
  parseCV-leaf f (functionT n) ts ()
  parseCV-leaf f (atT n)       ts p = cong (Maybe.map (λ v → v , ts)) (checked-T _ p _)
  parseCV-leaf f (hashT n)     ts p = cong (Maybe.map (λ v → v , ts)) (checked-T _ p _)
  parseCV-leaf f (stringT s)   ts p = cong (Maybe.map (λ v → v , ts)) (checked-T _ p _)
  parseCV-leaf f (numberT x)   ts p = cong (Maybe.map (λ v → v , ts)) (checked-T _ p _)
  parseCV-leaf f (percentT x)  ts p = cong (Maybe.map (λ v → v , ts)) (checked-T _ p _)
  parseCV-leaf f (dimT x u)    ts p = cong (Maybe.map (λ v → v , ts)) (checked-T _ p _)
  parseCV-leaf f wsT           ts p = cong (Maybe.map (λ v → v , ts)) (checked-T _ p _)
  parseCV-leaf f commentT      ts ()
  parseCV-leaf f (delimT c)    ts p = cong (Maybe.map (λ v → v , ts)) (checked-T _ p _)
  parseCV-leaf f colonT        ts p = cong (Maybe.map (λ v → v , ts)) (checked-T _ p _)
  parseCV-leaf f semiT         ts p = cong (Maybe.map (λ v → v , ts)) (checked-T _ p _)
  parseCV-leaf f commaT        ts p = cong (Maybe.map (λ v → v , ts)) (checked-T _ p _)
  parseCV-leaf f lparenT       ts ()
  parseCV-leaf f rparenT       ts ()
  parseCV-leaf f lbrackT       ts ()
  parseCV-leaf f rbrackT       ts ()
  parseCV-leaf f lbraceT       ts ()
  parseCV-leaf f rbraceT       ts ()

  -- A leaf token is not a closer.
  leaf-notCloser : ∀ t → T (isLeaf t) → isCloser t ≡ false
  leaf-notCloser (identT n)    p = refl
  leaf-notCloser (functionT n) ()
  leaf-notCloser (atT n)       p = refl
  leaf-notCloser (hashT n)     p = refl
  leaf-notCloser (stringT s)   p = refl
  leaf-notCloser (numberT x)   p = refl
  leaf-notCloser (percentT x)  p = refl
  leaf-notCloser (dimT x u)    p = refl
  leaf-notCloser wsT           p = refl
  leaf-notCloser commentT      ()
  leaf-notCloser (delimT c)    p = refl
  leaf-notCloser colonT        p = refl
  leaf-notCloser semiT         p = refl
  leaf-notCloser commaT        p = refl
  leaf-notCloser lparenT       ()
  leaf-notCloser rparenT       ()
  leaf-notCloser lbrackT       ()
  leaf-notCloser rbrackT       ()
  leaf-notCloser lbraceT       ()
  leaf-notCloser rbraceT       ()

  -- The tokens of a tree start with a token that is not a closer.
  head-tokensCV : ∀ v → ∃ λ t → ∃ λ ts → tokensCV v ≡ t ∷ ts × isCloser t ≡ false
  head-tokensCV (leaf t p)    = t , [] , refl , leaf-notCloser t p
  head-tokensCV (paren vs)    = lparenT , _ , refl , refl
  head-tokensCV (bracket vs)  = lbrackT , _ , refl , refl
  head-tokensCV (brace vs)    = lbraceT , _ , refl , refl
  head-tokensCV (func n p vs) = functionT n , _ , refl , refl

  len-pos : ∀ v → ∃ λ a → length (tokensCV v) ≡ suc a
  len-pos v with head-tokensCV v
  ... | t , ts , eq , _ = length ts , cong length eq

------------------------------------------------------------------------
-- The parser inverts `tokensList`
------------------------------------------------------------------------

-- `parseCV`, on a stream.
parseHead : ℕ → List CToken → Maybe (CV × List CToken)
parseHead f []       = nothing
parseHead f (t ∷ ts) = parseCV f t ts

-- What the induction proves about each tree.
Print-ok : CV → Set
Print-ok v = ∀ rest fuel → length (tokensCV v) ≤ fuel →
             parseHead fuel (tokensCV v ++ rest) ≡ just (v , rest)

private
  closer : Block → CToken
  closer parenB   = rparenT
  closer bracketB = rbrackT
  closer braceB   = rbraceT

  parseList-nil : ∀ f rest → StopsAt rest → parseList (suc f) rest ≡ just ([] , rest)
  parseList-nil f []       _ = refl
  parseList-nil f (t ∷ ts) h = cong (parseList₁ f t ts) h

  parseList-cons : ∀ f t ts R v vs rest → isCloser t ≡ false →
    parseCV f t ts ≡ just (v , R) → parseList f R ≡ just (vs , rest) →
    parseList (suc f) (t ∷ ts) ≡ just (v ∷ vs , rest)
  parseList-cons f t ts R v vs rest nc pv pl =
    trans (cong (parseList₁ f t ts) nc)
    (trans (cong (parseCons f) pv)
           (cong (Maybe.map (consCV v)) pl))

  -- A block is read back from its opener, its list and its closer.
  parseBlock-print : ∀ b vs rest f →
    parseList f (tokensList vs ++ closer b ∷ rest) ≡ just (vs , closer b ∷ rest) →
    parseBlock f b (tokensList vs ++ closer b ∷ rest) ≡ just (mkBlock b vs , rest)
  parseBlock-print parenB   vs rest f eq = cong (parseBlock₁ parenB) eq
  parseBlock-print bracketB vs rest f eq = cong (parseBlock₁ bracketB) eq
  parseBlock-print braceB   vs rest f eq = cong (parseBlock₁ braceB) eq

  closer-isCloser : ∀ b → isCloser (closer b) ≡ true
  closer-isCloser parenB   = refl
  closer-isCloser bracketB = refl
  closer-isCloser braceB   = refl

  -- Fuel for a block's list, from the fuel for the block.
  fuel-block : ∀ b f → suc (b + 1) ≤ f → suc b ≤ f
  fuel-block b f le = ≤-trans (s≤s (m≤m+n b 1)) le

  len-snoc : ∀ (X : List CToken) c → length (X ++ c ∷ []) ≡ length X + 1
  len-snoc X c = length-++ X

  fuel-of-block : ∀ (X : List CToken) c f → suc (length (X ++ c ∷ [])) ≤ f → suc (length X) ≤ f
  fuel-of-block X c f le =
    fuel-block (length X) f (subst (λ n → suc n ≤ f) (len-snoc X c) le)

mutual
  parseCV-print : ∀ v → Print-ok v
  parseCV-print (leaf t p) rest fuel _ = parseCV-leaf fuel t rest p
  parseCV-print (paren vs) rest fuel le =
    trans (cong (λ L → parseBlock₁ parenB (parseList fuel L)) (++-assoc (tokensList vs) (rparenT ∷ []) rest))
          (parseBlock-print parenB vs rest fuel
             (parseList-print vs (rparenT ∷ rest) refl fuel (fuel-of-block (tokensList vs) rparenT fuel le)))
  parseCV-print (bracket vs) rest fuel le =
    trans (cong (λ L → parseBlock₁ bracketB (parseList fuel L)) (++-assoc (tokensList vs) (rbrackT ∷ []) rest))
          (parseBlock-print bracketB vs rest fuel
             (parseList-print vs (rbrackT ∷ rest) refl fuel (fuel-of-block (tokensList vs) rbrackT fuel le)))
  parseCV-print (brace vs) rest fuel le =
    trans (cong (λ L → parseBlock₁ braceB (parseList fuel L)) (++-assoc (tokensList vs) (rbraceT ∷ []) rest))
          (parseBlock-print braceB vs rest fuel
             (parseList-print vs (rbraceT ∷ rest) refl fuel (fuel-of-block (tokensList vs) rbraceT fuel le)))
  parseCV-print (func n p vs) rest fuel le =
    trans (cong (λ L → parseFunc₁ n (parseList fuel L)) (++-assoc (tokensList vs) (rparenT ∷ []) rest))
    (trans (cong (parseFunc₁ n)
                 (parseList-print vs (rparenT ∷ rest) refl fuel (fuel-of-block (tokensList vs) rparenT fuel le)))
           (cong (Maybe.map (λ v → v , rest)) (checked-T _ p _)))

  -- A list of trees, then a closer or the end, is read back.
  parseList-print : ∀ vs rest → StopsAt rest → ∀ fuel → suc (length (tokensList vs)) ≤ fuel →
                    parseList fuel (tokensList vs ++ rest) ≡ just (vs , rest)
  parseList-print []       rest st zero    ()
  parseList-print []       rest st (suc f) _  = parseList-nil f rest st
  parseList-print (v ∷ vs) rest st zero    ()
  parseList-print (v ∷ vs) rest st (suc f) (s≤s lt) with head-tokensCV v | len-pos v
  ... | t , ts , eq , nc | a , lenv =
    subst (λ L → parseList (suc f) L ≡ just (v ∷ vs , rest)) (sym eqL)
          (parseList-cons f t (ts ++ R) R v vs rest nc pv pl)
    where
    R : List CToken
    R = tokensList vs ++ rest

    eqL : (tokensCV v ++ tokensList vs) ++ rest ≡ t ∷ (ts ++ R)
    eqL = trans (++-assoc (tokensCV v) (tokensList vs) rest) (cong (_++ R) eq)

    lt₁ : length (tokensCV v) + length (tokensList vs) ≤ f
    lt₁ = subst (_≤ f) (length-++ (tokensCV v)) lt

    fv : length (tokensCV v) ≤ f
    fv = ≤-trans (m≤m+n (length (tokensCV v)) (length (tokensList vs))) lt₁

    fl : suc (length (tokensList vs)) ≤ f
    fl = ≤-trans (s≤s (m≤n+m (length (tokensList vs)) a))
                 (subst (λ n → n + length (tokensList vs) ≤ f) lenv lt₁)

    pv : parseCV f t (ts ++ R) ≡ just (v , R)
    pv = subst (λ L → parseHead f L ≡ just (v , R)) (cong (_++ R) eq) (parseCV-print v R f fv)

    pl : parseList f R ≡ just (vs , rest)
    pl = parseList-print vs rest st f fl

parseTokens-tokensList : ∀ vs → parseTokens (tokensList vs) ≡ just vs
parseTokens-tokensList vs =
  cong parseWhole
    (subst (λ L → parseList (suc (length (tokensList vs))) L ≡ just (vs , []))
           (++-identityʳ (tokensList vs))
           (parseList-print vs [] tt (suc (length (tokensList vs))) (s≤s (≤-refl′ (length (tokensList vs))))))
  where
  ≤-refl′ : ∀ n → n ≤ n
  ≤-refl′ zero    = z≤n
  ≤-refl′ (suc n) = s≤s (≤-refl′ n)

-- The headline: the parser inverts the printer's token stream, comments
-- included.
parseCSS-printTokens : ∀ vs → parseCSS (printTokens vs) ≡ just vs
parseCSS-printTokens vs =
  trans (cong parseTokens (dropComments-printTokens vs)) (parseTokens-tokensList vs)
