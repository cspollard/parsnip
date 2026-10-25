{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The token stream of a tree: printing with separators
--
-- `tokensList` (`Data.CSS.AST`) lists the tokens of a tree, but printing
-- them back to back is wrong when two adjacent tokens would run together
-- (`a` `b` would print as the one identifier `ab`).  `insertSeps` puts the
-- comment token `/**/` between each pair of tokens `t`, `u` for which
-- `okFollow t (firstCls u)` fails, which is exactly what is needed for the
-- stream to be valid (`Data.CSS.Lexer.ValidSeq`): the tokenizer then reads
-- it back, comments included, and `dropComments` removes them.
--
-- * `printTokens-valid`:     the stream of a tree is valid;
-- * `dropComments-printTokens`: dropping the comments gives back the
--   tokens of the tree.
------------------------------------------------------------------------

module Data.CSS.Tokens where

open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Data.CSS.Valid
open import Data.CSS.Token
open import Data.CSS.AST
open import Data.CSS.Lexer using (validSeq; validSeq′; ValidSeq)

------------------------------------------------------------------------
-- Separators
------------------------------------------------------------------------

sepIf : Bool → List CToken → List CToken
sepIf true  l = l
sepIf false l = commentT ∷ l

-- The tokens after `t`, with a comment wherever `t` cannot be followed
-- directly by the next token.
tailSeps : CToken → List CToken → List CToken
tailSeps t []       = []
tailSeps t (u ∷ us) = sepIf (okFollow t (firstCls u)) (u ∷ tailSeps u us)

insertSeps : List CToken → List CToken
insertSeps []       = []
insertSeps (t ∷ ts) = t ∷ tailSeps t ts

printTokens : CSS → List CToken
printTokens vs = insertSeps (tokensList vs)

isComment : CToken → Bool
isComment commentT = true
isComment _        = false

dropComments′ : Bool → CToken → List CToken → List CToken
dropComments′ true  t r = r
dropComments′ false t r = t ∷ r

dropComments : List CToken → List CToken
dropComments []       = []
dropComments (t ∷ ts) = dropComments′ (isComment t) t (dropComments ts)

------------------------------------------------------------------------
-- Streams with separators are valid, and lose them again
------------------------------------------------------------------------

WF : CToken → Set
WF t = tokenWF t ≡ true

NoComment : CToken → Set
NoComment t = isComment t ≡ false

private
  and3 : ∀ {a b c} → a ≡ true → b ≡ true → c ≡ true → a ∧ (b ∧ c) ≡ true
  and3 refl refl refl = refl

  validSeq′-insert : ∀ t ts → All WF (t ∷ ts) → validSeq′ t (tailSeps t ts) ≡ true
  validSeq′-insert t []       (wt ∷ _) = wt
  validSeq′-insert t (u ∷ us) (wt ∷ wu ∷ wus) = go (okFollow t (firstCls u)) refl
    where
    ih : validSeq′ u (tailSeps u us) ≡ true
    ih = validSeq′-insert u us (wu ∷ wus)

    go : ∀ b → okFollow t (firstCls u) ≡ b →
         validSeq′ t (sepIf b (u ∷ tailSeps u us)) ≡ true
    go true  eq = and3 wt eq ih
    go false eq = and3 wt (okFollow-slash t) (and3 refl refl ih)

  dropComments-insert : ∀ t ts → All NoComment (t ∷ ts) → dropComments (tailSeps t ts) ≡ ts
  dropComments-insert t []       _ = refl
  dropComments-insert t (u ∷ us) (_ ∷ nu ∷ nus) = go (okFollow t (firstCls u))
    where
    ih : dropComments (tailSeps u us) ≡ us
    ih = dropComments-insert u us (nu ∷ nus)

    here : dropComments (u ∷ tailSeps u us) ≡ u ∷ us
    here = trans (cong (dropComments′ (isComment u) u) ih) (step (isComment u) nu)
      where
      step : ∀ b → b ≡ false → dropComments′ b u us ≡ u ∷ us
      step .false refl = refl

    go : ∀ b → dropComments (sepIf b (u ∷ tailSeps u us)) ≡ u ∷ us
    go true  = here
    go false = here

printTokens-valid′ : ∀ ts → All WF ts → ValidSeq (insertSeps ts)
printTokens-valid′ []       _        = refl
printTokens-valid′ (t ∷ ts) (w ∷ ws) = validSeq′-insert t ts (w ∷ ws)

dropComments-insertSeps : ∀ ts → All NoComment ts → dropComments (insertSeps ts) ≡ ts
dropComments-insertSeps []       _          = refl
dropComments-insertSeps (t ∷ ts) (n ∷ ns) = step (isComment t) n (dropComments-insert t ts (n ∷ ns))
  where
  step : ∀ b → b ≡ false → dropComments (tailSeps t ts) ≡ ts → dropComments′ b t (dropComments (tailSeps t ts)) ≡ t ∷ ts
  step .false refl eq = cong (t ∷_) eq

------------------------------------------------------------------------
-- The tokens of a tree
------------------------------------------------------------------------

private
  toEq : ∀ {b} → T b → b ≡ true
  toEq {true} _ = refl

  leaf-wf : ∀ t → T (isLeaf t) → WF t
  leaf-wf (identT n)    h = toEq h
  leaf-wf (functionT n) ()
  leaf-wf (atT n)       h = toEq h
  leaf-wf (hashT n)     h = toEq h
  leaf-wf (stringT s)   h = toEq h
  leaf-wf (numberT x)   h = refl
  leaf-wf (percentT x)  h = refl
  leaf-wf (dimT x u)    h = toEq h
  leaf-wf wsT           h = refl
  leaf-wf commentT      ()
  leaf-wf (delimT c)    h = toEq h
  leaf-wf colonT        h = refl
  leaf-wf semiT         h = refl
  leaf-wf commaT        h = refl
  leaf-wf lparenT       ()
  leaf-wf rparenT       ()
  leaf-wf lbrackT       ()
  leaf-wf rbrackT       ()
  leaf-wf lbraceT       ()
  leaf-wf rbraceT       ()

  leaf-nc : ∀ t → T (isLeaf t) → NoComment t
  leaf-nc (identT n)    h = refl
  leaf-nc (functionT n) ()
  leaf-nc (atT n)       h = refl
  leaf-nc (hashT n)     h = refl
  leaf-nc (stringT s)   h = refl
  leaf-nc (numberT x)   h = refl
  leaf-nc (percentT x)  h = refl
  leaf-nc (dimT x u)    h = refl
  leaf-nc wsT           h = refl
  leaf-nc commentT      ()
  leaf-nc (delimT c)    h = refl
  leaf-nc colonT        h = refl
  leaf-nc semiT         h = refl
  leaf-nc commaT        h = refl
  leaf-nc lparenT       ()
  leaf-nc rparenT       ()
  leaf-nc lbrackT       ()
  leaf-nc rbrackT       ()
  leaf-nc lbraceT       ()
  leaf-nc rbraceT       ()

mutual
  wf-tokensCV : ∀ v → All WF (tokensCV v)
  wf-tokensCV (leaf t h)    = leaf-wf t h ∷ []
  wf-tokensCV (paren vs)    = refl ∷ ++⁺ (wf-tokensList vs) (refl ∷ [])
  wf-tokensCV (bracket vs)  = refl ∷ ++⁺ (wf-tokensList vs) (refl ∷ [])
  wf-tokensCV (brace vs)    = refl ∷ ++⁺ (wf-tokensList vs) (refl ∷ [])
  wf-tokensCV (func n h vs) = toEq h ∷ ++⁺ (wf-tokensList vs) (refl ∷ [])

  wf-tokensList : ∀ vs → All WF (tokensList vs)
  wf-tokensList []       = []
  wf-tokensList (v ∷ vs) = ++⁺ (wf-tokensCV v) (wf-tokensList vs)

mutual
  nc-tokensCV : ∀ v → All NoComment (tokensCV v)
  nc-tokensCV (leaf t h)    = leaf-nc t h ∷ []
  nc-tokensCV (paren vs)    = refl ∷ ++⁺ (nc-tokensList vs) (refl ∷ [])
  nc-tokensCV (bracket vs)  = refl ∷ ++⁺ (nc-tokensList vs) (refl ∷ [])
  nc-tokensCV (brace vs)    = refl ∷ ++⁺ (nc-tokensList vs) (refl ∷ [])
  nc-tokensCV (func n h vs) = refl ∷ ++⁺ (nc-tokensList vs) (refl ∷ [])

  nc-tokensList : ∀ vs → All NoComment (tokensList vs)
  nc-tokensList []       = []
  nc-tokensList (v ∷ vs) = ++⁺ (nc-tokensCV v) (nc-tokensList vs)

printTokens-valid : ∀ vs → ValidSeq (printTokens vs)
printTokens-valid vs = printTokens-valid′ (tokensList vs) (wf-tokensList vs)

dropComments-printTokens : ∀ vs → dropComments (printTokens vs) ≡ tokensList vs
dropComments-printTokens vs = dropComments-insertSeps (tokensList vs) (nc-tokensList vs)
