{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- CSS rules (Level 2): a grammar on top of component values
--
-- A style sheet is a list of rules read from a list of component values
-- (`Data.CSS.AST`):
--
-- * an at-rule is an at-keyword leaf, a prelude, and then `;` or a
--   `{}` block;
-- * a qualified rule is a prelude and a `{}` block.
--
-- A prelude is a list of component values with no top-level `{}` block
-- (and, for at-rules, no top-level `;` leaf), and the prelude of a
-- qualified rule does not start with an at-keyword.  These conditions are
-- exactly what makes the rule boundaries recoverable, so
--
--   parseRules (printRules rs) ≡ just rs.
--
-- The conditions are evidence in the constructors (`T b`, irrelevant).
------------------------------------------------------------------------

module Data.CSS.Rule where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; T)
open import Data.Bool.ListAction using (all)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.List using (List; []; _∷_; _++_; length; concatMap)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤n+m; n<1+n)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Data.Sanitize using (fromEq; both)
open import Data.CSS.Valid using (Name; isValidIdent)
open import Data.CSS.Token
open import Data.CSS.AST

------------------------------------------------------------------------
-- Classifying component values
------------------------------------------------------------------------

isBraceCV isSemiCV isAtCV stopA : CV → Bool
isBraceCV (brace _) = true
isBraceCV _         = false

isSemiCV (leaf semiT _) = true
isSemiCV _              = false

isAtCV (leaf (atT _) _) = true
isAtCV _                = false

stopA v = isBraceCV v ∨ isSemiCV v

headAt : List CV → Bool
headAt []      = false
headAt (v ∷ _) = isAtCV v

-- Preludes
okQ okA : List CV → Bool
okQ p = all (λ v → not (isBraceCV v)) p ∧ not (headAt p)
okA p = all (λ v → not (stopA v)) p

data Rule : Set where
  qualified : (p : List CV) → T (okQ p) → (b : List CV) → Rule
  atRule    : (n : Name) → T (isValidIdent n) → (p : List CV) → T (okA p) →
              Maybe (List CV) → Rule

atLeaf : (n : Name) → T (isValidIdent n) → CV
atLeaf n h = leaf (atT n) h

semi : CV
semi = leaf semiT _

printRule : Rule → List CV
printRule (qualified p _ b)         = p ++ brace b ∷ []
printRule (atRule n h p _ nothing)  = atLeaf n h ∷ p ++ semi ∷ []
printRule (atRule n h p _ (just b)) = atLeaf n h ∷ p ++ brace b ∷ []

printRules : List Rule → List CV
printRules = concatMap printRule

------------------------------------------------------------------------
-- Parsing
------------------------------------------------------------------------

-- The component values up to the first one satisfying `stop`, that one,
-- and the rest.
splitStep : (CV → Bool) → CV → Bool → List CV → Maybe (List CV × CV × List CV) →
            Maybe (List CV × CV × List CV)
splitStep stop v true  vs _ = just ([] , v , vs)
splitStep stop v false vs r = Maybe.map (λ { (p , s , rest) → v ∷ p , s , rest }) r

split : (CV → Bool) → List CV → Maybe (List CV × CV × List CV)
split stop []       = nothing
split stop (v ∷ vs) = splitStep stop v (stop v) vs (split stop vs)

mkQ : (p : List CV) → (b : Bool) → okQ p ≡ b → List CV → Maybe Rule
mkQ p true  eq blk = just (qualified p (fromEq eq) blk)
mkQ p false eq blk = nothing

mkA : (n : Name) → T (isValidIdent n) → (p : List CV) → (b : Bool) → okA p ≡ b →
      Maybe (List CV) → Maybe Rule
mkA n h p true  eq k = just (atRule n h p (fromEq eq) k)
mkA n h p false eq k = nothing

-- The rule ending at the split point.
finishQ : Maybe (List CV × CV × List CV) → Maybe (Rule × List CV)
finishQ (just (p , brace b , rest)) = Maybe.map (λ r → r , rest) (mkQ p (okQ p) refl b)
finishQ _                           = nothing

finishA : (n : Name) → T (isValidIdent n) → Maybe (List CV × CV × List CV) → Maybe (Rule × List CV)
finishA n h (just (p , leaf semiT _ , rest)) = Maybe.map (λ r → r , rest) (mkA n h p (okA p) refl nothing)
finishA n h (just (p , brace b , rest))      = Maybe.map (λ r → r , rest) (mkA n h p (okA p) refl (just b))
finishA n h _                                = nothing

-- One rule from the front of a non-empty list.
parseRule : Bool → List CV → Maybe (Rule × List CV)
parseRule true  (leaf (atT n) h ∷ vs) = finishA n h (split stopA vs)
parseRule true  _                     = nothing
parseRule false ws                    = finishQ (split isBraceCV ws)

-- The first argument is fuel: each rule consumes at least one value.
parseRules : ℕ → List CV → Maybe (List Rule)
parseRulesCons : ℕ → Maybe (Rule × List CV) → Maybe (List Rule)

parseRules zero    _        = nothing
parseRules (suc f) []       = just []
parseRules (suc f) (v ∷ vs) = parseRulesCons f (parseRule (isAtCV v) (v ∷ vs))

parseRulesCons f nothing           = nothing
parseRulesCons f (just (r , rest)) = Maybe.map (r ∷_) (parseRules f rest)

parseRuleList : List CV → Maybe (List Rule)
parseRuleList vs = parseRules (suc (length vs)) vs

------------------------------------------------------------------------
-- Round trip
------------------------------------------------------------------------

module Lemmas where
  ∧-elim : ∀ a b → a ∧ b ≡ true → a ≡ true × b ≡ true
  ∧-elim true b h = refl , h

  not-true : ∀ b → not b ≡ true → b ≡ false
  not-true false _ = refl

  ∨-false : ∀ a b → a ∨ b ≡ false → a ≡ false × b ≡ false
  ∨-false false b h = refl , h

  not-∨ : ∀ a b → not (a ∨ b) ≡ true → a ≡ false × b ≡ false
  not-∨ a b h = ∨-false a b (not-true (a ∨ b) h)

  split-ok : ∀ stop p s rest → all (λ v → not (stop v)) p ≡ true → stop s ≡ true →
             split stop (p ++ s ∷ rest) ≡ just (p , s , rest)
  split-ok stop []       s rest _ hs rewrite hs = refl
  split-ok stop (v ∷ p) s rest hp hs with ∧-elim (not (stop v)) _ hp
  ... | hv , hp′ rewrite not-true (stop v) hv | split-ok stop p s rest hp′ hs = refl

  mkQ-ok : ∀ p b (eq : okQ p ≡ b) (h : T (okQ p)) blk →
           b ≡ true → mkQ p b eq blk ≡ just (qualified p h blk)
  mkQ-ok p true  eq h blk _ = cong (λ x → just (qualified p x blk)) (T-irrelevant (fromEq eq) h)
  mkQ-ok p false eq h blk ()

  mkA-ok : ∀ n hn p b (eq : okA p ≡ b) (h : T (okA p)) k →
           b ≡ true → mkA n hn p b eq k ≡ just (atRule n hn p h k)
  mkA-ok n hn p true  eq h k _ = cong (λ x → just (atRule n hn p x k)) (T-irrelevant (fromEq eq) h)
  mkA-ok n hn p false eq h k ()

  toEq : ∀ {b} → T b → b ≡ true
  toEq {true} _ = refl

  headAt-++ : ∀ p x → headAt p ≡ false → headAt x ≡ false → headAt (p ++ x) ≡ false
  headAt-++ []      x _ hx = hx
  headAt-++ (v ∷ p) x h  _ = h

  fuel-rest : ∀ (x : List CV) c cs (R : List CV) f →
              x ≡ c ∷ cs → length (x ++ R) < suc f → length R < f
  fuel-rest .(c ∷ cs) c cs R f refl (s≤s lt′) =
    ≤-trans (s≤s (subst (length R ≤_) (sym (length-++ cs)) (m≤n+m (length R) (length cs)))) lt′

  parseRule-q : ∀ p (h : T (okQ p)) b R →
                parseRule false (p ++ brace b ∷ R) ≡ just (qualified p h b , R)
  parseRule-q p h b R with ∧-elim _ _ (toEq h)
  ... | hall , _
    rewrite split-ok isBraceCV p (brace b) R hall refl
          | mkQ-ok p (okQ p) refl h b (toEq h) = refl

open Lemmas public

parse-rule : ∀ r R f → parseRules (suc f) (printRule r ++ R) ≡ Maybe.map (r ∷_) (parseRules f R)
parse-rule (qualified [] h b) R f = cong (parseRulesCons f) (parseRule-q [] h b R)
parse-rule (qualified (v ∷ p) h b) R f
  with ∧-elim _ _ (toEq h)
... | _ , hn
  rewrite not-true (isAtCV v) hn
        | ++-assoc p (brace b ∷ []) R = cong (parseRulesCons f) (parseRule-q (v ∷ p) h b R)
parse-rule (atRule n hn p ha nothing) R f
  rewrite ++-assoc p (semi ∷ []) R
        | split-ok stopA p semi R (toEq ha) refl
        | mkA-ok n hn p (okA p) refl ha nothing (toEq ha) = refl
parse-rule (atRule n hn p ha (just b)) R f
  rewrite ++-assoc p (brace b ∷ []) R
        | split-ok stopA p (brace b) R (toEq ha) refl
        | mkA-ok n hn p (okA p) refl ha (just b) (toEq ha) = refl

printRule-cons : ∀ r → ∃ λ v → ∃ λ vs → printRule r ≡ v ∷ vs
printRule-cons (qualified [] h b)      = brace b , [] , refl
printRule-cons (qualified (v ∷ p) h b) = v , p ++ brace b ∷ [] , refl
printRule-cons (atRule n h p _ nothing)  = atLeaf n h , p ++ semi ∷ [] , refl
printRule-cons (atRule n h p _ (just b)) = atLeaf n h , p ++ brace b ∷ [] , refl

parseRules-print : ∀ rs f → length (printRules rs) < f → parseRules f (printRules rs) ≡ just rs
parseRules-print rs       zero    ()
parseRules-print []       (suc f) _  = refl
parseRules-print (r ∷ rs) (suc f) lt with printRule-cons r
... | v , vs , eq =
  trans (parse-rule r (printRules rs) f)
        (cong (Maybe.map (r ∷_))
              (parseRules-print rs f (fuel-rest (printRule r) v vs (printRules rs) f eq lt)))

parseRuleList-printRules : ∀ rs → parseRuleList (printRules rs) ≡ just rs
parseRuleList-printRules rs =
  parseRules-print rs (suc (length (printRules rs))) (n<1+n (length (printRules rs)))
