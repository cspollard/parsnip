{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- CSS declaration lists (Level 2): the contents of a `{}` block
--
-- A declaration is `name : value ;`, where the value is a list of
-- component values with no top-level `;` leaf.  `!important` is not
-- treated specially: it is part of the value (`!` and `important` are
-- a delimiter and an identifier), which is how the component-value
-- grammar sees it.  The parser accepts a final declaration without its
-- `;`, and the printer always writes it.  The round-trip law is
--
--   parseDecls (printDecls ds) ≡ just ds.
------------------------------------------------------------------------

module Data.CSS.Declaration where

open import Data.Bool using (Bool; true; false; not; T)
open import Data.Bool.ListAction using (all)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.List using (List; []; _∷_; _++_; length; concatMap)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (n<1+n)
open import Data.Product using (_×_; _,_; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Data.Sanitize using (fromEq)
open import Data.CSS.Valid using (Name; isValidIdent)
open import Data.CSS.Token
open import Data.CSS.AST
open import Data.CSS.Rule using (isSemiCV; semi; split; split-ok; toEq; fuel-rest)

okV : List CV → Bool
okV = all (λ v → not (isSemiCV v))

data Decl : Set where
  decl : (n : Name) → T (isValidIdent n) → (v : List CV) → T (okV v) → Decl

colonCV : CV
colonCV = leaf colonT _

printDecl : Decl → List CV
printDecl (decl n h v _) = leaf (identT n) h ∷ colonCV ∷ v ++ semi ∷ []

printDecls : List Decl → List CV
printDecls = concatMap printDecl

------------------------------------------------------------------------
-- Parsing
------------------------------------------------------------------------

mkD : (n : Name) → T (isValidIdent n) → (v : List CV) → (b : Bool) → okV v ≡ b →
      Maybe Decl
mkD n h v true  eq = just (decl n h v (fromEq eq))
mkD n h v false eq = nothing

-- The declaration ending at the split point (or at the end of the list).
finishD : (n : Name) → T (isValidIdent n) → List CV →
          Maybe (List CV × CV × List CV) → Maybe (Decl × List CV)
finishD n h vs (just (p , leaf semiT _ , rest)) = Maybe.map (λ d → d , rest) (mkD n h p (okV p) refl)
finishD n h vs (just _)                          = nothing
finishD n h vs nothing                           = Maybe.map (λ d → d , []) (mkD n h vs (okV vs) refl)

parseDecl : List CV → Maybe (Decl × List CV)
parseDecl (leaf (identT n) h ∷ leaf colonT _ ∷ vs) = finishD n h vs (split isSemiCV vs)
parseDecl _                                        = nothing

parseDecls : ℕ → List CV → Maybe (List Decl)
parseDeclsCons : ℕ → Maybe (Decl × List CV) → Maybe (List Decl)

parseDecls zero    _        = nothing
parseDecls (suc f) []       = just []
parseDecls (suc f) (v ∷ vs) = parseDeclsCons f (parseDecl (v ∷ vs))

parseDeclsCons f nothing           = nothing
parseDeclsCons f (just (d , rest)) = Maybe.map (d ∷_) (parseDecls f rest)

parseDeclList : List CV → Maybe (List Decl)
parseDeclList vs = parseDecls (suc (length vs)) vs

------------------------------------------------------------------------
-- Round trip
------------------------------------------------------------------------

mkD-ok : ∀ n hn v b (eq : okV v ≡ b) (h : T (okV v)) →
         b ≡ true → mkD n hn v b eq ≡ just (decl n hn v h)
mkD-ok n hn v true  eq h _ = cong (λ x → just (decl n hn v x)) (T-irrelevant (fromEq eq) h)
mkD-ok n hn v false eq h ()

parse-decl : ∀ d R f → parseDecls (suc f) (printDecl d ++ R) ≡ Maybe.map (d ∷_) (parseDecls f R)
parse-decl (decl n hn v hv) R f
  rewrite ++-assoc v (semi ∷ []) R
        | split-ok isSemiCV v semi R (toEq hv) refl
        | mkD-ok n hn v (okV v) refl hv (toEq hv) = refl

printDecl-cons : ∀ d → ∃ λ x → ∃ λ xs → printDecl d ≡ x ∷ xs
printDecl-cons (decl n h v _) = leaf (identT n) h , colonCV ∷ v ++ semi ∷ [] , refl

parseDecls-print : ∀ ds f → length (printDecls ds) < f → parseDecls f (printDecls ds) ≡ just ds
parseDecls-print ds       zero    ()
parseDecls-print []       (suc f) _  = refl
parseDecls-print (d ∷ ds) (suc f) lt with printDecl-cons d
... | x , xs , eq =
  trans (parse-decl d (printDecls ds) f)
        (cong (Maybe.map (d ∷_))
              (parseDecls-print ds f (fuel-rest (printDecl d) x xs (printDecls ds) f eq lt)))

parseDeclList-printDecls : ∀ ds → parseDeclList (printDecls ds) ≡ just ds
parseDeclList-printDecls ds =
  parseDecls-print ds (suc (length (printDecls ds))) (n<1+n (length (printDecls ds)))
