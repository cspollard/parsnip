{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The tokenizer, and `lexer`: a stdlib RightInverse from valid token
-- streams to text
--
-- `tokenize` lexes tokens one at a time with `lexToken`
-- (`Data.XML.Token`); white space is significant, so nothing is skipped.
-- `lexer` is a `RightInverse` out of `ValidTokens`, the token streams
-- that print and lex back to themselves: every token is well formed
-- (`tokenWF`), no two character-data tokens are adjacent (they would
-- print as one), and the stream does not end in character data (which
-- needs a following `<`).  Its `from` is total by checking validity of
-- the tokenizer's output, which is decidable, and falling back to the
-- empty stream.
------------------------------------------------------------------------

module Data.XML.Lexer where

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Data.Bool using (Bool; true; false; _∧_; not; T)
open import Data.Bool.Properties using (T?) renaming (_≟_ to _≟ᵇ_)
open import Data.Char using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤n+m; n<1+n)
open import Data.List.Properties using (length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (RightInverse)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; setoid)

open import Data.XML.Escape using (escapeText-head)
open import Data.XML.Token
open import Data.Stage using (Chars; Subtype)

------------------------------------------------------------------------
-- The tokenizer
------------------------------------------------------------------------

tokenizeLoop : ℕ → List Char → Maybe (List XMLToken)
tokenizeCons : ℕ → Maybe (XMLToken × List Char) → Maybe (List XMLToken)

tokenizeLoop zero    _        = nothing
tokenizeLoop (suc f) []       = just []
tokenizeLoop (suc f) (c ∷ cs) = tokenizeCons f (lexToken (c ∷ cs))

tokenizeCons f nothing           = nothing
tokenizeCons f (just (t , rest)) = Maybe.map (t ∷_) (tokenizeLoop f rest)

tokenize : List Char → Maybe (List XMLToken)
tokenize cs = tokenizeLoop (suc (length cs)) cs

------------------------------------------------------------------------
-- Valid token streams
------------------------------------------------------------------------

isText : XMLToken → Bool
isText (textT _) = true
isText _         = false

-- `Run p q ts`: reading `ts` from state `p` ("the previous token was
-- text") every token is well formed and follows no text token with
-- another, ending in state `q`.
data Run : Bool → Bool → List XMLToken → Set where
  done : ∀ {p} → Run p p []
  step : ∀ {p q t ts} → tokenWF t ≡ true → T (not (p ∧ isText t)) →
         Run (isText t) q ts → Run p q (t ∷ ts)

ValidTokenSeq : List XMLToken → Set
ValidTokenSeq = Run false false

run++ : ∀ {p q r xs ys} → Run p q xs → Run q r ys → Run p r (xs ++ ys)
run++ done           ys = ys
run++ (step wf nt xs) ys = step wf nt (run++ xs ys)

run? : ∀ p q ts → Dec (Run p q ts)
run? p q [] with p ≟ᵇ q
... | yes refl = yes done
... | no  p≢q  = no (λ { done → p≢q refl })
run? p q (t ∷ ts) with tokenWF t ≟ᵇ true | T? (not (p ∧ isText t)) | run? (isText t) q ts
... | yes a | yes b | yes c = yes (step a b c)
... | no ¬a | _     | _     = no (λ { (step a _ _) → ¬a a })
... | _     | no ¬b | _     = no (λ { (step _ b _) → ¬b b })
... | _     | _     | no ¬c = no (λ { (step _ _ c) → ¬c c })

validTokenSeq? : ∀ ts → Dec (ValidTokenSeq ts)
validTokenSeq? = run? false false

-- Token streams that print and lex back (`Data.XML.Goals.ValidTokens`).
ValidTokens : Setoid 0ℓ 0ℓ
ValidTokens = Subtype (setoid (List XMLToken)) ValidTokenSeq

------------------------------------------------------------------------
-- Facts about printed tokens
------------------------------------------------------------------------

-- Every well-formed token prints to something non-empty.
printToken-cons : ∀ t → tokenWF t ≡ true → ∃ λ c → ∃ λ cs → printToken t ≡ c ∷ cs
printToken-cons (openT n as)   _  = '<' , _ , refl
printToken-cons (selfT n as)   _  = '<' , _ , refl
printToken-cons (closeT n)     _  = '<' , _ , refl
printToken-cons (textT [])     ()
printToken-cons (textT (c ∷ cs)) _ with escapeText-head c cs
... | d , ds , eq , _ = d , ds , eq

-- A tag starts with `<`.
tag-startsLt : ∀ t → T (not (isText t)) → ∃ λ r → printToken t ≡ '<' ∷ r
tag-startsLt (openT n as) _ = _ , refl
tag-startsLt (selfT n as) _ = _ , refl
tag-startsLt (closeT n)   _ = _ , refl
tag-startsLt (textT _)    ()

-- In a valid stream, the text after a token may follow it.
tokenFollow : ∀ {p t ts} → Run p false (t ∷ ts) → TokenFollow t (printTokenList ts)
tokenFollow {t = openT _ _}  _ = tt
tokenFollow {t = selfT _ _}  _ = tt
tokenFollow {t = closeT _}   _ = tt
tokenFollow {t = textT _} {ts = []} (step _ _ ())
tokenFollow {t = textT _} {ts = t′ ∷ ts} (step _ _ (step _ nt _)) with tag-startsLt t′ nt
... | r , eq = (r ++ printTokenList ts) , cong (_++ printTokenList ts) eq

------------------------------------------------------------------------
-- The tokenizer inverts the printer on valid streams
------------------------------------------------------------------------

private
  -- The fuel left after one token still exceeds the length of the rest.
  fuel-rest : ∀ (x : List Char) (c : Char) (cs R : List Char) f →
              x ≡ c ∷ cs → length (x ++ R) < suc f → length R < f
  fuel-rest .(c ∷ cs) c cs R f refl (s≤s lt′) =
    ≤-trans (s≤s (subst (length R Data.Nat.≤_) (sym (length-++ cs)) (m≤n+m (length R) (length cs)))) lt′

tokenize-print : ∀ {p ts} → Run p false ts → ∀ fuel →
                 length (printTokenList ts) < fuel →
                 tokenizeLoop fuel (printTokenList ts) ≡ just ts
tokenize-print r zero ()
tokenize-print done (suc f) _ = refl
tokenize-print {ts = t ∷ ts} r@(step wf nt rest) (suc f) lt with printToken-cons t wf
... | c , cs₀ , eq =
  trans (step-eq (printToken t ++ printTokenList ts) c (cs₀ ++ printTokenList ts)
                 (cong (_++ printTokenList ts) eq)
                 (lexToken-printToken t (printTokenList ts) wf (tokenFollow r)))
        (cong (Maybe.map (t ∷_))
              (tokenize-print rest f
                              (fuel-rest (printToken t) c cs₀ (printTokenList ts) f eq lt)))
  where
  step-eq : ∀ L c cs → L ≡ c ∷ cs →
            lexToken L ≡ just (t , printTokenList ts) →
            tokenizeLoop (suc f) L ≡ Maybe.map (t ∷_) (tokenizeLoop f (printTokenList ts))
  step-eq .(c ∷ cs) c cs refl lt′ = cong (tokenizeCons f) lt′

tokenize-printTokenList : ∀ ts → ValidTokenSeq ts →
                          tokenize (printTokenList ts) ≡ just ts
tokenize-printTokenList ts v =
  tokenize-print v (suc (length (printTokenList ts))) (n<1+n (length (printTokenList ts)))

------------------------------------------------------------------------
-- `lexer`
------------------------------------------------------------------------

-- The tokens of a text, or the empty stream when the text does not lex
-- to a valid stream.
lexValid′ : ∀ ts → Dec (ValidTokenSeq ts) → Σ[ ts′ ∈ List XMLToken ] ValidTokenSeq ts′
lexValid′ ts (yes v) = ts , v
lexValid′ ts (no  _) = [] , done

lexValidMaybe : Maybe (List XMLToken) → Σ[ ts ∈ List XMLToken ] ValidTokenSeq ts
lexValidMaybe nothing   = [] , done
lexValidMaybe (just ts) = lexValid′ ts (validTokenSeq? ts)

lexValid : List Char → Σ[ ts ∈ List XMLToken ] ValidTokenSeq ts
lexValid cs = lexValidMaybe (tokenize cs)

private
  lexValid′-valid : ∀ ts (d : Dec (ValidTokenSeq ts)) → ValidTokenSeq ts →
                    proj₁ (lexValid′ ts d) ≡ ts
  lexValid′-valid ts (yes _) _ = refl
  lexValid′-valid ts (no ¬v) v = ⊥-elim (¬v v)

  lexValid-print : ∀ ts → ValidTokenSeq ts → proj₁ (lexValid (printTokenList ts)) ≡ ts
  lexValid-print ts v =
    trans (cong (λ m → proj₁ (lexValidMaybe m)) (tokenize-printTokenList ts v))
          (lexValid′-valid ts (validTokenSeq? ts) v)

-- `lexer`.
lexer : RightInverse ValidTokens Chars
lexer = record
  { to        = λ x → printTokenList (proj₁ x)
  ; from      = lexValid
  ; to-cong   = cong (λ x → printTokenList x)
  ; from-cong = λ { refl → refl }
  ; inverseʳ  = λ { {x} refl → lexValid-print (proj₁ x) (proj₂ x) }
  }
