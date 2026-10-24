{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

------------------------------------------------------------------------
-- The recursive-descent parser, and `parser`: a stdlib RightInverse
-- from XML documents to valid token streams
--
-- `parseElement` is fuel-bounded recursive descent over `XMLToken`s.  The
-- fuel invariant is "fuel ≥ number of tokens consumed" (and, in the loop
-- over children, one more, for the call that finds the end tag).  An
-- element is a `selfT`, or an `openT`, its content, and the matching
-- `closeT`; the content is the text before the first child and each
-- child followed by the text after it, which is the AST's mixed-content
-- layout.  The parser checks what the AST needs (names, characters,
-- unique attributes) when it builds a node, and fails otherwise.
-- `parseElement-print` shows the parser inverts `printTokens` up to
-- `_≈ₓ_`, whatever tokens follow.
------------------------------------------------------------------------

module Data.XML.Parser where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false; _∧_; not; T)
open import Data.Char using (Char; toℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List as List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise; []; _∷_)
open import Data.Maybe as Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m; +-comm; n≤1+n; ≡⇒≡ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_∘_)
open import Function.Bundles using (RightInverse)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.XML.AST
open import Data.XML.Valid
open import Data.XML.Equality
open import Data.XML.Token
open import Data.XML.Lexer using (ValidTokens; Run; isText)
open import Data.XML.Tokens
open import Data.JSON.Stage using (Subtype)

------------------------------------------------------------------------
-- The parser
------------------------------------------------------------------------

-- Continue when a decidable check holds.
checked : ∀ {A : Set} (b : Bool) → (T b → Maybe A) → Maybe A
checked true  k = k tt
checked false _ = nothing

-- An element, if its name, attributes and text are legal XML.
mkNode : Name → Attributes → NodeData XMLDoc → Maybe XMLDoc
mkNode tag attrs (n , ts , f) =
  checked (isValidName tag) λ pt →
  checked (isValidAttrs attrs) λ pa →
  checked (isValidTexts ts) λ px →
  just (node tag attrs ts f {pt} {pa} {px})

-- The character data at the front of the stream (empty if there is none).
takeText : List XMLToken → Text × List XMLToken
takeText (textT t ∷ ts) = t , ts
takeText ts             = [] , ts

consChild : XMLDoc × Text → List (XMLDoc × Text) × List XMLToken →
            List (XMLDoc × Text) × List XMLToken
consChild x (cs , ts) = x ∷ cs , ts

finish : Name → Attributes → Content XMLDoc → List XMLToken → Maybe (XMLDoc × List XMLToken)
finish tag attrs c ts = Maybe.map (λ v → v , ts) (mkNode tag attrs (fromContent c))

mutual
  parseElement : ℕ → List XMLToken → Maybe (XMLDoc × List XMLToken)
  parseElement zero    _                = nothing
  parseElement (suc f) (selfT n as ∷ ts) = finish n as ([] , []) ts
  parseElement (suc f) (openT n as ∷ ts) = parseContent f n as (takeText ts)
  parseElement (suc f) _                = nothing

  -- After the start tag and the first text: the children, then the end tag.
  parseContent : ℕ → Name → Attributes → Text × List XMLToken → Maybe (XMLDoc × List XMLToken)
  parseContent f n as (t₀ , ts) = parseClose n as t₀ (parseChildren f ts)

  parseClose : Name → Attributes → Text → Maybe (List (XMLDoc × Text) × List XMLToken) →
               Maybe (XMLDoc × List XMLToken)
  parseClose n as t₀ (just (cs , closeT n′ ∷ ts)) = parseClose′ n as (t₀ , cs) ts (eqName n n′)
  parseClose n as t₀ _                            = nothing

  parseClose′ : Name → Attributes → Content XMLDoc → List XMLToken → Bool →
                Maybe (XMLDoc × List XMLToken)
  parseClose′ n as c ts true  = finish n as c ts
  parseClose′ n as c ts false = nothing

  -- Children, each with the text after it, up to (not including) an end tag.
  parseChildren : ℕ → List XMLToken → Maybe (List (XMLDoc × Text) × List XMLToken)
  parseChildren zero    _                = nothing
  parseChildren (suc f) (closeT n ∷ ts) = just ([] , closeT n ∷ ts)
  parseChildren (suc f) ts              = parseChild f (parseElement f ts)

  parseChild : ℕ → Maybe (XMLDoc × List XMLToken) →
               Maybe (List (XMLDoc × Text) × List XMLToken)
  parseChild f nothing          = nothing
  parseChild f (just (v , ts)) = parseChild′ f v (takeText ts)

  parseChild′ : ℕ → XMLDoc → Text × List XMLToken →
                Maybe (List (XMLDoc × Text) × List XMLToken)
  parseChild′ f v (t , ts) = Maybe.map (consChild (v , t)) (parseChildren f ts)

-- A complete token stream is one element.
parseWhole : Maybe (XMLDoc × List XMLToken) → Maybe XMLDoc
parseWhole (just (v , [])) = just v
parseWhole _               = nothing

parseTokens : List XMLToken → Maybe XMLDoc
parseTokens ts = parseWhole (parseElement (suc (length ts)) ts)

------------------------------------------------------------------------
-- Building a node
------------------------------------------------------------------------

private
  toEq : ∀ {b} → T b → b ≡ true
  toEq {true} _ = refl

  checked-T : ∀ {A : Set} b (p : T b) (k : T b → Maybe A) → checked b k ≡ k p
  checked-T true  p k = refl
  checked-T false () k

mkNode-valid : ∀ tag attrs n ts (f : Fin n → XMLDoc) pt pa px →
  mkNode tag attrs (n , ts , f) ≡ just (node tag attrs ts f {pt} {pa} {px})
mkNode-valid tag attrs n ts f pt pa px =
  trans (checked-T _ pt _) (trans (checked-T _ pa _) (checked-T _ px _))

-- Two `NodeData` are related when their text slots are equal and their
-- children bisimilar (the arities are equal, through `e`).
NodeRel : NodeData XMLDoc → NodeData XMLDoc → Set
NodeRel (n , ts , f) (m , ts′ , g) =
  Σ (n ≡ m) λ e → subst (λ k → Vec Text (suc k)) e ts ≡ ts′ × ∀ i → f i ≈ₓ g (subst Fin e i)

-- A node built from data related to the data of `v` is bisimilar to `v`.
build-node : ∀ tag attrs X n ts (f : Fin n → XMLDoc) pt pa px → NodeRel X (n , ts , f) →
  ∃ λ v′ → mkNode tag attrs X ≡ just v′
         × v′ ≈ₓ impure (shape tag attrs n ts pt pa px , f)
build-node tag attrs (n′ , ts′ , f′) n ts f pt pa px (refl , refl , h) =
  node tag attrs ts′ f′ {pt} {pa} {px}
  , mkNode-valid tag attrs n′ ts′ f′ pt pa px
  , ≈element refl refl h

-- Children and their trailing text, related.
ChildRel : Rel (XMLDoc × Text) 0ℓ
ChildRel (v′ , t′) (v , t) = v′ ≈ₓ v × t′ ≡ t

consNode-rel : ∀ t v′ x m (ts : Vec Text (suc m)) (f : Fin (suc m) → XMLDoc) →
               v′ ≈ₓ f zero → NodeRel x (m , ts , f ∘ suc) →
               NodeRel (consNode t v′ x) (suc m , t ∷ ts , f)
consNode-rel t v′ (n′ , ts′ , f′) m ts f hz (refl , refl , h) =
  refl , refl , λ { zero → hz; (suc i) → h i }

-- Parsed content related to `mixed n ts f` yields related node data.
fromContent-rel : ∀ n (ts : Vec Text (suc n)) (f : Fin n → XMLDoc)
                  (t′ : Text) (cs′ : List (XMLDoc × Text)) →
                  t′ ≡ proj₁ (mixed n ts f) → Pointwise ChildRel cs′ (proj₂ (mixed n ts f)) →
                  NodeRel (fromContent′ t′ cs′) (n , ts , f)
fromContent-rel zero    (t ∷ [])  f t′ []   refl []                    = refl , refl , λ ()
fromContent-rel (suc n) (t ∷ ts) f t′ ((v′ , t₁′) ∷ cs″) refl ((≈v , eq) ∷ pw) =
  consNode-rel t v′ (fromContent′ t₁′ cs″) n ts f ≈v
    (fromContent-rel n ts (f ∘ suc) t₁′ cs″ eq pw)

------------------------------------------------------------------------
-- Facts about token streams
------------------------------------------------------------------------

-- The stream starts with something that is not character data.
NT : List XMLToken → Set
NT []      = ⊥
NT (t ∷ _) = T (not (isText t))

private
  nt-start : ∀ {t} → ElemStart t → T (not (isText t))
  nt-start openS = tt
  nt-start selfS = tt

  -- The tokens of an element, followed by anything, start a tag.
  NT-elem : ∀ v W B → NT ((printTokens v ++ W) ++ B)
  NT-elem v W B with printTokens-head v
  ... | t , ts , eq , es =
    subst (λ L → NT ((L ++ W) ++ B)) (sym eq) (nt-start es)

  len-pos : ∀ v → ∃ λ a → length (printTokens v) ≡ suc a
  len-pos v with printTokens-head v
  ... | t , ts , eq , _ = length ts , cong length eq

takeText-text : ∀ t X → NT X → takeText (textTokens t ++ X) ≡ (t , X)
takeText-text []       []                 ()
takeText-text []       (openT n as ∷ X)   _ = refl
takeText-text []       (selfT n as ∷ X)   _ = refl
takeText-text []       (closeT n ∷ X)     _ = refl
takeText-text []       (textT t ∷ X)      ()
takeText-text (c ∷ cs) X                  _ = refl

-- The tokens of children, then an end tag, start with a tag.
NT-children : ∀ cs tag rest → NT (childTokens (mapChildren printTokens cs) ++ closeT tag ∷ rest)
NT-children []             tag rest = tt
NT-children ((c , t) ∷ cs) tag rest =
  NT-elem c (textTokens t ++ childTokens (mapChildren printTokens cs)) (closeT tag ∷ rest)

private
  parseChildren-elem′ : ∀ f t ts Y → ElemStart t →
    parseChildren (suc f) ((t ∷ ts) ++ Y) ≡ parseChild f (parseElement f ((t ∷ ts) ++ Y))
  parseChildren-elem′ f _ ts Y openS = refl
  parseChildren-elem′ f _ ts Y selfS = refl

-- An element's tokens do not start with an end tag, so `parseChildren`
-- parses an element.
parseChildren-elem : ∀ f v Y →
  parseChildren (suc f) (printTokens v ++ Y) ≡ parseChild f (parseElement f (printTokens v ++ Y))
parseChildren-elem f v Y with printTokens-head v
... | t , ts , eq , es =
  subst (λ L → parseChildren (suc f) (L ++ Y) ≡ parseChild f (parseElement f (L ++ Y)))
        (sym eq) (parseChildren-elem′ f t ts Y es)

------------------------------------------------------------------------
-- The parser inverts `printTokens`
------------------------------------------------------------------------

-- What the induction proves about each element.
Print-ok : XMLDoc → Set
Print-ok v = ∀ rest fuel → length (printTokens v) ≤ fuel →
             ∃ λ v′ → parseElement fuel (printTokens v ++ rest) ≡ just (v′ , rest) × v′ ≈ₓ v

private
  eqName-refl : ∀ n → eqName n n ≡ true
  eqName-refl []      = refl
  eqName-refl (c ∷ n) = ∧-join (toEq (≡⇒≡ᵇ (toℕ c) (toℕ c) refl)) (eqName-refl n)

  len-snoc : ∀ (X : List XMLToken) t → length (X ++ t ∷ []) ≡ suc (length X)
  len-snoc X t = trans (length-++ X) (+-comm (length X) 1)

  -- Fuel for the children after one child whose tokens are non-empty.
  fuel-children : ∀ (P M C : List XMLToken) a f →
                  length P ≡ suc a → length C ≤ length M → length P + length M ≤ f →
                  suc (length C) ≤ f
  fuel-children P M C a f lenP CM lt =
    ≤-trans (s≤s (≤-trans CM (m≤n+m (length M) a)))
            (subst (λ x → x + length M ≤ f) lenP lt)

  all-mixed : ∀ {P : XMLDoc → Set} n (ts : Vec Text (suc n)) (f : Fin n → XMLDoc) →
              (∀ i → P (f i)) → All (P ∘ proj₁) (proj₂ (mixed n ts f))
  all-mixed zero    (t ∷ [])  f p = []
  all-mixed (suc n) (t ∷ ts) f p = p zero ∷ all-mixed n ts (f ∘ suc) (p ∘ suc)

  -- One child, the text after it, and the rest are parsed back.
  parseChildren-cons : ∀ f c t C tag rest c′ cs″ →
    parseElement f (printTokens c ++ (textTokens t ++ (C ++ closeT tag ∷ rest)))
      ≡ just (c′ , textTokens t ++ (C ++ closeT tag ∷ rest)) →
    NT (C ++ closeT tag ∷ rest) →
    parseChildren f (C ++ closeT tag ∷ rest) ≡ just (cs″ , closeT tag ∷ rest) →
    parseChildren (suc f) (printTokens c ++ (textTokens t ++ (C ++ closeT tag ∷ rest)))
      ≡ just ((c′ , t) ∷ cs″ , closeT tag ∷ rest)
  parseChildren-cons f c t C tag rest c′ cs″ eqc nt eqs =
    trans (parseChildren-elem f c _)
    (trans (cong (parseChild f) eqc)
    (trans (cong (parseChild′ f c′) (takeText-text t (C ++ closeT tag ∷ rest) nt))
           (cong (Maybe.map (consChild (c′ , t))) eqs)))

  -- The children of a node are parsed back.
  parseChildren-print : ∀ cs → All (Print-ok ∘ proj₁) cs → ∀ tag rest fuel →
    suc (length (childTokens (mapChildren printTokens cs))) ≤ fuel →
    ∃ λ cs′ → parseChildren fuel (childTokens (mapChildren printTokens cs) ++ closeT tag ∷ rest)
                ≡ just (cs′ , closeT tag ∷ rest)
            × Pointwise ChildRel cs′ cs
  parseChildren-print []             []         tag rest zero ()
  parseChildren-print []             []         tag rest (suc f) _ = [] , refl , []
  parseChildren-print ((c , t) ∷ cs) (pc ∷ pcs) tag rest zero ()
  parseChildren-print ((c , t) ∷ cs) (pc ∷ pcs) tag rest (suc f) (s≤s lt) = body (len-pos c)
    where
    C : List XMLToken
    C = childTokens (mapChildren printTokens cs)

    M : List XMLToken
    M = textTokens t ++ C

    Y : List XMLToken
    Y = textTokens t ++ (C ++ closeT tag ∷ rest)

    assoc : (printTokens c ++ M) ++ closeT tag ∷ rest ≡ printTokens c ++ Y
    assoc = trans (++-assoc (printTokens c) M (closeT tag ∷ rest))
                  (cong (printTokens c ++_) (++-assoc (textTokens t) C (closeT tag ∷ rest)))

    lt₁ : length (printTokens c) + length M ≤ f
    lt₁ = subst (_≤ f) (length-++ (printTokens c) {M}) lt

    CM : length C ≤ length M
    CM = subst (length C ≤_) (sym (length-++ (textTokens t))) (m≤n+m (length C) (length (textTokens t)))

    body : (∃ λ a → length (printTokens c) ≡ suc a) →
           ∃ λ cs′ → parseChildren (suc f) ((printTokens c ++ M) ++ closeT tag ∷ rest)
                       ≡ just (cs′ , closeT tag ∷ rest)
                   × Pointwise ChildRel cs′ ((c , t) ∷ cs)
    body (a , lenc)
      with pc Y f (≤-trans (m≤m+n (length (printTokens c)) (length M)) lt₁)
         | parseChildren-print cs pcs tag rest f (fuel-children (printTokens c) M C a f lenc CM lt₁)
    ... | c′ , eqc , ≈c | cs″ , eqs , pw =
      (c′ , t) ∷ cs″ ,
      trans (cong (parseChildren (suc f)) assoc)
            (parseChildren-cons f c t C tag rest c′ cs″ eqc (NT-children cs tag rest) eqs) ,
      (≈c , refl) ∷ pw

  -- A node with a start tag, content, and end tag.
  openCase : ∀ tag attrs n ts pt pa px (f : Fin n → XMLDoc) → (∀ i → Print-ok (f i)) →
    printTokens (impure (shape tag attrs n ts pt pa px , f))
      ≡ openT tag attrs ∷ contentTokens (mapContent printTokens (mixed n ts f)) ++ closeT tag ∷ [] →
    Print-ok (impure (shape tag attrs n ts pt pa px , f))
  openCase tag attrs n ts pt pa px f ih eq rest fuel le
    with core rest fuel (subst (λ X → length X ≤ fuel) eq le)
    where
    cd : Content XMLDoc
    cd = mixed n ts f

    t₀ : Text
    t₀ = proj₁ cd

    cs : List (XMLDoc × Text)
    cs = proj₂ cd

    C : List XMLToken
    C = childTokens (mapChildren printTokens cs)

    X : List XMLToken
    X = textTokens t₀ ++ C

    core : ∀ rest fuel → length (openT tag attrs ∷ X ++ closeT tag ∷ []) ≤ fuel →
           ∃ λ v′ → parseElement fuel ((openT tag attrs ∷ X ++ closeT tag ∷ []) ++ rest) ≡ just (v′ , rest)
                  × v′ ≈ₓ impure (shape tag attrs n ts pt pa px , f)
    core rest zero ()
    core rest (suc f₀) (s≤s le₀) = body
      where
      le₁ : suc (length X) ≤ f₀
      le₁ = subst (_≤ f₀) (len-snoc X (closeT tag)) le₀

      CX : length C ≤ length X
      CX = subst (length C ≤_) (sym (length-++ (textTokens t₀))) (m≤n+m (length C) (length (textTokens t₀)))

      eqL : (X ++ closeT tag ∷ []) ++ rest ≡ textTokens t₀ ++ (C ++ closeT tag ∷ rest)
      eqL = trans (++-assoc X (closeT tag ∷ []) rest) (++-assoc (textTokens t₀) C (closeT tag ∷ rest))

      body : ∃ λ v′ → parseElement (suc f₀) ((openT tag attrs ∷ X ++ closeT tag ∷ []) ++ rest)
                        ≡ just (v′ , rest)
                    × v′ ≈ₓ impure (shape tag attrs n ts pt pa px , f)
      body with parseChildren-print cs (all-mixed n ts f ih) tag rest f₀ (≤-trans (s≤s CX) le₁)
      ... | cs′ , eqc , pw
        with build-node tag attrs (fromContent′ t₀ cs′) n ts f pt pa px
                        (fromContent-rel n ts f t₀ cs′ refl pw)
      ... | v′ , eqm , ≈v =
        v′ ,
        trans (cong (λ L → parseContent f₀ tag attrs (takeText L)) eqL)
        (trans (cong (parseContent f₀ tag attrs) (takeText-text t₀ (C ++ closeT tag ∷ rest) (NT-children cs tag rest)))
        (trans (cong (parseClose tag attrs t₀) eqc)
        (trans (cong (parseClose′ tag attrs (t₀ , cs′) rest) (eqName-refl tag))
               (cong (Maybe.map (λ v → v , rest)) eqm)))) ,
        ≈v
  ... | v′ , p , ≈v =
    v′ , subst (λ X → parseElement fuel (X ++ rest) ≡ just (v′ , rest)) (sym eq) p , ≈v

parseElement-print : ∀ v → Print-ok v
parseElement-print (pure ())
parseElement-print (impure (shape tag attrs zero ([] ∷ []) pt pa px , f)) rest zero ()
parseElement-print (impure (shape tag attrs zero ([] ∷ []) pt pa px , f)) rest (suc g) _ =
  node tag attrs ([] ∷ []) (λ ()) {pt} {pa} {px} ,
  cong (Maybe.map (λ v → v , rest)) (mkNode-valid tag attrs zero ([] ∷ []) (λ ()) pt pa px) ,
  ≈element refl refl (λ ())
parseElement-print (impure (shape tag attrs zero ((x ∷ xs) ∷ []) pt pa px , f)) =
  openCase tag attrs zero ((x ∷ xs) ∷ []) pt pa px f (λ ())
    (trans (printTokens-node tag attrs zero ((x ∷ xs) ∷ []) pt pa px f)
           (cong (elementTokens tag attrs) (mixed-map zero ((x ∷ xs) ∷ []) f printTokens)))
parseElement-print (impure (shape tag attrs (suc n) (t ∷ ts) pt pa px , f)) =
  openCase tag attrs (suc n) (t ∷ ts) pt pa px f (λ i → parseElement-print (f i))
    (trans (printTokens-node tag attrs (suc n) (t ∷ ts) pt pa px f)
           (cong (elementTokens tag attrs) (mixed-map (suc n) (t ∷ ts) f printTokens)))

------------------------------------------------------------------------
-- `parser`
------------------------------------------------------------------------

parseTokens-printTokens : ∀ v → ∃ λ v′ → parseTokens (printTokens v) ≡ just v′ × v′ ≈ₓ v
parseTokens-printTokens v with parseElement-print v [] (suc (length (printTokens v))) (n≤1+n _)
... | v′ , p , ≈v =
  v′ ,
  cong parseWhole
    (subst (λ X → parseElement (suc (length (printTokens v))) X ≡ just (v′ , []))
           (++-identityʳ (printTokens v)) p) ,
  ≈v

-- A document to return where parsing fails.
defaultDoc : XMLDoc
defaultDoc = parent ('a' ∷ []) [] (zero , λ ())

-- `parser` (see `Data.XML.Goals`).  `to` pairs the tokens with the proof that
-- they are valid; `from` parses, with `defaultDoc` where parsing fails.
parser : RightInverse XMLSetoid ValidTokens
parser = record
  { to        = λ v → printTokens v , printTokens-valid v
  ; from      = λ x → fromMaybe defaultDoc (parseTokens (proj₁ x))
  ; to-cong   = printTokens-cong
  ; from-cong = λ { refl → ≈ₓ-refl }
  ; inverseʳ  = λ { {v} {ts , _} refl → inv v }
  }
  where
  inv : ∀ v → fromMaybe defaultDoc (parseTokens (printTokens v)) ≈ₓ v
  inv v with parseTokens-printTokens v
  ... | v′ , eq , ≈v = subst (_≈ₓ v) (sym (cong (fromMaybe defaultDoc) eq)) ≈v
