{-# OPTIONS --safe --cubical-compatible -WnoUnsupportedIndexedMatch #-}

module Data.JSON.Geo where


open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Sign using (+; -)
open import Data.String using (String; _==_; fromList)
open import Data.List using (List; []; _∷_; map; foldr; concatMap)
import Data.List as List
open import Data.Product using (_×_; _,_; proj₁; proj₂; map₁)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin using (Fin; zero; suc)
open import Data.Float using (Float; fromℤ; _+_; _÷_) renaming (_-_ to _f-_)
open import Function using (_∘_; _$_; id)

open import Data.Container hiding (Position)
import Data.Container.Combinator as CC
open import Data.Container.FreeMonad as FM

open import Data.JSON.AST
open JSONCont
  using
  ( JSONType; object; array; prim; objectCToEntries; PrimJSONType; primstring; primnumber
  ; primbool; primnull
  )

------------------------------------------------------------------------
-- Target Cartographic Structures
------------------------------------------------------------------------

data Space : Set where
  WGS84     : Space
  Projected : Space

record Position (s : Space) : Set where
  constructor pos
  field
    lon : Float
    lat : Float
    alt : Maybe Float

record BoundingBox (s : Space) : Set where
  constructor bbox
  field
    minLon minLat maxLon maxLat : Float

data Geometry (s : Space) : Set where
  Point           : Position s → Geometry s
  LineString      : List (Position s) → Geometry s
  Polygon         : List (List (Position s)) → Geometry s
  MultiPolygon    : List (List (List (Position s))) → Geometry s

data FeaturePayload : Set where
  Political  : (iso3 : String) (colorIdx7 : Fin 7) (isDisputed : Bool) → FeaturePayload
  Hydrology  : (strokeWeight : Float) → FeaturePayload
  Physical   : (featureClass : String) → FeaturePayload
  Unknown    : FeaturePayload

record LoD : Set where
  constructor lodInfo
  field
    scaleRank : ℕ
    minZoom   : Float

record NEFeatureMeta : Set where
  constructor neMeta
  field
    lod     : LoD
    name    : Maybe String
    payload : FeaturePayload

record Feature (s : Space) (Props : Set) : Set where
  constructor mkFeature
  field
    geometry   : Maybe (Geometry s)
    properties : Props

record FeatureCollection (s : Space) (Props : Set) : Set where
  constructor mkFeatureCollection
  field
    features : List (Feature s Props)

------------------------------------------------------------------------
-- Eliminators for JSON
------------------------------------------------------------------------

-- Structural View of a JSON node
data JSONView : Set where
  VObject : List (String × JSON) → JSONView
  VArray  : (n : ℕ) (lookup : Fin n → JSON) → JSONView
  VString : String → JSONView
  VNumber : JSONNumber → JSONView
  VBool   : Bool → JSONView
  VNull   : JSONView

-- Top-level pattern eliminator (unpacks Container Free Monad node directly)
matchJSON : JSON → JSONView
matchJSON (impure ((object , shp) , pos)) =
  VObject (List.map (map₁ fromList) (objectCToEntries (shp , pos)))
matchJSON (impure ((array , n) , pos)) =
  VArray n pos
matchJSON (impure ((prim primstring , str) , _)) = VString (fromList str)
matchJSON (impure ((prim primnumber , num) , _)) = VNumber num
matchJSON (impure ((prim primbool , b) , _))     = VBool b
matchJSON (impure ((prim primnull , _) , _))     = VNull

------------------------------------------------------------------------
-- Direct Selective Decoders
------------------------------------------------------------------------

jsonNumToFloat : JSONNumber → Float
jsonNumToFloat (jsonNumber s integral frac exp) =
  let
    finToFloat : Fin 10 → Float
    finToFloat n = fromℤ (+_ (Data.Fin.toℕ n))

    fracFloat : List (Fin 10) → Float
    fracFloat []       = 0.0
    fracFloat (d ∷ ds) = (finToFloat d + fracFloat ds) ÷ 10.0

    baseVal = fromℤ (+_ integral) + fracFloat frac
  in case s of λ where
       - → 0.0 f- baseVal
       + → baseVal
  where
  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x

lookupProp : String → List (String × JSON) → Maybe JSON
lookupProp _ [] = nothing
lookupProp k ((k' , v) ∷ rest) with k == k'
... | true  = just v
... | false = lookupProp k rest

getString : JSON → Maybe String
getString j with matchJSON j
... | VString s = just s
... | _         = nothing

getFloat : JSON → Maybe Float
getFloat j with matchJSON j
... | VNumber n = just (jsonNumToFloat n)
... | _         = nothing

getNat : JSON → Maybe ℕ
getNat j with matchJSON j
... | VNumber _ = just 0 -- conversion hook
... | _         = nothing

getObject : JSON → Maybe (List (String × JSON))
getObject j with matchJSON j
... | VObject kvs = just kvs
... | _           = nothing

-- Fast coordinate unpacker: directly reads [lon, lat]
parseCoord : JSON → Maybe (Position WGS84)
parseCoord j with matchJSON j
... | VArray 2 lookup = do
  lon ← getFloat (lookup zero)
  lat ← getFloat (lookup (suc zero))
  just (pos lon lat nothing)
  where
  open import Category.Monad using (RawMonad)
  open import Data.Maybe.Categorical using (monad)
  open RawMonad monad
... | VArray (suc (suc (suc _))) lookup = do
  lon ← getFloat (lookup zero)
  lat ← getFloat (lookup (suc zero))
  alt ← getFloat (lookup (suc (suc zero)))
  just (pos lon lat (just alt))
  where
  open import Category.Monad using (RawMonad)
  open import Data.Maybe.Categorical using (monad)
  open RawMonad monad
... | _ = nothing

-- Coordinate arrays (LineStrings, Rings)
parseCoordList : JSON → List (Position WGS84)
parseCoordList j with matchJSON j
... | VArray n lookup =
  let
    collect : ∀ k → (Fin k → JSON) → List (Position WGS84)
    collect zero _     = []
    collect (suc m) lk with parseCoord (lk zero)
    ... | just p  = p ∷ collect m (lk ∘ suc)
    ... | nothing = collect m (lk ∘ suc)
  in collect n lookup
... | _ = []

parseRings : JSON → List (List (Position WGS84))
parseRings j with matchJSON j
... | VArray n lookup =
  let
    collect : ∀ k → (Fin k → JSON) → List (List (Position WGS84))
    collect zero _    = []
    collect (suc m) lk = parseCoordList (lk zero) ∷ collect m (lk ∘ suc)
  in collect n lookup
... | _ = []

-- Geometry decoder: selectively reads only "type" and "coordinates"
parseGeometry : JSON → Maybe (Geometry WGS84)
parseGeometry j with getObject j
... | nothing  = nothing
... | just kvs = do
  typeStr ← lookupProp "type" kvs >>= getString
  coords  ← lookupProp "coordinates" kvs
  case typeStr of λ where
    "Point"        → Data.Maybe.map Point (parseCoord coords)
    "LineString"   → just (LineString (parseCoordList coords))
    "Polygon"      → just (Polygon (parseRings coords))
    "MultiPolygon" →
      case matchJSON coords of λ where
        (VArray n lk) →
          let
            collect : ∀ k → (Fin k → JSON) → List (List (List (Position WGS84)))
            collect zero _     = []
            collect (suc m) lk' = parseRings (lk' zero) ∷ collect m (lk' ∘ suc)
          in just (MultiPolygon (collect n lk))
        _ → nothing
    _              → nothing
  where
  open import Category.Monad using (RawMonad)
  open import Data.Maybe.Categorical using (monad)
  open RawMonad monad
  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x

-- Properties decoder: pulls only relevant cartographic attributes
parseProperties : JSON → NEFeatureMeta
parseProperties j with getObject j
... | nothing  = neMeta (lodInfo 0 0.0) nothing Unknown
... | just kvs =
  let
    sRank   = Data.Maybe.fromMaybe 0 (lookupProp "scalerank" kvs >>= getNat)
    mZoom   = Data.Maybe.fromMaybe 0.0 (lookupProp "min_zoom" kvs >>= getFloat)
    pName   = lookupProp "NAME" kvs >>= getString
    fClass  = lookupProp "featurecla" kvs >>= getString
    iso3    = lookupProp "ADM0_A3" kvs >>= getString

    payload = case (iso3 , fClass) of λ where
      (just code , _)    → Political code zero false
      (_ , just "River") → Hydrology 1.0
      (_ , just cls)     → Physical cls
      _                  → Unknown
  in neMeta (lodInfo sRank mZoom) pName payload
  where
  open import Category.Monad using (RawMonad)
  open import Data.Maybe.Categorical using (monad)
  open import Data.Maybe using (fromMaybe)
  open RawMonad monad
  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x

-- Top-level Feature and FeatureCollection decoders
parseFeature : JSON → Maybe (Feature WGS84 NEFeatureMeta)
parseFeature j with getObject j
... | nothing  = nothing
... | just kvs =
  let
    geom  = lookupProp "geometry" kvs >>= parseGeometry
    props = parseProperties (Data.Maybe.fromMaybe (impure ((prim primnull , tt) , λ ())) (lookupProp "properties" kvs))
  in just (mkFeature geom props)
  where
  open import Category.Monad using (RawMonad)
  open import Data.Maybe.Categorical using (monad)
  open RawMonad monad

parseFeatureCollection : JSON → FeatureCollection WGS84 NEFeatureMeta
parseFeatureCollection j with getObject j
... | nothing  = mkFeatureCollection []
... | just kvs with lookupProp "features" kvs
...   | nothing       = mkFeatureCollection []
...   | just featNode with matchJSON featNode
...     | VArray n lookup =
      let
        collect : ∀ k → (Fin k → JSON) → List (Feature WGS84 NEFeatureMeta)
        collect zero _     = []
        collect (suc m) lk with parseFeature (lk zero)
        ... | just f  = f ∷ collect m (lk ∘ suc)
        ... | nothing = collect m (lk ∘ suc)
      in mkFeatureCollection (collect n lookup)
...     | _ = mkFeatureCollection []