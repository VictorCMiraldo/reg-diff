open import Prelude hiding (_⊔_)
open import Prelude.Vector

{-
  Here we define the basic diffing functionality
  for the universe of regular types
-}

module RegDiff.Diff.Base 
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

{-
  First we introduce some definitions to
  take care of our module parameters
-}

  ty-eq : (k : Fin n) → Eq (lookup k v)
  ty-eq k = lookupᵢ k eqs

{- 
  Now we import the universe of codes for the given constants
-}

  open import RegDiff.Generic.Base v
    public
  open import RegDiff.Generic.Eq v eqs
    public

{- 
  Definition of patches for regular datatypes follow
-}

  data D (B : U → Set) : U → Set → Set where
    DB  : {A : Set}{ty : U} → B ty → D B ty A
    D1  : {A : Set} → D B u1 A
    DA  : {A : Set}(x y : A) → D B I A
    DK  : {A : Set}(k : Fin n)
        → (x y : lookup k v) → D B (K k) A
    D⊗  : {A : Set}{ty tv : U}
        → D B ty A → D B tv A → D B (ty ⊗ tv) A
    Di1 : {A : Set}{ty tv : U}
        → D B ty A → D B (ty ⊕ tv) A
    Di2 : {A : Set}{ty tv : U}
        → D B tv A → D B (ty ⊕ tv) A
    Ds1 : {A : Set}{ty tv : U}
        → ⟦ ty ⟧ A → ⟦ tv ⟧ A → D B (ty ⊕ tv) A
    Ds2 : {A : Set}{ty tv : U}
        → ⟦ tv ⟧ A → ⟦ ty ⟧ A → D B (ty ⊕ tv) A

  ⊥' : U → Set
  ⊥' _ = ⊥

  D-src : {A : Set}{ty : U} → D ⊥' ty A → ⟦ ty ⟧ A
  D-src (DB ())
  D-src D1 = unit
  D-src (DA x y) = x
  D-src (DK k x y) = x
  D-src (D⊗ d e) = D-src d , D-src e
  D-src (Di1 d) = i1 (D-src d)
  D-src (Di2 d) = i2 (D-src d)
  D-src (Ds1 x y) = i1 x
  D-src (Ds2 x y) = i2 x

  D-dst : {A : Set}{ty : U} → D ⊥' ty A → ⟦ ty ⟧ A
  D-dst (DB ())
  D-dst D1 = unit
  D-dst (DA x y) = y
  D-dst (DK k x y) = y
  D-dst (D⊗ d e) = D-dst d , D-dst e
  D-dst (Di1 d) = i1 (D-dst d)
  D-dst (Di2 d) = i2 (D-dst d)
  D-dst (Ds1 x y) = i2 y
  D-dst (Ds2 x y) = i1 y

{-
  The diffing function is trivial
-}

  diff : {A : Set}(ty : U)
       → (x y : ⟦ ty ⟧ A) → D ⊥' ty A
  diff I x y 
    = DA x y
  diff u1 x y 
    = D1
  diff (K k) x y 
    = DK k x y
  diff (ty ⊕ tv) (i1 x) (i1 y) = Di1 (diff ty x y)
  diff (ty ⊕ tv) (i1 x) (i2 y) = Ds1 x y
  diff (ty ⊕ tv) (i2 x) (i1 y) = Ds2 x y
  diff (ty ⊕ tv) (i2 x) (i2 y) = Di2 (diff tv x y)
  diff (ty ⊗ tv) (x1 , x2) (y1 , y2) 
    = D⊗ (diff ty x1 y1 ) (diff tv x2 y2)

  cost : {A : Set}{ty : U}
       → D ⊥' ty A → ℕ
  cost (DB ())
  cost D1 = 1
  cost (DA x y) = 1
  cost (DK k x y)
    = dec-elim (const 0) (const 1) (Eq.cmp (ty-eq k) x y)
  cost (D⊗ d e) = cost d + cost e
  cost (Di1 d) = cost d
  cost (Di2 d) = cost d
  cost {A} {ty ⊕ tv} (Ds1 x y) = 1 + size ty x + size tv y
  cost {A} {ty ⊕ tv} (Ds2 x y) = 1 + size tv x + size ty y

  _⊔_ : {A : Set}{ty : U}
      → (d e : D ⊥' ty A) → D ⊥' ty A
  d ⊔ e with cost d ≤?-ℕ cost e
  ...| yes _ = d
  ...| no  _ = e

{- 
  Application is also very simple
-}

  apply : {A : Set}{{eqA : Eq A}}(ty : U)
        → D ⊥' ty A → ⟦ ty ⟧ A → Maybe (⟦ ty ⟧ A)
  apply ty (DB ()) e
  apply {{eq _≟_}} I (DA x y) e 
    with x ≟ e
  ...| yes _ = just y
  ...| no  _ = nothing
  apply u1 D1 e = just unit
  apply (K k) (DK _ x y) e
    with Eq.cmp (ty-eq k) x e
  ...| yes _ = just y
  ...| no  _ = nothing
  apply (ty ⊗ tv) (D⊗ d1 d2) (x , y) 
    = _,_ <M> apply ty d1 x <M*> apply tv d2 y
  apply (ty ⊕ tv) (Di1 d) (i1 e) 
    = i1 <M> apply ty d e
  apply (ty ⊕ tv) (Di1 d) (i2 e) 
    = nothing
  apply (ty ⊕ tv) (Di2 d) (i1 e) 
    = nothing
  apply (ty ⊕ tv) (Di2 d) (i2 e) 
    = i2 <M> apply tv d e
  apply (ty ⊕ tv) (Ds1 x y) (i1 e) 
    with dec-eq ty x e
  ...| yes _ = just (i2 y)
  ...| no  _ = nothing
  apply (ty ⊕ tv) (Ds1 x y) (i2 e) 
    = nothing
  apply (ty ⊕ tv) (Ds2 x y) (i1 e) 
    = nothing
  apply (ty ⊕ tv) (Ds2 x y) (i2 e)
    with dec-eq tv x e
  ...| yes _ = just (i1 y)
  ...| no  _ = nothing
  
{-
  Now we repeat everything for fixed points
-}

  data Dμ (B : U → Set)(ty : U) : Set where
    Dμ-nil : Dμ B ty
    Dμ-B   : B ty → Dμ B ty → Dμ B ty
    Dμ-ins : ⟦ ty ⟧ Unit → Dμ B ty → Dμ B ty
    Dμ-del : ⟦ ty ⟧ Unit → Dμ B ty → Dμ B ty
    Dμ-mod : D B ty Unit   → Dμ B ty → Dμ B ty

  μ-ins : {ty : U} → ⟦ ty ⟧ Unit → List (μ ty) → List (μ ty)
  μ-ins {ty} x xs
    = let xs0 , xs1 = lsplit (ar ty x) xs
       in maybe (λ y → y ∷ xs1) [] (μ-plug x xs0)

  Dμ-src : {ty : U} → Dμ ⊥' ty → List (μ ty)
  Dμ-src (Dμ-B () d)
  Dμ-src Dμ-nil = []
  Dμ-src (Dμ-ins x d) = Dμ-src d
  Dμ-src (Dμ-del x d) = μ-ins x (Dμ-src d)
  Dμ-src (Dμ-mod x d) = μ-ins (D-src x) (Dμ-src d)

  Dμ-dst : {ty : U} → Dμ ⊥' ty → List (μ ty)
  Dμ-dst (Dμ-B () d)
  Dμ-dst Dμ-nil = []
  Dμ-dst (Dμ-del x d) = Dμ-dst d
  Dμ-dst (Dμ-ins x d) = μ-ins x (Dμ-dst d)
  Dμ-dst (Dμ-mod x d) = μ-ins (D-dst x) (Dμ-dst d)
  
  costμ : {ty : U} → Dμ ⊥' ty → ℕ
  costμ Dμ-nil = 0
  costμ (Dμ-B () d)
  costμ {ty} (Dμ-ins x d) = size ty x + costμ d
  costμ {ty} (Dμ-del x d) = size ty x + costμ d
  costμ {ty} (Dμ-mod x d) = cost x + costμ d

  _⊔μ_ : {ty : U} → Dμ ⊥' ty → Dμ ⊥' ty → Dμ ⊥' ty
  d ⊔μ e with costμ d ≤?-ℕ costμ e
  ...| yes _ = d
  ...| no  _ = e

  {-# TERMINATING #-}
  diffμ : {ty : U}(x y : List (μ ty)) → Dμ ⊥' ty
  diffμ []       []       = Dμ-nil
  diffμ []       (y ∷ ys) = Dμ-ins (μ-hd y) (diffμ [] (μ-ch y ++ ys)) 
  diffμ (x ∷ xs) []       = Dμ-del (μ-hd x) (diffμ (μ-ch x ++ xs) [])
  diffμ {ty} (x ∷ xs) (y ∷ ys) 
    = let d1 = Dμ-ins (μ-hd y) (diffμ (x ∷ xs) (μ-ch y ++ ys)) 
          d2 = Dμ-del (μ-hd x) (diffμ (μ-ch x ++ xs) (y ∷ ys))
          d3 = Dμ-mod (diff ty (μ-hd x) (μ-hd y)) 
                      (diffμ (μ-ch x ++ xs) (μ-ch y ++ ys))
       in d3 ⊔μ (d1 ⊔μ d2)

  applyμ : {ty : U} → Dμ ⊥' ty → List (μ ty) → Maybe (List (μ ty))
  applyμ (Dμ-B () d) l
  applyμ Dμ-nil [] = just []
  applyμ Dμ-nil (x ∷ l) = nothing
  applyμ (Dμ-ins x d) l = μ-ins x <M> applyμ d l
  applyμ (Dμ-del x d) [] = nothing
  applyμ {ty} (Dμ-del x d) (l₀ ∷ l) 
    with dec-eq ty x (μ-hd l₀)
  ...| yes _ = applyμ d (μ-ch l₀ ++ l)
  ...| no  _ = nothing
  applyμ (Dμ-mod x d) [] = nothing
  applyμ {ty} (Dμ-mod x d) (l₀ ∷ l) 
    with apply ty x (μ-hd l₀) 
  ...| nothing = nothing
  ...| just x' = μ-ins x' <M> applyμ d (μ-ch l₀ ++ l)
