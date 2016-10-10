open import Prelude hiding (_⊔_)
open import Prelude.Vector

{-
  Here we define the basic diffing functionality
  for the universe of regular types
-}

module RegDiff.Diff.Regular
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
  USet : Set₁
  USet = U → Set

  data D (P : USet) : U → Set → Set where
    DA  : {A : Set}{ty : U} → P ty → D P ty A
    D1  : {A : Set} → D P u1 A
    DI  : {A : Set}(x y : A) → D P I A
    DK  : {A : Set}(k : Fin n)
        → (x y : lookup k v) → D P (K k) A
    D⊗  : {A : Set}{ty tv : U}
        → D P ty A → D P tv A → D P (ty ⊗ tv) A
    Di1 : {A : Set}{ty tv : U}
        → D P ty A → D P (ty ⊕ tv) A
    Di2 : {A : Set}{ty tv : U}
        → D P tv A → D P (ty ⊕ tv) A
    Ds1 : {A : Set}{ty tv : U}
        → ⟦ ty ⟧ A → ⟦ tv ⟧ A → D P (ty ⊕ tv) A
    Ds2 : {A : Set}{ty tv : U}
        → ⟦ tv ⟧ A → ⟦ ty ⟧ A → D P (ty ⊕ tv) A

  D' : U → Set → Set
  D' = D (λ _ → ⊥) 

  D-src : {A : Set}{ty : U} → D' ty A → ⟦ ty ⟧ A
  D-src (DA ())
  D-src D1 = unit
  D-src (DI x y) = x
  D-src (DK k x y) = x
  D-src (D⊗ d e) = D-src d , D-src e
  D-src (Di1 d) = i1 (D-src d)
  D-src (Di2 d) = i2 (D-src d)
  D-src (Ds1 x y) = i1 x
  D-src (Ds2 x y) = i2 x

  D-dst : {A : Set}{ty : U} → D' ty A → ⟦ ty ⟧ A
  D-dst (DA ())
  D-dst D1 = unit
  D-dst (DI x y) = y
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
       → (x y : ⟦ ty ⟧ A) → D' ty A
  diff I x y 
    = DI x y
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
       → D' ty A → ℕ
  cost (DA ())
  cost D1 = 0
  cost (DI x y) = 1
  cost (DK k x y)
    = dec-elim (const 0) (const 1) (Eq.cmp (ty-eq k) x y)
  cost (D⊗ d e) = cost d + cost e
  cost (Di1 d) = cost d
  cost (Di2 d) = cost d
  cost {A} {ty ⊕ tv} (Ds1 x y) = 1 + size ty x + size tv y
  cost {A} {ty ⊕ tv} (Ds2 x y) = 1 + size tv x + size ty y

  _⊔_ : {A : Set}{ty : U}
      → (d e : D' ty A) → D' ty A
  d ⊔ e with cost d ≤?-ℕ cost e
  ...| yes _ = d
  ...| no  _ = e

{-
  It is very important to know which diffs change, or not, the
  arity of their source.

  We say a patch is stable if it does not change any coproduct,
  and, hence, keeps the arity.

  Stable : {A : Set}{ty : U} → D ty A → Set
  Stable D1 = Unit
  Stable (DA x y) = Unit
  Stable (DK k x y) = Unit
  Stable (D⊗ d e) = Stable d × Stable e
  Stable (Di1 d) = Stable d
  Stable (Di2 d) = Stable d
  Stable {ty = ty ⊕ tv} (Ds1 x y) = ar ty x ≡ ar tv y
  Stable {ty = ty ⊕ tv} (Ds2 x y) = ar tv x ≡ ar ty y

  -- Stability is trivial do decide
  Stable-dec : {A : Set}{ty : U}(d : D ty A)
             → Dec (Stable d)
  Stable-dec D1 = yes unit
  Stable-dec (DA x y) = yes unit
  Stable-dec (DK k x y) = yes unit
  Stable-dec (D⊗ d e) 
    with Stable-dec d
  ...| no ¬p = no (¬p ∘ p1)
  ...| yes p 
    with Stable-dec e
  ...| no ¬q = no (¬q ∘ p2)
  ...| yes q = yes (p , q)
  Stable-dec (Di1 d) = Stable-dec d
  Stable-dec (Di2 d) = Stable-dec d
  Stable-dec {ty = ty ⊕ tv} (Ds1 x y) 
    = ar ty x ≟-ℕ ar tv y
  Stable-dec {ty = ty ⊕ tv} (Ds2 x y) 
    = ar tv x ≟-ℕ ar ty y
-}
{- 
  Application is also very simple
-}

  apply : {A : Set}{{eqA : Eq A}}(ty : U)
        → D' ty A → ⟦ ty ⟧ A → Maybe (⟦ ty ⟧ A)
  apply _ (DA ())
  apply {{eq _≟_}} I (DI x y) e 
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
