open import Prelude hiding (_⊔_)
open import Prelude.Vector

{-
  Here we define the basic diffing functionality
  for the universe of regular types
-}

module RegDiff.Diff.Residual.Residual
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Diff.Base v eqs
  open import RegDiff.Diff.Properties.Aligned v eqs
    
  data C (A : Set) : U → Set where
    uuI : (o x y : A) → C A I
    uuK : (k : Fin n)(o x y : lookup k v) → C A (K k) 
    

  res : {A : Set}{{eqA : Eq A}}{ty : U}
      → (p q : D ⊥' ty A)(hip : p || q) → D (C A) ty A
  res (DB ()) q hip
  res p (DB ()) hip
  res D1 D1 hip = D1
  res {{eq _≟_}} (DA x1 x2) (DA y1 y2) hip 
    with x2 ≟ y2
  ...| yes _ = DA x2 x2
  ...| no  _ = DB (uuI x1 x2 y2)
  res (DK k x1 x2) (DK .k y1 y2) h 
    with Eq.cmp (ty-eq k) x2 y2
  ...| yes _ = DK k x1 x2
  ...| no  _ = DB (uuK k x1 x2 y2)
  res (D⊗ e1 e2) (D⊗ q1 q2) h 
    = D⊗ (res e1 q1 (p1 (×-inj h))) (res e2 q2 (p2 (×-inj h)))
  res (Di1 p) (Di1 q) h = Di1 (res p q (i1-inj h))
  res (Di1 p) (Di2 q) ()
  res (Di1 p) (Ds1 y1 y2) h = {!!}
  res (Di1 p) (Ds2 y1 y2) h = {!!}
  res (Di2 p) q h = {!!}
  res (Ds1 x1 x2) q h = {!!}
  res (Ds2 x1 x2) q h = {!!}
