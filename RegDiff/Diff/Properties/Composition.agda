open import Prelude
open import Prelude.Vector

module RegDiff.Diff.Properties.Composition
      {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Diff.Regular v eqs
  open import RegDiff.Diff.Fixpoint2 v eqs
  open import RegDiff.Diff.Properties.Sequential v eqs

  comp : {A : Set}{ty : U}
       → (p q : D ty A)(hip : p ⟶ q)
       → D ty A
  comp D1 D1 hip = D1
  comp (DA x0 x1) (DA y0 y1) hip = DA x0 y1
  comp (DK k x0 x1) (DK .k y0 y1) hip = DK k x0 y1
  comp (D⊗ pp pq) (D⊗ qp qq) hip 
    = let hip0 , hip1 = ×-inj hip
       in D⊗ (comp pp qp hip0) (comp pq qq hip1)
  comp (Di1 p) (Di1 q) hip 
    = Di1 (comp p q (i1-inj hip))
  comp (Di1 p) (Ds1 y0 y1) hip 
    = Ds1 (D-src p) y1
  comp (Di2 p) (Di2 q) hip 
    = Di2 (comp p q (i2-inj hip))
  comp (Di2 p) (Ds2 y0 y1) hip 
    = Ds2 (D-src p) y1  
  comp (Ds1 x0 x1) (Di2 q) hip 
    = Ds1 x0 (D-dst q)
  comp (Ds1 x0 x1) (Ds2 y0 y1) hip 
    = Di1 (diff _ x0 y1)
  comp (Ds2 x0 x1) (Di1 q) hip 
    = Ds2 x0 (D-dst q)
  comp (Ds2 x0 x1) (Ds1 y0 y1) hip 
    = Di2 (diff _ x0 y1)
  comp (Di1 p) (Di2 q) () 
  comp (Di1 p) (Ds2 y0 y1) ()
  comp (Di2 p) (Di1 q) () 
  comp (Di2 p) (Ds1 y0 y1) ()
  comp (Ds1 x0 x1) (Di1 q) ()
  comp (Ds1 x0 x1) (Ds1 y0 y1) ()
  comp (Ds2 x0 x1) (Di2 q) ()
  comp (Ds2 x0 x1) (Ds2 y0 y1) ()

  compμ : {ty : U}(p q : Dμ ty)
        → (hip : p ⟶μ q)
        → Dμ ty
  compμ p (ins y am q) hip = ins y am (compμ p q hip)
  compμ (del x al p) q hip = del x al (compμ p q hip)
  compμ (ins x al p) (del y am q) hip 
    = compμ p q (⟶μ-ins-del x y al am p q hip)
  compμ (ins x al d) (mod y0 y1 hip₀ qs) hip = {!!}
  compμ (mod x y hip₀ ds) q hip = {!!}
