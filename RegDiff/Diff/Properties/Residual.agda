open import Prelude
open import Prelude.Vector

module RegDiff.Diff.Properties.Residual
    {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Diff.Regular v eqs
  open import RegDiff.Diff.Fixpoint v eqs
  open import RegDiff.Diff.Properties.Aligned v eqs

  data Conflict : U → Set where
    GrowL : {ty : U}(x : ⟦ ty ⟧ Unit)
          → Al (μ ty) (ar ty x)
          → Conflict ty
    GrowR : {ty : U}(x : ⟦ ty ⟧ Unit)
          → Al (μ ty) (ar ty x)
          → Conflict ty
    GrowLR : {ty : U}(x : ⟦ ty ⟧ Unit)
           → Al (μ ty) (ar ty x)
           → (y : ⟦ ty ⟧ Unit)
           → Al (μ ty) (ar ty y)
           → Conflict ty


  res : {ty : U}{A : Set}
      → (p q : D' ty A) → p ∥ q → D Conflict ty A
  res p q hip = {!!}
  
  resμ : {ty : U}(p q : Dμ' ty) 
       → p ∥μ q → Dμ Conflict ty
  resμ (aux () p) _ hip
  resμ _ (aux () q) hip
  resμ (ins x cx p) (ins w cw q) hip 
    = aux (GrowLR x cx w cw) (resμ p q hip)
  resμ (ins x cx p) (del w cw q) hip 
    = aux (GrowL x cx) (resμ p (del w cw q) hip)
  resμ (ins x cx p) (mod w z h1 q) hip
    = aux (GrowL x cx) (resμ p (mod w z h1 q) hip)
  resμ (del x cx p) (ins w cw q) hip 
    = aux (GrowR w cw) (resμ (del x cx p) q hip)
  resμ (del x cx p) (del w cw q) (h0 , h1 , h2)
    = resμ p q h2
  resμ (del x cs p) (mod w z h1 q) (j0 , j1) 
    = {!!}
  resμ (mod x y h0 p) (ins w cw q) hip 
    = aux (GrowR w cw) (resμ (mod x y h0 p) q hip)
  resμ (mod x y h0 p) (del w cw q) hip = {!!}
  resμ (mod x y h0 p) (mod w z h1 q) hip = {!!}
