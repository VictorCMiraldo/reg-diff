open import Prelude
open import Prelude.Vector

module RegDiff.Generic.Eq 
    {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v) where

  open import RegDiff.Generic.Base v

  dec-eq : {A : Set}{{eqA : Eq A}}
         → (ty : U)(x y : ⟦ ty ⟧ A)
         → Dec (x ≡ y)
  dec-eq {{eq _≟_}} I x y 
    = x ≟ y
  dec-eq u1 unit unit 
    = yes refl
  dec-eq (K k) x y 
    = Eq.cmp (lookupᵢ k eqs) x y
  dec-eq (ty ⊕ tv) (i1 x) (i1 y) 
    with dec-eq ty x y
  ...| yes prf = yes (cong i1 prf)
  ...| no  prf = no (prf ∘ i1-inj)
  dec-eq (ty ⊕ tv) (i1 x) (i2 y) 
    = no (λ ())
  dec-eq (ty ⊕ tv) (i2 x) (i1 y) 
    = no (λ ())
  dec-eq (ty ⊕ tv) (i2 x) (i2 y) 
    with dec-eq tv x y
  ...| yes prf = yes (cong i2 prf)
  ...| no  prf = no (prf ∘ i2-inj)
  dec-eq (ty ⊗ tv) (x1 , x2) (y1 , y2)
    with dec-eq ty x1 y1
  ...| no prf = no (prf ∘ p1 ∘ ×-inj)
  ...| yes prf1
    with dec-eq tv x2 y2
  ...| no prf = no (prf ∘ p2 ∘ ×-inj)
  ...| yes prf2 = yes (cong₂ _,_ prf1 prf2)
           

  {-# TERMINATING #-}
  dec-eqμ : {ty : U}(x y : μ ty)
          → Dec (x ≡ y)
  dec-eqμ {ty} ⟨ x ⟩ ⟨ y ⟩ 
    with dec-eq {{eq dec-eqμ}} ty x y 
  ...| yes p = yes (cong ⟨_⟩ p)
  ...| no ¬p = no (¬p ∘ ⟨⟩-inj)
