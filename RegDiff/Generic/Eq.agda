open import Prelude
open import Prelude.Eq
open import Prelude.Vector

module RegDiff.Generic.Eq 
    {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v) where

  open import RegDiff.Generic.Base v

  K-inj : {i j : Fin n} → K i ≡ K j → i ≡ j
  K-inj refl = refl

  ⊗-inj : {a b c d : U} → a ⊗ b ≡ c ⊗ d → a ≡ c × b ≡ d
  ⊗-inj refl = refl , refl

  ⊕-inj : {a b c d : U} → a ⊕ b ≡ c ⊕ d → a ≡ c × b ≡ d
  ⊕-inj refl = refl , refl

  U-eq : (ty tv : U) → Dec (ty ≡ tv)
  U-eq I I = yes refl
  U-eq I u1 = no (λ ())
  U-eq I (K k) = no (λ ())
  U-eq I (tv ⊕ tv₁) = no (λ ())
  U-eq I (tv ⊗ tv₁) = no (λ ())
  U-eq u1 I = no (λ ())
  U-eq u1 u1 = yes refl
  U-eq u1 (K k) = no (λ ())
  U-eq u1 (tv ⊕ tv₁) = no (λ ())
  U-eq u1 (tv ⊗ tv₁) = no (λ ())
  U-eq (K k) I = no (λ ())
  U-eq (K k) u1 = no (λ ())
  U-eq (K k) (K k₁) 
    with k ≟-Fin k₁
  ...| yes prf = yes (cong K prf)
  ...| no  abs = no (abs ∘ K-inj)
  U-eq (K k) (tv ⊕ tv₁) = no (λ ())
  U-eq (K k) (tv ⊗ tv₁) = no (λ ())
  U-eq (ty ⊕ ty₁) I = no (λ ())
  U-eq (ty ⊕ ty₁) u1 = no (λ ())
  U-eq (ty ⊕ ty₁) (K k) = no (λ ())
  U-eq (ty ⊕ ty₁) (tv ⊕ tv₁) 
    with U-eq ty tv | U-eq ty₁ tv₁
  ...| no abs | _ = no (abs ∘ p1 ∘ ⊕-inj)
  ...| yes h0 | no abs = no (abs ∘ p2 ∘ ⊕-inj)
  ...| yes h0 | yes h1 = yes (cong₂ _⊕_ h0 h1)
  U-eq (ty ⊕ ty₁) (tv ⊗ tv₁) = no (λ ())
  U-eq (ty ⊗ ty₁) I = no (λ ())
  U-eq (ty ⊗ ty₁) u1 = no (λ ())
  U-eq (ty ⊗ ty₁) (K k) = no (λ ())
  U-eq (ty ⊗ ty₁) (tv ⊕ tv₁) = no (λ ())
  U-eq (ty ⊗ ty₁) (tv ⊗ tv₁) 
    with U-eq ty tv | U-eq ty₁ tv₁
  ...| no abs | _ = no (abs ∘ p1 ∘ ⊗-inj)
  ...| yes h0 | no abs = no (abs ∘ p2 ∘ ⊗-inj)
  ...| yes h0 | yes h1 = yes (cong₂ _⊗_ h0 h1)

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

  instance
    μ-eq : {T : U} → Eq (μ T)
    μ-eq = eq dec-eqμ
