open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import RegDiff.Generic.Parms

module RegDiff.Generic.Eq 
    {ks# : ℕ}(ks : Vec Set ks#)(eqs : VecI Eq ks) where

  open import RegDiff.Generic.Multirec ks

  I-inj : {n : ℕ}{k l : Fin n} → I k ≡ I l → k ≡ l
  I-inj refl = refl

  K-inj : {n : ℕ}{i j : Fin ks#} → K {n = n} i ≡ K j → i ≡ j
  K-inj refl = refl

  ⊗-inj : {n : ℕ}{a b c d : Uₙ n} → a ⊗ b ≡ c ⊗ d → a ≡ c × b ≡ d
  ⊗-inj refl = refl , refl

  ⊕-inj : {n : ℕ}{a b c d : Uₙ n} → a ⊕ b ≡ c ⊕ d → a ≡ c × b ≡ d
  ⊕-inj refl = refl , refl

  U-eq : {n : ℕ}(ty tv : Uₙ n) → Dec (ty ≡ tv)
  U-eq (I x) (I y) with x ≟-Fin y
  ...| yes h0  = yes (cong I h0)
  ...| no  abs = no (abs ∘ I-inj)
  U-eq (I _) u1 = no (λ ())
  U-eq (I _) (tv ⊕ tv₁) = no (λ ())
  U-eq (I _) (tv ⊗ tv₁) = no (λ ())
  U-eq (I _) (K _) = no (λ ())
  U-eq (K k) (I _) = no (λ ())
  U-eq (K k) u1 = no (λ ())
  U-eq (K k) (K k₁) 
    with k ≟-Fin k₁
  ...| yes prf = yes (cong K prf)
  ...| no  abs = no (abs ∘ K-inj)
  U-eq (K k) (tv ⊕ tv₁) = no (λ ())
  U-eq (K k) (tv ⊗ tv₁) = no (λ ())
  U-eq u1 (I _) = no (λ ())
  U-eq u1 (K _) = no (λ ())
  U-eq u1 u1 = yes refl
  U-eq u1 (tv ⊕ tv₁) = no (λ ())
  U-eq u1 (tv ⊗ tv₁) = no (λ ())
  U-eq (ty ⊕ ty₁) (I _) = no (λ ())
  U-eq (ty ⊕ ty₁) (K _) = no (λ ())
  U-eq (ty ⊕ ty₁) u1 = no (λ ())
  U-eq (ty ⊕ ty₁) (tv ⊕ tv₁) 
    with U-eq ty tv | U-eq ty₁ tv₁
  ...| no abs | _ = no (abs ∘ p1 ∘ ⊕-inj)
  ...| yes h0 | no abs = no (abs ∘ p2 ∘ ⊕-inj)
  ...| yes h0 | yes h1 = yes (cong₂ _⊕_ h0 h1)
  U-eq (ty ⊕ ty₁) (tv ⊗ tv₁) = no (λ ())
  U-eq (ty ⊗ ty₁) (I _) = no (λ ())
  U-eq (ty ⊗ ty₁) (K _) = no (λ ())
  U-eq (ty ⊗ ty₁) u1 = no (λ ())
  U-eq (ty ⊗ ty₁) (tv ⊕ tv₁) = no (λ ())
  U-eq (ty ⊗ ty₁) (tv ⊗ tv₁) 
    with U-eq ty tv | U-eq ty₁ tv₁
  ...| no abs | _ = no (abs ∘ p1 ∘ ⊗-inj)
  ...| yes h0 | no abs = no (abs ∘ p2 ∘ ⊗-inj)
  ...| yes h0 | yes h1 = yes (cong₂ _⊗_ h0 h1)

  dec-eq : {n : ℕ}{A : Parms n}
         → (eqA : ∀{k}(x y : A k) → Dec (x ≡ y))
         → (ty : Uₙ n)(x y : ⟦ ty ⟧ A)
         → Dec (x ≡ y)
  dec-eq e (I k) x y 
    = e x y
  dec-eq e u1 unit unit 
    = yes refl
  dec-eq e (K k) x y 
    = Eq.cmp (lookupᵢ k eqs) x y
  dec-eq e (ty ⊕ tv) (i1 x) (i1 y) 
    with dec-eq e ty x y
  ...| yes prf = yes (cong i1 prf)
  ...| no  prf = no (prf ∘ i1-inj)
  dec-eq e (ty ⊕ tv) (i1 x) (i2 y) 
    = no (λ ())
  dec-eq e (ty ⊕ tv) (i2 x) (i1 y) 
    = no (λ ())
  dec-eq e (ty ⊕ tv) (i2 x) (i2 y) 
    with dec-eq e tv x y
  ...| yes prf = yes (cong i2 prf)
  ...| no  prf = no (prf ∘ i2-inj)
  dec-eq e (ty ⊗ tv) (x1 , x2) (y1 , y2)
    with dec-eq e ty x1 y1
  ...| no prf = no (prf ∘ p1 ∘ ×-inj)
  ...| yes prf1
    with dec-eq e tv x2 y2
  ...| no prf = no (prf ∘ p2 ∘ ×-inj)
  ...| yes prf2 = yes (cong₂ _,_ prf1 prf2)

  {-# TERMINATING #-}
  _≟_ : {n : ℕ}{F : Fam n}{k : Fin n}
      → (x y : Fix F k) 
      → Dec (x ≡ y)
  _≟_ {n} {F} {k} ⟨ x ⟩ ⟨ y ⟩ 
    with dec-eq _≟_ (lookup k F) x y
  ...| yes h0  = yes (cong ⟨_⟩ h0)
  ...| no  abs = no (abs ∘ ⟨⟩-inj)
