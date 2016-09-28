open import Prelude
open import Prelude.Vector

module RegDiff.Diff.Properties.Identity
      {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Diff.Regular v eqs
  -- open import RegDiff.Diff.Fixpoint v eqs

  IsID : {A : Set}{ty : U}
       → D ty A → Set
  IsID D1       = Unit
  IsID (DA x y) = x ≡ y
  IsID (DK k x y) = x ≡ y
  IsID (D⊗ p q) = IsID p × IsID q
  IsID (Di1 p) = IsID p
  IsID (Di2 p) = IsID p
  IsID (Ds1 x y) = ⊥
  IsID (Ds2 x y) = ⊥

  IsID? : {A : Set}{{eq : Eq A}}{ty : U}
        → (p : D ty A) → Dec (IsID p)
  IsID? D1 = yes unit
  IsID? {{eq _≟_}} (DA x y) = x ≟ y
  IsID? (DK k x y) = Eq.cmp (ty-eq k) x y
  IsID? (D⊗ p q) 
    with IsID? p
  ...| no ¬h = no (¬h ∘ p1)
  ...| yes h
    with IsID? q
  ...| no ¬j = no (¬j ∘ p2)
  ...| yes j = yes (h , j)
  IsID? (Di1 p) = IsID? p
  IsID? (Di2 p) = IsID? p
  IsID? (Ds1 x y) = no (λ z → z)
  IsID? (Ds2 x y) = no (λ z → z)

  IsID-correct
    : {A : Set}{ty : U}
    → (p : D ty A)(hip : IsID p)
    → D-src p ≡ D-dst p
  IsID-correct D1 hip 
    = refl
  IsID-correct (DA x y) hip 
    = hip
  IsID-correct (DK k x y) hip 
    = hip
  IsID-correct (D⊗ p q) (h0 , h1)
    = cong₂ _,_ (IsID-correct p h0) (IsID-correct q h1)
  IsID-correct (Di1 p) hip 
    = cong i1 (IsID-correct p hip)
  IsID-correct (Di2 p) hip 
    = cong i2 (IsID-correct p hip)
  IsID-correct (Ds1 x y) ()
  IsID-correct (Ds2 x y) ()
