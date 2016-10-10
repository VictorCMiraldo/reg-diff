open import Prelude
open import Prelude.Vector

module RegDiff.Diff.Properties.Identity
      {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Diff.Regular v eqs
  open import RegDiff.Diff.Fixpoint v eqs

{-
  An inductive characterization of when a diff is the identity diff
-}

  IsID : {A : Set}{ty : U}
       → D' ty A → Set
  IsID (DA ())
  IsID D1       = Unit
  IsID (DI x y) = x ≡ y
  IsID (DK k x y) = x ≡ y
  IsID (D⊗ p q) = IsID p × IsID q
  IsID (Di1 p) = IsID p
  IsID (Di2 p) = IsID p
  IsID (Ds1 x y) = ⊥
  IsID (Ds2 x y) = ⊥

  {-# TERMINATING #-}
  IsIDμ : {ty : U} → Dμ' ty → Set
  IsIDμ (aux () _)
  IsIDμ (ins _ _ _) = ⊥
  IsIDμ (del _ _ _) = ⊥
  IsIDμ (mod x y hip ds) = x ≡ y × All IsIDμ ds 

{-
  Decidability proofs
-}

  IsID? : {A : Set}{{eq : Eq A}}{ty : U}
        → (p : D' ty A) → Dec (IsID p)
  IsID? (DA ())
  IsID? D1 = yes unit
  IsID? {{eq _≟_}} (DI x y) = x ≟ y
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

  All? : {n : ℕ}{A : Set}{P : A → Set}
       → (dec : (a : A) → Dec (P a))
       → (v : Vec A n) → Dec (All P v)
  All? dec [] = yes []
  All? dec (x ∷ xs) 
    with dec x
  ...| no ¬h = no (λ { (pk ∷ _) → ¬h pk })
  ...| yes h 
    with All? dec xs
  ...| no ¬hs = no (λ { (_ ∷ pks) → ¬hs pks })
  ...| yes hs = yes (h ∷ hs)

  {-# TERMINATING #-}
  IsIDμ? : {ty : U}(p : Dμ' ty) → Dec (IsIDμ p)
  IsIDμ? (aux () _)
  IsIDμ? (ins _ _ _) = no (λ z → z)
  IsIDμ? (del _ _ _) = no (λ z → z)
  IsIDμ? {ty} (mod x y hip ds) 
    with dec-eq ty x y
  ...| no ¬x≡y = no (¬x≡y ∘ p1)
  ...| yes x≡y 
    with All? IsIDμ? ds
  ...| no ¬h = no (¬h ∘ p2)
  ...| yes h = yes (x≡y , h)

{-
  Now some correctness proofs
-}

  IsID-correct
    : {A : Set}{ty : U}
    → (p : D' ty A)(hip : IsID p)
    → D-src p ≡ D-dst p
  IsID-correct (DA ())
  IsID-correct D1 hip 
    = refl
  IsID-correct (DI x y) hip 
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
