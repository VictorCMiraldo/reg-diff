open import Prelude hiding (_⊔_)
open import Prelude.Vector
open import Prelude.ListProperties

open import Data.Nat using (_<_)
open import Prelude.NatProperties

{-
  Here we prove basic correctness properties
  for our diff primitives.
-}

module RegDiff.Diff.Properties.Correctness.Regular
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Diff.Regular v eqs
  open import RegDiff.Diff.Fixpoint v eqs

{- 
  diff source and destination lemmas.
-}

  diff-src-lemma
    : {A : Set}(ty : U)(x y : ⟦ ty ⟧ A)
    → D-src (diff ty x y) ≡ x
  diff-src-lemma I x y = refl
  diff-src-lemma u1 unit unit = refl
  diff-src-lemma (K k) x y = refl
  diff-src-lemma (ty ⊕ tv) (i1 x) (i1 y) 
    = cong i1 (diff-src-lemma ty x y)
  diff-src-lemma (ty ⊕ tv) (i1 x) (i2 y) 
    = refl
  diff-src-lemma (ty ⊕ tv) (i2 x) (i1 y) 
    = refl
  diff-src-lemma (ty ⊕ tv) (i2 x) (i2 y) 
    = cong i2 (diff-src-lemma tv x y)
  diff-src-lemma (ty ⊗ tv) (x1 , x2) (y1 , y2)
    = cong₂ _,_ (diff-src-lemma ty x1 y1) 
                (diff-src-lemma tv x2 y2)

  diff-dst-lemma
    : {A : Set}(ty : U)(x y : ⟦ ty ⟧ A)
    → D-dst (diff ty x y) ≡ y
  diff-dst-lemma I x y = refl
  diff-dst-lemma u1 unit unit = refl
  diff-dst-lemma (K k) x y = refl
  diff-dst-lemma (ty ⊕ tv) (i1 x) (i1 y) 
    = cong i1 (diff-dst-lemma ty x y)
  diff-dst-lemma (ty ⊕ tv) (i1 x) (i2 y) 
    = refl
  diff-dst-lemma (ty ⊕ tv) (i2 x) (i1 y) 
    = refl
  diff-dst-lemma (ty ⊕ tv) (i2 x) (i2 y) 
    = cong i2 (diff-dst-lemma tv x y)
  diff-dst-lemma (ty ⊗ tv) (x1 , x2) (y1 , y2)
    = cong₂ _,_ (diff-dst-lemma ty x1 y1) 
                (diff-dst-lemma tv x2 y2)

{- 
  Application respects src and dst
-}

  apply-lemma 
    : {A : Set}{{eqA : Eq A}}{ty : U}(d : D ty A)
    → apply ty d (D-src d) ≡ just (D-dst d)
  apply-lemma D1 = refl
  apply-lemma {{eq _≟_}} (DA x y) 
    with x ≟ x
  ...| yes _ = refl
  ...| no ¬p = ⊥-elim (¬p refl)
  apply-lemma (DK k x y) 
    with Eq.cmp (ty-eq k) x x
  ...| no ¬p = ⊥-elim (¬p refl)
  ...| yes _ = refl
  apply-lemma (D⊗ d e) 
    rewrite apply-lemma d
          | apply-lemma e
          = refl
  apply-lemma (Di1 d) 
    rewrite apply-lemma d = refl
  apply-lemma (Di2 d) 
    rewrite apply-lemma d = refl 
  apply-lemma {ty = ty ⊕ tv} (Ds1 x y) 
    with dec-eq ty x x
  ...| yes _ = refl 
  ...| no ¬p = ⊥-elim (¬p refl)
  apply-lemma {ty = ty ⊕ tv} (Ds2 x y)
    with dec-eq tv x x
  ...| yes _ = refl 
  ...| no ¬p = ⊥-elim (¬p refl)

{-
  Now some lemmas about stability
-}

  stable-ar-lemma 
    : {A : Set}{ty : U}(d : D ty A)(hip : Stable d)
    → ar ty (D-src d) ≡ ar ty (D-dst d)
  stable-ar-lemma D1 hip = refl
  stable-ar-lemma (DA x y) hip = refl
  stable-ar-lemma (DK k x y) hip = refl
  stable-ar-lemma (D⊗ d e) (hipd , hipe) 
    = cong₂ _+_ (stable-ar-lemma d hipd) (stable-ar-lemma e hipe)
  stable-ar-lemma (Di1 d) hip = stable-ar-lemma d hip
  stable-ar-lemma (Di2 d) hip = stable-ar-lemma d hip
  stable-ar-lemma (Ds1 x y) p = p
  stable-ar-lemma (Ds2 x y) p = p

{-
  Last but not least, cost function lemmas
-}

  ≤-refl : {n : ℕ} → n ≤ n
  ≤-refl {zero} = z≤n
  ≤-refl {suc n} = s≤s ≤-refl

  postulate
    +-exch : ∀ m n o p → (m + n) + (o + p) ≡ (m + o) + (n + p)

  cost-ubnd
    : {A : Set}(ty : U)(x y : ⟦ ty ⟧ A)
    → cost (diff ty x y) < size ty x + size ty y
  cost-ubnd I x y = s≤s (s≤s z≤n)
  cost-ubnd (K k) x y 
    with Eq.cmp (ty-eq k) x y
  ...| yes _ = s≤s z≤n
  ...| no  _ = s≤s (s≤s z≤n)
  cost-ubnd u1 x y = (s≤s z≤n)
  cost-ubnd (ty ⊕ tv) (i1 x) (i1 y) 
    rewrite +-suc (size ty x) (size ty y)
          = ≤-step (≤-step (cost-ubnd ty x y))
  cost-ubnd (ty ⊕ tv) (i1 x) (i2 y) 
    rewrite +-suc (size ty x) (size tv y)
          = ≤-refl
  cost-ubnd (ty ⊕ tv) (i2 x) (i1 y) 
    rewrite +-suc (size tv x) (size ty y)
          = ≤-refl
  cost-ubnd (ty ⊕ tv) (i2 x) (i2 y)
    rewrite +-suc (size tv x) (size tv y)
          = ≤-step (≤-step (cost-ubnd tv x y))
  cost-ubnd (ty ⊗ tv) (x1 , x2) (y1 , y2) 
    rewrite +-exch (size ty x1) (size tv x2) (size ty y1) (size tv y2)
          = ≤-+-distr (cost-ubnd ty x1 y1) 
                      (≤-unstep (cost-ubnd tv x2 y2))

