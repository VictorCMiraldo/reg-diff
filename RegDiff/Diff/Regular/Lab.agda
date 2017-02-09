open import Prelude hiding (⊥)
open import Prelude.Eq
open import Prelude.RelCalc.Base


module RegDiff.Diff.Regular.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Parms
  open ToyParms

  open import RegDiff.Diff.Universe konstants keqs PARMS WB-PARMS
  open import RegDiff.Diff.Trivial.Base konstants keqs PARMS WB-PARMS
    public
  open import RegDiff.Diff.Regular.Base konstants keqs PARMS WB-PARMS
    public


  Type1 : U
  Type1 = u1 
        ⊕ (I x₁ ⊗ I x₁ ⊗ []) 
        ⊕ []

  Type2 : U
  Type2 = Type1 ++ (I x₁ ⊗ I x₁ ⊗ I x₁ ⊗ []) ∷ []

  Type3 : U
  Type3 = I x₁ ⊗ I x₁ ⊗ I x₁ ⊗ I x₁ ⊗ I x₁ ⊗ [] ⊕ []

  Type4 : U
  Type4 = I x₁ ⊗ I x₁ ⊗ I x₁ ⊗ I x₁ ⊗ I x₁ ⊗ I x₁ ⊗ [] ⊕ []

  Prod1 : Prod 3
  Prod1 = K kℕ ⊗ I x₁ ⊗ I x₁ ⊗ I x₁ ⊗ []

  Prod2 : Prod 3
  Prod2 = K kℕ ⊗ I x₁ ⊗ I x₁ ⊗ []

  Prod3 : Prod 3
  Prod3 = I x₁ ⊗ I x₁ ⊗ []

  Prod4 : Prod 3
  Prod4 = K kℕ ⊗ K kℕ ⊗ []

  d1 : Patch* Type2
  d1 = diff1* (i2 (i1 (3 , 6 , unit))) 
              (i2 (i2 (i1 (5 , 3 , 6 , unit))))

  
  test1 : List (Al Trivialₐ Prod4 Prod4)
  test1 = align* (4 , 1 , unit) (10 , 20 , unit)

  test2 : List (Al Trivialₐ Prod1 Prod2)
  test2 = align* (4 , 1 , 2 , 3 , unit) (5 , 1 , 3 , unit)

  ProdG : ℕ → Prod 3
  ProdG zero = []
  ProdG (suc n) = K kℕ ⊗ ProdG n

  input : (n : ℕ) → ⟦ ProdG n ⟧ₚ
  input zero = unit
  input (suc n) = n , input n

  test3 : (n : ℕ) → List (Al Trivialₐ (ProdG n) (ProdG n))
  test3 n = align* (input n) (input n)

  size-test3-1 : length (test3 1) ≡ 1
  size-test3-1 = refl

  size-test3-2 : length (test3 2) ≡ 3
  size-test3-2 = refl

  size-test3-3 : length (test3 3) ≡ 9
  size-test3-3 = refl

  -- XXX: Surely, that must be defined in the stdlib?! Can't find it..
  _**_ : ℕ → ℕ → ℕ
  m ** zero = 1
  m ** suc n = m * (m ** n)

  -- XXX: the moment you think "hey, why would I prove something in Agda?"
  postulate
    size-test3 : ∀ n → length (test3 n) ≡ 3 ** (n ∸ 1)
