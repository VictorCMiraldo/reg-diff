open import Prelude hiding (⊥)
open import Prelude.Eq
open import Prelude.RelCalc.Base


module RegDiff.Diff.Regular.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Parms
  open ToyParms
  open import RegDiff.Generic.Regular konstants public
  open import RegDiff.Generic.Eq konstants keqs public

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

  d1 : Patch* Type2
  d1 = diff1* (i2 (i1 (3 , 6 , unit))) 
              (i2 (i2 (i1 (5 , 3 , 6 , unit))))

  
