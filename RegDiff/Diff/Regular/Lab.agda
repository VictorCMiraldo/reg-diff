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
  open import RegDiff.Diff.Regular.Apply konstants keqs PARMS WB-PARMS
    public
  open import RegDiff.Diff.Regular.Domain konstants keqs PARMS WB-PARMS
    public

  Type1 : U
  Type1 = u1 ⊕ I x₁ ⊕ I x₁ ⊗ I x₁

  Type2 : U
  Type2 = (K kℕ) 
        ⊕ (K kBool) ⊗ I x₂
        ⊕ I x₁ ⊗ ((K kℕ) ⊕ I x₂)
        ⊕ I x₁ ⊗ I x₁

  Type3 : U
  Type3 = u1 ⊕ I x₃ ⊕ I x₃ ⊗ I x₃

  d1 : Patch Type1
  d1 = diff1 (i2 (i1 6)) (i2 (i2 (1 , 6)))

  d3 : Patch Type3
  d3 = diff1 (i2 (i1 (weighted 1))) (i2 (i2 (weighted 100 , weighted 30)))

{-
  module T1 where
  
    open DIFF    ℕ (const 1) public
    -- open DOMAINS ℕ (const 1) public

    d1 : Patch Type1
    d1 = diff1 (i2 (i1 1)) (i2 (i2 (6 , 1)))

    d2 : Patch Type2
    d2 = diff1 (i2 (i1 (true , 5))) (i1 5)


  open T1
-}
