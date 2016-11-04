open import Prelude
open import Prelude.Eq

module RegDiff.Diff.Regular.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Base konstants public
  open import RegDiff.Generic.Eq konstants keqs public

  import RegDiff.Diff.Regular.Base konstants keqs 
    as DIFF
  import RegDiff.Diff.Regular.Domains konstants keqs
    as DOMAINS

  Type1 : U
  Type1 = u1 ⊕ I ⊕ I ⊗ I

  Type2 : U
  Type2 = (K kℕ) 
        ⊕ (K kBool) ⊗ I 
        ⊕ I ⊗ ((K kℕ) ⊕ I)
        ⊕ I ⊗ I

  module T1 where
  
    open DIFF    ℕ (const 1) public
    open DOMAINS ℕ (const 1) public

    d1 : S Δ Type1 Type1
    d1 = diff1 (i2 (i1 1)) (i2 (i2 (6 , 1)))

    d2 : S Δ Type2 Type2
    d2 = diff1 (i2 (i1 (true , 5))) (i1 5)


  open T1 public
