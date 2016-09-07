open import Prelude hiding (_⊔_)
open import Prelude.Vector

module RegDiff.Diff.Properties.Aligned
    {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v) where

  open import RegDiff.Diff.Base v eqs

  _||_ : {A : Set}{ty : U}
       → (p q : D ⊥' ty A) → Set
  p || q = D-src p ≡ D-src q
