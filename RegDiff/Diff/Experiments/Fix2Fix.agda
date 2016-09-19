open import Prelude hiding (_⊔_)
open import Prelude.Vector

{-
  Here we experiment with a translation from Fixpoint2
  to Fixpoint representation of patches.
-}

module RegDiff.Diff.Experiments.Fix2Fix 
      {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Diff.Regular v eqs
  open import RegDiff.Diff.Fixpoint  v eqs as F1
  open import RegDiff.Diff.Fixpoint2 v eqs as F2

  {-# TERMINATING #-}
  flatten-with 
    : {ty : U}{n : ℕ} → (⟦ ty ⟧ Unit → F1.Dμ ty → F1.Dμ ty) 
    → Vec (μ ty) n → F1.Dμ ty
  flatten-with f [] = Dμ-nil
  flatten-with f (x ∷ xs) = f (μ-hd x) (flatten-with f (μ-chv x ++v xs))

  _+++_ : {ty : U} → F1.Dμ ty → F1.Dμ ty → F1.Dμ ty
  Dμ-nil       +++ f = f
  (Dμ-ins x d) +++ f = Dμ-ins x (d +++ f)
  (Dμ-del x d) +++ f = Dμ-del x (d +++ f)
  (Dμ-mod x d) +++ f = Dμ-mod x (d +++ f)

  mutual
    al-with : {ty : U}{n : ℕ}
            → (⟦ ty ⟧ Unit → F1.Dμ ty → F1.Dμ ty) 
            → Al (μ ty) n → F1.Dμ ty → F1.Dμ ty
    al-with {n = zero}  f  unit cont 
      = Dμ-nil
    al-with {n = suc n} f (v ∷ vs , fz)   cont 
      = cont +++ flatten-with f vs
    al-with {n = suc zero} f (v ∷ vs , fs ()) cont 
    al-with {n = suc (suc n)} f (v ∷ vs , fs i) cont 
      = flatten-with f (v ∷ []) +++ al-with f (vs , i) cont

    tr : {ty : U} → F2.Dμ ty → F1.Dμ ty
    tr (Dμ.ins x al d) 
      = Dμ-ins x (al-with Dμ-ins al (tr d))
    tr (Dμ.del x al d) 
      = Dμ-del x (al-with Dμ-del al (tr d))
    tr {ty} (Dμ.mod x y hip d) 
      = Dμ-mod (diff ty x y) (tr* d)

    tr* : {ty : U}{n : ℕ} → Vec (F2.Dμ ty) n → F1.Dμ ty
    tr* [] = Dμ-nil
    tr* (v ∷ vs) = tr v +++ tr* vs
