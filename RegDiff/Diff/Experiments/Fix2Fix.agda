open import Prelude hiding (_⊔_)
open import Prelude.Vector

{-
  Here we experiment with a translation from Fixpoint2
  to Fixpoint representation of patches.
-}

module RegDiff.Diff.Experiments.Fix2Fix 
      {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Diff.Regular v eqs public
  open import RegDiff.Diff.Properties.Correctness.Regular v eqs
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

  -- And now, the hard proof...
  -- At the moment, I don't really believe I can prove this
{-
  mutual

    e2d : (ty : U)(x y : μ ty)
        → tr (F2.diffμ x y) ≡ F1.diffμ (x ∷ []) (y ∷ [])
    e2d ty x y
      with μ-chv x | μ-chv y
    ...| chX | chY
      with μ-hd x | μ-hd y
    ...| hdX | hdY 
      with ar ty hdX ≟-ℕ ar ty hdY | Stable-dec (diff ty hdX hdY)
    ...| no abs | yes p  = ⊥-elim (abs {!!})
    ...| yes p  | no abs = ⊥-elim (abs {!!})
    ...| no ¬p  | no  _  
      with ar ty hdX ≟-ℕ 0
    e2d ty x y | chX | chY | hdX | hdY | no _ | no _ | yes p₁ 
       = {!!}
    e2d ty x y | chX | chY | hdX | hdY | no _ | no _ | no p₁
       with ar ty hdY ≟-ℕ 0 
    e2d ty x y | chX | chY | hdX | hdY | no _ | no _ | no p₁ | yes p₂
      = {!!}
    e2d ty x y | chX | chY | hdX | hdY | no _ | no _ | no p₁ | no p₂
      = {!!}
    -- with ar ty hdX ≟-ℕ ar ty hdY | Stable-dec (diff ty hdX hdY)
    e2d ty x y | chX | chY | hdX | hdY | yes p  | yes _  
       = {!!}
-}
