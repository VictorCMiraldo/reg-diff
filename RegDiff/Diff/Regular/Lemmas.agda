{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.List.All
open import Prelude.PartialFuncs.Base
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Lemmas
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Regular.Base ks keqs A _≟-A_
  open import RegDiff.Diff.Regular.Apply ks keqs A _≟-A_

-- TODO:
--       Move these lemmas somewhere more appropriate.
--
--

  ≟-Fin-refl
    : {n : ℕ}(i : Fin n) → (i ≟-Fin i) ≡ yes refl
  ≟-Fin-refl i with i ≟-Fin i
  ...| no abs = ⊥-elim (abs refl)
  ...| yes refl = refl

  sop-inject-inv
    : {ty : U}(i : Constr ty)(d : ⟦ typeOf ty i ⟧ₚ)
    → sop (inject {ty = ty} i d) ≡ strip i d
  sop-inject-inv {[]} () d
  sop-inject-inv {x ∷ ty} fz d = refl
  sop-inject-inv {x ∷ ty} (fs i) d 
    rewrite sop-inject-inv {ty} i d
      = refl

  fromInj-inject
    : {ty : U}(i : Constr ty)(d : ⟦ typeOf ty i ⟧ₚ)
    → from-inj (inject {ty = ty} i d) ≡ just d 
  fromInj-inject {ty} i d
    rewrite sop-inject-inv {ty} i d 
          | ≟-Fin-refl i
          = refl

  -- I though this would be more usefull... agda doesn't
  -- like this type of eliminator.
  spine-elim
    : {ty : U}(x y : ⟦ ty ⟧)
    → (x ≡ y × spine x y ≡ Scp)
    ⊎ Σ (Constr ty) 
        (λ i → Σ (⟦ typeOf ty i ⟧ₚ × ⟦ typeOf ty i ⟧ₚ)
                 (λ { (dx , dy) → spine x y ≡ Scns i (zipₚ dx dy) }))
    ⊎ Σ (Constr ty × Constr ty)
        (λ { (i , j) → Σ (⟦ typeOf ty i ⟧ₚ × ⟦ typeOf ty j ⟧ₚ)
               (λ { (dx , dy) → spine x y ≡ Schg i j (dx , dy) }) })
  spine-elim {ty} x y with dec-eq _≟-A_ ty x y
  ...| yes p = i1 (p , refl)
  ...| no  _ with sop x | sop y
  spine-elim _ _ | no _
     | strip cx dx | strip cy dy 
     with cx ≟-Fin cy
  spine-elim _ _ | no _ | strip cx dx | strip _ dy
     | yes refl 
     = i2 (i1 (cx , (dx , dy) , refl))
  spine-elim _ _ | no _ | strip cx dx | strip cy dy
     | no _ 
     = i2 (i2 ((cx , cy) , ((dx , dy) , refl)))
{-
  S-app-prod-ind-step
    : {y : Atom}{ty : Π}{P : ΠΠSet}(dx dy : ⟦ y ⟧ₐ)(dxs dys : ⟦ ty ⟧ₚ)
    → 
-}
-- The lemmas that follow have not been used
