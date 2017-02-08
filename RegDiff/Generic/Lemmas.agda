open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.List.All
open import Prelude.PartialFuncs.Base
open import RegDiff.Generic.Parms

module RegDiff.Generic.Lemmas
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open import RegDiff.Generic.Multirec ks
  open import RegDiff.Generic.Eq ks keqs

  private
    U : Set
    U = Sum parms#

  ≟-Fin-refl
    : {n : ℕ}(i : Fin n) → (i ≟-Fin i) ≡ yes refl
  ≟-Fin-refl i with i ≟-Fin i
  ...| no abs = ⊥-elim (abs refl)
  ...| yes refl = refl

  sop-inject-inv
    : {ty : U}(i : Constr ty)(d : ⟦ typeOf ty i ⟧ₚ A)
    → sop (inject {ty = ty} i d) ≡ strip i d
  sop-inject-inv {[]} () d
  sop-inject-inv {x ∷ ty} fz d = refl
  sop-inject-inv {x ∷ ty} (fs i) d 
    rewrite sop-inject-inv {ty} i d
      = refl

  fromInj-inject
    : {ty : U}(i : Constr ty)(d : ⟦ typeOf ty i ⟧ₚ A)
    → from-inj (inject {ty = ty} i d) ≡ just d 
  fromInj-inject {ty} i d
    rewrite sop-inject-inv {ty} i d 
          | ≟-Fin-refl i
          = refl
