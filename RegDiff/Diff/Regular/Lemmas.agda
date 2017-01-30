open import Prelude
open import Prelude.Eq
open import Prelude.Vector
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

  spine-cns≢Scp : {ty : U}(x y : ⟦ ty ⟧)
               → spine-cns x y ≡ Scp → ⊥
  spine-cns≢Scp x y hip with sop x | sop y
  spine-cns≢Scp _ _ hip
    | strip cx dx | strip cy dy 
    with cx ≟-Fin cy
  spine-cns≢Scp _ _ () | strip _ _ | strip _ _ 
     | yes refl
  spine-cns≢Scp _ _ () | strip _ _ | strip _ _ 
     | no  _ 


  Scp-elim : {ty : U}(x y : ⟦ ty ⟧)
           → spine x y ≡ Scp → x ≡ y
  Scp-elim {ty} x y hip 
    with dec-eq _≟-A_ ty x y 
  ...| yes p     = p
  ...| no  _     = ⊥-elim (spine-cns≢Scp x y hip)
