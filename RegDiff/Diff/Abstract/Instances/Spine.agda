open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.ListI
open import Prelude.PartialFuncs.Base

open import RegDiff.Generic.Parms

open import RegDiff.Diff.Abstract.Base

module RegDiff.Diff.Abstract.Instances.Spine
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Regular.Base ks keqs A _≟-A_
  open import RegDiff.Diff.Regular.Apply ks keqs A _≟-A_

  open Monad {{...}}

  S-Diffable : Diffable ⟦_⟧ₚ → Diffable₀ ⟦_⟧
  S-Diffable doP = record 
    { P₀     = S (P doP) 
    ; cands₀ = λ x y → S-mapM (uncurry (cands doP)) (spine x y)
    ; apply₀ = S-app (apply doP) 
    ; cost₀ = S-cost (cost doP) 
    }

  private 
    module Hypothesis (doP : Diffable ⟦_⟧ₚ)
                            (IsDiff-P : IsDiff ⟦_⟧ₚ doP)
        where

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

      spine≡Scp-elim : {ty : U}(x y : ⟦ ty ⟧)
                     → spine x y ≡ Scp → x ≡ y
      spine≡Scp-elim {ty} x y hip 
        with dec-eq _≟-A_ ty x y 
      ...| yes p     = p
      ...| no  _     = ⊥-elim (spine-cns≢Scp x y hip)

      lemma-cands-0 : {ty : U}(x y : ⟦ ty ⟧)
                    → All (IsCand₀ (S-Diffable doP) x y) 
                          (cands₀ (S-Diffable doP) x y)
      lemma-cands-0 x y with spine x y
      ...| Scp        = {!!}
      ...| Scns i ps  = {!!}
      ...| Schg i j p = {!!}
       
      IsDiff-S : IsDiff₀ ⟦_⟧ (S-Diffable doP)
      IsDiff-S = record
        { candidates-ok₀ = {!!}
        ; candidates-nonnil₀ = {!!}
        ; cost-eq = {!!}
        ; cost-order₀ = {!!}
        }
