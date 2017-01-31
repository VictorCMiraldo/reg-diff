{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector using (Vec ; VecI)
open import Prelude.Monad
open import Prelude.List.All
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
  open import RegDiff.Diff.Regular.Lemmas ks keqs A _≟-A_

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

      S-app-Scns-elim
        : {ty : U}{i : Constr ty}{dx dy : ⟦ typeOf ty i ⟧ₚ}
        → (p : All (contr (P doP) ∘ β) (typeOf ty i))
        → S-app-prod (apply doP) p dx ≡ just dy
        → S-app (apply doP) (Scns i p) (inject {ty = ty} i dx) 
        ≡ just (inject i dy)
      S-app-Scns-elim {ty} {i} {dx} {dy} p hip 
        rewrite fromInj-inject {ty} i dx
              | hip
              = refl

      S-app-prod-hip
        : {ty : Π}(dx dy : ⟦ ty ⟧ₚ)
        → All (λ z → S-app-prod (apply doP) z dx ≡ just dy)
              (mapMᵢ (uncurry (cands doP)) (zipₚ dx dy))
      S-app-prod-hip {[]} unit unit = refl ∷ []
      S-app-prod-hip {x ∷ ty} (dx , dxs) (dy , dys)
        = All-bind-split 
          (uncurry (cands doP) ((dx , unit) , dy , unit))
          (λ qi → mapMᵢ (uncurry (cands doP)) (zipₚ dxs dys) 
              >>= return ∘ _∷_ qi) 
          {!!}


      lemma-cands-0 : {ty : U}(x y : ⟦ ty ⟧)
                    → All (IsCand₀ (S-Diffable doP) x y) 
                          (cands₀ (S-Diffable doP) x y)
      lemma-cands-0 {ty} x y with dec-eq _≟-A_ ty x y
      ...| yes p = (cong just p) ∷ []
      ...| no  _ with sop x | sop y
      lemma-cands-0 _ _ | no _
         | strip cx dx | strip cy dy 
         with cx ≟-Fin cy
      lemma-cands-0 _ _ | no _ | strip cx dx | strip _ dy
         | yes refl 
         = All-bind-return-split 
              (mapMᵢ (uncurry (cands doP)) (zipₚ dx dy)) 
              (Scns cx) 
              (All-transport (λ {x} p → S-app-Scns-elim x p) 
                             (S-app-prod-hip dx dy))
      lemma-cands-0 _ _ | no _ | strip cx dx | strip _ dy
         | no _ = {!!}

      IsDiff-S : IsDiff₀ ⟦_⟧ (S-Diffable doP)
      IsDiff-S = record
        { candidates-ok₀ = {!!}
        ; candidates-nonnil₀ = {!!}
        ; cost-eq = {!!}
        ; cost-order₀ = {!!}
        }
