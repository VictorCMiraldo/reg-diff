open import Prelude
open import Prelude.Eq
open import Prelude.Vector using (Vec ; VecI)
open import Prelude.Monad
open import Prelude.List.All
open import Prelude.List.Lemmas
open import Prelude.Nat.Lemmas
open import Prelude.PartialFuncs.Base

open import RegDiff.Generic.Parms

open import RegDiff.Diff.Abstract.Base

module RegDiff.Diff.Abstract.Instances.Multirec
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
    where

open Monad {{...}}
open Applicative {{...}}

import RegDiff.Generic.Multirec ks as MREC
import RegDiff.Generic.Eq ks keqs as EQ
import RegDiff.Diff.Multirec.Base ks keqs as BASE
import RegDiff.Diff.Multirec.Apply ks keqs as APPLY

module Internal {fam# : ℕ}(fam : MREC.Fam fam#) where

  open import RegDiff.Diff.Universe ks keqs (MREC.Fix fam) EQ._≟_
  open import RegDiff.Diff.Trivial.Base ks keqs (MREC.Fix fam) EQ._≟_
  open import RegDiff.Diff.Abstract.Instances.Trivial ks keqs (MREC.Fix fam) EQ._≟_
  open import RegDiff.Diff.Abstract.Instances.Patch ks keqs (MREC.Fix fam) EQ._≟_
  open BASE.Internal fam
  open APPLY.Internal fam

  Fix-Diffable : Diffable (Fix fam)
  Fix-Diffable = record 
    { P = λ a b → Patchμ (T a) (T b)
    ; cands = diffμ* 
    ; apply = Patchμ-app 
    ; cost = Patchμ-cost 
    }

  Lift-Fix-Diffable : Diffable ⟦_⟧ₐ
  Lift-Fix-Diffable = record 
    { P = UU→AA Patchμ 
    ; cands = diffμ*-atoms
    ; apply = α-app Patchμ-app₀
    ; cost = {!!}
    }

  Patchμ-app-ins
    : {k : Famᵢ}{ty : U}(x : Fix fam k)(cy : Constr ty)
    → (dy : ⟦ typeOf ty cy ⟧ₚ)
    → {p : Al (UU→AA Patchμ) (I k ∷ []) (typeOf ty cy)}
    → Al-app (α-app Patchμ-app₀) p (x , unit) ≡ just dy
    → Patchμ-app₀ (ins cy p) (unmu x) ≡ just (inject {ty = ty} cy dy)
  Patchμ-app-ins ⟨ x ⟩ cy dy hip 
    rewrite hip = refl

  Patchμ-app-del
    : {ty : U}{k : Famᵢ}(cx : Constr ty)(dx : ⟦ typeOf ty cx ⟧ₚ)
    → (y : Fix fam k)
    → {p : Al (UU→AA Patchμ) (typeOf ty cx) (I k ∷ [])}
    → Al-app (α-app Patchμ-app₀) p dx ≡ just (y , unit)
    → Patchμ-app₀ (del cx p) (inject {ty = ty} cx dx) ≡ just (unmu y)
  Patchμ-app-del {ty = ty} cx dx ⟨ y ⟩ hip 
    rewrite sop-inject-inv {ty = ty} cx dx 
          | ≟-Fin-refl cx
          | hip
          = refl

  Patchμ-app-fix
    : {k k' : Famᵢ}(x : ⟦ I k ⟧ₐ)(y : ⟦ I k' ⟧ₐ)
    → {p : P Fix-Diffable k k'}
    → IsCand Fix-Diffable x y p
    → IsCand Lift-Fix-Diffable x y (fix p)
  Patchμ-app-fix ⟨ x ⟩ ⟨ y ⟩ {p = p} hip 
    with Patchμ-app₀ p x
  ...| nothing = hip
  ...| just px = hip

  private
    mutual
      alignμ'-correct
        : {ty tv : Π}(xs : ⟦ ty ⟧ₚ)(ys : ⟦ tv ⟧ₚ)
        → All (λ p → Al-app (α-app Patchμ-app₀) p xs ≡ just ys)  
              (alignμ' xs ys)
      alignμ'-correct {[]} {[]} xs ys = []
      alignμ'-correct {[]} {_ ∷ _} xs ys = []
      alignμ'-correct {_ ∷ _} {[]} xs ys = []
      alignμ'-correct {ty ∷ tys} {tv ∷ tvs} xs ys 
        = Al-Correct Lift-Fix-Diffable lemma-lift-cands-correct xs ys

      lemma-ins-correct₀
        : {k : Famᵢ}{ty : U}(x : Fix fam k)(y : ⟦ ty ⟧)
        → All (λ p → Patchμ-app₀ p (unmu x) ≡ just y) (diffμ*-ins x y)
      lemma-ins-correct₀ x y with sop y
      lemma-ins-correct₀ x _ | strip cy dy
        = All-<$>-commute (ins cy) 
                          (mapᵢ (λ {p} → Patchμ-app-ins x cy dy {p}) 
                                (alignμ'-correct (x , unit) dy))

      lemma-ins-correct
        : {k k' : Famᵢ}(x : Fix fam k)(y : ⟦ T k' ⟧)
        → All (λ p → Patchμ-app {k} {k'} p x ≡ just ⟨ y ⟩) (diffμ*-ins x y)
      lemma-ins-correct {k} {k'} x y
        = mapᵢ (λ {p} → Patchμ-app-app₀-trₗ {k} {k'} x y {p}) 
               (lemma-ins-correct₀ x y)

      lemma-del-correct₀
        : {ty : U}{k' : Famᵢ}(x : ⟦ ty ⟧)(y : Fix fam k')
        → All (λ p → Patchμ-app₀ p x ≡ just (unmu y)) (diffμ*-del x y)
      lemma-del-correct₀ x y with sop x
      lemma-del-correct₀ {ty = ty} _ y | strip cx dx
        = All-<$>-commute (del cx) 
                          (mapᵢ (λ {p} → Patchμ-app-del {ty = ty} cx dx y {p}) 
                                (alignμ'-correct dx (y , unit)))

      lemma-del-correct
        : {k k' : Famᵢ}(x : ⟦ T k ⟧)(y : Fix fam k')
        → All (λ p → Patchμ-app {k} {k'} p ⟨ x ⟩ ≡ just y) (diffμ*-del x y)
      lemma-del-correct {k} {k'} x y
        = mapᵢ (λ {p} → Patchμ-app-app₀-trᵣ {k} {k'} x y {p}) 
               (lemma-del-correct₀ x y)

      lemma-mod-correct
        : {k k' : Famᵢ}(x : ⟦ T k ⟧)(y : ⟦ T k' ⟧)
        → All (λ p → Patchμ-app {k} {k'} p ⟨ x ⟩ ≡ just ⟨ y ⟩) 
              (diffμ*-mod x y)
      lemma-mod-correct x y = {!!}

      {-# TERMINATING #-}
      lemma-cands-correct
        : {k k' : Famᵢ}(x : Fix fam k)(y : Fix fam k')
        → All (IsCand Fix-Diffable x y) (cands Fix-Diffable x y)
      lemma-cands-correct {k} {k'} ⟨ x ⟩ ⟨ y ⟩ 
        = lemma-mod-correct {k} {k'} x y 
        ++ₐ (lemma-ins-correct {k} {k'} ⟨ x ⟩ y 
        ++ₐ  lemma-del-correct {k} {k'} x ⟨ y ⟩)

      lemma-lift-cands-correct
        : CandsCorrect ⟦_⟧ₐ Lift-Fix-Diffable
      lemma-lift-cands-correct {I k} {I k'} x y
        = All-<$>-commute fix 
                          (mapᵢ (λ {p} → Patchμ-app-fix x y {p}) 
                          (lemma-cands-correct x y))
      lemma-lift-cands-correct {K k} {K k'} x y 
        = {!!} ∷ []
      lemma-lift-cands-correct {I _} {K _}  x y = []
      lemma-lift-cands-correct {K _} {I _}  x y = []



  Fix-Correct : CandsCorrect (Fix fam) Fix-Diffable
  Fix-Correct = lemma-cands-correct

  Lift-Fix-Correct : CandsCorrect ⟦_⟧ₐ Lift-Fix-Diffable
  Lift-Fix-Correct = lemma-lift-cands-correct

  
