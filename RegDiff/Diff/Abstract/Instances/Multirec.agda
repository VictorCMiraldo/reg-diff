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
  open BASE.Internal fam
  open APPLY.Internal fam

  Fix-Diffable : Diffable (Fix fam)
  Fix-Diffable = record 
    { P = λ a b → Patchμ (T a) (T b)
    ; cands = diffμ* 
    ; apply = Patchμ-app 
    ; cost = Patchμ-cost 
    }

  private
    lemma-ins-correct₀
      : {k : Famᵢ}{ty : U}(x : Fix fam k)(y : ⟦ ty ⟧)
      → All (λ p → Patchμ-app₀ p (unmu x) ≡ just y) (diffμ*-ins x y)
    lemma-ins-correct₀ x y with sop y
    lemma-ins-correct₀ x _ | strip cy dy
      = All-<$>-commute {!!} {!!}

    lemma-ins-correct
      : {k k' : Famᵢ}(x : Fix fam k)(y : ⟦ T k' ⟧)
      → All (λ p → Patchμ-app {k} {k'} p x ≡ just ⟨ y ⟩) (diffμ*-ins x y)
    lemma-ins-correct {k} {k'} x y
      = mapᵢ (λ {p} → Patchμ-app-app₀-trₗ {k} {k'} x y {p}) 
             (lemma-ins-correct₀ x y)

    lemma-del-correct₀
      : {ty : U}{k' : Famᵢ}(x : ⟦ ty ⟧)(y : Fix fam k')
      → All (λ p → Patchμ-app₀ p x ≡ just (unmu y)) (diffμ*-del x y)
    lemma-del-correct₀ x y = {!!}

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
    lemma-mod-correct = {!!}

    lemma-cands-correct
      : {k k' : Famᵢ}(x : Fix fam k)(y : Fix fam k')
      → All (IsCand Fix-Diffable x y) (cands Fix-Diffable x y)
    lemma-cands-correct {k} {k'} ⟨ x ⟩ ⟨ y ⟩ 
      = lemma-mod-correct {k} {k'} x y 
      ++ₐ (lemma-ins-correct {k} {k'} ⟨ x ⟩ y 
      ++ₐ  lemma-del-correct {k} {k'} x ⟨ y ⟩)
      


  Fix-CandsCorrect : CandsCorrect (Fix fam) Fix-Diffable
  Fix-CandsCorrect = record
    { cands-correct = lemma-cands-correct
    ; cands-nonnil  = {!!}
    }

  
