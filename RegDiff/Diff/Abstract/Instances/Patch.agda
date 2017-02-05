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

module RegDiff.Diff.Abstract.Instances.Patch
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

open import RegDiff.Diff.Universe ks keqs A _≟-A_
open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Base ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Apply ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Lemmas ks keqs A _≟-A_

open Monad {{...}}

open import RegDiff.Diff.Abstract.Instances.Spine ks keqs A _≟-A_
  public
open import RegDiff.Diff.Abstract.Instances.Alignment ks keqs A _≟-A_
  public

Patch-Diffable : Diffable ⟦_⟧ₐ → Diffable₀ ⟦_⟧
Patch-Diffable doP = record 
  { P₀     = Patch (P doP)
  ; cands₀ = cands₀ (S-Diffable (Al-Diffable doP))
  ; apply₀ = apply₀ (S-Diffable (Al-Diffable doP))
  ; cost₀  = cost₀  (S-Diffable (Al-Diffable doP))
  }

Patch-CandsCorrect
  : (doP : Diffable ⟦_⟧ₐ)(okP : CandsCorrect ⟦_⟧ₐ doP)
  → CandsCorrect₀ ⟦_⟧ (Patch-Diffable doP)
Patch-CandsCorrect doP okP
  = S-CandsCorrect (Al-Diffable doP) (Al-CandsCorrect doP okP)
