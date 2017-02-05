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

module RegDiff.Diff.Abstract.Instances.Alignment
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

open import RegDiff.Diff.Universe ks keqs A _≟-A_
open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Base.AlignmentOptimized ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Apply ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Lemmas ks keqs A _≟-A_

open Monad {{...}}

-- The diffable is virtually the same as the AlignmentNaive version
Al-Diffable : Diffable ⟦_⟧ₐ → Diffable ⟦_⟧ₚ
Al-Diffable doP = record 
  { P     = Al (P doP) 
  ; cands = λ x y → align* x y >>= Al-mapM (uncurry (cands doP))
  ; apply = Al-app (apply doP) 
  ; cost  = Al-cost (cost doP) 
  }

private 
  module HypothesisCands 
           (doP : Diffable ⟦_⟧ₐ)
           (okP : CandsCorrect ⟦_⟧ₐ doP)
      where

    open CandsCorrect

    open import RegDiff.Diff.Abstract.Instances.AlignmentNaive 
      ks keqs A _≟-A_ 
      renaming ( Al-Diffable to AlN-Diffable
               ; Al-CandsCorrect to AlN-CandsCorrect)

    postulate
      opt⊆naive 
        : {ty tv : Π}(x : ⟦ ty ⟧ₚ)(y : ⟦ tv ⟧ₚ)
        → cands (Al-Diffable doP) x y ⊆ cands (AlN-Diffable doP) x y

    lemma-cands-ok 
        : {ty tv : Π}(x : ⟦ ty ⟧ₚ)(y : ⟦ tv ⟧ₚ)
        → All (IsCand (Al-Diffable doP) x y) (cands (Al-Diffable doP) x y)
    lemma-cands-ok x y 
      = All-⊆ (opt⊆naive x y) 
              (cands-correct (AlN-CandsCorrect doP okP) x y)

    postulate
      lemma-cands-length 
        : {ty tv : Π}(x : ⟦ ty ⟧ₚ)(y : ⟦ tv ⟧ₚ)
        → 1 ≤ length (cands (Al-Diffable doP) x y)

    Al-CandsCorrect-priv : CandsCorrect ⟦_⟧ₚ (Al-Diffable doP)
    Al-CandsCorrect-priv = record
      { cands-correct = lemma-cands-ok
      ; cands-nonnil  = lemma-cands-length
      }

-- Finally, we export a concise definition!
Al-CandsCorrect : (doP : Diffable ⟦_⟧ₐ)(okP : CandsCorrect ⟦_⟧ₐ doP)
               → CandsCorrect ⟦_⟧ₚ (Al-Diffable doP)
Al-CandsCorrect doP okP = Al-CandsCorrect-priv
  where
    open HypothesisCands doP okP
