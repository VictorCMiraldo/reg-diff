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

module RegDiff.Diff.Abstract.Instances.AlignmentNaive
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

open import RegDiff.Diff.Universe ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Base.AlignmentNaive ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Apply ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Lemmas ks keqs A _≟-A_

open Monad {{...}}

-- The same as we did for Spines, we now do for alignments.
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


    lemma-cands-ok 
      : {ty tv : Π}(x : ⟦ ty ⟧ₚ)(y : ⟦ tv ⟧ₚ)
      → All (IsCand (Al-Diffable doP) x y) (cands (Al-Diffable doP) x y)
    lemma-cands-ok {[]} {[]} unit unit 
      = refl ∷ []
    lemma-cands-ok {[]} {tv ∷ tvs} unit (y , ys) 
      = {!!}
    lemma-cands-ok {ty ∷ tys} {[]} (x , xs) unit
      = {!!}
    lemma-cands-ok {ty ∷ tys} {tv ∷ tvs} (x , xs) (y , ys) 
      = {!!}


    lemma-cands-length 
      : {ty tv : Π}(x : ⟦ ty ⟧ₚ)(y : ⟦ tv ⟧ₚ)
      → 1 ≤ length (cands (Al-Diffable doP) x y)
    lemma-cands-length x y = {!!}


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
      
      
