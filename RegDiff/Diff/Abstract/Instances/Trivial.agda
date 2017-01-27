open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.PartialFuncs.Base

open import RegDiff.Generic.Parms

open import RegDiff.Diff.Abstract.Base

module RegDiff.Diff.Abstract.Instances.Trivial
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_
  open import RegDiff.Diff.Trivial.Apply ks keqs A _≟-A_

  diffable-delta : {A : Set}(P : A → Set)
                 → (eqA : (x y : A) → Dec (x ≡ y))
                 → (eqP : (k : A)(x y : P k) → Dec (x ≡ y))
                 → Diffable P
  diffable-delta P eqA eqP = record 
    { P = delta P 
    ; cands = λ x y → (x , y) ∷ [] 
    ; apply = Δ-apply P eqA eqP 
    ; cost = cost-delta P eqA eqP 
    }

  
