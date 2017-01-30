open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.PartialFuncs.Base
open import RegDiff.Generic.Parms

module RegDiff.Diff.Trivial.Lemmas
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_
  open import RegDiff.Diff.Trivial.Apply ks keqs A _≟-A_

  module Internal {A : Set}(⟦_⟧ : A → Set)
                  (eqA : (x y : A) → Dec (x ≡ y))
                  (eqP : (k : A)(x y : ⟦ k ⟧) → Dec (x ≡ y)) 
    where

    -- singl(eton) function is correct!
    singl-correct
      : {a b : A}(x : ⟦ a ⟧)(y : ⟦ b ⟧)
      → singl ⟦_⟧ eqP x y x ≡ just y
    singl-correct {a} x y 
      with eqP a x x 
    ...| no abs = ⊥-elim (abs refl)
    ...| yes _  = refl

    -- And has a useful elimination principle
    singl-elim
      : {a b : A}(x k : ⟦ a ⟧)(y z : ⟦ b ⟧)
      → singl ⟦_⟧ eqP x y k ≡ just z
      → x ≡ k × y ≡ z
    singl-elim {a} x k y z hip 
      with eqP a x k
    ...| yes px = px , just-inj hip
    singl-elim {a} x k y z ()
       | no _ 
