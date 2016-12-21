open import Prelude
open import Prelude.Monad
open import Prelude.Functor


module Prelude.PartialFuncs.PartialOrder where

  open Monad {{...}}
  open Functor {{...}}

  infix 20 _≼_
  data _≼_ {a}{A : Set a} : Maybe A → Maybe A → Set a where
    base : {y : Maybe A}          → nothing ≼ y
    up   : {x y : A}     → x ≡ y  → just x ≼ just y

  ≼-refl : ∀{a}{A : Set a}{x : Maybe A}
         → x ≼ x
  ≼-refl {x = nothing}  = base
  ≼-refl {x = just x}   = up refl

  ≼-asym : ∀{a}{A : Set a}{x y : Maybe A}
         → x ≼ y → y ≼ x → x ≡ y
  ≼-asym base base      = refl
  ≼-asym (up x) (up _)  = cong just x

  ≼-trans : ∀{a}{A : Set a}{x y z : Maybe A}
          → x ≼ y → y ≼ z → x ≼ z
  ≼-trans base base      = base
  ≼-trans base (up _)    = base
  ≼-trans (up p) (up q)  = up (trans p q)

  _≼*_ : ∀{a b}{A : Set a}{B : Set b}
       → (A → Maybe B) → (A → Maybe B)
       → Set (a ⊔ b)
  f ≼* g = ∀{x} → f x ≼ g x
