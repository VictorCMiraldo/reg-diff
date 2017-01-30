open import Prelude
open import Prelude.Monad

module Prelude.List.Any where

  open import Data.List.Any
    using (Any; here; there)
    public

  here-inj : ∀{a p}{A : Set a}{P : A → Set p}{l : List A}
              {k : A}{x y : P k}
           → _≡_ {A = Any P (k ∷ l)} (here x) (here y) → x ≡ y
  here-inj refl = refl

  there-inj : ∀{a p}{A : Set a}{P : A → Set p}{l : List A}
              {k : A}{x y : Any P l}
           → _≡_ {A = Any P (k ∷ l)} (there x) (there y) → x ≡ y
  there-inj refl = refl
