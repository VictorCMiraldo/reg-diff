open import Prelude

module Prelude.Vector where

  open import Data.Vec 
    using (Vec; []; _∷_; head; tail; lookup; tabulate) 
    renaming (_++_ to _++v_)
    public

  data VecI {a b}{A : Set a}(F : A → Set b) : {n : ℕ} → Vec A n → Set (a ⊔ b) where
    []  : VecI F []
    _∷_ : {n : ℕ}{K : A}{V : Vec A n}
        → F K → VecI F V → VecI F (K ∷ V)

  lookupᵢ : ∀{a b}{A : Set a}{F : A → Set b}{n : ℕ}{v : Vec A n}
          → (i : Fin n) → VecI F v → F (lookup i v)
  lookupᵢ fz (x ∷ vs) = x
  lookupᵢ (fs i) (x ∷ vs) = lookupᵢ i vs

  ∷ᵥ-inj : {n : ℕ}{A : Set}{v u : A}{vs us : Vec A n}
         → _≡_ {A = Vec A (suc n)}(v ∷ vs) (u ∷ us)
         → v ≡ u × vs ≡ us
  ∷ᵥ-inj refl = refl , refl
