open import Prelude
open import Prelude.Eq
open import Prelude.Vector

module RegDiff.Generic.Fixpoint {ks# : ℕ}(ks : Vec Set ks#)(eqs : VecI Eq ks) 
    where

  open import RegDiff.Generic.Eq ks eqs
  open import RegDiff.Generic.Multirec ks 
    renaming (I to Iₙ; ⟦_⟧ to interp; Fix to Fixₘ)
    public

  I : Uₙ 1
  I = Iₙ fz

  ⟦_⟧ : Uₙ 1 → Set → Set
  ⟦ ty ⟧ A = interp ty (λ _ → A)

  Fix : Uₙ 1 → Set
  Fix F = Fixₘ (F ∷ []) fz

  {-# TERMINATING #-}
  _≟-Fix_ : {ty : Uₙ 1}(x y : Fix ty) → Dec (x ≡ y)
  _≟-Fix_ {ty} x y = x ≟ y

  μ-size : {ty : Uₙ 1} → Fix ty → ℕ
  μ-size = Fam-size

  unmu-size : {ty tv : Uₙ 1}
        → ⟦ ty ⟧ (Fix tv) → ℕ
  unmu-size {ty = ty} = size1 ((1 +_) ∘ μ-size) ty
