open import Prelude
open import Prelude.Eq
open import Prelude.Vector

module RegDiff.SOP.Generic.Fixpoint {ks# : ℕ}(ks : Vec Set ks#)(eqs : VecI Eq ks) 
    where

  open import RegDiff.SOP.Generic.Eq ks eqs
  open import RegDiff.SOP.Generic.Multirec ks 
    renaming (I to Iₙ; ⟦_⟧ to interp; Fix to Fixₘ)
    public

  I : Atom 1
  I = Iₙ fz

  ⟦_⟧ : σπ 1 → Set → Set
  ⟦ ty ⟧ A = interp ty (λ _ → A)

  Fix : σπ 1 → Set
  Fix F = Fixₘ (F ∷ []) fz

  {-# TERMINATING #-}
  _≟-Fix_ : {ty : σπ 1}(x y : Fix ty) → Dec (x ≡ y)
  _≟-Fix_ {ty} x y = x ≟ y

  μ-size : {ty : σπ 1} → Fix ty → ℕ
  μ-size = Fam-size

  unmu-size : {ty tv : σπ 1}
        → ⟦ ty ⟧ (Fix tv) → ℕ
  unmu-size {ty = ty} = size1 ((1 +_) ∘ μ-size) ty