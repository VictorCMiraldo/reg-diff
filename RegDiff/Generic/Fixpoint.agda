open import Prelude
open import Prelude.Eq
open import Prelude.Vector

module RegDiff.Generic.Fixpoint {ks# : ℕ}(ks : Vec Set ks#)(eqs : VecI Eq ks) 
    where

  open import RegDiff.Generic.Eq ks eqs
  open import RegDiff.Generic.Regular ks 
    renaming (U to Uₙ; I to Iₙ; ⟦_⟧ to interp)
    public

  U : Set
  U = Uₙ 1

  I : U
  I = Iₙ fz

  ⟦_⟧ : U → Set → Set
  ⟦ t ⟧ A = interp t (const A)

  data Fix (F : U) : Set where
    ⟨_⟩ : ⟦ F ⟧ (Fix F) → Fix F

  ⟨⟩-inj : {ty : U}{x y : ⟦ ty ⟧ (Fix ty)}
         → _≡_ {A = Fix ty} ⟨ x ⟩ ⟨ y ⟩ → x ≡ y
  ⟨⟩-inj refl = refl

  unmu : {ty : U} → Fix ty → ⟦ ty ⟧ (Fix ty)
  unmu ⟨ x ⟩ = x

  {-# TERMINATING #-}
  _≟-Fix_ : {ty : U}(x y : Fix ty) → Dec (x ≡ y)
  _≟-Fix_ {ty} ⟨ x ⟩ ⟨ y ⟩ 
    with dec-eq _≟-Fix_ ty x y
  ...| yes h = yes (cong ⟨_⟩ h)
  ...| no  h = no (h ∘ ⟨⟩-inj)

  {-# TERMINATING #-}
  cata : {A : Set}{ty : U}
       → (⟦ ty ⟧ A → A) → Fix ty → A
  cata {A} {ty} f ⟨ x ⟩ = f (gmap ty (cata f) x)

  μ-size : {ty : U} → Fix ty → ℕ
  μ-size {ty} = cata (suc ∘ size1 id ty)

  unmu-size : {ty tv : U}
        → ⟦ ty ⟧ (Fix tv) → ℕ
  unmu-size {ty = ty} = size1 ((1 +_) ∘ μ-size) ty
