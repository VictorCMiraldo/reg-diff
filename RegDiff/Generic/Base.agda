open import Prelude
open import Prelude.Vector

module RegDiff.Generic.Base {n : ℕ}(parms : Vec Set n)  where

{-
  Here we define the universe of regular types and the
  generic functions we need to perform diffing over them.

  Constants will be handled by the vector passed around
  as a module parameter.
-}

  data U : Set where
    I   : U
    u1  : U
    K   : (k : Fin n) → U
    _⊕_ : (ty : U) → (tv : U) → U
    _⊗_ : (ty : U) → (tv : U) → U

  infixr 25 _⊗_
  infixr 22 _⊕_

  ⟦_⟧ : U → Set → Set
  ⟦ I       ⟧ A = A
  ⟦ u1      ⟧ A = Unit
  ⟦ K x     ⟧ A = lookup x parms
  ⟦ ty ⊕ tv ⟧ A = ⟦ ty ⟧ A ⊎ ⟦ tv ⟧ A
  ⟦ ty ⊗ tv ⟧ A = ⟦ ty ⟧ A × ⟦ tv ⟧ A

  data μ (ty : U) : Set where
    ⟨_⟩ : ⟦ ty ⟧ (μ ty) → μ ty

  ⟨⟩-inj : {ty : U}{x y : ⟦ ty ⟧ (μ ty)}
         → _≡_ {A = μ ty} ⟨ x ⟩ ⟨ y ⟩ → x ≡ y
  ⟨⟩-inj refl = refl

  unmu : {ty : U} → μ ty → ⟦ ty ⟧ (μ ty)
  unmu ⟨ x ⟩ = x

{-
  Generic map
-}

  gmap : {A B : Set}(ty : U)(f : A → B)
       → ⟦ ty ⟧ A → ⟦ ty ⟧ B
  gmap I         f x       = f x
  gmap u1        f x       = unit
  gmap (K k)     f x       = x
  gmap (ty ⊕ tv) f (i1 x)  = i1 (gmap ty f x)
  gmap (ty ⊕ tv) f (i2 y)  = i2 (gmap tv f y)
  gmap (ty ⊗ tv) f (x , y) = gmap ty f x , gmap tv f y

  fgt : {A : Set}(ty : U) → ⟦ ty ⟧ A → ⟦ ty ⟧ Unit
  fgt ty = gmap ty (const unit)

{- 
  And generic size
-}

  size1 : {A : Set}(f : A → ℕ)(ty : U)
       → ⟦ ty ⟧ A → ℕ
  size1 f I x = (f x)
  size1 f u1 x = 1
  size1 f (K k) x = 1
  size1 f (ty ⊕ tv) (i1 x) = 1 + size1 f ty x
  size1 f (ty ⊕ tv) (i2 y) = 1 + size1 f tv y
  size1 f (ty ⊗ tv) (x , y) = size1 f ty x + size1 f tv y

  size0 : {A : Set}(ty : U) → ⟦ ty ⟧ A → ℕ
  size0 = size1 (const 1)

  {-# TERMINATING #-}
  cata : {A : Set}{ty : U}
       → (⟦ ty ⟧ A → A) → μ ty → A
  cata {A} {ty} f ⟨ x ⟩ = f (gmap ty (cata f) x)

  μ-size : {ty : U} → μ ty → ℕ
  μ-size {ty} = cata (suc ∘ size1 id ty)

  sizeμ : {ty tv : U}
        → ⟦ ty ⟧ (μ tv) → ℕ
  sizeμ {ty = ty} = size1 ((5 +_) ∘ μ-size) ty
