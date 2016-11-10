open import Prelude
open import Prelude.Vector

module RegDiff.Generic.Regular {ks# : ℕ}(ks : Vec Set ks#) where

  open import RegDiff.Generic.Parms

{-
  Here we define the universe of regular types over
  n-variables and the generic functions we need to 
  perform diffing over them.

  Constants will be handled by the vector passed around
  as a module parameter.
-}


  data U (n : ℕ) : Set where
    I    : Fin n         → U n
    K    : Fin ks#       → U n
    u1   :                 U n
    _⊕_  : (ty tv : U n) → U n
    _⊗_  : (ty tv : U n) → U n

  infixr 25 _⊗_
  infixr 22 _⊕_

  ⟦_⟧ : {n : ℕ} → U n → Parms n → Set
  ⟦ I x     ⟧ A = A x
  ⟦ K x     ⟧ A = lookup x ks
  ⟦ u1      ⟧ A = Unit
  ⟦ ty ⊕ tv ⟧ A = ⟦ ty ⟧ A ⊎ ⟦ tv ⟧ A
  ⟦ ty ⊗ tv ⟧ A = ⟦ ty ⟧ A × ⟦ tv ⟧ A

{-
  Generic map
-}

  gmap : {n : ℕ}{A B : Parms n}(ty : U n)(f : A ⇉ B)
       → ⟦ ty ⟧ A → ⟦ ty ⟧ B
  gmap (I i)     f x       = f x
  gmap u1        f x       = unit
  gmap (K k)     f x       = x
  gmap (ty ⊕ tv) f (i1 x)  = i1 (gmap ty f x)
  gmap (ty ⊕ tv) f (i2 y)  = i2 (gmap tv f y)
  gmap (ty ⊗ tv) f (x , y) = gmap ty f x , gmap tv f y


{- 
  And generic size
-}

  size1 : {n : ℕ}{A : Parms n}(f : ∀{k} → A k → ℕ)(ty : U n)
       → ⟦ ty ⟧ A → ℕ
  size1 f (I i) x = (f x)
  size1 f u1 x = 1
  size1 f (K k) x = 1
  size1 f (ty ⊕ tv) (i1 x) = 1 + size1 f ty x
  size1 f (ty ⊕ tv) (i2 y) = 1 + size1 f tv y
  size1 f (ty ⊗ tv) (x , y) = size1 f ty x + size1 f tv y

  size-const : {n : ℕ}{A : Parms n}(ty : U n) → ⟦ ty ⟧ A → ℕ
  size-const = size1 (const 1)

