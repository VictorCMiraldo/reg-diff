open import Prelude
open import Prelude.Vector

module RegDiff.Generic.Serialization.TypeSafe
      {n : ℕ}(v : Vec Set n)
    where

  open import RegDiff.Generic.Base v

  data W (S : Set)(P : S → Set) : Set where
    sup : (s : S)(f : P s → W S P) → W S P

  μS : U → Set
  μS ty = ⟦ ty ⟧ Unit

  μP : (ty : U) → μS ty → Set
  μP ty μs = Fin (ar ty μs)

  μW : U → Set
  μW ty = W (μS ty) (μP ty)

  {-# TERMINATING #-}
  μ-w : {ty : U} → μ ty → μW ty
  μ-w el = sup (μ-hd el) (λ n → lookup n (vmap μ-w (μ-chv el)))
