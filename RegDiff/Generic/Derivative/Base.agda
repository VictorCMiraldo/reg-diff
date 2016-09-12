open import Prelude 
open import Prelude.Vector

module RegDiff.Generic.Derivative.Base
      {n : ℕ}(v : Vec Set n) -- (eqs : VecI Eq v)
    where

  open import RegDiff.Generic.Base v

  data Ctx (A : Set) : U → Set where
    hole  : Ctx A I
    left  : {ty tv : U} → Ctx A ty → Ctx A (ty ⊕ tv)
    right : {ty tv : U} → Ctx A tv → Ctx A (ty ⊕ tv)
    fst   : {ty tv : U} → Ctx A ty → ⟦ tv ⟧ A → Ctx A (ty ⊗ tv)
    snd   : {ty tv : U} → Ctx A tv → ⟦ ty ⟧ A → Ctx A (ty ⊗ tv)

  _▸_ : {A : Set}{ty : U}
      → Ctx A ty → A → ⟦ ty ⟧ A
  hole      ▸ x = x
  left ctx  ▸ x = i1 (ctx ▸ x)
  right ctx ▸ x = i2 (ctx ▸ x)
  fst ctx k ▸ x = (ctx ▸ x) , k
  snd ctx k ▸ x = k , (ctx ▸ x)
