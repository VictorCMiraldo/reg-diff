open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Diff.Residual
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)(A : Set)
       {{eqA : Eq A}}(sized : A → ℕ)
    where

  open import RegDiff.Generic.Base v
  open import RegDiff.Generic.Eq v eqs
  open import RegDiff.Diff.Spine v eqs A sized

  _+₂_ : UUSet → UUSet → UUSet
  (P +₂ Q) ty tv = P ty tv ⊎ Q ty tv

  C : UUSet
  C ty tv = Unit

  res : {ty tv : U} → S Δ ty tv → S Δ ty tv → S (C +₂ Δ) ty tv
  res (SX x) o = {!!}
  res (Ssym s) o = {!!}
  res Scp o = {!!}
  res (S⊗ s s₁) o = {!!}
  res (Sfst x s) o = {!!}
  res (Ssnd x s) o = {!!}
  res (Si1 s) o = {!!}
  res (Si2 s) o = {!!}
