\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Diff.Fixpoint.Domains
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open Monad {{...}} renaming (μ to join)
  open Applicative {{...}}

  open import RegDiff.Generic.Base v
  open import RegDiff.Generic.Eq v eqs
  import RegDiff.Diff.Fixpoint.Base v eqs as FIXPOINT

  module Internal (T : U) where
    open FIXPOINT.Internal T public
\end{code}

\begin{code}
    open import RegDiff.Diff.Regular.Domains v eqs (μ T) μ-size
      public

    mutual
      {-# TERMINATING #-}
      SI-dom : {ty tv : U} → SI Δ ty tv → (⟦ ty ⟧ (μ T) → Set)
      SI-dom (Svar x)     = dom SI-domran x ∘ unmu 
      SI-dom (Sins x)     = dom SI-domran x
      SI-dom (SY (x , _)) = (x ≡_)

      SI-ran : {ty tv : U} → SI Δ ty tv → (⟦ tv ⟧ (μ T) → Set)
      SI-ran (Svar x)     = ran SI-domran x ∘ unmu
      SI-ran (Sins x)     = ran SI-domran x ∘ ⟨_⟩ 
      SI-ran (SY (_ , y)) = (y ≡_)

      SI-domran : HasDomRan (SI Δ)
      SI-domran = hasdomran SI-dom SI-ran

    domμ : {ty tv : U} → S (SI Δ) ty tv → ⟦ ty ⟧ (μ T) → Set
    domμ = dom SI-domran

    ranμ : {ty tv : U} → S (SI Δ) ty tv → ⟦ tv ⟧ (μ T) → Set
    ranμ = ran SI-domran
\end{code}
