\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Diff.Fixpoint.Apply
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open Monad {{...}} renaming (μ to join)
  open Applicative {{...}}

  open import RegDiff.Generic.Base v
  open import RegDiff.Generic.Eq v eqs
  import RegDiff.Diff.Fixpoint.Base v eqs as FIXPOINT
\end{code}

  Just like the diffing of fixpoints, we need an internal
  module to keep track of the fixpoint in question:

\begin{code}
  module Internal (T : U) where

    open FIXPOINT.Internal T
    open import RegDiff.Diff.Regular.Apply v eqs (μ T) μ-size
\end{code}

\begin{code}
    mutual
      SI-applyₗ : {ty tv : U} → SI Δ ty tv → ⟦ ty ⟧ (μ T) → Maybe (⟦ tv ⟧ (μ T))
      SI-applyₗ (Svar x) el = ⟨_⟩ <$> Sμ-applyₗ x (unmu el)
      SI-applyₗ (Sins x) el = unmu <$> Sμ-applyₗ x el
      SI-applyₗ {ty} {tv} (SY x) el = goₗ Δ-apply {ty} {tv} x el

      SI-applyᵣ : {ty tv : U} → SI Δ ty tv → ⟦ tv ⟧ (μ T) → Maybe (⟦ ty ⟧ (μ T))
      SI-applyᵣ (Svar x) el = ⟨_⟩ <$> Sμ-applyᵣ x (unmu el)
      SI-applyᵣ (Sins x) el = Sμ-applyᵣ x ⟨ el ⟩
      SI-applyᵣ {ty} {tv} (SY x) el = goᵣ Δ-apply {ty} {tv} x el

      {-# TERMINATING #-}
      Sμ-applyₗ : {ty tv : U} → Sμ Δ ty tv → ⟦ ty ⟧ (μ T) → Maybe (⟦ tv ⟧ (μ T))
      Sμ-applyₗ s x = S-applyₗ (apply SI-applyₗ SI-applyᵣ) s x

      Sμ-applyᵣ : {ty tv : U} → Sμ Δ ty tv → ⟦ tv ⟧ (μ T) → Maybe (⟦ ty ⟧ (μ T))
      Sμ-applyᵣ s x = S-applyᵣ (apply SI-applyₗ SI-applyᵣ) s x


    applyμₗ : Sμ Δ T T → μ T → Maybe (μ T)
    applyμₗ s ⟨ x ⟩ = ⟨_⟩ <$> Sμ-applyₗ s x

    applyμᵣ : Sμ Δ T T → μ T → Maybe (μ T)
    applyμᵣ s ⟨ x ⟩ = ⟨_⟩ <$> Sμ-applyᵣ s x
\end{code}
