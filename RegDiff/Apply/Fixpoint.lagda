\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Apply.Fixpoint
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  -- open Monad {{...}}
  open Applicative {{...}}

  open import RegDiff.Generic.Base v
  open import RegDiff.Generic.Eq v eqs
  import RegDiff.Diff.Fixpoint v eqs as FIXPOINT
\end{code}

  Tying the know for fixpoints is not so hard.
  The important insight is that the parameter A
  is going to be (μ T) now.

  We hence abstract T as a module parameter.

\begin{code}
  module Internal (T : U) where

    open FIXPOINT.Internal T
    open import RegDiff.Apply.Base v eqs (μ T) μ-size
\end{code}

\begin{code}
    mutual
      applyₗ-SI : {ty tv : U} → SI Δ ty tv → ⟦ ty ⟧ (μ T) → Maybe (⟦ tv ⟧ (μ T))
      applyₗ-SI (Svar x) el = ⟨_⟩ <$> applyμₗ x (unmu el)
      applyₗ-SI (Sins x) el = unmu <$> applyμₗ x el
      applyₗ-SI {ty} {tv} (SY x) el = goₗ apply-Δ {ty} {tv} x el

      applyᵣ-SI : {ty tv : U} → SI Δ ty tv → ⟦ tv ⟧ (μ T) → Maybe (⟦ ty ⟧ (μ T))
      applyᵣ-SI (Svar x) el = ⟨_⟩ <$> applyμᵣ x (unmu el)
      applyᵣ-SI (Sins x) el = applyμᵣ x ⟨ el ⟩
      applyᵣ-SI {ty} {tv} (SY x) el = goᵣ apply-Δ {ty} {tv} x el

      {-# TERMINATING #-}
      applyμₗ : {ty tv : U} → S (SI Δ) ty tv → ⟦ ty ⟧ (μ T) → Maybe (⟦ tv ⟧ (μ T))
      applyμₗ s x = applyₗ (apply applyₗ-SI applyᵣ-SI) s x

      applyμᵣ : {ty tv : U} → S (SI Δ) ty tv → ⟦ tv ⟧ (μ T) → Maybe (⟦ ty ⟧ (μ T))
      applyμᵣ s x = applyᵣ (apply applyₗ-SI applyᵣ-SI) s x

    applyμ♭ : S (SI Δ) T T → μ T → Maybe (μ T)
    applyμ♭ s ⟨ x ⟩ = ⟨_⟩ <$> applyμₗ s x
\end{code}
