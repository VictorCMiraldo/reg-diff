  Here we define application for
  Regular-type patches.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Diff.Regular.Apply
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)(A : Set)
       {{eqA : Eq A}}(sized : A → ℕ)
    where

  open import RegDiff.Generic.Base v
  open import RegDiff.Generic.Eq v eqs
  open import RegDiff.Diff.Regular.Base v eqs A sized
\end{code}

  The application functions in both directions makes it easy
  to see how the two phases of the algorithm play together.

\begin{code}
  mutual
    S-applyₗ : {ty tv : U}{P : UUSet}
           → (doP : Appliable P)
           → S P ty tv → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
    S-applyₗ doP (SX x) el = goₗ doP x el
    S-applyₗ doP (Ssym s) el = S-applyᵣ doP s el
    S-applyₗ doP Scp x = just x
    S-applyₗ doP (S⊗ s o) (el , dl) = _,_ <$> S-applyₗ doP s el <*> S-applyₗ doP o dl
    S-applyₗ doP (Sfst x s) el = (_, x) <$> S-applyₗ doP s el
    S-applyₗ doP (Ssnd x s) el = (x ,_) <$> S-applyₗ doP s el
    S-applyₗ doP (Si1 s) el = i1 <$> S-applyₗ doP s el
    S-applyₗ doP (Si2 s) el = i2 <$> S-applyₗ doP s el

    S-applyᵣ : {ty tv : U}{P : UUSet}
           → (doP : Appliable P)
           → S P ty tv → ⟦ tv ⟧ A → Maybe (⟦ ty ⟧ A)
    S-applyᵣ doP (SX x) el = goᵣ doP x el
    S-applyᵣ doP (Ssym s) el = S-applyₗ doP s el
    S-applyᵣ doP Scp x = just x
    S-applyᵣ doP (S⊗ s o) (el , dl) =  _,_ <$> S-applyᵣ doP s el <*> S-applyᵣ doP o dl
    S-applyᵣ doP (Sfst {k = k} x s) (el , x')
      with dec-eq k x x' 
    ...| yes _ = S-applyᵣ doP s el
    ...| no  _ = nothing
    S-applyᵣ doP (Ssnd {k = k} x s) (x' , el)
      with dec-eq k x x' 
    ...| yes _ = S-applyᵣ doP s el
    ...| no  _ = nothing
    S-applyᵣ doP (Si1 s) (i1 el) = S-applyᵣ doP s el
    S-applyᵣ doP (Si1 s) (i2 el) = nothing
    S-applyᵣ doP (Si2 s) (i1 el) = nothing
    S-applyᵣ doP (Si2 s) (i2 el) = S-applyᵣ doP s el

  SΔ-applyₗ : {ty tv : U} → S Δ ty tv → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
  SΔ-applyₗ = S-applyₗ Δ-apply

  SΔ-applyᵣ : {ty tv : U} → S Δ ty tv → ⟦ tv ⟧ A → Maybe (⟦ ty ⟧ A)
  SΔ-applyᵣ = S-applyᵣ Δ-apply
\end{code}
