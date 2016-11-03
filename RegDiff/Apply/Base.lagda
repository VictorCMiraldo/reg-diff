\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Apply.Base
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)(A : Set)
       {{eqA : Eq A}}(sized : A → ℕ)
    where

  open import RegDiff.Generic.Base v
  open import RegDiff.Generic.Eq v eqs
  open import RegDiff.Diff.Spine v eqs A sized
\end{code}

\begin{code}
  mutual
    applyₗ : {ty tv : U}{P : UUSet}
           → (doP : Appliable P)
           → S P ty tv → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
    applyₗ doP (SX x) el = goₗ doP x el
    applyₗ doP (Ssym s) el = applyᵣ doP s el
    applyₗ doP Scp x = just x
    applyₗ doP (S⊗ s o) (el , dl) = _,_ <$> applyₗ doP s el <*> applyₗ doP o dl
    applyₗ doP (Sfst x s) el = (_, x) <$> applyₗ doP s el
    applyₗ doP (Ssnd x s) el = (x ,_) <$> applyₗ doP s el
    applyₗ doP (Si1 s) el = i1 <$> applyₗ doP s el
    applyₗ doP (Si2 s) el = i2 <$> applyₗ doP s el

    applyᵣ : {ty tv : U}{P : UUSet}
           → (doP : Appliable P)
           → S P ty tv → ⟦ tv ⟧ A → Maybe (⟦ ty ⟧ A)
    applyᵣ doP (SX x) el = goᵣ doP x el
    applyᵣ doP (Ssym s) el = applyₗ doP s el
    applyᵣ doP Scp x = just x
    applyᵣ doP (S⊗ s o) (el , dl) =  _,_ <$> applyᵣ doP s el <*> applyᵣ doP o dl
    applyᵣ doP (Sfst {k = k} x s) (el , x')
      with dec-eq k x x' 
    ...| yes _ = applyᵣ doP s el
    ...| no  _ = nothing
    applyᵣ doP (Ssnd {k = k} x s) (x' , el)
      with dec-eq k x x' 
    ...| yes _ = applyᵣ doP s el
    ...| no  _ = nothing
    applyᵣ doP (Si1 s) (i1 el) = applyᵣ doP s el
    applyᵣ doP (Si1 s) (i2 el) = nothing
    applyᵣ doP (Si2 s) (i1 el) = nothing
    applyᵣ doP (Si2 s) (i2 el) = applyᵣ doP s el
\end{code}
