  Here we define application for
  Regular-type patches.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Apply
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where

  open import RegDiff.Generic.Multirec ks
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Regular.Base ks keqs A WBA
    public
\end{code}

  The application functions in both directions makes it easy
  to see how the two phases of the algorithm play together.

\begin{code}
  S-apply : {ty : U}{P : UUSet}
         → (doP : Appliable P)
         → S P ty → ⟦ ty ⟧ A → Maybe (⟦ ty ⟧ A)
  S-apply doP (SX x) el          = goₗ doP x el
  S-apply doP Scp x              = just x
  S-apply doP (S⊗ s o) (el , dl) = _,_ <$> S-apply doP s el <*> S-apply doP o dl
  S-apply doP (Si1 s) (i1 el)    = i1 <$> S-apply doP s el
  S-apply doP (Si1 s) (i2 el)    = nothing
  S-apply doP (Si2 s) (i1 el)    = nothing
  S-apply doP (Si2 s) (i2 el)    = i2 <$> S-apply doP s el

  C-applyₗ : {ty tv : U}{P : UUSet}
           → (doP : Appliable P)
           → C P ty tv → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
  C-applyₗ doP (CX x) el  = goₗ doP x el
  C-applyₗ doP (Ci1 c) el = i1 <$> C-applyₗ doP c el
  C-applyₗ doP (Ci2 c) el = i2 <$> C-applyₗ doP c el

  C-applyᵣ : {ty tv : U}{P : UUSet}
           → (doP : Appliable P)
           → C P ty tv → ⟦ tv ⟧ A → Maybe (⟦ ty ⟧ A)
  C-applyᵣ doP (CX x) el  = goᵣ doP x el
  C-applyᵣ doP (Ci1 c) (i1 el) = C-applyᵣ doP c el
  C-applyᵣ doP (Ci1 c) (i2 el) = nothing
  C-applyᵣ doP (Ci2 c) (i1 el) = nothing
  C-applyᵣ doP (Ci2 c) (i2 el) = C-applyᵣ doP c el

  C-Appliable : {P : UUSet} → Appliable P → Appliable (C P)
  C-Appliable doP = apply (C-applyₗ doP) (C-applyᵣ doP)

  Al-applyₗ : {ty tv : U}{P : UUSet}
            → (doP : Appliable P)
            → Al P ty tv → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
  Al-applyₗ doP (AX x) el = {!!}
  Al-applyₗ doP (A⊗ a a') el = {!!}
  Al-applyₗ doP (Ap1 x a) el = {!!}
  Al-applyₗ doP (Ap1ᵒ x a) el = {!!}
  Al-applyₗ doP (Ap2 x a) el = {!!}
  Al-applyₗ doP (Ap2ᵒ x a) el = {!!}

\end{code}

    S-applyₗ doP (Sfst x s) el = (_, x) <$> S-applyₗ doP s el
    S-applyₗ doP (Ssnd x s) el = (x ,_) <$> S-applyₗ doP s el

    S-applyᵣ doP (Sfst {k = k} x s) (el , x')
      with dec-eq k x x' 
    ...| yes _ = S-applyᵣ doP s el
    ...| no  _ = nothing
    S-applyᵣ doP (Ssnd {k = k} x s) (x' , el)
      with dec-eq k x x' 
    ...| yes _ = S-applyᵣ doP s el
    ...| no  _ = nothing
