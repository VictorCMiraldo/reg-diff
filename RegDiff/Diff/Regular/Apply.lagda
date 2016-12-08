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
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Regular.Base ks keqs A WBA
\end{code}

  The application functions in both directions makes it easy
  to see how the two phases of the algorithm play together.

begin{code}
  S-apply : {ty : U}{P : UUSet}
         → (∀{k} → P k k → ⟦ k ⟧ → Maybe ⟦ k ⟧)
         → S P ty → ⟦ ty ⟧ A → Maybe ⟦ ty ⟧
  S-apply doP (SX x) el          = doP x el
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
  C-applyₗ doP (Ci1ᵒ c) (i1 el) = C-applyₗ doP c el
  C-applyₗ doP (Ci1ᵒ c) (i2 el) = nothing
  C-applyₗ doP (Ci2ᵒ c) (i1 el) = nothing
  C-applyₗ doP (Ci2ᵒ c) (i2 el) = C-applyₗ doP c el

  C-applyᵣ : {ty tv : U}{P : UUSet}
           → (doP : Appliable P)
           → C P ty tv → ⟦ tv ⟧ A → Maybe (⟦ ty ⟧ A)
  C-applyᵣ doP (CX x) el  = goᵣ doP x el
  C-applyᵣ doP (Ci1 c) (i1 el) = C-applyᵣ doP c el
  C-applyᵣ doP (Ci1 c) (i2 el) = nothing
  C-applyᵣ doP (Ci2 c) (i1 el) = nothing
  C-applyᵣ doP (Ci2 c) (i2 el) = C-applyᵣ doP c el
  C-applyᵣ doP (Ci1ᵒ c) el = i1 <$> C-applyᵣ doP c el
  C-applyᵣ doP (Ci2ᵒ c) el = i2 <$> C-applyᵣ doP c el

  C-Appliable : {P : UUSet} → Appliable P → Appliable (C P)
  C-Appliable doP = apply (C-applyₗ doP) (C-applyᵣ doP)

  Al-applyₗ : {ty tv : U}{P : UUSet}
            → (doP : Appliable P)
            → Al P ty tv → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
  Al-applyₗ doP (AX x) el = goₗ doP x el
  Al-applyₗ doP (A⊗ a a') (el , dl) = _,_ <$> Al-applyₗ doP a el <*> Al-applyₗ doP a' dl
  Al-applyₗ doP (Ap1 x a) el = (_, x) <$> Al-applyₗ doP a el
  Al-applyₗ doP (Ap1ᵒ {tw = tw} x a) (el , x') 
    with dec-eq _≟-A_ tw x x'
  ...| yes h = Al-applyₗ doP a el  
  ...| no  h = nothing
  Al-applyₗ doP (Ap2 x a) el = (x ,_) <$> Al-applyₗ doP a el
  Al-applyₗ doP (Ap2ᵒ {tw = tw} x a) (x' , el) 
    with dec-eq _≟-A_ tw x x'
  ...| yes h = Al-applyₗ doP a el  
  ...| no  h = nothing

  Al-applyᵣ : {ty tv : U}{P : UUSet}
            → (doP : Appliable P)
            → Al P ty tv → ⟦ tv ⟧ A → Maybe (⟦ ty ⟧ A)
  Al-applyᵣ doP (AX x) el = goᵣ doP x el
  Al-applyᵣ doP (A⊗ a a') (el , dl) = _,_ <$> Al-applyᵣ doP a el <*> Al-applyᵣ doP a' dl
  Al-applyᵣ doP (Ap1ᵒ x a) el = (_, x) <$> Al-applyᵣ doP a el
  Al-applyᵣ doP (Ap1 {tw = tw} x a) (el , x') 
    with dec-eq _≟-A_ tw x x'
  ...| yes h = Al-applyᵣ doP a el  
  ...| no  h = nothing
  Al-applyᵣ doP (Ap2ᵒ x a) el = (x ,_) <$> Al-applyᵣ doP a el
  Al-applyᵣ doP (Ap2 {tw = tw} x a) (x' , el) 
    with dec-eq _≟-A_ tw x x'
  ...| yes h = Al-applyᵣ doP a el  
  ...| no  h = nothing

  Al-Appliable : {P : UUSet} → Appliable P → Appliable (Al P)
  Al-Appliable doP = apply (Al-applyₗ doP) (Al-applyᵣ doP)
\end{code}

begin{code}
  private
    patch-appliable : Appliable (C (Al Δ))
    patch-appliable = C-Appliable (Al-Appliable Δ-apply)

  Patch-applyₗ : {ty : U} → Patch ty → ⟦ ty ⟧ A → Maybe (⟦ ty ⟧ A)
  Patch-applyₗ = S-apply (goₗ patch-appliable)

  Patch-applyᵣ : {ty : U} → Patch ty → ⟦ ty ⟧ A → Maybe (⟦ ty ⟧ A)
  Patch-applyᵣ = S-apply (goᵣ patch-appliable)
\end{code}
