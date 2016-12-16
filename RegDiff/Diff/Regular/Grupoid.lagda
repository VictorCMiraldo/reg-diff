\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.ListI
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Grupoid
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Regular.Base ks keqs A _≟-A_
  open import RegDiff.Diff.Regular.Apply ks keqs A _≟-A_
\end{code}

\begin{code}
  HasInv : {X : Set} → (X → X → Set) → Set
  HasInv Q = ∀{x₁ x₂} → Q x₁ x₂ → Q x₂ x₁
\end{code}
\begin{code}
  Δₐ-inv : HasInv Δₐ
  Δₐ-inv (x , y) = (y , x)

  Δₚ-inv : HasInv Δₚ
  Δₚ-inv (x , y) = (y , x)

  Δₛ-inv : HasInv Δₛ
  Δₛ-inv (x , y) = (y , x)
\end{code}
\begin{code}
  S-inv : {P : UUSet}(doP : HasInv P){ty : U} → S P ty → S P ty
  S-inv doP Scp         = Scp
  S-inv doP (SX p)      = SX (doP p)
  S-inv doP (Scns i ps) = Scns i (mapᵢ doP ps)
\end{code}
\begin{code}
  C-inv : {P : ΠΠSet}(doP : HasInv P) → HasInv (C P)
  C-inv doP (CX i j p) = CX j i (doP p)
\end{code}
\begin{code}
  Al-inv : {P : AASet}(doP : HasInv P) → HasInv (Al P)
  Al-inv doP A0         = A0
  Al-inv doP (Ap1  x a) = Ap1ᵒ x (Al-inv doP a)
  Al-inv doP (Ap1ᵒ x a) = Ap1  x (Al-inv doP a)
  Al-inv doP (AX   x a) = AX (doP x) (Al-inv doP a)
\end{code}
\begin{code}
  Patch-inv : {P : AASet}(doP : HasInv P){ty : U} → Patch P ty → Patch P ty
  Patch-inv doP = S-inv (C-inv (Al-inv doP))
\end{code}
\begin{code}
  PatchΔₐ-inv : {P : AASet}(doP : HasInv P){ty : U} → Patch Δₐ ty → Patch Δₐ ty
  PatchΔₐ-inv doP = Patch-inv (λ {ty} {tv} → Δₐ-inv {ty} {tv})
\end{code}


\begin{code}
  HasCmp : {X : Set} → (X → X → Set) → Set
  HasCmp Q = ∀{x₁ x₂ x₃} → Q x₂ x₃ → Q x₁ x₂ → Maybe (Q x₁ x₃)
\end{code}
\begin{code}
  Δₐ-cmp : HasCmp Δₐ
  Δₐ-cmp {_} {a} (w , z) (x , w') 
    with dec-eqₐ _≟-A_ a w w' 
  ...| yes _ = just (x , z)
  ...| no  _ = nothing

  Δₚ-cmp : HasCmp Δₚ
  Δₚ-cmp {_} {p} (w , z) (x , w')
    with dec-eqₚ _≟-A_ p w w' 
  ...| yes _ = just (x , z)
  ...| no  _ = nothing

  Δₛ-cmp : HasCmp Δₛ
  Δₛ-cmp {_} {s} (w , z) (x , w')
    with dec-eq _≟-A_ s w w' 
  ...| yes _ = just (x , z)
  ...| no  _ = nothing
\end{code}
\begin{code}
  S-cmp : {P : UUSet}(doP : HasCmp P){ty : U} → S P ty → S P ty → Maybe (S P ty)
  S-cmp s s' = {!!}
\end{code}
