\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector

module RegDiff.Diff.Base
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)(A : Set)
       {{eqA : Eq A}}(sized : A → ℕ)
    where

  open import RegDiff.Generic.Base v
  open import RegDiff.Generic.Eq v eqs
\end{code}

\begin{code}
  UUSet : Set₁
  UUSet = U → U → Set
\end{code}

%<*delta-def>
\begin{code}
  Δ : UUSet
  Δ ty tv = ⟦ ty ⟧ A × ⟦ tv ⟧ A
\end{code}
%</delta-def>


\begin{code}
  cost-Δ : {ty tv : U} → Δ ty tv → ℕ
  cost-Δ {ty} {tv} (x , y) with U-eq ty tv
  cost-Δ {ty} {.ty} (x , y) | yes refl
    with dec-eq ty x y
  ...| yes _ = 0
  ...| no  _ = size1 sized ty x + size1 sized ty y
  cost-Δ {ty} {tv}  (x , y) | no _
    = size1 sized ty x + size1 sized tv y
\end{code}

\begin{code}
  record Appliable (Q : UUSet) : Set where
    constructor apply
    field
      goₗ : ∀{ty tv} → Q ty tv → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
      goᵣ : ∀{ty tv} → Q ty tv → ⟦ tv ⟧ A → Maybe (⟦ ty ⟧ A)

  open Appliable public

  apply-Δ : Appliable Δ
  apply-Δ 
    = apply (λ {ty} {tv} → doit {ty} {tv}) 
            (λ { {ty} {tv} (x , y) z → doit {tv} {ty} (y , x) z })
    where
      doit : {ty tv : U} → Δ ty tv → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
      doit {ty} {tv} (x , y) z
        with dec-eq ty x z
      ...| yes _ = just y
      ...| no  _ = nothing
\end{code}
