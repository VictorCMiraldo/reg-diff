  This is the trivial diff algorithm. Nothing
  surprising here.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector

module RegDiff.Diff.Trivial.Base
       {parms# : ℕ}(parms : Vec Set parms#)(eqs : VecI Eq parms)
    where

  open import RegDiff.Generic.Multirec parms
  open import RegDiff.Generic.Eq parms eqs
\end{code}

  This module serves the purpose of defining a bunch of
  auxiliary functions for later on.

\begin{code}
  UUSet : Set₁
  UUSet = {n : ℕ} → Setⁿ n → U n → U n → Set
\end{code}

  As usual, we say that the diagonal functor
  is the trivial diff.

%<*delta-def>
\begin{code}
  Δ : UUSet
  Δ A ty tv = ⟦ ty ⟧ A × ⟦ tv ⟧ A
\end{code}
%</delta-def>

  It has a cost function:

\begin{code}
  cost-Δ : {n : ℕ}{ty tv : U n}{A : Setⁿ n}
         → (sized : ∀{k} → A k → ℕ)
         → Δ A ty tv → ℕ
  cost-Δ {_} {ty} {tv}  f (x , y) with U-eq ty tv
  cost-Δ {_} {ty} {.ty} f (x , y) | yes refl
    with dec-eq {!!} ty x y
  ...| yes _ = 0
  ...| no  _ = size1 f ty x + size1 f ty y
  cost-Δ {_} {ty} {tv}  f (x , y) | no _
    = size1 f ty x + size1 f tv y
\end{code}

  And it can be applied in both directions:

\begin{code}
  record Appliable (Q : UUSet) : Set₁ where
    constructor apply
    field
      goₗ : {n : ℕ}{ty tv : U n}{A : Setⁿ n} 
          → Q A ty tv → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
      goᵣ : {n : ℕ}{ty tv : U n}{A : Setⁿ n} 
          → Q A ty tv → ⟦ tv ⟧ A → Maybe (⟦ ty ⟧ A)

  open Appliable public

  Δ-apply : Appliable Δ
  Δ-apply 
    = apply (λ {n} {ty} {tv} → doit {n} {ty} {tv}) 
            (λ { {_} {ty} {tv} (x , y) z → doit {ty = tv} {tv = ty} (y , x) z })
    where
      doit : {n : ℕ}{ty tv : U n}{A : Setⁿ n} 
           → Δ A ty tv → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
      doit {_} {ty} {tv} (x , y) z
        with dec-eq {!!} ty x z
      ...| yes _ = just y
      ...| no  _ = nothing
\end{code}
