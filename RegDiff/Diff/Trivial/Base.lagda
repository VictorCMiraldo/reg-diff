  This is the trivial diff algorithm. Nothing
  surprising here.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import RegDiff.Generic.Parms
\end{code}

%<*Trivial-module-decl>
\begin{code}
module RegDiff.Diff.Trivial.Base
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where
\end{code}
%</Trivial-module-decl>

\begin{code}
  open import RegDiff.Generic.Multirec ks
  open import RegDiff.Generic.Eq ks keqs
\end{code}

  This module serves the purpose of defining a bunch of
  auxiliary functions for later on.

%<*Trivial-defs>
\begin{code}
  U : Set
  U = Uₙ parms#

  sized : {p : Fin parms#} → A p → ℕ
  sized = parm-size WBA

  _≟-A_ : {p : Fin parms#}(x y : A p) → Dec (x ≡ y)
  _≟-A_ = parm-cmp WBA

  UUSet : Set₁
  UUSet = U → U → Set
\end{code}
%</Trivial-defs>

  As usual, we say that the diagonal functor
  is the trivial diff.

%<*delta-def>
\begin{code}
  Δ : UUSet
  Δ ty tv = ⟦ ty ⟧ A × ⟦ tv ⟧ A
\end{code}
%</delta-def>

  It has a cost function:

\begin{code}
  cost-Δ-raw : {ty tv : U} → Δ ty tv → ℕ
  cost-Δ-raw {ty} {tv} (x , y) 
    -- = size1 sized ty x + size1 sized tv y
    = 1
\end{code}

%<*Trivial-cost-def>
\begin{code}
  cost-Δ : {ty tv : U} → Δ ty tv → ℕ
  cost-Δ {ty} {tv}  (x , y) with U-eq ty tv
  cost-Δ {ty} {.ty} (x , y) | yes refl
    with dec-eq _≟-A_ ty x y
  ...| yes _ = 0
  ...| no  _ = cost-Δ-raw {ty} {ty} (x , y)
  cost-Δ {ty} {tv}  (x , y) | no _
    = cost-Δ-raw {ty} {tv} (x ,  y)
\end{code}
%</Trivial-cost-def>

\begin{code}
  delta : {ty tv : U} → ⟦ ty ⟧ A → ⟦ tv ⟧ A → Δ ty tv
  delta x y = (x , y)
\end{code}

  And it can be applied in both directions:

\begin{code}
  record Appliable (Q : UUSet) : Set₁ where
    constructor apply
    field
      goₗ : {ty tv : U}
          → Q ty tv → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
      goᵣ : {ty tv : U}
          → Q ty tv → ⟦ tv ⟧ A → Maybe (⟦ ty ⟧ A)

  open Appliable public

  Δ-apply : Appliable Δ
  Δ-apply 
    = apply (λ {ty} {tv} → doit {ty} {tv}) 
            (λ { {ty} {tv} (x , y) z → doit {ty = tv} {tv = ty} (y , x) z })
    where
      doit : {ty tv : U}
           → Δ ty tv → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
      doit {ty} {tv} (x , y) z
        with dec-eq _≟-A_ ty x z
      ...| yes _ = just y
      ...| no  _ = nothing
\end{code}
