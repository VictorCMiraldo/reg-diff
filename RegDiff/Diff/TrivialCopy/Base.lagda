  This is the trivial diff algorithm. Nothing
  surprising here.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import RegDiff.Generic.Parms

module RegDiff.Diff.TrivialCopy.Base
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where

  open import RegDiff.Generic.Multirec ks
  open import RegDiff.Generic.Eq ks keqs
\end{code}

  This module serves the purpose of defining a bunch of
  auxiliary functions for later on.

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

  As usual, we say that the diagonal functor
  is the trivial diff.

%<*delta-def>
\begin{code}
  Δ : UUSet
  Δ ty tv = ty ≡ tv ⊎ ⟦ ty ⟧ A × ⟦ tv ⟧ A
\end{code}
%</delta-def>

  It has a cost function:

\begin{code}
  cost-Δ : {ty tv : U} → Δ ty tv → ℕ
  cost-Δ           (i1 _)       = 0
  cost-Δ {ty} {tv} (i2 (x , y)) = size1 sized ty x + size1 sized tv y

  delta : {ty tv : U} → ⟦ ty ⟧ A → ⟦ tv ⟧ A → Δ ty tv
  delta {ty} {tv} x y with U-eq ty tv
  ...| no _ = i2 (x , y)
  delta {ty} {.ty} x y | yes refl
    with dec-eq _≟-A_ ty x y 
  ...| yes _ = i1 refl
  ...| no  _ = i2 (x , y)
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

  appₗ : {ty tv : U}
       → Δ ty tv → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
  appₗ {ty} {.ty} (i1 refl)    z = just z
  appₗ {ty} {tv}  (i2 (x , y)) z
    with dec-eq _≟-A_ ty x z
  ...| yes _ = just y
  ...| no  _ = nothing

  appᵣ : {ty tv : U}
       → Δ ty tv → ⟦ tv ⟧ A → Maybe (⟦ ty ⟧ A)
  appᵣ {ty} {.ty} (i1 refl)    z = just z
  appᵣ {ty} {tv}  (i2 (x , y)) z
    with dec-eq _≟-A_ tv y z
  ...| yes _ = just x
  ...| no  _ = nothing

  Δ-apply : Appliable Δ
  Δ-apply 
    = apply appₗ appᵣ      
\end{code}
