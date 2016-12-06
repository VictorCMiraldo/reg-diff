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
module RegDiff.SOP.Diff.Trivial.Base
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where
\end{code}
%</Trivial-module-decl>

\begin{code}
  open import RegDiff.SOP.Generic.Multirec ks
    renaming (Atom to Atom'; ⟦_⟧ₐ to interpₐ; ⟦_⟧ₚ to interpₚ;
              ⟦_⟧ to interpₛ)
  open import RegDiff.SOP.Generic.Eq ks keqs
\end{code}

  This module serves the purpose of defining a bunch of
  auxiliary functions for later on.

%<*Trivial-defs>
\begin{code}
  U : Set
  U = σπ parms#

  Atom : Set
  Atom = Atom' parms#
  
  Π : Set
  Π = π parms#

  sized : {p : Fin parms#} → A p → ℕ
  sized = parm-size WBA

  _≟-A_ : {p : Fin parms#}(x y : A p) → Dec (x ≡ y)
  _≟-A_ = parm-cmp WBA
\end{code}
%</Trivial-defs>
%<*Trivial-aux-defs>
\begin{code}
  ⟦_⟧ₐ : Atom → Set
  ⟦ a ⟧ₐ = interpₐ a A

  ⟦_⟧ₚ : Π → Set
  ⟦ p ⟧ₚ = interpₚ p A

  ⟦_⟧ : U → Set
  ⟦ u ⟧ = interpₛ u A

  UUSet : Set₁
  UUSet = U → U → Set

  AASet : Set₁
  AASet = Atom → Atom → Set

  ΠΠSet : Set₁
  ΠΠSet = Π → Π → Set

  contr : ∀{a b}{A : Set a}{B : Set b}
        → (A → A → B) → A → B
  contr p x = p x x

  UU→AA : UUSet → AASet
  UU→AA P a a' = P (α a) (α a')
\end{code}
%</Trivial-aux-defs>

  As usual, we say that the diagonal functor
  is the trivial diff.

  Here we define the diagonal functor modulo denotational
  semantics. This reduces code duplication as we will
  need diagonals over Atoms, Products and Sums

%<*delta-polymorphic-def>
\begin{code}
  delta : ∀{a}{A : Set a}(P : A → Set)
        → A → A → Set
  delta P a₁ a₂ = P a₁ × P a₂
\end{code}
%</delta-polymorphic-def>

%<*cost-delta-polymorphic-def>
\begin{code}
  cost-delta-raw : ℕ
  cost-delta-raw = 2

  cost-delta : ∀{α}{A : Set α}{ty tv : A}(P : A → Set)
               (eqA : (x y : A) → Dec (x ≡ y))
               (eqP : (k : A)(x y : P k) → Dec (x ≡ y))
             → delta P ty tv → ℕ
  cost-delta {ty = ty} {tv = tv} P eqA eqP (pa1 , pa2) 
    with eqA ty tv
  ...| no _ = cost-delta-raw
  cost-delta {ty = ty} P eqA eqP (pa1 , pa2) 
     | yes refl with eqP ty pa1 pa2
  ...| no  _ = cost-delta-raw
  ...| yes _ = 0
\end{code}
%</cost-delta-polymorphic-def>

%<*delta-a-def>
\begin{code}
  Δₐ : AASet
  Δₐ = delta ⟦_⟧ₐ

  cost-Δₐ : {ty tv : Atom} → Δₐ ty tv → ℕ
  cost-Δₐ {ty} {tv} = cost-delta {ty = ty} {tv} ⟦_⟧ₐ Atom-eq (dec-eqₐ _≟-A_)
\end{code}
%</delta-a-def>

%<*delta-p-def>
\begin{code}
  Δₚ : ΠΠSet
  Δₚ = delta ⟦_⟧ₚ

  cost-Δₚ : {ty tv : Π} → Δₚ ty tv → ℕ
  cost-Δₚ {ty} {tv} = cost-delta {ty = ty} {tv} ⟦_⟧ₚ π-eq (dec-eqₚ _≟-A_)
\end{code}
%</delta-a-def>

%<*delta-s-def>
\begin{code}
  Δₛ : UUSet
  Δₛ = delta ⟦_⟧

  cost-Δₛ : {ty tv : U} → Δₛ ty tv → ℕ
  cost-Δₛ {ty} {tv} = cost-delta {ty = ty} {tv} ⟦_⟧ σπ-eq (dec-eq _≟-A_)
\end{code}
%</delta-s-def>
