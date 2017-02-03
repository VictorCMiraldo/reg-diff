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
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where
\end{code}
%</Trivial-module-decl>

\begin{code}
  open import RegDiff.Diff.Universe ks keqs A _≟-A_
\end{code}

  As usual, we say that the "diagonal" functor
  is the trivial diff.

  Here we define the diagonal functor modulo denotational
  semantics. This reduces code duplication as we will
  need diagonals over Atoms, Products and Sums

%<*trivial-polymorphic-def>
\begin{code}
  trivial : ∀{a}{A : Set a}(P : A → Set)
        → A → A → Set
  trivial P a₁ a₂ = P a₁ × P a₂
\end{code}
%</trivial-polymorphic-def>

%<*cost-trivial-polymorphic-def>
\begin{code}
  cost-trivial-raw : ℕ
  cost-trivial-raw = 2

  cost-trivial : ∀{α}{A : Set α}{ty tv : A}(P : A → Set)
               (eqA : (x y : A) → Dec (x ≡ y))
               (eqP : (k : A)(x y : P k) → Dec (x ≡ y))
             → trivial P ty tv → ℕ
  cost-trivial {ty = ty} {tv = tv} P eqA eqP (pa1 , pa2) 
    with eqA ty tv
  ...| no _ = cost-trivial-raw
  cost-trivial {ty = ty} P eqA eqP (pa1 , pa2) 
     | yes refl with eqP ty pa1 pa2
  ...| no  _ = cost-trivial-raw
  ...| yes _ = 0
\end{code}
%</cost-trivial-polymorphic-def>

%<*trivial-a-def>
\begin{code}
  Trivialₐ : AASet
  Trivialₐ = trivial ⟦_⟧ₐ

  cost-Trivialₐ : {ty tv : Atom} → Trivialₐ ty tv → ℕ
  cost-Trivialₐ {ty} {tv} = cost-trivial {ty = ty} {tv} ⟦_⟧ₐ Atom-eq (dec-eqₐ _≟-A_)
\end{code}
%</trivial-a-def>

%<*trivial-p-def>
\begin{code}
  Trivialₚ : ΠΠSet
  Trivialₚ = trivial ⟦_⟧ₚ

  cost-Trivialₚ : {ty tv : Π} → Trivialₚ ty tv → ℕ
  cost-Trivialₚ {ty} {tv} = cost-trivial {ty = ty} {tv} ⟦_⟧ₚ Prod-eq (dec-eqₚ _≟-A_)
\end{code}
%</trivial-a-def>

%<*trivial-s-def>
\begin{code}
  Trivialₛ : UUSet
  Trivialₛ = trivial ⟦_⟧

  cost-Trivialₛ : {ty tv : U} → Trivialₛ ty tv → ℕ
  cost-Trivialₛ {ty} {tv} = cost-trivial {ty = ty} {tv} ⟦_⟧ Sum-eq (dec-eq _≟-A_)
\end{code}
%</trivial-s-def>
