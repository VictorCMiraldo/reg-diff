\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.PartialFuncs.Base
open import RegDiff.Generic.Parms

module RegDiff.Diff.Trivial.Apply
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open import RegDiff.Diff.Universe ks keqs A _≟-A_
  open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_
\end{code}

  The application functions in both directions makes it easy
  to see how the two phases of the algorithm play together.

\begin{code}
  HasApp : UUSet → Set
  HasApp Q = ∀{ty tv} → Q ty tv → ⟦ ty ⟧ ⇀ ⟦ tv ⟧
\end{code}

\begin{code}
  HasAppₐ : AASet → Set
  HasAppₐ Q = ∀{ty tv} → Q ty tv → ⟦ ty ⟧ₐ ⇀ ⟦ tv ⟧ₐ
\end{code}

\begin{code}
  HasAppₚ : ΠΠSet → Set
  HasAppₚ Q = ∀{ty tv} → Q ty tv → ⟦ ty ⟧ₚ ⇀ ⟦ tv ⟧ₚ
\end{code}

\begin{code}
  singl   : ∀{α}{A : Set α}{ty tv : A}(P : A → Set)
            (eqP : (k : A)(x y : P k) → Dec (x ≡ y))
          → P ty → P tv → (P ty ⇀ P tv)
  singl {ty = ty} P eqP pa pb
    = ((const pb) ♭) & (So ∘ eqP ty pa)
\end{code}
\begin{code}
  Trivial-apply : ∀{α}{A : Set α}{ty tv : A}(P : A → Set)
            (eqA : (x y : A) → Dec (x ≡ y))
            (eqP : (k : A)(x y : P k) → Dec (x ≡ y))
          → trivial P ty tv → (P ty ⇀ P tv)
  Trivial-apply {ty = ty} {tv = tv} P eqA eqP (pa1 , pa2)
    with eqA ty tv
  ...| no _ = singl P eqP pa1 pa2
  Trivial-apply {ty = ty} P eqA eqP (pa1 , pa2) 
     | yes refl with eqP ty pa1 pa2
  ...| no  _ = singl P eqP pa1 pa2
  ...| yes _ = id ♭
\end{code}
\begin{code}
  Trivialₐ-apply : {ty tv : Atom} → Trivialₐ ty tv → (⟦ ty ⟧ₐ ⇀ ⟦ tv ⟧ₐ)
  Trivialₐ-apply {ty} {tv} = Trivial-apply {ty = ty} {tv} ⟦_⟧ₐ Atom-eq (dec-eqₐ _≟-A_)

  Trivialₚ-apply : {ty tv : Π} → Trivialₚ ty tv → (⟦ ty ⟧ₚ ⇀ ⟦ tv ⟧ₚ)
  Trivialₚ-apply {ty} {tv} = Trivial-apply {ty = ty} {tv} ⟦_⟧ₚ Prod-eq (dec-eqₚ _≟-A_)

  Trivialₛ-apply : {ty tv : U} → Trivialₛ ty tv → (⟦ ty ⟧ ⇀ ⟦ tv ⟧)
  Trivialₛ-apply {ty} {tv} = Trivial-apply {ty = ty} {tv} ⟦_⟧ Sum-eq (dec-eq _≟-A_)
\end{code}
