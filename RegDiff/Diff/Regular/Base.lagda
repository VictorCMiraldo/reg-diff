  Here we define a refinement over the trivial diff.
  Instead of storing both values as a whole,
  we will store a bunch of transformations that
  could transform one into the other.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Base
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open Monad {{...}}

  open import RegDiff.Diff.Universe ks keqs A _≟-A_
  open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_

  -- Now the spine is just re-exported
  open import RegDiff.Diff.Regular.Base.Spine ks keqs A _≟-A_
    public

  -- And the alignment aswell.
  open import RegDiff.Diff.Regular.Base.AlignmentOptimized ks keqs A _≟-A_
    public
\end{code}



%<*Patch-def>
\begin{code}
  Patch : AASet → U → Set
  Patch P = S (Al P)
\end{code}
%</Patch-def>
\begin{code}
  Patch-cost : {ty : U}{P : AASet}(doP : ∀{k v} → P k v → ℕ)
             → Patch P ty → ℕ
  Patch-cost doP = S-cost (Al-cost doP)

  Patch-mapM : {ty : U}{M : Set → Set}{{m : Monad M}}
               {P Q : AASet}(X : ∀{k v} → P k v → M (Q k v))
             → Patch P ty → M (Patch Q ty)
  Patch-mapM X = S-mapM (Al-mapM X)
\end{code}
\begin{code}
  Patch-cost-Trivialₐ : {ty : U} → Patch Trivialₐ ty → ℕ
  Patch-cost-Trivialₐ = Patch-cost (λ {k} {v} → cost-Trivialₐ {k} {v})

  Patch* : U → Set
  Patch* = List ∘ Patch Trivialₐ

  Patch& : U → Set
  Patch& = List ∘ (ℕ ×_) ∘ Patch Trivialₐ

  addCosts : {ty : U} → Patch* ty → Patch& ty
  addCosts = map (λ k → Patch-cost-Trivialₐ k , k)

  choose : {ty : U} → Patch Trivialₐ ty → Patch Trivialₐ ty → Patch Trivialₐ ty
  choose c d with Patch-cost-Trivialₐ c ≤?-ℕ Patch-cost-Trivialₐ d
  ...| yes _ = d
  ...| no  _ = c

  _<>_ : {ty : U} → Patch Trivialₐ ty → List (Patch Trivialₐ ty) → Patch Trivialₐ ty
  c <> [] = c
  c <> (d ∷ ds) = (choose c d) <> ds
\end{code}
%<*diff1-star-def>
\begin{code}
  diff1* : {ty : U}(x y : ⟦ ty ⟧) → Patch* ty
  diff1* x y = S-mapM (uncurry align*) (spine x y)
\end{code}
%</diff1-star-def>
%<*diff1-def>
\begin{code}
  diff1 : {ty : U} → ⟦ ty ⟧ → ⟦ ty ⟧ → Patch Trivialₐ ty
  diff1 x y with diff1* x y
  ...| s ∷ ss = s <> ss
  ...| []     = impossible
     where postulate impossible : {ty : U} → Patch Trivialₐ ty
\end{code}
%</diff1-def>


 TODO: Prove that diff1* is NEVER the empty list.
