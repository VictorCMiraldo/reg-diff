\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import RegDiff.Generic.Parms

module RegDiff.Diff.Copy.Base
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where

  open Monad {{...}}

  open import RegDiff.Generic.Multirec ks
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Trivial.Base ks keqs A WBA
    public
\end{code}

  Here we add the first patch instruction 
  to our arsenal: Copy

\begin{code}
  data Cpy (P : UUSet) : U → U → Set where
    set : {ty tv  : U} → P ty tv  → Cpy P ty tv
    cpy : {ty     : U}            → Cpy P ty ty
\end{code}

\begin{code}
  Cpy-mapM : {ty tv : U}{M : Set → Set}{{m : Monad M}}{P Q : UUSet}
           → (f : ∀{k v} → P k v → M (Q k v))
           → Cpy P ty tv → M (Cpy Q ty tv)
  Cpy-mapM f (set x) = f x >>= return ∘ set
  Cpy-mapM f cpy     = return cpy
\end{code}

\begin{code}
  Cpy-cost : {ty tv : U}{P : UUSet}
           → (doP : P ty tv → ℕ)
           → Cpy P ty tv → ℕ
  Cpy-cost doP (set x) = doP x
  Cpy-cost doP cpy     = 0
\end{code}

\begin{code}
  copy : {ty tv : U} → ⟦ ty ⟧ A → ⟦ tv ⟧ A → Cpy Δ ty tv
  copy {ty} {tv} x y 
    with U-eq ty tv
  ...| no _ = set (x , y)
  copy {ty} {.ty} x y | yes refl
    with dec-eq _≟-A_ ty x y
  ...| no  _ = set (x , y)
  ...| yes _ = cpy
\end{code}
