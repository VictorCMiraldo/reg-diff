  Now, we use the previous diff for regular types
  and tie the know for fixpoints.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Diff.Fixpoint.Base
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open Monad {{...}} renaming (μ to join)
  open Applicative {{...}}

  open import RegDiff.Generic.Base v
  open import RegDiff.Generic.Eq v eqs

  
\end{code}

  First things first. We need to keep track of the
  the type we are taking the fixpoint of.

  We abstract this as a module parameter:

\begin{code}
  module Internal (T : U) where
\end{code}

  We then proceed to use the diff for regular types 
  applied to the correct parameters. 

\begin{code}
    open import RegDiff.Diff.Regular.Base v eqs (μ T) μ-size
      public
\end{code}

  The insight for fixpoints is that we can traverse trough a variable
  as long as we can diff something of type T or we can
  "skip" traversing a variable and insert something there instead.

%<*SI-def>
\begin{code}
    data SI (P : UUSet) : U → U → Set where
      Svar : S (SI P) T T → SI P I I
      Sins : S (SI P) T I → SI P T T
      SY   : {ty tv : U} → P ty tv → SI P ty tv
\end{code}
%</SI-def>

  For convenience, we define an Sμ:

%<*Smu-def>
\begin{code}
    Sμ : UUSet → UUSet
    Sμ P = S (SI P)
\end{code}
%</Smu-def>

  We piggyback on the
  previous definitions and expand our cost function
  to handle SI's now:

\begin{code}
    {-# TERMINATING #-}
    SI-cost : {ty tv : U}{P : UUSet}
            → (costP : ∀{ty tv} → P ty tv → ℕ)
            → SI P ty tv → ℕ
    SI-cost c (Svar x) = S-cost (SI-cost c) x
    SI-cost c (Sins x) = 1 + S-cost (SI-cost c) x
    SI-cost c (SY x) = c x

    SμΔ-cost : {ty tv : U} → Sμ Δ ty tv → ℕ
    SμΔ-cost = S-cost (SI-cost (λ {ty} {tv} xy → cost-Δ {ty} {tv} xy))

    private
      infixr 20 _<>_
      _<>_ : {ty tv : U} → Sμ Δ ty tv → List (Sμ Δ ty tv) →  Sμ Δ ty tv
      s <> [] = s
      s <> (o ∷ os) with SμΔ-cost s ≤?-ℕ SμΔ-cost o 
      ...| yes _ = s <> os
      ...| no  _ = o <> os
\end{code}

  Diffing a value of a fixed point is defined next.

  Note how it is important to NOT get out of the list monad until
  we have computed everything. Otherwise we will not be exploring
  every possibility.

\begin{code}
    mutual
      {-# TERMINATING #-}
      refine : {ty tv : U} → Δ ty tv → List (SI Δ ty tv)
      refine {I} {I} (x , y)   = Svar <$> (spineμ x y)
      refine {ty} {tv} (x , y) = return (SY (x , y))

      spineμ' : {ty tv : U} → ⟦ ty ⟧ (μ T) → ⟦ tv ⟧ (μ T) → List (Sμ Δ ty tv)
      spineμ' x y = spine x y >>= S-mapM refine

      spineμ : μ T → μ T → List (Sμ Δ T T)
      spineμ ⟨ x ⟩ ⟨ y ⟩ 
        =  spineμ' x y
        ++ ((SX ∘ Sins)        <$> (spineμ' x ⟨ y ⟩))
        ++ ((Ssym ∘ SX ∘ Sins) <$> (spineμ' y ⟨ x ⟩))
\end{code}

  Finally, we can choose the actual patch between all possibilities when we have computed
  all of them.

  We have to stay in the List monad in order to guarantee that the algorithm
  is exploring all possiblities.

\begin{code}
    diffμ : μ T → μ T → Sμ Δ T T
    diffμ x y with spineμ x y
    ...| []     = SX (SY (unmu x , unmu y))
    ...| s ∷ ss = s <> ss
\end{code}



