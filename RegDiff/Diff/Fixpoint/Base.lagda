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

  _+ᵤ_ : (U → U → Set) → (U → U → Set) → (U → U → Set)
  (P +ᵤ Q) ty tv = (P ty tv) ⊎ (Q ty tv)
  
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

    mutual
      Patchμ : U → Set
      Patchμ ty = S (SVar +ᵤ Cμ) ty

      Cμ : U → U → Set
      Cμ ty tv = C (CI +ᵤ (Sym (CI +ᵤ C Δ))) ty tv

      data SVar : U → U → Set where
        Svar : Patchμ T → SVar I I

      data CI : U → U → Set where
        Cins  : Cμ T I   → CI T T
        Cs    : {ty : U} → Patchμ ty → CI ty ty
\end{code}
%</SI-def>

  For convenience, we define an Sμ:

%<*Smu-def>
begin{code}
    Sμ : UUSet → UUSet
    Sμ P = S (SI P)
\end{code}
%</Smu-def>

  We piggyback on the
  previous definitions and expand our cost function
  to handle SI's now:

begin{code}
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
{-
      {-# TERMINATING #-}
      refine : {ty tv : U} → Δ ty tv → List (SI Δ ty tv)
      refine {I} {I} (x , y)   = Svar <$> (spineμ x y)
      refine {ty} {tv} (x , y) = return (SY (x , y))
-}
      {-# TERMINATING #-}
      refine-S : {ty : U} → Δ ty ty → List ((SVar +ᵤ Cμ) ty ty)
      refine-S {I}  (x , y) = (i1 ∘ Svar) <$> diffμ x y
      refine-S {ty} (x , y) = i2          <$> changeμ x y

      spineμ : {ty : U} → ⟦ ty ⟧ (μ T) → ⟦ ty ⟧ (μ T) → List (Patchμ ty)
      spineμ x y = spine-cp x y >>= S-mapM refine-S

      changeμ : {ty tv : U} → ⟦ ty ⟧ (μ T) → ⟦ tv ⟧ (μ T) → List (Cμ ty tv)
      changeμ x y = change-sym x y 
                >>= C-mapM (λ k → (i2 ∘ i2) <$> return k)

      diffμ : μ T → μ T → List (Patchμ T)
      diffμ ⟨ x ⟩ ⟨ y ⟩ 
        =  spineμ x y
        ++ ((SX ∘ i2 ∘ CX ∘ i1 ∘ Cins)      <$> changeμ x ⟨ y ⟩)
        ++ ((SX ∘ i2 ∘ CX ∘ i2 ∘ i1 ∘ Cins) <$> changeμ y ⟨ x ⟩)
{-
        ++ ((SX ∘ Sins)        <$> (spineμ' x ⟨ y ⟩))
        ++ ((Ssym ∘ SX ∘ Sins) <$> (spineμ' y ⟨ x ⟩))
-}
\end{code}

  Finally, we can choose the actual patch between all possibilities when we have computed
  all of them.

  We have to stay in the List monad in order to guarantee that the algorithm
  is exploring all possiblities.

begin{code}
    diffμ : μ T → μ T → Sμ Δ T T
    diffμ x y with spineμ x y
    ...| []     = SX (SY (unmu x , unmu y))
    ...| s ∷ ss = s <> ss
\end{code}



