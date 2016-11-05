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
      Cμ ty tv = (CID +ᵤ C (Sym (C Δ))) ty tv

      data SVar : U → U → Set where
        Svar : Patchμ T → SVar I I

      data CID : U → U → Set where
        Cins  : C Δ T I → CID T T
        Cdel  : C Δ I T → CID T T
        -- Cs    : {ty : U} → Patchμ ty → CI ty ty
\end{code}
%</SI-def>

\begin{code}
    mutual
      {-# TERMINATING #-}
      Patchμ-cost : {ty : U} → Patchμ ty → ℕ
      Patchμ-cost = S-cost SVar+Cμ-cost
    
      SVar+Cμ-cost : {ty tv : U} → (SVar +ᵤ Cμ) ty tv → ℕ
      SVar+Cμ-cost (i1 (Svar x)) = Patchμ-cost x
      SVar+Cμ-cost (i2 y) = Cμ-cost y

      Cμ-cost : {ty tv : U} → Cμ ty tv → ℕ
      Cμ-cost (i1 (Cins x)) = 1 + CΔ-cost x
      Cμ-cost (i1 (Cdel x)) = 1 + CΔ-cost x
      Cμ-cost (i2 y) = CSymCΔ-cost y
\end{code}

  Diffing a value of a fixed point is defined next.

  Note how it is important to NOT get out of the list monad until
  we have computed everything. Otherwise we will not be exploring
  every possibility.

\begin{code}
    mutual
      {-# TERMINATING #-}
      refine-S : {ty : U} → Δ ty ty → List ((SVar +ᵤ Cμ) ty ty)
      refine-S {I}  (x , y) = (i1 ∘ Svar) <$> diffμ* x y
      refine-S {ty} (x , y) = i2          <$> changeμ x y

      spineμ : {ty : U} → ⟦ ty ⟧ (μ T) → ⟦ ty ⟧ (μ T) → List (Patchμ ty)
      spineμ x y = spine-cp x y >>= S-mapM refine-S

      changeμ : {ty tv : U} → ⟦ ty ⟧ (μ T) → ⟦ tv ⟧ (μ T) → List (Cμ ty tv)
      changeμ x y = change-sym x y >>= return ∘ i2 
    {- change-sym x y 
                >>= C-mapM (λ k → (i2 ∘ i2) <$> return k) -}

      diffμ* : μ T → μ T → List (Patchμ T)
      diffμ* ⟨ x ⟩ ⟨ y ⟩ 
        =  spineμ x y
        ++ ((SX ∘ i2 ∘ i1 ∘ Cins) <$> change x ⟨ y ⟩)
        ++ ((SX ∘ i2 ∘ i1 ∘ Cdel) <$> change ⟨ x ⟩ y)
\end{code}

\begin{code}
    _<μ>_ : {ty : U} → Patchμ ty → List (Patchμ ty) → Patchμ ty
    s <μ> []       = s
    s <μ> (o ∷ os) with Patchμ-cost s ≤?-ℕ Patchμ-cost o
    ...| yes _ = s <μ> os
    ...| no  _ = o <μ> os

    diffμ : μ T → μ T → Patchμ T
    diffμ x y with diffμ* x y
    ...| []     = SX (i2 (i2 (CX (CX (unmu y , unmu x)))))
    ...| s ∷ ss = s <μ> ss
\end{code}



