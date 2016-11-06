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
      Patchμ ty = S (SVar +ᵤ Cμ Rec) ty

      data Rec : U → U → Set where
        fix : Patchμ T → Rec I I
        set : ∀{ty tv} → Δ ty tv → Rec ty tv

      data SVar : U → U → Set where
        Svar : Patchμ T → SVar I I

      data Cμ (P : UUSet) : U → U → Set where
        Cins  : C P I T → Cμ P T T
        Cdel  : C P T I → Cμ P T T
        Cmod  : {ty tv : U}
              → C (Sym (C P)) ty tv → Cμ P ty tv
\end{code}
%</SI-def>

\begin{code}
    mutual
      {-# TERMINATING #-}
      Patchμ-cost : {ty : U} → Patchμ ty → ℕ
      Patchμ-cost = S-cost (SVar+Cμ-cost Rec-cost)

      Rec-cost : {ty tv : U} → Rec ty tv → ℕ
      Rec-cost (fix x) = Patchμ-cost x
      Rec-cost {ty} {tv} (set x) = cost-Δ {ty} {tv} x
    
      SVar+Cμ-cost : {ty tv : U}{P : UUSet} 
                   → (costP : ∀{k v} → P k v → ℕ)
                   → (SVar +ᵤ Cμ P) ty tv → ℕ
      SVar+Cμ-cost c (i1 (Svar x)) = Patchμ-cost x
      SVar+Cμ-cost c (i2 y)        = Cμ-cost c y

      Cμ-cost : {ty tv : U}{P : UUSet} 
              → (costP : ∀{k v} → P k v → ℕ)
              → Cμ P ty tv → ℕ
      Cμ-cost c (Cins x) = 1 + C-cost c x
      Cμ-cost c (Cdel x) = 1 + C-cost c x
      Cμ-cost c (Cmod y) = C-cost (C-cost c) y
\end{code}

  Diffing a value of a fixed point is defined next.

  Note how it is important to NOT get out of the list monad until
  we have computed everything. Otherwise we will not be exploring
  every possibility.

\begin{code}
    mutual
      refine-C : {ty tv : U} → Δ ty tv → List (Rec ty tv)
      refine-C {I} {I} (x , y) = fix <$> diffμ* x y
      refine-C         (x , y) = return (set (x , y))

      {-# TERMINATING #-}
      refine-S : {ty : U} → Δ ty ty → List ((SVar +ᵤ Cμ Rec) ty ty)
      refine-S {I}  (x , y) = (i1 ∘ Svar) <$> diffμ* x y
      refine-S {ty} (x , y) = i2          <$> changeμ x y

      spineμ : {ty : U} → ⟦ ty ⟧ (μ T) → ⟦ ty ⟧ (μ T) → List (Patchμ ty)
      spineμ x y = spine-cp x y >>= S-mapM refine-S

      changeμ : {ty tv : U} → ⟦ ty ⟧ (μ T) → ⟦ tv ⟧ (μ T) → List (Cμ Rec ty tv)
      changeμ x y = change-sym x y >>= C-mapM (C-mapM refine-C) 
                                   >>= return ∘ Cmod
    {- change-sym x y 
                >>= C-mapM (λ k → (i2 ∘ i2) <$> return k) -}

      diffμ* : μ T → μ T → List (Patchμ T)
      diffμ* ⟨ x ⟩ ⟨ y ⟩ 
        =  spineμ x y
        ++ ((SX ∘ i2 ∘ Cdel) <$> (change x ⟨ y ⟩ >>= C-mapM refine-C))
        ++ ((SX ∘ i2 ∘ Cins) <$> (change ⟨ x ⟩ y >>= C-mapM refine-C))
\end{code}

\begin{code}
    _<μ>_ : {ty : U} → Patchμ ty → List (Patchμ ty) → Patchμ ty
    s <μ> []       = s
    s <μ> (o ∷ os) with Patchμ-cost s ≤?-ℕ Patchμ-cost o
    ...| yes _ = s <μ> os
    ...| no  _ = o <μ> os

    diffμ : μ T → μ T → Patchμ T
    diffμ x y with diffμ* x y
    ...| []     = SX (i2 (Cmod (CX (CX (set (unmu x , unmu y))))))
    ...| s ∷ ss = s <μ> ss
\end{code}



