  Now, we use the previous diff for regular types
  and tie the know for fixpoints.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import RegDiff.Generic.Parms

module RegDiff.Diff.Fixpoint.Base
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  open import RegDiff.Generic.Fixpoint ks keqs
  open import RegDiff.Generic.Eq ks keqs

  _+ᵤ_ : (U → U → Set) → (U → U → Set) → (U → U → Set)
  (P +ᵤ Q) ty tv = (P ty tv) ⊎ (Q ty tv)
  
\end{code}

  First things first. We need to keep track of the
  the type we are taking the fixpoint of.

  We abstract this as a module parameter:

\begin{code}
  module Internal (T : U) where

    PARMS : Fin 1 → Set
    PARMS = const (Fix T)

    WB-PARMS : WBParms PARMS
    WB-PARMS 
      = wb-parms 
        (λ { {fz} → μ-size 
           ; {fs ()} 
           }) 
        (λ { {fz} → _≟-Fix_ 
           ; {fs ()} 
           })
\end{code}

  We then proceed to use the diff for regular types 
  applied to the correct parameters. 

\begin{code}
    open import RegDiff.Diff.Regular.Base ks keqs PARMS WB-PARMS
      hiding (U)
      public
\end{code}

  The idea then, is to extend the Spine with an additional
  constructor to traverse through variables.

  The changes, are fairly different, though.

  An insertion is one round of injections;
  A deletion is one round of pattern-mathing;
  A modification is one round of each!

  At the end, we end up having to align products in the
  same way we did for regular types and tie the know with a Rec
  type, that lets one either "set" a value or go back to diffing 
  the actual fixpoint again.

%<*SI-def>
\begin{code}
    mutual
      Patchμ : U → Set
      Patchμ ty = S (SVar +ᵤ Cμ (Al Rec)) ty

      data Rec : U → U → Set where
        fix : Patchμ T → Rec I I
        set : ∀{ty tv} → Δ ty tv → Rec ty tv

      data SVar : U → U → Set where
        Svar : Patchμ T → SVar I I

      data Cμ (P : UUSet) : U → U → Set where
        Cins  : C      P  I T → Cμ P T T
        Cdel  : C (Sym P) I T → Cμ P T T
        Cmod  : {ty tv : U}
              → C (Sym (C (Sym P))) ty tv → Cμ P ty tv
\end{code}
%</SI-def>

  The workflow is as usual: we have cost functions
  and we piggy back on the definitions from regular types for
  everything.

  There is a bunch of synonyms here to help the type-checker.

\begin{code}
    mutual
      {-# TERMINATING #-}
      Patchμ-cost : {ty : U} → Patchμ ty → ℕ
      Patchμ-cost = S-cost (SVar+Cμ-cost (Al-cost Rec-cost))

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
      refine-Al : {ty tv : U} → Δ ty tv → List (Rec ty tv)
      refine-Al {Iₙ fz} {Iₙ fz} (x , y) = fix <$> diffμ* x y
      refine-Al                 (x , y) = return (set (x , y))
      
      refine-CSym : {ty tv : U} → Δ ty tv → List (Sym (Al Rec) ty tv)
      refine-CSym (x , y) = refine-C (y , x)

      refine-C : {ty tv : U} → Δ ty tv → List (Al Rec ty tv)
      refine-C {Iₙ fz} {Iₙ fz} (x , y) = (AX ∘ fix) <$> diffμ* x y
      refine-C                 (x , y) = align x y >>= Al-mapM refine-Al

      {-# TERMINATING #-}
      refine-S : {ty : U} → Δ ty ty → List ((SVar +ᵤ Cμ (Al Rec)) ty ty)
      refine-S {Iₙ fz}  (x , y) = (i1 ∘ Svar) <$> diffμ* x y
      refine-S {ty}     (x , y) = i2          <$> changeμ x y

      spineμ : {ty : U}(x y : ⟦ ty ⟧ (Fix T)) → List (Patchμ ty)
      spineμ x y = spine-cp x y >>= S-mapM refine-S

      changeμ : {ty tv : U} → ⟦ ty ⟧ (Fix T) → ⟦ tv ⟧ (Fix T) → List (Cμ (Al Rec) ty tv)
      changeμ x y = change-sym x y >>= CSym²-mapM refine-C 
                >>= return ∘ Cmod

      diffμ* : Fix T → Fix T → List (Patchμ T)
      diffμ* ⟨ x ⟩ ⟨ y ⟩ 
        =  spineμ x y
        ++ ((SX ∘ i2 ∘ Cdel) <$> (change ⟨ y ⟩ x >>= C-mapM refine-CSym))
        ++ ((SX ∘ i2 ∘ Cins) <$> (change ⟨ x ⟩ y >>= C-mapM refine-C))
\end{code}

\begin{code}
    _<μ>_ : {ty : U} → Patchμ ty → List (Patchμ ty) → Patchμ ty
    s <μ> []       = s
    s <μ> (o ∷ os) with Patchμ-cost s ≤?-ℕ Patchμ-cost o
    ...| yes _ = s <μ> os
    ...| no  _ = o <μ> os

    diffμ : Fix T → Fix T → Patchμ T
    diffμ x y with diffμ* x y
    ...| []     = SX (i2 (Cmod (CX (CX (AX (set (unmu x , unmu y)))))))
    ...| s ∷ ss = s <μ> ss
\end{code}



