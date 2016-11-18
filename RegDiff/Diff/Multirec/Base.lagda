  Here we try to tie the know for a mutually recursive family
  of datatypes.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import RegDiff.Generic.Parms

module RegDiff.Diff.Multirec.Base
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  open import RegDiff.Generic.Multirec ks
  open import RegDiff.Generic.Eq ks keqs
\end{code}
%<*UUSet-coprod>
\begin{code}
  _+ᵤ_ : {n : ℕ} → (Uₙ n → Uₙ n → Set) → (Uₙ n → Uₙ n → Set) → (Uₙ n → Uₙ n → Set)
  (P +ᵤ Q) ty tv = (P ty tv) ⊎ (Q ty tv)
\end{code}
%</UUSet-coprod>
\begin{code}
  WB-FAM : {n : ℕ}{fam : Fam n} → WBParms (Fix fam)
  WB-FAM = wb-parms Fam-size _≟_
\end{code}

  The idea is almost the same as for fixpoints,
  but now, we parametrize over a family of datatypes.

\begin{code}
  module Internal {fam# : ℕ}(fam : Fam fam#) where
\end{code}

\begin{code}
    open import RegDiff.Diff.Regular.Base ks keqs (Fix fam) WB-FAM
      public
\end{code}

  And now, we just change the types slightly, but
  the rationale behind this is the same as normal fixpoints.

  But now, instead oh matching only I's, we match (I k)'s.

%<*Fami-def>
\begin{code}
    Famᵢ : Set
    Famᵢ = Fin fam#

    T : Famᵢ → Uₙ fam#
    T k = lookup k fam
\end{code}
%</Fami-def>
%<*Patchmu-def>
\begin{code}
    mutual
      data Patchμ : U → U → Set where
        skel : {ty     : U}     → S       Patchμ ty      → Patchμ ty ty
        chng : {ty tv  : U}     → Cμ (Al  Patchμ) ty tv  → Patchμ ty tv
        fix  : {k k'   : Famᵢ}  → Patchμ (T k) (T k')    → Patchμ (I k) (I k')
        set  : {ty tv  : U}     → Δ ty tv                → Patchμ ty tv
\end{code}
%</Patchmu-def>
%<*Patchmu-aux-def>
\begin{code}
      data Cμ (P : UUSet) : U → U → Set where
        Cins  : {k k' : Famᵢ} → C       P  (I k) (T k')  → Cμ P (T k) (T k')
        Cdel  : {k k' : Famᵢ} → C (Sym  P) (I k) (T k')  → Cμ P (T k') (T k)
        Cmod  : {ty tv : U}
              → C (Sym (C (Sym P))) ty tv → Cμ P ty tv
\end{code}
%</Patchmu-aux-def>

  The rest of the code is exactly the same as for single fixpoints.

\begin{code}
    mutual
      {-# TERMINATING #-}
      Patchμ-cost : {ty tv : U} → Patchμ ty tv → ℕ
      Patchμ-cost (skel x) = S-cost Patchμ-cost x
      Patchμ-cost (chng x) = Cμ-cost (Al-cost Patchμ-cost) x
      Patchμ-cost (fix s)  = Patchμ-cost s
      Patchμ-cost (set {ty} {tv} x)  = cost-Δ {ty} {tv} x

      Cμ-cost : {ty tv : U}{P : UUSet} 
              → (costP : ∀{k v} → P k v → ℕ)
              → Cμ P ty tv → ℕ
      Cμ-cost c (Cins x) = 1 + C-cost c x
      Cμ-cost c (Cdel x) = 1 + C-cost c x
      Cμ-cost c (Cmod y) = C-cost (C-cost c) y
\end{code}

\begin{code}
    mutual
      refine-S : {ty : U} → Δ ty ty → List (Patchμ ty ty)
      refine-S {I k}  (x , y) = fix  <$> diffμ* x y
      refine-S        (x , y) = chng <$> changeμ x y

      spineμ : {ty tv : U} → ⟦ ty ⟧ (Fix fam) → ⟦ tv ⟧ (Fix fam) → List (Patchμ ty tv)
      spineμ {ty} {tv} x y with U-eq ty tv 
      ...| no _     = chng <$> changeμ x y
      spineμ {ty} {.ty} x y 
         | yes refl = skel <$> S-mapM refine-S (spine-cp x y)

      changeμ : {ty tv : U} 
              → ⟦ ty ⟧ (Fix fam) → ⟦ tv ⟧ (Fix fam) 
              → List (Cμ (Al Patchμ) ty tv)
      changeμ x y = Cmod <$> CSym²-mapM refine-C (change-sym-det x y)

      refine-C : {k v : U} → Δ k v → List (Al Patchμ k v)
      refine-C {I k} {I k'} (x , y) = (AX ∘ fix) <$> diffμ* x y
      refine-C              (x , y) = align x y >>= Al-mapM refine-Al

      refine-Al : {k v : U} → Δ k v → List (Patchμ k v)
      refine-Al {I k} {I k'} (x , y) = fix <$> diffμ* x y
      refine-Al              (x , y) = return (set (x , y))

      refine-CSym : {k v : U} → Δ k v → List (Sym (Al Patchμ) k v)
      refine-CSym (x , y) = refine-C (y , x)
  
      {-# TERMINATING #-}
      diffμ* : {k k' : Famᵢ} → Fix fam k → Fix fam k' → List (Patchμ (T k) (T k'))
      diffμ* {k} {k'} ⟨ x ⟩ ⟨ y ⟩ 
        =  spineμ {T k} {T k'} x y
        ++ ((chng ∘ Cdel {k = k'} {k}) <$> (C-mapM refine-CSym (change ⟨ y ⟩ x)))
        ++ ((chng ∘ Cins {k = k} {k'}) <$> (C-mapM refine-C    (change ⟨ x ⟩ y)))
\end{code}
%<*refinements>
begin{code}
    mutual
      refine-Al : {ty tv : U} → Δ ty tv → List (Rec ty tv)
      refine-Al {I k} {I k'} (x , y) 
        with k ≟-Fin k'
      ...| no _ = return (set (delta {I k} {I k'} x y))
      refine-Al {I k} {I .k} (x , y) 
         | yes refl = fix <$> diffμ* x y
      refine-Al {ty} {tv} (x , y) = return (set (delta {ty} {tv} x y))
      
      refine-CSym : {ty tv : U} → Δ ty tv → List (Sym (Al Rec) ty tv)
      refine-CSym (x , y) = refine-C (y , x)

      refine-C : {ty tv : U} → Δ ty tv → List (Al Rec ty tv)
      refine-C {I k} {I k'} (x , y) 
        with k ≟-Fin k'
      ...| no _ = align x y >>= Al-mapM refine-Al
      refine-C {I k} {I .k} (x , y) 
         | yes refl = (AX ∘ fix) <$> diffμ* x y
      refine-C              (x , y) = align x y >>= Al-mapM refine-Al

      {-# TERMINATING #-}
      refine-S : {ty : U} → Δ ty ty → List ((SVar +ᵤ Cμ (Al Rec)) ty ty)
      refine-S {I k}  (x , y) = (i1 ∘ Svar) <$> diffμ* x y
      refine-S {ty}   (x , y) = i2          <$> changeμ x y
\end{code}
%</refinements>
%<*spinemu-def>
begin{code}
      spineμ : {ty : U}(x y : ⟦ ty ⟧ (Fix fam)) → List (Patchμ ty)
      spineμ x y = S-mapM refine-S (spine-cp x y)
\end{code}
%</spinemu-def>
%<*changemu-def>
begin{code}
      changeμ : {ty tv : U} 
              → ⟦ ty ⟧ (Fix fam) → ⟦ tv ⟧ (Fix fam) 
              → List (Cμ (Al Rec) ty tv)
      changeμ x y = change-sym x y >>= CSym²-mapM refine-C 
                >>= return ∘ Cmod
\end{code}
%</changemu-def>
%<*diffmu-nondet-def>
begin{code}
      diffμ* : {k : Famᵢ} → Fix fam k → Fix fam k → List (Patchμ (T k))
      diffμ* {k} ⟨ x ⟩ ⟨ y ⟩ 
        =  spineμ {T k} x y
        ++ ((SX ∘ i2 ∘ Cdel {k = k}) <$> (C-mapM refine-CSym (change ⟨ y ⟩ x)))
        ++ ((SX ∘ i2 ∘ Cins {k = k}) <$> (C-mapM refine-C    (change ⟨ x ⟩ y)))
\end{code}
%</diffmu-nondet-def>

\begin{code}
    _<μ>_ : {ty tv : U} → Patchμ ty tv → List (Patchμ ty tv) → Patchμ ty tv
    s <μ> []       = s
    s <μ> (o ∷ os) with Patchμ-cost s ≤?-ℕ Patchμ-cost o
    ...| yes _ = s <μ> os
    ...| no  _ = o <μ> os

    diffμ : {k : Famᵢ} → Fix fam k → Fix fam k → Patchμ (T k) (T k)
    diffμ {k} x y with diffμ* x y
    ...| []     = set (unmu x , unmu y)
    ...| s ∷ ss = s <μ> ss
\end{code}



