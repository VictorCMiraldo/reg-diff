  Here we try to tie the knot for a mutually recursive family
  of datatypes.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.Multirec.Base
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  import RegDiff.Generic.Multirec ks as MREC
  import RegDiff.Generic.Eq ks keqs as EQ
\end{code}

  The idea is almost the same as for fixpoints,
  but now, we parametrize over a family of datatypes.

\begin{code}
  module Internal {fam# : ℕ}(fam : MREC.Fam fam#) where
\end{code}

\begin{code}
    open import RegDiff.Diff.Universe ks keqs (MREC.Fix fam) EQ._≟_
    open import RegDiff.Diff.Trivial.Base ks keqs (MREC.Fix fam) EQ._≟_
    open import RegDiff.Diff.Regular.Base ks keqs (MREC.Fix fam) EQ._≟_
      public
\end{code}

  And now, we just change the types slightly, but
  the rationale behind this is the same as normal fixpoints.

  But now, instead oh matching only I's, we match (I k)'s.

%<*Fami-def>
\begin{code}
    Famᵢ : Set
    Famᵢ = Fin fam#

    T : Famᵢ → Sum fam#
    T k = lookup k fam
\end{code}
%</Fami-def>
%<*Patchmu-skel-def>
\begin{code}
    data Patchμ : U → U → Set where
      skel  : {ty : U} → Patch (UU→AA Patchμ) ty 
            → Patchμ ty ty
\end{code}
%</Patchmu-skel-def>
%<*Patchmu-ins-del-def>
\begin{code}
      ins   : {ty : U}{k : Famᵢ}(i : Constr ty)
            → Al (UU→AA Patchμ) (I k ∷ []) (typeOf ty i) 
            → Patchμ (T k) ty
      del   : {ty : U}{k : Famᵢ}(i : Constr ty)
            → Al (UU→AA Patchμ) (typeOf ty i) (I k ∷ [])  
            → Patchμ ty (T k)
\end{code}
%</Patchmu-ins-del-def>
%<*Patchmu-fix-set-def>
\begin{code}
      fix   : {k k'   : Famᵢ}  
            → Patchμ (T k) (T k')      
            → Patchμ (α (I k)) (α (I k'))
      set   : {ty tv : U} 
            → Trivialₛ ty tv
            → Patchμ ty tv
\end{code}
%</Patchmu-fix-set-def>

%<*Patchmu-cost>
\begin{code}
    {-# TERMINATING #-}
    Patchμ-cost : {ty tv : U} → Patchμ ty tv → ℕ
    Patchμ-cost (skel x)  
      = Patch-cost Patchμ-cost x
    Patchμ-cost (ins i x) 
      = Al-cost Patchμ-cost x
    Patchμ-cost (del i x) 
      = Al-cost Patchμ-cost x
    Patchμ-cost (fix p)   
      = Patchμ-cost p
    Patchμ-cost (set x)
      = cost-Trivialₛ x
\end{code}
%</Patchmu-cost>

\begin{code}
    mutual
\end{code}
%<*diffmu-atoms>
\begin{code}
      diffμ*-atoms : {ty tv : Atom} → ⟦ ty ⟧ₐ → ⟦ tv ⟧ₐ → List (UU→AA Patchμ ty tv)
      diffμ*-atoms {I ty} {I tv} x y  = fix <$> diffμ* x y
      diffμ*-atoms {K ty} {K tv} x y  = return (set (to-α {K ty} x , to-α {K tv} y))
      diffμ*-atoms {K ty} {I tv} x y  = []
      diffμ*-atoms {I ty} {K tv} x y  = []
\end{code}
%</diffmu-atoms>
%<*alignmu-def>
\begin{code}
      alignμ  : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ
              → List (Al (UU→AA Patchμ) ty tv)
      alignμ x y = align* x y >>= Al-mapM (uncurry diffμ*-atoms)
\end{code}
%</alignmu-def>
%<*alignmu-nonempty-def>
\begin{code}      
      alignμ'  : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ
               → List (Al (UU→AA Patchμ) ty tv)
      alignμ' {[]}     {_}      _ _  = []
      alignμ' {_}      {[]}     _ _  = []
      alignμ' {_ ∷ _}  {_ ∷ _}  x y  = alignμ x y
\end{code}
%</alignmu-nonempty-def>
%<*diffmu-mod>
\begin{code}
      diffμ*-mod : {ty tv : U} → ⟦ ty ⟧ → ⟦ tv ⟧ → List (Patchμ ty tv)
      diffμ*-mod {ty} {tv} x y with Sum-eq ty tv
      ...| no _ = []
      diffμ*-mod x y
         | yes refl 
         = skel <$> S-mapM (uncurry alignμ) (spine x y)
{-
         = skel <$> (diff1* x y >>= Patch-mapM (uncurry diffμ*-atoms))
-}
\end{code}
%</diffmu-mod>
%<*diffmu-ins>
\begin{code}
      diffμ*-ins : {ty : U}{k : Famᵢ} → Fix fam k → ⟦ ty ⟧ → List (Patchμ (T k) ty)
      diffμ*-ins x y with sop y
      diffμ*-ins x _ | strip cy dy 
        = ins cy <$> alignμ' (x , unit) dy
\end{code}
%</diffmu-ins>
%<*diffmu-del>
\begin{code}
      diffμ*-del : {ty : U}{k : Famᵢ} → ⟦ ty ⟧ → Fix fam k → List (Patchμ ty (T k))
      diffμ*-del x y with sop x
      diffμ*-del _ y | strip cx dx
        = del cx <$> alignμ' dx (y , unit) 
\end{code}
%</diffmu-del>
%<*diff-mu-non-det>
\begin{code}
      {-# TERMINATING #-}
      diffμ* : {k k' : Famᵢ} → Fix fam k → Fix fam k' → List (Patchμ (T k) (T k'))
      diffμ* {k} {k'} ⟨ x ⟩ ⟨ y ⟩ 
        =   diffμ*-mod {T k}            {T k'}    x      y
        ++  diffμ*-ins {lookup k' fam}  {k}    ⟨  x ⟩    y
        ++  diffμ*-del {lookup k fam}   {k'}      x   ⟨  y ⟩
\end{code}
%</diff-mu-non-det>

\begin{code}
    _<μ>_ : {ty tv : U} → Patchμ ty tv → List (Patchμ ty tv) → Patchμ ty tv
    s <μ> []       = s
    s <μ> (o ∷ os) with Patchμ-cost s ≤?-ℕ Patchμ-cost o
    ...| yes _ = s <μ> os
    ...| no  _ = o <μ> os

    Patchμ* : U → U → Set
    Patchμ* ty tv = List (Patchμ ty tv)

    Patchμ& : U → U → Set
    Patchμ& ty tv = List (ℕ × Patchμ ty tv)

    addCostsμ : {ty tv : U} → Patchμ* ty tv → Patchμ& ty tv
    addCostsμ = map (λ x → Patchμ-cost x , x)

    filterCostsμ : {ty tv : U} → ℕ → Patchμ* ty tv → Patchμ* ty tv
    filterCostsμ n = filter (cmp n ∘ Patchμ-cost)
      where
        cmp : ℕ → ℕ → Bool
        cmp zero zero = true
        cmp (suc n) (suc m) = cmp n m
        cmp _ _ = false
\end{code}
%<*diffmu-det>
\begin{code}
    diffμ : {k k' : Famᵢ} → Fix fam k → Fix fam k' → Patchμ (T k) (T k')
    diffμ {k} x y with diffμ* x y
    ...| s ∷ ss  = s <μ> ss
    ...| []      = set (unmu x , unmu y)
\end{code}
%</diffmu-det>
