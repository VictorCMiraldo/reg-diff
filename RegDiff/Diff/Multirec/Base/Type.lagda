\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.Multirec.Base.Type
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  import RegDiff.Generic.Multirec ks as MREC
  import RegDiff.Generic.Eq ks keqs as EQ

  module Internal {fam# : ℕ}(fam : MREC.Fam fam#) where

    open import RegDiff.Diff.Universe ks keqs (MREC.Fix fam) EQ._≟_
    open import RegDiff.Diff.Trivial.Base ks keqs (MREC.Fix fam) EQ._≟_
    open import RegDiff.Diff.Regular.Base ks keqs (MREC.Fix fam) EQ._≟_
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
