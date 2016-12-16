\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.PartialFuncs.Base
open import RegDiff.Generic.Parms

module RegDiff.Diff.Multirec.Grupoid
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Multirec.Base ks keqs
    renaming (module Internal to MRECInternal)
\end{code}

\begin{code}
  module Internal {fam# : ℕ}(fam : Fam fam#) where

    open MRECInternal fam
    open import RegDiff.Diff.Regular.Grupoid ks keqs (Fix fam) _≟_
      public
\end{code}
\begin{code}
    {-# TERMINATING #-}
    Patchμ-inv : HasInv Patchμ
    Patchμ-inv (skel p)    = skel (Patch-inv Patchμ-inv p)
    Patchμ-inv (ins i al)  = del i (Al-inv Patchμ-inv al)
    Patchμ-inv (del i al)  = ins i (Al-inv Patchμ-inv al)
    Patchμ-inv (fix p)     = fix (Patchμ-inv p)
    Patchμ-inv (set xy)    = set (Δₛ-inv xy)

    Patchμ-cmp : HasCmp Patchμ
    Patchμ-cmp (skel p)      = {!!}
    Patchμ-cmp (ins {k = k} i al)  b 
      = {!!}
    Patchμ-cmp (del i al)    = {!!}
    Patchμ-cmp (fix p)       = {!!}
    Patchμ-cmp (set xy)      = {!!}

\end{code}
    
