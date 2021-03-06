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

    knot : {P : UUSet}(doP : HasCmp P) → HasCmp (UU→AA P)
    knot doP = doP
\end{code}
    
begin{code}
    Alμ : Π → Π → Set
    Alμ = Al (UU→AA Patchμ)

    Al-push : {k : Famᵢ}{ty : Π}{tv : U}(i : Constr ty)
            → Patchμ ty (T k)
            → Alμ (I k ∷ []) tv
            → Maybe (Alμ 
\end{code}

\begin{code}
    {-# TERMINATING #-}
    Patchμ-cmp : {k i j : Famᵢ}
               → Patchμ (T i) (T j) → Patchμ (T k) (T i) → Maybe (Patchμ (T k) (T j))
    Patchμ-cmp {k} {i} {j} (ins {ty = .(T j)} {.i} cᵢ al) q = {!!}
    Patchμ-cmp {k} {i} {j} p q = {!!}
    
    
\end{code}

begin{code}
    {-# TERMINATING #-}
    Patchμ-cmp : HasCmp Patchμ
    Patchμ-cmp (skel p)  q = {!!}
    Patchμ-cmp (ins {k = k} i al) q 
      = ins i <$> {!!}
    -- Patchμ-cmp (ins {k = k} i al) (set q) = ?
    -- Patchμ-cmp (ins {k = k} i al) (del {k = .k} j q) = ?
    Patchμ-cmp (del i al) q   = {!!}
    Patchμ-cmp (fix p)    q   = {!!}
    Patchμ-cmp (set xy)   q   = {!!}

\end{code}
    
