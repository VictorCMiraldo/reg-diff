  Diffing fixpoints is trivial once we have done it for
  mutually recursive families:

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector

module RegDiff.SOP.Diff.Fixpoint.Base
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open import RegDiff.SOP.Generic.Fixpoint ks keqs
  open import RegDiff.SOP.Generic.Eq ks keqs
  import RegDiff.SOP.Diff.Multirec.Base ks keqs
    as MREC

  module Internal (T : Uₙ 1) where
    open MREC.Internal (T ∷ []) public
\end{code}
