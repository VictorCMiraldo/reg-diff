\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Diff.Fixpoint.Apply
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open import RegDiff.Generic.Fixpoint ks keqs
  open import RegDiff.Generic.Eq ks keqs
  import RegDiff.Diff.Multirec.Apply ks keqs
    as MREC
\end{code}

  module Internal (T : ?) where
    open MREC.Internal (T ∷ []) public
\end{code}
