\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Diff.Fixpoint.Apply
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open import RegDiff.Generic.Multirec ks
  import RegDiff.Diff.Multirec.Apply ks keqs
    as MREC

  module Internal (T : Sum 1) where
    open MREC.Internal (T ∷ []) public
\end{code}
