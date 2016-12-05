\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.SOP.Diff.Fixpoint.Domain
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}} renaming (μ to join)
  open Applicative {{...}}

  open import RegDiff.Generic.Fixpoint ks keqs
  open import RegDiff.Generic.Eq ks keqs
  import RegDiff.Diff.Multirec.Domain ks keqs
    as MREC

  module Internal (T : Uₙ 1) where
    open MREC.Internal (T ∷ []) public
\end{code}
