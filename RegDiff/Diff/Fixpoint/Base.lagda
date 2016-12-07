  Diffing fixpoints is trivial once we have done it for
  mutually recursive families:

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector

module RegDiff.Diff.Fixpoint.Base
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open import RegDiff.Generic.Fixpoint ks keqs
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ)
  open import RegDiff.Generic.Eq ks keqs
  import RegDiff.Diff.Multirec.Base ks keqs
    as MREC

  module Internal (T : σπ 1) where
    open MREC.Internal (T ∷ []) public
\end{code}
