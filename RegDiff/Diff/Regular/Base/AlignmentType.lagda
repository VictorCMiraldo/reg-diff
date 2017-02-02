\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Base.AlignmentType
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open Monad {{...}}

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_
\end{code}


%<*Al-def>
\begin{code}
  data Al (P : Atom → Atom → Set) : Π → Π → Set where
    A0   :                                          Al P [] []
    Ap1  : ∀{a ty tv}     → ⟦ a ⟧ₐ  → Al P ty tv →  Al P (a ∷ ty) tv
    Ap1ᵒ : ∀{a ty tv}     → ⟦ a ⟧ₐ  → Al P ty tv →  Al P ty       (a ∷ tv)
    AX   : ∀{a a' ty tv}  → P a a'  → Al P ty tv →  Al P (a ∷ ty) (a' ∷ tv)
\end{code}
%</Al-def>
