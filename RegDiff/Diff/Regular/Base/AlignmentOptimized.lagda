\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Base.AlignmentOptimized
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open Monad {{...}}

  open import RegDiff.Diff.Universe ks keqs A _≟-A_
  open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_

  -- Our alignment datatype is just reexported
  open import RegDiff.Diff.Regular.Base.AlignmentType ks keqs A _≟-A_
    public
\end{code}

%</Al-cost-def>
\begin{code}
  is-ap1 : {ty tv : Π} → Al Trivialₐ ty tv → Bool
  is-ap1 (Ap1 _ _) = true
  is-ap1 _         = false

  is-ap1ᵒ : {ty tv : Π} → Al Trivialₐ ty tv → Bool
  is-ap1ᵒ (Ap1ᵒ _ _) = true
  is-ap1ᵒ _          = false 
\end{code}
%<*align-star-def>
\begin{code}
  align* : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ → List (Al Trivialₐ ty tv)
  align* {[]}     {[]}     m n = return A0
  align* {[]}     {v ∷ tv} m (n , nn) 
    = Ap1ᵒ n <$> align* m nn
  align* {y ∷ ty} {[]}     (m , mm) n 
    = Ap1 m <$> align* mm n
  align* {y ∷ ty} {v ∷ tv} (m , mm) (n , nn)
    =  align? m n (align* mm nn)
    ++ Ap1  m       <$> filter (not ∘ is-ap1ᵒ)  (align* mm (n , nn))
    ++ Ap1ᵒ n       <$> filter (not ∘ is-ap1)   (align* (m , mm) nn)
    where
      align? : {ty tv : Atom}{tys tvs : Π} 
             → ⟦ ty ⟧ₐ → ⟦ tv ⟧ₐ → List (Al Trivialₐ tys tvs)
             → List (Al Trivialₐ (ty ∷ tys) (tv ∷ tvs))
      align? {I _} {I _} x y xys = AX (x , y) <$> xys
      align? {K _} {K _} x y xys = AX (x , y) <$> xys
      align? {I _} {K _} x y xys = []
      align? {K _} {I _} x y xys = []
      
\end{code}
%</align-star-def>
