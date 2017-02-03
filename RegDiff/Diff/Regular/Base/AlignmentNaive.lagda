\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Base.AlignmentNaive
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

%<*align-star-def>
\begin{code}
  align* : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ → List (Al Trivialₐ ty tv)
  align* {[]}     {[]}     m n = return A0
  align* {[]}     {v ∷ tv} m (n , nn) 
    = Ains n <$> align* m nn
  align* {y ∷ ty} {[]}     (m , mm) n 
    = Adel m <$> align* mm n
  align* {y ∷ ty} {v ∷ tv} (m , mm) (n , nn)
    =  AX (m , n)   <$> align* mm nn
    ++ Adel  m       <$> align* mm (n , nn)
    ++ Ains n       <$> align* (m , mm) nn      
\end{code}
%</align-star-def>
