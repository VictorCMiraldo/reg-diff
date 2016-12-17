\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.ListI
open import RegDiff.Generic.Parms

module RegDiff.Diff.Multirec.Diff3
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  import RegDiff.Diff.Multirec.Base ks keqs
    as MREC

  module Internal {fam# : ℕ}(fam : Fam fam#) where
    open MREC.Internal fam public    
\end{code}

\begin{code}
    data _⋒_ : {ty tv : U}(p q : Patchμ ty tv) → Set where
       ⋒-skel : {ty : U}{p q : Patch (UU→AA Patchμ) ty}
              → (skel p) ⋒ (skel q)
      
\end{code}
