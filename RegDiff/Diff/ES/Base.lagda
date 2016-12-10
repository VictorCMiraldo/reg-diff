  Here we implement Marco/Lempsink approach
  to mutually recursive families diffs.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.ListI
open import RegDiff.Generic.Parms

module RegDiff.Diff.ES.Base
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs

  _+ᵤ_ : {n : ℕ} → (σπ n → σπ n → Set) → (σπ n → σπ n → Set) → (σπ n → σπ n → Set)
  (P +ᵤ Q) ty tv = (P ty tv) ⊎ (Q ty tv)

  WB-FAM : {n : ℕ}{fam : Fam n} → WBParms (Fix fam)
  WB-FAM = wb-parms Fam-size _≟_

  module Internal {fam# : ℕ}(fam : Fam fam#) where

    open import RegDiff.Diff.Regular.Base ks keqs (Fix fam) WB-FAM
      public

    Famᵢ : Set
    Famᵢ = Fin fam#

    T : Famᵢ → σπ fam#
    T k = lookup k fam

    constr : Atom → Set
    constr (I k) = Constr (T k)
    constr (K k) = lookup k ks

    tyOf : (a : Atom) → constr a → π fam#
    tyOf (I x) c = typeOf (T x) c
    tyOf (K x) c = []
\end{code}
\begin{code}
    data ES : List Atom → List Atom → Set where
      end  : ES [] []
      ins  : {txs tys : List Atom}
           → {k : Atom}(ck : constr k)
           → ES txs (tyOf k ck ++ tys)
           → ES txs (k ∷ tys)
      del  : {txs tys : List Atom}
           → {k : Atom}(ck : constr k)
           → ES (tyOf k ck ++ txs) tys
           → ES (k ∷ txs) tys
      cpy  : {txs tys : List Atom}
           → {k : Atom}(ck : constr k)
           → ES (tyOf k ck ++ txs) (tyOf k ck ++ tys)
           → ES (k ∷ txs) (k ∷ tys)
\end{code}
\begin{code}
    append : {x : Π}{txs : List Atom}
           → ⟦ x ⟧ₚ → ListI ⟦_⟧ₐ txs → ListI ⟦_⟧ₐ (x ++ txs)
    append {[]} _ txs = txs
    append {x ∷ xs} (x' , x's) txs = x' ∷ append x's txs
\end{code}
\begin{code}
    mutual
      doIns : {ty : Atom}{txs tys : List Atom} 
            → ⟦ ty ⟧ₐ → ListI ⟦_⟧ₐ txs → ListI ⟦_⟧ₐ tys
            → ES txs (ty ∷ tys)
      doIns {K ty} y     txs tys = ins y (diff txs tys)
      doIns {I ty} ⟨ y ⟩ txs tys with sop y
      doIns {I ty} ⟨ _ ⟩ txs tys | strip cy dy
        = ins cy (diff txs (append dy tys))

      doDel : {tx : Atom}{txs tys : List Atom} 
            → ⟦ tx ⟧ₐ → ListI ⟦_⟧ₐ txs → ListI ⟦_⟧ₐ tys
            → ES (tx ∷ txs) tys
      doDel {K ty} x     txs tys = del x (diff txs tys)
      doDel {I ty} ⟨ x ⟩ txs tys with sop x
      doDel {I ty} ⟨ _ ⟩ txs tys | strip cx dx
        = del cx (diff (append dx txs) tys)

      {-# TERMINATING #-}
      diff : {txs tys : List Atom}
           → ListI ⟦_⟧ₐ txs
           → ListI ⟦_⟧ₐ tys
           → ES txs tys
      diff []        []        = end
      diff []        (y ∷ ys)  = doIns y [] ys
      diff (x ∷ xs)  []        = doDel x xs []
      diff (x₂ ∷ xs₂) (x₃ ∷ ys) = {!!}
\end{code}
