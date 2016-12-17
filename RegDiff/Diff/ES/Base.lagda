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

  module Internal {fam# : ℕ}(fam : Fam fam#) where

    open import RegDiff.Diff.Regular.Base ks keqs (Fix fam) _≟_
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

    cost : {txs tys : List Atom}
         → ES txs tys → ℕ
    cost end = 0
    cost (ins ck es) = 1 + cost es
    cost (del ck es) = 1 + cost es
    cost (cpy ck es) = cost es

    infixl 20 _⊔es_
    _⊔es_ : {txs tys : List Atom}
         → ES txs tys → ES txs tys → ES txs tys
    c ⊔es d with cost c ≤?-ℕ cost d 
    ...| yes _ = c
    ...| no  _ = d
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

    
      doDelIns : {tx ty : Atom}{txs tys : List Atom}
               → ⟦ tx ⟧ₐ → ⟦ ty ⟧ₐ → ListI ⟦_⟧ₐ txs → ListI ⟦_⟧ₐ tys
               → ES (tx ∷ txs) (ty ∷ tys)
      doDelIns x y txs tys 
        = doDel x txs (y ∷ tys) ⊔es doIns y (x ∷ txs) tys

      doMod' : {tx : Famᵢ}{txs tys : List Atom}
            → ⟦ I tx ⟧ₐ → ⟦ I tx ⟧ₐ → ListI ⟦_⟧ₐ txs → ListI ⟦_⟧ₐ tys
            → ES (I tx ∷ txs) (I tx ∷ tys)
      doMod' ⟨ x ⟩ ⟨ y ⟩ txs tys with sop x | sop y
      doMod' ⟨ _ ⟩ ⟨ _ ⟩ txs tys
        | strip cx dx | strip cy dy
        with cx ≟-Fin cy
      ...| no _ = doDelIns ⟨ inject cx dx ⟩ ⟨ inject cy dy ⟩  txs tys
      doMod' ⟨ _ ⟩ ⟨ _ ⟩ txs tys
         | strip cx dx | strip _ dy 
         | yes refl 
         =    cpy cx (diff (append dx txs) (append dy tys)) 
         ⊔es  doDelIns ⟨ inject cx dx ⟩ ⟨ inject cx dy ⟩  txs tys

      doMod : {tx ty : Atom}{txs tys : List Atom}
            → ⟦ tx ⟧ₐ → ⟦ ty ⟧ₐ → ListI ⟦_⟧ₐ txs → ListI ⟦_⟧ₐ tys
            → ES (tx ∷ txs) (ty ∷ tys)
      doMod {I tx} {I ty} x y txs tys 
        with tx ≟-Fin ty
      ...| no  _     = doDelIns x y txs tys
      doMod {I tx} {I _} x y txs tys 
         | yes refl  with x ≟ y
      ...| no  _ = doDelIns x y txs tys 
      ...| yes _ = doMod' x y txs tys  
      doMod {K tx} {K ty} x y txs tys 
        with tx ≟-Fin ty
      ...| no  _     = doDelIns x y txs tys
      doMod {K tx} {K _} x y txs tys 
         | yes refl  with Eq.cmp (lookupᵢ tx keqs) x y
      ...| no  _ = doDelIns x y txs tys
      ...| yes _ =    cpy x (diff txs tys) 
                 ⊔es  doDelIns x y txs tys      
      doMod {_} {_} x y txs tys = doDelIns x y txs tys

      {-# TERMINATING #-}
      diff : {txs tys : List Atom}
           → ListI ⟦_⟧ₐ txs
           → ListI ⟦_⟧ₐ tys
           → ES txs tys
      diff []        []        = end
      diff []        (y ∷ ys)  = doIns y [] ys
      diff (x ∷ xs)  []        = doDel x xs []
      diff (x ∷ xs)  (y ∷ ys)  = doMod x y xs ys
\end{code}
