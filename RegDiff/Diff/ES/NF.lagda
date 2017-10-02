\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.Lemmas
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.ES.NF
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  import RegDiff.Generic.Multirec ks as MREC
  import RegDiff.Generic.Eq ks keqs as EQ
  import RegDiff.Diff.ES.Base as BASE

  module Internal {fam# : ℕ}(fam : MREC.Fam fam#) where

    open import RegDiff.Diff.Universe ks keqs (MREC.Fix fam) EQ._≟_
    open import RegDiff.Diff.Trivial.Base ks keqs (MREC.Fix fam) EQ._≟_
    open BASE.Internal ks keqs fam
      renaming (ES to BaseES)
\end{code}

  An edit script is said to be in 'normal-form'
  iff it consists of insert-delete-copy chunks,
  that is:

    (I*D*C+)*

\begin{code}
    data Phase : Set where
      I D C1 C0 : Phase

    data ES : Phase → List Atom → List Atom → Set where
      skipI : {txs tys : List Atom}
            → ES D txs tys
            → ES I txs tys
      ins  : {txs tys : List Atom}
           → {k : Atom}(ck : constr k)
           → ES I txs (tyOf k ck ++ tys)
           → ES I txs (k ∷ tys)
--      insTree : {txs tys : List Atom}
--              → {k : Atom}(el : ⟦ k ⟧ₐ)
--              → ES I txs tys
--              → ES I txs (k ∷ tys) 

      skipD : {txs tys : List Atom}
            → ES C1 txs tys
            → ES D txs tys
      del  : {txs tys : List Atom}
           → {k : Atom}(ck : constr k)
           → ES D (tyOf k ck ++ txs) tys
           → ES D (k ∷ txs) tys

      nil   : ES C1 [] []
      cpy1  : {txs tys : List Atom}
            → {k : Atom}(ck : constr k)
            → ES C0 (tyOf k ck ++ txs) (tyOf k ck ++ tys)
            → ES C1 (k ∷ txs) (k ∷ tys)

      skipC : {txs tys : List Atom}
            → ES I  txs tys
            → ES C0 txs tys
      cpy   : {txs tys : List Atom}
            → {k : Atom}(ck : constr k)
            → ES C0 (tyOf k ck ++ txs) (tyOf k ck ++ tys)
            → ES C0 (k ∷ txs) (k ∷ tys)
\end{code}

\begin{code}
    nest-I : {txs tys tzs : List Atom}
           → ({tys : List Atom} → ES D txs tys → ES D tzs tys)
           → ES I txs tys → ES I tzs tys
    nest-I f (ins ck es)     = ins ck (nest-I f es)
 --   nest-I f (insTree tr es) = insTree tr (nest-I f es) 
    nest-I f (skipI rest)    = skipI (f rest)

    nest-D : {txs tys tzs : List Atom}
           → ({txs : List Atom} → ES C1 txs tys → ES C1 txs tzs)
           → ES D txs tys → ES D txs tzs
    nest-D f (del ck es) = del ck (nest-D f es)
    nest-D f (skipD rest) = skipD (f rest)


    mutual
      normalize-C0 : {txs tys : List Atom}
                   → BaseES txs tys → ES C0 txs tys
      normalize-C0 end         = skipC (skipI (skipD nil))
      normalize-C0 (ins ck es) = skipC (normalize (ins ck es))
      normalize-C0 (del ck es) = skipC (normalize (del ck es))
      normalize-C0 (cpy ck es) = cpy ck (normalize-C0 es)
 
      normalize : {txs tys : List Atom}
                → BaseES txs tys → ES I txs tys
      normalize end         = skipI (skipD nil)
      normalize (ins ck es) = ins ck (normalize es)
      normalize (del ck es) = nest-I (del ck) (normalize es)
      normalize (cpy ck es) = skipI (skipD (cpy1 ck (normalize-C0 es)))
\end{code}
