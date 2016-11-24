\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.RelCalc.Base
open import RegDiff.Generic.Parms

module RegDiff.Diff.Multirec.Domain
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  open import RegDiff.Generic.Multirec ks
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Multirec.Base ks keqs
    renaming (module Internal to MRECInternal)

  module Internal {fam# : ℕ}(fam : Fam fam#) where

    open MRECInternal fam
    open import RegDiff.Diff.Regular.Domain ks keqs (Fix fam) WB-FAM

    ⟨⟩ : {k : Famᵢ} → (Fix fam k ⟵ ⟦ T k ⟧ (Fix fam))
    ⟨⟩ = fun ⟨_⟩

    Cμ-rel : {P : UUSet} → HasRel P → HasRel (Cμ P)
    Cμ-rel doP (Cins x) = C-rel (Al-rel doP) x ∙ ⟨⟩
    Cμ-rel doP (Cdel x) = ⟨⟩ ᵒ ∙ C-rel (Al-rel doP) x
    Cμ-rel doP (Cmod x) = S-rel (C-rel (Al-rel doP)) x

    {-# TERMINATING #-}
    Patchμ-rel : HasRel Patchμ
    Patchμ-rel (fix p) = ⟨⟩ ∙ Patchμ-rel p ∙ ⟨⟩ ᵒ
    Patchμ-rel (chng s) = Cμ-rel Patchμ-rel s
    Patchμ-rel (set {ty} s) = Δ-rel {ty} {ty} s
    
\end{code}
