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
    Cμ-rel doP (Cins x) = C-rel doP x ∙ ⟨⟩
    Cμ-rel doP (Cdel x) = ⟨⟩ ᵒ ∙ (C-rel (λ d → doP d ᵒ) x) ᵒ
    Cμ-rel doP (Cmod x) = CSymCSym-rel doP x

    mutual
      Rec-rel : HasRel Rec
      Rec-rel (fix r) = Patchμ-rel r
      Rec-rel (set {ty} {tv} t) = Δ-rel {ty} {tv} t

      SVar+Cμ-rel : HasRel (SVar +ᵤ Cμ (Al Rec))
      SVar+Cμ-rel (i1 (Svar x)) = Patchμ-rel x
      SVar+Cμ-rel (i2 y)        = Cμ-rel (Al-rel Rec-rel) y

      {-# TERMINATING #-}
      Patchμ-rel : {k : Famᵢ} → Patchμ (T k) → EndoRel (Fix fam k)
      Patchμ-rel p = ⟨⟩ ∙ S-rel SVar+Cμ-rel p ∙ ⟨⟩ ᵒ
\end{code}
