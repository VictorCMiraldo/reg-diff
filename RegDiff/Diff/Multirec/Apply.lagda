\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import RegDiff.Generic.Parms

module RegDiff.Diff.Multirec.Apply
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  open import RegDiff.Generic.Multirec ks
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Multirec.Base ks keqs
    renaming (module Internal to MRECInternal)
\end{code}

\begin{code}
  module Internal {fam# : ℕ}(fam : Fam fam#) where

    open MRECInternal fam
    open import RegDiff.Diff.Regular.Apply ks keqs (Fix fam) WB-FAM
      public
\end{code}

\begin{code}
    Cμ-applyₗ : {ty tv : U}{P : UUSet}
              → (doP : Appliable P)
              → Cμ P ty tv → ⟦ ty ⟧ (Fix fam) → Maybe (⟦ tv ⟧ (Fix fam))
    Cμ-applyₗ doP (Cins x) el 
      = C-applyₗ doP x ⟨ el ⟩
    Cμ-applyₗ doP (Cdel x) el 
      = unmu <$> C-applyᵣ (Sym-Appliable doP) x el
    Cμ-applyₗ doP (Cmod x) el 
      = C-applyₗ (SymCSym-Appliable doP) x el

    Cμ-applyᵣ : {ty tv : U}{P : UUSet}
              → (doP : Appliable P)
              → Cμ P ty tv → ⟦ tv ⟧ (Fix fam) → Maybe (⟦ ty ⟧ (Fix fam))
    Cμ-applyᵣ doP (Cins x) el 
      = unmu <$> C-applyᵣ doP x el 
    Cμ-applyᵣ doP (Cdel x) el 
      = C-applyₗ (Sym-Appliable doP) x ⟨ el ⟩
    Cμ-applyᵣ doP (Cmod x) el 
      = C-applyᵣ (SymCSym-Appliable doP) x el

    Cμ-Appliable : {P : UUSet} → Appliable P → Appliable (Cμ P)
    Cμ-Appliable doP = apply (Cμ-applyₗ doP) (Cμ-applyᵣ doP)

    mutual
      Rec-applyₗ : {ty tv : U} → Rec ty tv → ⟦ ty ⟧ (Fix fam) → Maybe (⟦ tv ⟧ (Fix fam))
      Rec-applyₗ           (fix x) el = Patchμ-applyₗ x el
      Rec-applyₗ {ty} {tv} (set x) el = goₗ Δ-apply {ty} {tv} x el

      Rec-applyᵣ : {ty tv : U} → Rec ty tv → ⟦ tv ⟧ (Fix fam) → Maybe (⟦ ty ⟧ (Fix fam))
      Rec-applyᵣ           (fix x) el = Patchμ-applyᵣ x el
      Rec-applyᵣ {ty} {tv} (set x) el = goᵣ Δ-apply {ty} {tv} x el

      AlRec-Appliable : Appliable (Al Rec)
      AlRec-Appliable = Al-Appliable (apply Rec-applyₗ Rec-applyᵣ)

      SVar+Cμ-applyₗ : {k : U} → (SVar +ᵤ Cμ (Al Rec)) k k
                     → ⟦ k ⟧ (Fix fam) → Maybe (⟦ k ⟧ (Fix fam))
      SVar+Cμ-applyₗ (i1 (Svar x)) v = Patchμ-applyₗ x v
      SVar+Cμ-applyₗ (i2 y) v        = Cμ-applyₗ AlRec-Appliable y v

      SVar+Cμ-applyᵣ : {k : U} → (SVar +ᵤ Cμ (Al Rec)) k k
                     → ⟦ k ⟧ (Fix fam) → Maybe (⟦ k ⟧ (Fix fam))
      SVar+Cμ-applyᵣ (i1 (Svar x)) v = Patchμ-applyᵣ x v
      SVar+Cμ-applyᵣ (i2 y) v        = Cμ-applyᵣ AlRec-Appliable y v

      {-# TERMINATING #-}
      Patchμ-applyₗ : {k : Famᵢ} → Patchμ (T k) → Fix fam k → Maybe (Fix fam k)
      Patchμ-applyₗ p ⟨ x ⟩ = ⟨_⟩ <$> S-apply SVar+Cμ-applyₗ p x

      {-# TERMINATING #-}
      Patchμ-applyᵣ : {k : Famᵢ} → Patchμ (T k) → Fix fam k → Maybe (Fix fam k)
      Patchμ-applyᵣ p ⟨ x ⟩ = ⟨_⟩ <$> S-apply SVar+Cμ-applyᵣ p x
\end{code}
