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
      {-# TERMINATING #-}
      Patchμ-applyₗ  : {ty tv : U} 
                     → Patchμ ty tv → ⟦ ty ⟧ (Fix fam) → Maybe (⟦ tv ⟧ (Fix fam))
      Patchμ-applyₗ (skel s)  x    = S-apply Patchμ-applyₗ s x
      Patchμ-applyₗ (chng c)  x    = Cμ-applyₗ (Al-Appliable Patchμ-Appliable) c x
      Patchμ-applyₗ (fix p) ⟨ x ⟩  = ⟨_⟩ <$> Patchμ-applyₗ p x
      Patchμ-applyₗ {ty} {tv} (set p) x = goₗ Δ-apply {ty = ty} {tv} p x

      {-# TERMINATING #-}
      Patchμ-applyᵣ  : {ty tv : U} 
                     → Patchμ ty tv → ⟦ tv ⟧ (Fix fam) → Maybe (⟦ ty ⟧ (Fix fam))
      Patchμ-applyᵣ (skel s)  x    = S-apply Patchμ-applyᵣ s x
      Patchμ-applyᵣ (chng c)  x    = Cμ-applyᵣ (Al-Appliable Patchμ-Appliable) c x
      Patchμ-applyᵣ (fix p) ⟨ x ⟩  = ⟨_⟩ <$> Patchμ-applyᵣ p x
      Patchμ-applyᵣ {ty} {tv} (set p) x = goᵣ Δ-apply {ty = ty} {tv} p x

      Patchμ-Appliable : Appliable Patchμ
      Patchμ-Appliable = apply Patchμ-applyₗ Patchμ-applyᵣ

    Patchμ-apply-famₗ
      : {k k' : Famᵢ} 
      → Patchμ (T k) (T k') → Fix fam k → Maybe (Fix fam k')
    Patchμ-apply-famₗ p ⟨ x ⟩ = ⟨_⟩ <$> Patchμ-applyₗ p x

    Patchμ-apply-famᵣ
      : {k k' : Famᵢ} 
      → Patchμ (T k) (T k') → Fix fam k' → Maybe (Fix fam k)
    Patchμ-apply-famᵣ p ⟨ x ⟩ = ⟨_⟩ <$> Patchμ-applyᵣ p x
\end{code}
