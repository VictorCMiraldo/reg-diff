\begin{code}
open import Prelude hiding (⊥)
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
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Multirec.Base ks keqs
    renaming (module Internal to MRECInternal)

  module Internal {fam# : ℕ}(fam : Fam fam#) where

    open MRECInternal fam
    open import RegDiff.Diff.Regular.Domain ks keqs (Fix fam) _≟_

    ⟨⟩ : {k : Famᵢ} → (Fix fam k ⟵ ⟦ T k ⟧)
    ⟨⟩ = fun ⟨_⟩

    ⟨⟩ₚ : {k : Famᵢ} → (⟦ I k ∷ [] ⟧ₚ ⟵ ⟦ T k ⟧)
    ⟨⟩ₚ = π₁ ᵒ ∙ ⟨⟩

    ⟨⟩ₐ : {k : Famᵢ} → (⟦ (I k ∷ []) ∷ [] ⟧ ⟵ ⟦ T k ⟧)
    ⟨⟩ₐ = ι₁ ∙ ⟨⟩ₚ

    {-# TERMINATING #-}
    Patchμ-rel : HasRel Patchμ
    Patchμ-rel (skel p)  = S-rel (C-rel (Al-rel (α-rel Patchμ-rel))) p
    Patchμ-rel (ins i x) = inj ∙ Al-rel (α-rel Patchμ-rel) x ∙ ⟨⟩ₚ
    Patchμ-rel (del i x) = ⟨⟩ₚ ᵒ ∙ Al-rel (α-rel Patchμ-rel) x ∙ inj ᵒ
    Patchμ-rel (fix p)   = ⟨⟩ₐ ∙ Patchμ-rel p ∙ ⟨⟩ₐ ᵒ
    Patchμ-rel (set xy)  = Δₛ-rel xy
\end{code}
    
