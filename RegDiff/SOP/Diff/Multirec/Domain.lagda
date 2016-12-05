\begin{code}
open import Prelude hiding (⊥)
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.RelCalc.Base
open import RegDiff.Generic.Parms

module RegDiff.SOP.Diff.Multirec.Domain
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  open import RegDiff.SOP.Generic.Multirec ks
  open import RegDiff.SOP.Generic.Eq ks keqs
  open import RegDiff.SOP.Diff.Multirec.Base ks keqs
    renaming (module Internal to MRECInternal)

  module Internal {fam# : ℕ}(fam : Fam fam#) where

    open MRECInternal fam
    open import RegDiff.SOP.Diff.Regular.Domain ks keqs (Fix fam) WB-FAM

    abstract
      ⟨⟩ : {k : Famᵢ} → (Fix fam k ⟵ ⟦ T k ⟧ (Fix fam))
      ⟨⟩ = fun ⟨_⟩

      ⟨⟩ₚ : {k : Famᵢ} → (⟦ I k ∷ [] ⟧ₚ (Fix fam) ⟵ ⟦ T k ⟧ (Fix fam))
      ⟨⟩ₚ = π₁ ᵒ ∙ ⟨⟩
  
      ⟨⟩ₐ : {k : Famᵢ} → (⟦ (I k ∷ []) ∷ [] ⟧ (Fix fam) ⟵ ⟦ T k ⟧ (Fix fam))
      ⟨⟩ₐ = ι₁ ∙ ⟨⟩ₚ

      knot : {P : UUSet} → HasRel P → HasRelₐ (UU→AA P)
      knot doP x y z = doP x (i1 (y , unit)) (i1 (z , unit))

      SET : {k : Fin ks#} → ( x y : lookup k ks ) → EndoRel (⟦ (K k ∷ []) ∷ [] ⟧ (Fix fam))
      SET x y = (π₁ ᵒ ∙ (≣ᵣ y) ∙ (≣ᵣ x) ∙ π₁) -|- ⊥

    Cμ-rel : {P : AASet} → HasRelₐ P → HasRel (Cμ P)
    Cμ-rel doP (Cins i x)   = inj   ∙ Al-rel doP x ∙ ⟨⟩ₚ
    Cμ-rel doP (Cdel i x)   = ⟨⟩ₚ ᵒ ∙ Al-rel doP x ∙ inj ᵒ
    Cμ-rel doP (Cmod i j x) = inj   ∙ Al-rel doP x ∙ inj ᵒ
    Cμ-rel doP (Ccpy i ls) = whatever
      where postulate whatever : ∀{a}{A : Set a} → A

    {-# TERMINATING #-}
    Patchμ-rel : HasRel Patchμ
    Patchμ-rel (chng c)  = Cμ-rel (knot Patchμ-rel) c
    Patchμ-rel (fix p)   = ⟨⟩ₐ ∙ Patchμ-rel p ∙ ⟨⟩ₐ ᵒ
    Patchμ-rel (set {k = k} x y) 
      with Eq.cmp (lookupᵢ k keqs) x y
    ...| yes _ = ID
    ...| no  _ = SET {k} x y
    Patchμ-rel cp        = ID
\end{code}
