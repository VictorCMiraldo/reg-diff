\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.PartialFuncs.Base
open import RegDiff.Generic.Parms

module RegDiff.Diff.Multirec.Apply
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  import RegDiff.Generic.Multirec ks as MREC
  import RegDiff.Generic.Eq ks keqs as EQ
  open import RegDiff.Diff.Multirec.Base ks keqs
    renaming (module Internal to MRECInternal)
\end{code}

\begin{code}
  module Internal {fam# : ℕ}(fam : MREC.Fam fam#) where

    open MRECInternal fam
    open import RegDiff.Diff.Universe ks keqs (MREC.Fix fam) EQ._≟_
    open import RegDiff.Diff.Trivial.Apply ks keqs (MREC.Fix fam) EQ._≟_
    open import RegDiff.Diff.Regular.Apply ks keqs (MREC.Fix fam) EQ._≟_
      public
\end{code}
\begin{code}
    ⟨⟩ₚ : {k : Famᵢ} → ⟦ T k ⟧ ⇀ ⟦ I k ∷ [] ⟧ₚ
    ⟨⟩ₚ  k = just (⟨ k ⟩ , unit) 

    ⟨⟩ₚᵒ : {k : Famᵢ} → ⟦ I k ∷ [] ⟧ₚ ⇀ ⟦ T k ⟧
    ⟨⟩ₚᵒ (⟨ k ⟩ , unit) = just k

    ⟨⟩ₐ  : {k : Famᵢ} → ⟦ T k ⟧ ⇀ ⟦ (I k ∷ []) ∷ [] ⟧
    ⟨⟩ₐ k = just (i1 (⟨ k ⟩ , unit))

    ⟨⟩ₐᵒ : {k : Famᵢ} → ⟦ (I k ∷ []) ∷ [] ⟧ ⇀ ⟦ T k ⟧
    ⟨⟩ₐᵒ (i2 ())
    ⟨⟩ₐᵒ (i1 (⟨ k ⟩ , unit)) = just k

    α-app : {a b : Atom}{P : UUSet}
          → (doP : HasApp P)
          → P (α a) (α b)
          → ⟦ a ⟧ₐ ⇀ ⟦ b ⟧ₐ
    α-app {a} {b} doP wit = (return ∘ from-α {b}) 
                          ∙ doP wit 
                          ∙ (return ∘ to-α {a}) 

    {-# TERMINATING #-}
    Patchμ-app₀ : HasApp Patchμ
    Patchμ-app₀ (skel p)  = Patch-app (α-app Patchμ-app₀) p
    Patchμ-app₀ (ins i x) = to-inj ∙ Al-app (α-app Patchμ-app₀) x ∙ ⟨⟩ₚ
    Patchμ-app₀ (del i x) = ⟨⟩ₚᵒ ∙ Al-app (α-app Patchμ-app₀) x ∙ from-inj
    Patchμ-app₀ (fix p)   = ⟨⟩ₐ ∙ Patchμ-app₀ p ∙ ⟨⟩ₐᵒ
    Patchμ-app₀ (set xy)  = Trivialₛ-apply xy
\end{code}

\begin{code}
    Patchμ-app : {k k' : Famᵢ} → Patchμ (T k) (T k') 
               → Fix fam k ↦ Fix fam k'
    Patchμ-app p = (⟨_⟩ ♭) ∙ Patchμ-app₀ p ∙ (unmu ♭)         
\end{code}

\begin{code}
    Patchμ-app-app₀-trₗ
      : {k k' : Famᵢ}(x : Fix fam k)(y : ⟦ T k' ⟧)
      → {p : Patchμ (T k) (T k')}
      → Patchμ-app₀ p (unmu x) ≡ just y
      → Patchμ-app {k} {k'} p x ≡ just ⟨ y ⟩
    Patchμ-app-app₀-trₗ ⟨ x ⟩ y hip 
      rewrite hip = refl

    Patchμ-app-app₀-trᵣ
      : {k k' : Famᵢ}(x : ⟦ T k ⟧)(y : Fix fam k')
      → {p : Patchμ (T k) (T k')}
      → Patchμ-app₀ p x ≡ just (unmu y)
      → Patchμ-app {k} {k'} p ⟨ x ⟩ ≡ just y
    Patchμ-app-app₀-trᵣ x ⟨ y ⟩ hip 
      rewrite hip = refl
\end{code}
