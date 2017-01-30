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

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Multirec.Base ks keqs
    renaming (module Internal to MRECInternal)
\end{code}

\begin{code}
  module Internal {fam# : ℕ}(fam : Fam fam#) where

    open MRECInternal fam
    open import RegDiff.Diff.Regular.Apply ks keqs (Fix fam) _≟_
      public
\end{code}
\begin{code}
    ⟨⟩ₚ : {k : Famᵢ} → ⟦ T k ⟧ ↦ ⟦ I k ∷ [] ⟧ₚ
    ⟨⟩ₚ  k = just (⟨ k ⟩ , unit) 

    ⟨⟩ₚᵒ : {k : Famᵢ} → ⟦ I k ∷ [] ⟧ₚ ↦ ⟦ T k ⟧
    ⟨⟩ₚᵒ (⟨ k ⟩ , unit) = just k

    ⟨⟩ₐ  : {k : Famᵢ} → ⟦ T k ⟧ ↦ ⟦ (I k ∷ []) ∷ [] ⟧
    ⟨⟩ₐ k = just (i1 (⟨ k ⟩ , unit))

    ⟨⟩ₐᵒ : {k : Famᵢ} → ⟦ (I k ∷ []) ∷ [] ⟧ ↦ ⟦ T k ⟧
    ⟨⟩ₐᵒ (i2 ())
    ⟨⟩ₐᵒ (i1 (⟨ k ⟩ , unit)) = just k

    α-app : {a b : Atom}{P : UUSet}
          → (doP : HasApp P)
          → P (α a) (α b)
          → ⟦ a ⟧ₐ ↦ ⟦ b ⟧ₐ
    α-app {a} {b} doP wit = (return ∘ from-α {b}) 
                          ∙ doP wit 
                          ∙ (return ∘ to-α {a}) 

    {-# TERMINATING #-}
    Patchμ-app : HasApp Patchμ
    Patchμ-app (skel p)  = Patch-app (α-app Patchμ-app) p
    Patchμ-app (ins i x) = to-inj ∙ Al-app (α-app Patchμ-app) x ∙ ⟨⟩ₚ
    Patchμ-app (del i x) = ⟨⟩ₚᵒ ∙ Al-app (α-app Patchμ-app) x ∙ from-inj
    Patchμ-app (fix p)   = ⟨⟩ₐ ∙ Patchμ-app p ∙ ⟨⟩ₐᵒ
    Patchμ-app (set xy)  = Trivialₛ-apply xy
\end{code}
