\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.ListI
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Correct
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open Monad {{...}}

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Regular.Base ks keqs A _≟-A_
  open import RegDiff.Diff.Regular.Apply ks keqs A _≟-A_
\end{code}

\begin{code}
  record HasPatch {A : Set}(P : A → Set) : Set₁ where
    field
      T     : A → A → Set
      diff  : {a₁ a₂ : A} → P a₁ → P a₂ → T a₁ a₂
      app   : {a₁ a₂ : A} → T a₁ a₂ → P a₁ → Maybe (P a₂)

  open HasPatch

  HasPatch-sums : HasPatch {Π} ⟦_⟧ₚ → HasPatch ⟦_⟧
  HasPatch-sums p = record 
    { T = λ ty tv → Σ (ty ≡ tv)    (λ _ → S (T p) ty)
                  ⊎ Σ (¬ ty ≡ tv)  (λ _ → ⟦ ty ⟧ × ⟦ tv ⟧)
    ; diff = {!!} 
    ; app = {!!} }
\end{code}
