\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Diff.DomRan
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)(A : Set)
       {{eqA : Eq A}}(sized : A → ℕ)
    where

  open Monad {{...}}

  open import RegDiff.Generic.Base v
  open import RegDiff.Diff.Spine v eqs A sized
\end{code}

\begin{code}
  record HasDomRan (Q : UUSet) : Set₁ where
    constructor hasdomran 
    field
      qdom : ∀{ty tv} → Q ty tv → ⟦ ty ⟧ A → Set
      qran : ∀{ty tv} → Q ty tv → ⟦ tv ⟧ A → Set

  open HasDomRan
\end{code}

\begin{code}
  Δ-domran : HasDomRan Δ
  Δ-domran 
    = hasdomran (λ { (x , _) → (x ≡_) }) 
                (λ { (_ , y) → (y ≡_) })

  mutual
    ran : {ty tv : U}{P : UUSet} → (doP : HasDomRan P)
        → S P ty tv → ⟦ tv ⟧ A → Set
    ran r (SX x)     = qran r x
    ran r (Ssym s)   = dom r s
    ran r Scp        = const Unit
    ran r (S⊗ s o)   = ran r s >< ran r o
    ran r (Sfst x s) = ran r s >< (x ≡_)
    ran r (Ssnd x s) = (x ≡_)  >< ran r s
    ran r (Si1 s)    = ran r s -|- const ⊥
    ran r (Si2 s)    = const ⊥ -|- ran r s

    dom : {ty tv : U}{P : UUSet} → (doP : HasDomRan P)
        → S P ty tv → ⟦ ty ⟧ A → Set
    dom d (SX x)     = qdom d x
    dom d (Ssym s)   = ran d s
    dom d Scp        = const Unit
    dom d (S⊗ s o)   = dom d s >< dom d o
    dom d (Sfst x s) = dom d s
    dom d (Ssnd x s) = dom d s
    dom d (Si1 s)    = dom d s
    dom d (Si2 s)    = dom d s

  dom1 : {ty tv : U} → S Δ ty tv → ⟦ ty ⟧ A → Set
  dom1 = dom Δ-domran

  ran1 : {ty tv : U} → S Δ ty tv → ⟦ tv ⟧ A → Set
  ran1 = ran Δ-domran
\end{code}

  Now the tricky lemma!
  If cost R < cost S then S ⊆ R.

begin{code}
  module CostLemma (P : UUSet)(domran : HasDomRan P)
                   (costP : ∀{ty tv} → P ty tv → ℕ)
      where

    cost : {ty tv : U} → S P ty tv → ℕ
    cost = S-cost costP

    dom' : {ty tv : U} → S P ty tv → ⟦ ty ⟧ A → Set
    dom' = dom domran

    ran' : {ty tv : U} → S P ty tv → ⟦ tv ⟧ A → Set
    ran' = ran domran

    _⇒_ : {A : Set}(X Y : A → Set) → Set
    X ⇒ Y = ∀ a → X a → Y a

    mutual
      cost-dom : {ty tv : U}(r s : S P ty tv)
               → cost s ≤ cost r
               → dom' s ⇒ dom' r
      cost-dom (SX x) s hip a x₁ = {!!}
      cost-dom (Ssym r) s hip a x = {!!}
      cost-dom Scp s hip a x = {!!}
      cost-dom (S⊗ r o) s hip a x = {!!}
      cost-dom (Sfst x r) s hip a x₁ = {!!}
      cost-dom (Ssnd x r) s hip a x₁ = {!!}
      cost-dom (Si1 r) s hip a x = {!!}
      cost-dom (Si2 r) s hip a x = {!!}
end{code}
