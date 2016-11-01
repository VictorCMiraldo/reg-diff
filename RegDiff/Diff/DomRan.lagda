\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Relation.Binary

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
