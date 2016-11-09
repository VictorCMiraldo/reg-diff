open import Prelude
open import Prelude.Vector

module RegDiff.Generic.Multirec {parms# : ℕ}(parms : Vec Set parms#) 
    where

  open import RegDiff.Generic.Regular parms public
    
  Fam : ℕ → Set
  Fam n = Vec (U n) n

  data Fix {n : ℕ}(F : Fam n) : Fin n → Set where
    ⟨_⟩ : ∀{k} → ⟦ lookup k F ⟧ (Fix F) → Fix F k
