open import Prelude
open import Prelude.Vector

module RegDiff.Generic.Multirec {ks# : ℕ}(ks : Vec Set ks#) 
    where

  open import RegDiff.Generic.Regular ks 
    renaming (U to Uₙ)
    public
    
  Fam : ℕ → Set
  Fam n = Vec (Uₙ n) n

  data Fix {n : ℕ}(F : Fam n) : Fin n → Set where
    ⟨_⟩ : ∀{k} → ⟦ lookup k F ⟧ (Fix F) → Fix F k

  ⟨⟩-inj : {n : ℕ}{F : Fam n}{k : Fin n}
           {x y : ⟦ lookup k F ⟧ (Fix F)}
         → _≡_ {A = Fix F k} ⟨ x ⟩ ⟨ y ⟩ → x ≡ y
  ⟨⟩-inj refl = refl

  unmu : {n : ℕ}{F : Fam n}{k : Fin n}
       → Fix F k → ⟦ lookup k F ⟧ (Fix F)
  unmu ⟨ x ⟩ = x

  {-# TERMINATING #-}
  Fam-size : {n : ℕ}{F : Fam n}
           → {k : Fin n} → Fix F k → ℕ
  Fam-size {n} {F} {k} ⟨ x ⟩ = size1 Fam-size (lookup k F) x
