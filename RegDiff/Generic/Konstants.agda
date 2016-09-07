open import Prelude
open import Prelude.Vector

module RegDiff.Generic.Konstants where

  konstants : Vec Set _
  konstants = ℕ ∷ Bool ∷ []

  keqs : VecI Eq konstants
  keqs = eq-ℕ 
       ∷ eq-Bool 
       ∷ []
  
  
  kℕ : Fin 2
  kℕ = fz

  kBool : Fin 2
  kBool = fs fz
