open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import RegDiff.Generic.Parms

module RegDiff.Generic.Konstants where

{-
  Here we provide some toy constants
-}

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



