open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import RegDiff.Generic.Parms

module RegDiff.Generic.Konstants where

  open import Data.String

  eq-String : Eq String
  eq-String = eq decide
    where
      open import Agda.Builtin.TrustMe

      postulate magic : ⊥

      decide : (x y : String) -> Dec (x ≡ y)
      decide x y with primStringEquality x y
      ...| true = yes primTrustMe
      ...| false = no (λ x → magic)

{-
  Here we provide some toy constants
-}

  konstants : Vec Set _
  konstants = ℕ ∷ Bool ∷ String ∷ []

  keqs : VecI Eq konstants
  keqs = eq-ℕ 
       ∷ eq-Bool 
       ∷ eq-String
       ∷ []
  
  
  kℕ : Fin 3
  kℕ = fz

  kBool : Fin 3
  kBool = fs fz

  kString : Fin 3
  kString = fs (fs fz)
