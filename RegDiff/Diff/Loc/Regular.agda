open import Prelude
open import Prelude.Vector

{-
  Here we exploit the connection between patches
  and lists of locations!
-}

module RegDiff.Diff.Loc.Regular
      {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Generic.Subtype.Base v
  open import RegDiff.Diff.Regular v eqs

  Change : Set → U → Set
  Change A ty = Σ U (λ k → Dir ty k × ⟦ k ⊗ k ⟧ A)

  L : Set → U → Set
  L A ty = List (Change A ty)

  walk : {A : Set}{ty tv : U}
       → ({k : U} → Dir ty k → Dir tv k)
       → L A ty → L A tv
  walk f = map (id ×' (f ×' id)) 

  go : {A : Set}{ty : U}(d : D ty A)
     → L A ty
  go D1 = []
  go (DA x y) = [] -- (I , here , (x , y)) ∷ []
  go (DK k x y) = ((K k) , (here , (x , y))) ∷ []
  go (D⊗ d e) 
    = let l0 = go d
          l1 = go e
       in walk fst l0 ++ walk snd l1
  go (Di1 d) = walk left (go d)
  go (Di2 d) = walk right (go d)
  go {ty = ty ⊕ tv} (Ds1 x y) 
    = ((ty ⊕ tv) , (here , (i1 x , i2 y))) ∷ []
  go {ty = ty ⊕ tv} (Ds2 x y) 
    = ((ty ⊕ tv) , (here , (i2 x , i1 y))) ∷ []
