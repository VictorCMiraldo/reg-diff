open import Prelude
open import Prelude.Vector

{-
  Here we exploit the connection between patches
  and lists of locations!
-}

module RegDiff.Diff.Loc.Base
      {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Diff.Base v eqs
  open import RegDiff.Generic.Subtype.Base v

  L : Set → U → Set
  L A ty = List (Σ U (λ k → Dir ty k × ⟦ k ⊗ k ⟧ A))

  Lμ : U → Set
  Lμ ty = List (Σ U (λ k → Dirμ ty k × ⟦ k ⊗ k ⟧ (μ ty)))

  walk : {A : Set}{ty tv : U}
       → ({k : U} → Dir ty k → Dir tv k)
       → L A ty → L A tv
  walk f = map (id ×' (f ×' id)) 

  go : {A : Set}{ty : U}(d : D ⊥' ty A)
     → L A ty
  go (DB ())
  go D1 = []
  go (DA x y) = (I , here , (x , y)) ∷ []
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
  
  goμ : {ty : U}(d : Dμ ⊥' ty)
      → Lμ ty
  goμ Dμ-nil = []
  goμ (Dμ-B () d)
  goμ (Dμ-ins x d) 
    = let l = goμ d
       in {!!}
  goμ (Dμ-del x d) = {!!}
  goμ (Dμ-mod x d) = {!!}
