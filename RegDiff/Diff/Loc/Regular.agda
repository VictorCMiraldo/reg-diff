open import Prelude
open import Prelude.Vector
open import Prelude.Monad

{-
  Here we exploit the connection between patches
  and lists of locations!
-}

module RegDiff.Diff.Loc.Regular
      {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open Monad {{...}}

  open import RegDiff.Generic.Subtype.Base v
  open import RegDiff.Diff.Regular v eqs

  Change : Set → U → Set
  Change A ty = Σ U (λ k → Dir ty k × ⟦ k ⊗ k ⟧ A)

  L : Set → U → Set
  L A ty = List (Change A ty)

  translate
    : {A : Set}{ty tv : U}
    → ({k : U} → Dir ty k → Dir tv k)
    → Change A ty → Change A tv
  translate f = (id ×' (f ×' id))

  walk : {A : Set}{ty tv : U}
       → ({k : U} → Dir ty k → Dir tv k)
       → L A ty → L A tv
  walk f = map (translate f) 

{-
  Translating a regular diff into a list of
  location and changes is trivial
-}

  go : {A : Set}{ty : U}(d : D ty A)
     → L A ty
  go D1         = []
  go (DA x y)   = (I , here , (x , y)) ∷ []
  go (DK k x y) = ((K k) , (here , (x , y))) ∷ []
  go (D⊗ d e)   = walk fst (go d) ++ walk snd (go e)
  go (Di1 d)    = walk left (go d)
  go (Di2 d)    = walk right (go d)
  go {ty = ty ⊕ tv} (Ds1 x y) 
    = ((ty ⊕ tv) , (here , (i1 x , i2 y))) ∷ []
  go {ty = ty ⊕ tv} (Ds2 x y) 
    = ((ty ⊕ tv) , (here , (i2 x , i1 y))) ∷ []

{- 
  When the parameter is unit, we can ignore the changes over I
-}

  Change-is-not-I : {A : Set}{ty : U} → Change A ty → Bool
  Change-is-not-I (I , _) = false
  Change-is-not-I (_ , _) = true

  go1 : {ty : U}(d : D ty Unit) → L Unit ty
  go1 d = filter Change-is-not-I (go d)

{-
  Now, we gotta be able to apply these changes!
-}

  applyC : {A : Set}{{eqA : Eq A}}{ty : U} 
         → Change A ty → ⟦ ty ⟧ A → Maybe (⟦ ty ⟧ A)
  applyC {A} {ty} (ty₀ , dir , (k , l)) x 
    = on dir cmp-and-set x
    where
      cmp-and-set : ⟦ ty₀ ⟧ A → Maybe (⟦ ty₀ ⟧ A)
      cmp-and-set x₀
        with dec-eq ty₀ k x₀
      ...| no  _ = nothing
      ...| yes _ = just l

  applyAll : {A : Set}{{eqA : Eq A}}{ty : U} 
           → L A ty → ⟦ ty ⟧ A → Maybe (⟦ ty ⟧ A)
  applyAll []       x = just x
  applyAll (l ∷ ls) x = applyC l x >>= applyAll ls

{-
  Now some useful lemmas!
-}

  applyC-left
    : {A : Set}{{eqA : Eq A}}{ty tv : U}
    → (c : Change A ty)(x : ⟦ ty ⟧ A)
    → applyC (translate (left {tv = tv}) c) (i1 x) ≡ i1 <M> applyC c x
  applyC-left {A} {ty = ty} {tv} (ty₀ , dir , (k , l)) x 
    = {!!}

  applyAll-walk-left
    : {A : Set}{{eqA : Eq A}}{ty tv : U}
    → (ls : L A ty)(x : ⟦ ty ⟧ A)
    → applyAll (walk (left {tv = tv}) ls) (i1 x) ≡ i1 <M> applyAll ls x  
  applyAll-walk-left [] x = refl
  applyAll-walk-left (x ∷ ls) x₁ = {!!}
  
  applyAll-correct 
    : {A : Set}{{eqA : Eq A}}{ty : U}
    → (d : D ty A)
    → applyAll (go d) (D-src d) ≡ just (D-dst d)
  applyAll-correct D1 = refl
  applyAll-correct {{eq _≟_}} (DA x y)
    with x ≟ x
  ...| yes refl = refl
  ...| no  ¬p   = ⊥-elim (¬p refl)
  applyAll-correct (DK k x y)
    with Eq.cmp (ty-eq k) x x
  ...| yes refl = refl
  ...| no  ¬p   = ⊥-elim (¬p refl)
  applyAll-correct (D⊗ d e) = {!!}
  applyAll-correct (Di1 d)  = {!!}
  applyAll-correct (Di2 d) = {!!}
  applyAll-correct (Ds1 x y) = {!!}
  applyAll-correct (Ds2 x y) = {!!}
