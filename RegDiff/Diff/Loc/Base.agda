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
  open import RegDiff.Generic.Derivative.Base v

  Change : Set → U → Set
  Change A ty = Σ U (λ k → Dir ty k × ⟦ k ⊗ k ⟧ A)

  L : Set → U → Set
  L A ty = List (Change A ty)

  data Changeμ (ty : U) : Set where
    loc : (k : U) → Dirμ ty k → (x y : ⟦ k ⟧ Unit) → ar k x ≡ ar k y → Changeμ ty
    ins : Dirμ ty ty → (x : ⟦ ty ⟧ Unit) → Vec (List (Changeμ ty)) (ar ty x) → Changeμ ty
    del : Dirμ ty ty → (x : ⟦ ty ⟧ Unit) → Vec (List (Changeμ ty)) (ar ty x) → Changeμ ty

  Lμ : U → Set
  Lμ = List ∘ Changeμ

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

  to-Changeμ : {ty : U} → L Unit ty → Lμ ty
  to-Changeμ [] = []
  to-Changeμ ((d₀ , dir , (dif0 , dif1)) ∷ ls) 
    = loc d₀ (hd dir) dif0 dif1 {!!} ∷ to-Changeμ ls

  app-dir : {ty : U} → Dir ty I → Changeμ ty → Changeμ ty
  app-dir d (loc d₀ dir x0 x1 hip) 
    = loc d₀ (tl d dir) x0 x1 hip
  app-dir d (ins ch₀ ctx ls) = ins (tl d ch₀) ctx ls
  app-dir d (del ch₀ ctx ls) = del (tl d ch₀) ctx ls

  postulate
    do-insertion : {ty : U} → Lμ ty
    do-delete    : {ty : U} → Lμ ty

  dμ-cat : {ty : U} → List (Dμ ty) → Dμ ty
  dμ-cat [] = Dμ-nil
  dμ-cat (Dμ-nil ∷ l) = dμ-cat l
  dμ-cat (Dμ-ins x d ∷ l) = Dμ-ins x (dμ-cat (d ∷ l))
  dμ-cat (Dμ-del x d ∷ l) = Dμ-del x (dμ-cat (d ∷ l))
  dμ-cat (Dμ-mod x d ∷ l) = Dμ-mod x (dμ-cat (d ∷ l))

  replicatev : {A : Set}(n : ℕ) → A → Vec A n
  replicatev zero a = []
  replicatev (suc n) a = a ∷ replicatev n a

  dμ-ch-split : {ty : U}(n : ℕ) → List (Dμ ty) → Vec (Dμ ty) n × Dμ ty
  dμ-ch-split zero l = [] , dμ-cat l
  dμ-ch-split (suc n) [] = replicatev (suc n) Dμ-nil , Dμ-nil
  dμ-ch-split (suc n) (x ∷ l) 
    = let v , r = dμ-ch-split n l
       in x ∷ v , r

  {-# TERMINATING #-}
  goμ : {ty : U} → Dμ ty → Lμ ty
  goμ Dμ-nil = []
  goμ {ty = ty} (Dμ-ins x d) 
    = let vs , ds = dμ-ch-split (ar ty x) (dμ-ch d)
       in ins (hd here) x (vmap goμ vs) ∷ goμ ds
  goμ {ty = ty} (Dμ-del x d) 
    = let vs , ds = dμ-ch-split (ar ty x) (dμ-ch d)
       in del (hd here) x (vmap goμ vs) ∷ goμ ds
  goμ {ty = ty} (Dμ-mod x d) 
    = let x' = go x
       in to-Changeμ x' ++ concat (zipWith (λ dir op → map (app-dir dir) (goμ op)) 
                                           (rome ty (D-src x)) 
                                           (dμ-ch d))

  cmp-set : {A : Set}{{eqA : Eq A}}{ty : U}
          → (¬ ty ≡ I) → ⟦ ty ⊗ ty ⟧ A → ⟦ ty ⟧ A → Maybe (⟦ ty ⟧ A)
  cmp-set {ty = ty} ok (x , y) k with dec-eq ty x k
  ...| yes _ = just y
  ...| no  _ = nothing

  cmp-setμ : {ty : U} → (¬ ty ≡ I)
           → ⟦ ty ⊗ ty ⟧ Unit → μ ty → Maybe (μ ty)
  cmp-setμ {ty = ty} ok (dx0 , dx1) val 
    with plug-view val
  cmp-setμ {ty = ty} ok (dx0 , dx1) _ | plugged hdVal chVal 
    with ar ty dx0 ≟-ℕ ar ty dx1
  ...| no  _ = nothing
  ...| yes _ = {!!}

  apply1 : {ty : U} → Changeμ ty → μ ty → Maybe (μ ty)
  apply1 (loc d₀ dir x0 c1 hip) k = onμ dir {!!} k
  apply1 (ins d₀ ctx xs) k = {!!}
  apply1 (del d₀ ctx xs) k = {!!}
  
  APPLY : {ty : U} → Lμ ty → μ ty → μ ty
  APPLY = {!!}
