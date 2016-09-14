open import Prelude hiding (_⊔_)
open import Prelude.Vector

{-
  Here we define the basic diffing functionality
  for the universe of regular types
-}

module RegDiff.Diff.Fixpoint2
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Diff.Regular v eqs

  Al : Set → ℕ → Set
  Al A zero = Unit
  Al A (suc n) = Vec A (suc n) × Fin (suc n)

  Al-size : {ty : U}{n : ℕ} → Al (μ ty) n → ℕ
  Al-size {n = zero}  al = 0
  Al-size {n = suc n} (al , f)
    = vsum (vmap μ-size (vdrop al f))

  mutual
    data Dμ (ty : U) : Set where
      nop : Dμ ty
      ins : (x : ⟦ ty ⟧ Unit)
          → Al (μ ty) (ar ty x)
          → Dμ ty
          → Dμ ty
      del : (x : ⟦ ty ⟧ Unit)
          → Al (μ ty) (ar ty x)
          → Dμ ty
          → Dμ ty
      mod : (x y : ⟦ ty ⟧ Unit)
          → (hip : ar ty x ≡ ar ty y)
          → Vec (Dμ ty) (ar ty x)
          → Dμ ty


  {-# TERMINATING #-}
  costμ : {ty : U} → Dμ ty → ℕ
  costμ nop = 0
  costμ {ty} (ins x x₁ d) 
    = size ty x + Al-size x₁ + costμ d
  costμ {ty} (del x x₁ d) 
    = size ty x + Al-size x₁ + costμ d
  costμ {ty} (mod x y hip d) 
    = size ty x + size ty y + vsum (vmap costμ d)

  _⊔μ_ : {ty : U} → Dμ ty → Dμ ty → Dμ ty
  p ⊔μ q with costμ p ≤?-ℕ costμ q
  ...| yes _ = p
  ...| no  _ = q

  ⊔μ* : {n : ℕ}{ty : U} → Vec (Dμ ty) (suc n) → Fin (suc n)
  ⊔μ* {n} {ty} (v ∷ vs) 
    = min (costμ v , fz) (vzip refl vs (vmap fs (enum-fin n)))
    where  
      enum-fin : (k : ℕ) → Vec (Fin k) k
      enum-fin zero = []
      enum-fin (suc n) = fz ∷ (vmap fs (enum-fin n))

      min : {k : ℕ} → ℕ × Fin (suc n) 
          → Vec (Dμ ty × Fin (suc n)) k → Fin (suc n)
      min (_ , i) [] = i
      min curr ((x , i) ∷ xs)
        with costμ x ≤?-ℕ (p1 curr)
      ...| yes _ = min (costμ x , i) xs
      ...| no  _ = min curr xs

  ifd_then_else_ 
    : {A B : Set} → Dec A → (A → B) → (¬ A → B) → B
  ifd (yes p) then f else _ = f p
  ifd (no ¬p) then _ else g = g ¬p

  mutual
    {-# TERMINATING #-}
    diffμ : {ty : U} → μ ty → μ ty → Dμ ty
    diffμ {ty} x y
      with μ-chv x | μ-chv y
    ...| chX | chY
      with μ-hd x | μ-hd y
    ...| hdX | hdY
      = ifd (ar ty hdX ≟-ℕ ar ty hdY)
        then (λ p → mod hdX hdY p (diffμ* p chX chY) 
                  ⊔μ (do-del ⊔μ do-ins))
        else (λ _ → do-del ⊔μ do-ins)
      where
        do-del
          = let al , rest = alignl chX y
             in del hdX al rest

        do-ins
          = let al , rest = alignr x chY
             in ins hdY al rest

    diffμ* : {n k : ℕ}{ty : U}
           → (hip : n ≡ k)
           → Vec (μ ty) n
           → Vec (μ ty) k 
           → Vec (Dμ ty) n
    diffμ* refl []       []       = []
    diffμ* refl (x ∷ xs) (y ∷ ys) 
      = diffμ x y ∷ diffμ* refl xs ys

    alignl : {n : ℕ}{ty : U}
           → Vec (μ ty) n → μ ty → Al (μ ty) n × Dμ ty
    alignl {zero} v x = unit , nop
    alignl {suc n} v x 
      = let ds = vmap (λ l → diffμ l x) v
            c  = ⊔μ* ds
         in (v , c) , lookup c ds

    alignr : {n : ℕ}{ty : U}
           → μ ty → Vec (μ ty) n →  Al (μ ty) n × Dμ ty
    alignr {zero} x v = unit , nop
    alignr {suc n} x v 
      = let ds = vmap (λ l → diffμ x l) v
            c  = ⊔μ* ds
         in (v , c) , lookup c ds
