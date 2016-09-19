open import Prelude hiding (_⊔_)
open import Prelude.Vector

{-
  Here we define the basic diffing functionality
  for the universe of regular types
-}

module RegDiff.Diff.Fixpoint
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Diff.Regular v eqs

  data Dμ (ty : U) : Set where
    Dμ-nil : Dμ ty
    Dμ-ins : ⟦ ty ⟧ Unit → Dμ ty → Dμ ty
    Dμ-del : ⟦ ty ⟧ Unit → Dμ ty → Dμ ty
    -- Dμ-mod : Σ (D ty Unit) Stable → Dμ ty → Dμ ty
    Dμ-mod : D ty Unit → Dμ ty → Dμ ty

  μ-ins : {ty : U} → ⟦ ty ⟧ Unit → List (μ ty) → List (μ ty)
  μ-ins {ty} x xs
    = let xs0 , xs1 = lsplit (ar ty x) xs
       in maybe (λ y → y ∷ xs1) [] (μ-plug x xs0)

  Dμ-src : {ty : U} → Dμ ty → List (μ ty)
  Dμ-src Dμ-nil = []
  Dμ-src (Dμ-ins x d) = Dμ-src d
  Dμ-src (Dμ-del x d) = μ-ins x (Dμ-src d)
  Dμ-src (Dμ-mod x d) = μ-ins (D-src x) (Dμ-src d)

  Dμ-dst : {ty : U} → Dμ ty → List (μ ty)
  Dμ-dst Dμ-nil = []
  Dμ-dst (Dμ-del x d) = Dμ-dst d
  Dμ-dst (Dμ-ins x d) = μ-ins x (Dμ-dst d)
  Dμ-dst (Dμ-mod x d) = μ-ins (D-dst x) (Dμ-dst d)
  
  costμ : {ty : U} → Dμ ty → ℕ
  costμ Dμ-nil = 0
  costμ {ty} (Dμ-ins x d) = size ty x + costμ d
  costμ {ty} (Dμ-del x d) = size ty x + costμ d
  costμ {ty} (Dμ-mod x d) = cost x + costμ d

  _⊔μ_ : {ty : U} → Dμ ty → Dμ ty → Dμ ty
  d ⊔μ e with costμ d ≤?-ℕ costμ e
  ...| yes _ = d
  ...| no  _ = e

  ifd_then_else_ : {A B : Set} → Dec A → (A → B) → (¬ A → B) → B
  ifd (yes p) then f else _ = f p
  ifd (no ¬p) then _ else g = g ¬p

  {-# TERMINATING #-}
  diffμ : {ty : U}(x y : List (μ ty)) → Dμ ty
  diffμ []       []       = Dμ-nil
  diffμ []       (y ∷ ys) = Dμ-ins (μ-hd y) (diffμ [] (μ-ch y ++ ys)) 
  diffμ (x ∷ xs) []       = Dμ-del (μ-hd x) (diffμ (μ-ch x ++ xs) [])
  diffμ {ty} (x ∷ xs) (y ∷ ys) 
    = let dxy = diff ty (μ-hd x) (μ-hd y) 
          rxy = diffμ (μ-ch x ++ xs) (μ-ch y ++ ys)
       in ifd (Stable-dec dxy) 
          then (λ p → Dμ-mod dxy rxy ⊔μ ins-or-del) 
          else (λ _ → ins-or-del)
    where
      ins-or-del = Dμ-ins (μ-hd y) (diffμ (x ∷ xs) (μ-ch y ++ ys))
                ⊔μ Dμ-del (μ-hd x) (diffμ (μ-ch x ++ xs) (y ∷ ys))

  applyμ : {ty : U} → Dμ ty → List (μ ty) → Maybe (List (μ ty))
  applyμ Dμ-nil [] = just []
  applyμ Dμ-nil (x ∷ l) = nothing
  applyμ (Dμ-ins x d) l = μ-ins x <M> applyμ d l
  applyμ (Dμ-del x d) [] = nothing
  applyμ {ty} (Dμ-del x d) (l₀ ∷ l) 
    with dec-eq ty x (μ-hd l₀)
  ...| yes _ = applyμ d (μ-ch l₀ ++ l)
  ...| no  _ = nothing
  applyμ (Dμ-mod x d) [] = nothing
  applyμ {ty} (Dμ-mod x d) (l₀ ∷ l) 
    with apply ty x (μ-hd l₀) 
  ...| nothing = nothing
  ...| just x' = μ-ins x' <M> applyμ d (μ-ch l₀ ++ l)


  dμ-splitd : {ty : U}(n : ℕ) → Dμ ty → Dμ ty × Dμ ty
  dμ-splitd zero    d      = Dμ-nil , d
  dμ-splitd (suc n) Dμ-nil = Dμ-nil , Dμ-nil
  dμ-splitd {ty} (suc n) (Dμ-ins x d) 
    = let d0 , d1 = dμ-splitd (ar ty x + n) d 
       in Dμ-ins x d0 , d1
  dμ-splitd {ty} (suc n) (Dμ-del x d)
    = let d0 , d1 = dμ-splitd (ar ty x + n) d 
       in Dμ-del x d0 , d1
  dμ-splitd {ty} (suc n) (Dμ-mod x d) 
    = let d0 , d1 = dμ-splitd (ar ty (D-src x) + n) d 
       in Dμ-mod x d0 , d1
  
  {-# TERMINATING #-}
  dμ-ch : {ty : U} → Dμ ty → List (Dμ ty)
  dμ-ch d with dμ-splitd 1 d
  ...| d0 , Dμ-nil = d0 ∷ []
  ...| d0 , d1     = d0 ∷ dμ-ch d1
