open import Prelude hiding (_⊔_)
open import Prelude.Vector

module RegDiff.Diff.Properties.Aligned
    {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v) where

  open import RegDiff.Diff.Regular v eqs
  open import RegDiff.Diff.Fixpoint v eqs
  open import RegDiff.Diff.Properties.Identity v eqs

  _∥_ : {A : Set}{ty : U}
       → (p q : D' ty A) → Set
  p ∥ q = D-src p ≡ D-src q

  All' 
    : {n m : ℕ}{A : Set}
    → (P : A → Set)(Q : A → Set)
    → Fin n → m ≡ n → Vec A m → Set
  All' P Q () refl []
  All' P Q fz refl (x ∷ xs) = Q x × All P xs
  All' P Q (fs i) refl (x ∷ xs) 
    = P x × All' P Q i refl xs

  {-# TERMINATING #-}
  _∥μ_ : {ty : U}
      → (p q : Dμ' ty) → Set
  aux () p ∥μ _ 
  _ ∥μ aux () q 
  ins x cx p    ∥μ ins y cy q = p ∥μ q
  ins x cx p    ∥μ del y cy q = p ∥μ (del y cy q)
  ins x cx p    ∥μ mod w z h1 qs = p ∥μ (mod w z h1 qs)
  del x cx p    ∥μ ins y cy q = del x cx p ∥μ q
  del x cx p    ∥μ del y cy q 
    = Σ (x ≡ y) (λ { k → cx ≅ cy × (p ∥μ q) })
  _∥μ_ {ty} (del x (cx , i) p) (mod w z h1 qs) 
    = Σ (x ≡ w) 
        (λ k → All' IsIDμ (p ∥μ_) i 
                    (cong (ar ty) (sym k)) qs)
  mod x y h0 ps ∥μ ins w cw q = mod x y h0 ps ∥μ q
  _∥μ_ {ty} (mod x y h0 ps) (del w (cw , i) q) 
    = Σ (x ≡ w) 
        (λ k → All' IsIDμ (_∥μ q) i 
                    (cong (ar ty) k) ps)
  _∥μ_ {ty} (mod x y h0 ps) (mod w z h1 qs) 
    = Σ (x ≡ w) (λ k → All (uncurry _∥μ_) (vzip (cong (ar ty) k) ps qs))
