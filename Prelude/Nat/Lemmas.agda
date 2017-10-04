open import Prelude
open import Relation.Binary

module Prelude.Nat.Lemmas where

  open import Data.Nat.Properties.Simple
    using (+-comm)
    public

  open import Data.Nat
  open import Data.Nat.Properties
    using ( ≤-steps
          ; 1+n≰n
          ; m≤m+n
          )
    renaming (≤-decTotalOrder to DTO)
    public

  private
    TO : _
    TO = DecTotalOrder.isTotalOrder DTO

    PO : _
    PO = IsTotalOrder.isPartialOrder TO

    PreO : _
    PreO = IsPartialOrder.isPreorder PO

  ≤-total : (m n : ℕ) → m ≤ n ⊎ n ≤ m
  ≤-total m n = IsTotalOrder.total TO m n

  ≤-antisym : ∀{m n} → m ≤ n → n ≤ m → m ≡ n
  ≤-antisym = IsPartialOrder.antisym PO
  
  ≤-trans : ∀{m n o} → m ≤ n → n ≤ o → m ≤ o
  ≤-trans = IsPreorder.trans PreO

  ≤-refl : ∀{m} → m ≤ m
  ≤-refl = IsPreorder.reflexive PreO refl

  1≤-witness : ∀{m} → 1 ≤ m → ∃ (λ n → m ≡ suc n)
  1≤-witness (s≤s {n = n} w) = n , refl
