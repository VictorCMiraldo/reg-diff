open import Prelude
open import Relation.Binary

module Prelude.Nat.Lemmas where

  open import Data.Nat
    renaming (decTotalOrder to DTO)
  open import Data.Nat.Properties
    using ( ≤-steps
          ; 1+n≰n
          )
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
