open import Prelude
open import Relation.Binary

module Prelude.Nat.Lemmas where

  open import Data.Nat.Properties.Simple
    using (+-comm)
    public

  open import Data.Nat.Properties
    using ( ≤-steps
          ; 1+n≰n
          ; m≤m+n
          ; ≤-total
          ; ≤-antisym
          ; ≤-trans
          ; ≤-refl
          )
    public

  1≤-witness : ∀{m} → 1 ≤ m → ∃ (λ n → m ≡ suc n)
  1≤-witness (s≤s {n = n} w) = n , refl
