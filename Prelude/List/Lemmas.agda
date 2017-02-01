open import Prelude
open import Prelude.Monad

module Prelude.List.Lemmas where

  open Monad {{...}}

  open import Data.List.Properties
    using ( map-++-commute
          ; concat-map
          ; map-id
          ; map-compose
          ; foldr-cong
          ; map-cong
          ; length-map
          ; length-++
          )
    renaming (∷-injective to ∷-inj)
    public

  length-concat : ∀{a}{A : Set a}(xs : List (List A))
                → length (concat xs) ≡ sum (map length xs)
  length-concat []         = refl
  length-concat (xs ∷ xss) 
    = trans (length-++ xs)
            (cong (length xs +_) (length-concat xss))

  length->>=-return
    : ∀{a}{A B : Set a}
    → {f : A → B}(l : List A)
    → length l ≤ length (l >>= return ∘ f)
  length->>=-return []      = z≤n
  length->>=-return (x ∷ l) = s≤s (length->>=-return l)
    
