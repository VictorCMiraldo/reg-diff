open import Prelude
open import Prelude.Functor.Decl

open import Data.List.Properties
  using (map-id; map-compose)

module Prelude.Functor.Instances where

  instance
    FunctorMaybe : ∀{a} → Functor {a} Maybe
    FunctorMaybe = functor 
      (λ k → maybe (just ∘ k) nothing) 
      (λ { (just x) → refl
         ; nothing  → refl
         }) 
      (λ { (just x) g f → refl 
         ; nothing  g f → refl 
         })

    FunctorList : ∀{a} → Functor {a} List
    FunctorList = functor map map-id (λ x g f → sym (map-compose x))
