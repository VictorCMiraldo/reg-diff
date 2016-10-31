open import Prelude

module Prelude.Functor.Decl where

  record Functor {a}(F : Set a → Set a) : Set (ls a) where
    constructor functor
    field
      fmap  : {A B : Set a} → (A → B) → F A → F B

      fmap-id : {A : Set a}(x : F A) → fmap id x ≡ x
      fmap-∘  : {A B C : Set a}(x : F A)(g : B → C)(f : A → B)
              → fmap g (fmap f x) ≡ fmap (g ∘ f) x

  open Functor public
