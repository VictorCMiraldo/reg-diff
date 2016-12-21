open import Prelude
open import Prelude.Monad
open import Prelude.Functor


module Prelude.PartialFuncs.Base where

  open Monad {{...}}
  open Functor {{...}}

  open import Prelude.PartialFuncs.PartialOrder
    public

  infix 3 _↦_
  _↦_ : ∀{a b} → Set a → Set b → Set (a ⊔ b)
  A ↦ B = A → Maybe B

  _♭ : ∀{a b}{A : Set a}{B : Set b} → (A → B) → (A ↦ B)
  f ♭ = return ∘ f

{-
  ########################
         PRODUCTS
-}

  π₁ : ∀{a}{A B : Set a} → (A × B) ↦ A
  π₁ = p1 ♭

  π₂ : ∀{a}{A B : Set a} → (A × B) ↦ B
  π₂ = p2 ♭

  split♯ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}
         → (A ↦ B) → (A ↦ C)
         → A ↦ (B × C)
  split♯ f g = Maybe-δ ∘ split f g

  split♯-uni'-1 : ∀{a}{A B C : Set a}
               → (f : A ↦ B)(g : A ↦ C)(x : A)
               → (π₁ ∙ split♯ f g) x ≼ f x
  split♯-uni'-1 f g x 
    with f x | g x
  ...| nothing | nothing = base
  ...| just fx | nothing = base
  ...| nothing | just gx = base
  ...| just fx | just gx = up refl

  split♯-uni'-2 : ∀{a}{A B C : Set a}
               → (f : A ↦ B)(g : A ↦ C)(x : A)
               → (π₂ ∙ split♯ f g) x ≼ g x
  split♯-uni'-2 f g x 
    with f x | g x
  ...| nothing | nothing = base
  ...| just fx | nothing = base
  ...| nothing | just gx = base
  ...| just fx | just gx = up refl

  
  _><_ : ∀{a}{A B C D : Set a}
       → (f : A ↦ C)(g : B ↦ D)
       → (A × B) ↦ (C × D)
  f >< g = split♯ (f ∙ π₁) (g ∙ π₂)

{-
  ########################
       COPRODUCTS
-}

  ι₁ : ∀{a}{A B : Set a} → A ↦ (A ⊎ B)
  ι₁ = return ∘ i1

  ι₂ : ∀{a}{A B : Set a} → B ↦ (A ⊎ B)
  ι₂ = return ∘ i2

{-
  ########################
       GUARDS
-}

  infixl 15 _&_
  _&_ : ∀{a}{A B : Set a} → (A ↦ B) → (A → Bool) → A ↦ B
  (f & Z) x with Z x
  ...| true  = f x
  ...| false = nothing

  _∧_ : ∀{a}{A : Set a} → (A → Bool) → (A → Bool) → A → Bool
  (Z ∧ W) x = Z x and W x 

  &-join : ∀{a}{A B : Set a}(f : A ↦ B)(Z W : A → Bool)(x : A)
         → (f & Z & W) x ≡ (f & (W ∧ Z)) x
  &-join f Z W x 
    with Z x | inspect Z x | W x
  ...| false | _ | false = refl
  ...| false | [ Zx ] | true 
    rewrite Zx = refl
  ...| true  | _ | false = refl
  ...| true  | [ Zx ] | true 
    rewrite Zx = refl

  &-absorb-l : ∀{a}{A B C : Set a}(f : A ↦ B){g : B ↦ C}
             → (Z : A → Bool)(x : A)
             → (g ∙ f & Z) x ≡ ((g ∙ f) & Z) x 
  &-absorb-l f Z x with Z x
  ...| false = refl 
  ...| true  = refl

  &-absorb-r : ∀{a}{A B C : Set a}(f : B ↦ C){g : A → B}
             → (Z : B → Bool)(x : A)
             → (f & Z ∙ g ♭) x ≡ ((f ∙ g ♭) & (Z ∘ g)) x
  &-absorb-r f {g} Z x 
    with Z (g x)
  ...| true  = refl
  ...| false = refl
 
  &-split♯-1 : ∀{a}{A B C : Set a}
             → (f : C ↦ A)(g : C ↦ B)(Z : C → Bool)(x : C)
             → (split♯ (f & Z) g) x ≡ (split♯ f g & Z) x
  &-split♯-1 f g Z x 
    with Z x
  ...| true  = refl
  ...| false with g x
  ...| nothing = refl 
  ...| just _  = refl

  &-split♯-2 : ∀{a}{A B C : Set a}
             → (f : C ↦ A)(g : C ↦ B)(Z : C → Bool)(x : C)
             → (split♯ f (g & Z)) x ≡ (split♯ f g & Z) x
  &-split♯-2 f g Z x 
    with Z x
  ...| true  = refl
  ...| false with f x
  ...| nothing = refl 
  ...| just _  = refl

  
