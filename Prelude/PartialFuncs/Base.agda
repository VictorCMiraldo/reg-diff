open import Prelude
open import Prelude.Monad
open import Prelude.Functor


module Prelude.PartialFuncs.Base where

  open Monad {{...}}
  open Functor {{...}}

  data Unitₐ {a} : Set a where
    unit : Unitₐ

  data ⊥ₐ {a} : Set a where

  δ  : ∀{a b}{A : Set a}{B : Set b}
     → Maybe A × Maybe B → Maybe (A × B)
  δ (just x  , just y)   = just (x , y)
  δ (nothing , just _)   = nothing
  δ (just _  , nothing)  = nothing
  δ (nothing , nothing)  = nothing

  infix 20 _≼_
  _≼_ : ∀{a}{A : Set a} → Maybe A → Maybe A → Set a
  nothing ≼ y        = Unitₐ
  just x  ≼ nothing  = ⊥ₐ
  just x  ≼ just y   = x ≡ y

  infix 3 _↦_
  _↦_ : ∀{a b} → Set a → Set b → Set (a ⊔ b)
  A ↦ B = A → Maybe B

  infixr 10 _∙_
  _∙_ : ∀{a}{A B C : Set a} → B ↦ C → A ↦ B → A ↦ C 
  g ∙ f = (_>>= g) ∘ f

  id♯ : ∀{a}{A : Set a} → A ↦ A
  id♯ = return

  const♯ : ∀{a b}{A : Set a}{B : Set b}
        → B → A ↦ B
  const♯ b = return ∘ const b

  ! : ∀{a}{A : Set a} → A ↦ Unit
  ! _ = just unit

{-
  ########################
         PRODUCTS
-}

  π₁ : ∀{a}{A B : Set a} → (A × B) ↦ A
  π₁ = return ∘ p1

  π₂ : ∀{a}{A B : Set a} → (A × B) ↦ B
  π₂ = return ∘ p2

  split♯ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}
         → (A ↦ B) → (A ↦ C)
         → A ↦ (B × C)
  split♯ f g = δ ∘ split f g

  split♯-uni'-1 : ∀{a}{A B C : Set a}
               → (f : A ↦ B)(g : A ↦ C)(x : A)
               → (π₁ ∙ split♯ f g) x ≼ f x
  split♯-uni'-1 f g x 
    with f x | g x
  ...| nothing | nothing = unit
  ...| just fx | nothing = unit
  ...| nothing | just gx = unit
  ...| just fx | just gx = refl

  split♯-uni'-2 : ∀{a}{A B C : Set a}
               → (f : A ↦ B)(g : A ↦ C)(x : A)
               → (π₂ ∙ split♯ f g) x ≼ g x
  split♯-uni'-2 f g x 
    with f x | g x
  ...| nothing | nothing = unit
  ...| just fx | nothing = unit
  ...| nothing | just gx = unit
  ...| just fx | just gx = refl

  
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
