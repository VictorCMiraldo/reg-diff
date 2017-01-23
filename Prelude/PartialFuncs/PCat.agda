open import Prelude hiding (id; _≤_)
open import Prelude.Monad
open import Prelude.Functor
open import Prelude.PartialFuncs.Base

module Prelude.PartialFuncs.PCat where

-- First we define some nomenclature:

  -- Objects
  ℙ₀ : Set₁
  ℙ₀ = Set

  -- And arrows
  ℙ₁ : ℙ₀ → ℙ₀ → Set
  ℙ₁ x y = x → Maybe y

  -- with the expected identity:
  id : ∀{X : ℙ₀} → ℙ₁ X X
  id x = just x
  
  -- Now we define the p-product structure,
  -- which is the usual product.
  _×ₚ_ : ℙ₀ → ℙ₀ → ℙ₀
  A ×ₚ B = A × B

  -- with action on arrows defined by:
  ×ₚ-map : ∀{A B C D : ℙ₀}
         → (f : ℙ₁ A B)(g : ℙ₁ C D)
         → ℙ₁ (A ×ₚ C) (B ×ₚ D)
  ×ₚ-map f g = split♯ (f ∙ π₁) (g ∙ π₂) 

  -- it is trivially a bi-functor!
  -- equipped with the diagonal natural
  -- transformation:
  Δ : ∀{A : ℙ₀} → ℙ₁ A (A ×ₚ A)
  Δ x = just (x , x)

  -- the projections are just the regular π₁ and π₂.

  π₁-id : ∀{X : ℙ₀}
        → (π₁ ∙ Δ) ≡ id {X}
  π₁-id = fun-ext (λ x → refl)

  -- TODO: this is all trivial... finish later

  -- The nice stuff: the extension order is the very same as 
  -- the order we are considering amongst our partial functions!

  _≤_ : ∀{X Y} → ℙ₁ X Y → ℙ₁ X Y → Set
  β ≤ γ = fmap FunctorMaybe p1 ∘ split♯ γ β ≡ β

  η-ext : ∀{a b}{A : Set a}{B : Set b}
        → {f g : A → B}(h : f ≡ g)
        → (x : A) → f x ≡ g x
  η-ext h x rewrite h = refl

  Maybe-magic : ∀{a b}{A : Set a}{B : Set b}{x : A}
              → (_≡_ {a} {Maybe A} nothing (just x)) → B
  Maybe-magic ()

  go : ∀{X Y}(f g : ℙ₁ X Y)
     → f ≤ g → f ≼* g
  go f g hip {x} with f x | inspect f x
  ...| nothing | _ = base
  ...| just fx | [ FX ] with g x | inspect g x
  ...| nothing | [ GX ] 
     with η-ext hip x 
  ...| hipX rewrite GX | FX = Maybe-magic hipX 
  go f g hip {x} | just fx | [ FX ]
     | just gx | [ GX ] 
     with η-ext hip x
  ...| hipX rewrite GX | FX = up (sym (just-inj hipX))

  back : ∀{X Y}(f g : ℙ₁ X Y)
       → f ≼* g → f ≤ g
  back f g hip = fun-ext (λ x → back' f g x hip)
    where
      back' : ∀{X Y}(f g : ℙ₁ X Y)(x : X)
            → f x ≼ g x → (fmap FunctorMaybe p1 ∘ split♯ g f) x ≡ f x
      back' f g x hip with f x
      ...| nothing with g x
      ...| just gx = refl 
      ...| nothing = refl
      back' f g x hip | just fx with g x
      back' f g x (up refl) | just fx | .(just fx) 
        = refl
