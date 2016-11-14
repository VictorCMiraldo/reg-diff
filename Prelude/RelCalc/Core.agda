open import Prelude
  renaming ( either to either-prelude
           ; split  to split-prelude
           )
  hiding (_+_; _*_; ⊥)

module Prelude.RelCalc.Core where

  data Bot {a} : Set a where

  data Top {a} : Set a where
    top : Top

{-
  Basic definitions
-}

  _⟵_ : ∀{a} → Set a → Set a → Set (ls a)
  _⟵_ {a} B A = B → A → Set a

  EndoRel : ∀{a} → Set a → Set (ls a)
  EndoRel A = A ⟵ A

  _⊆_ : ∀{a}{A B : Set a}(R S : B ⟵ A) → Set a
  R ⊆ S = ∀ {x y} → R x y → S x y

  _≡-Rel_ : ∀{a}{A B : Set a}(R S : B ⟵ A) → Set a
  R ≡-Rel S = R ⊆ S × S ⊆ R

  postulate
    -- univalence axiom for relations!
    ≡-Rel-ext : ∀{a}{A B : Set a}(R S : B ⟵ A)
              → R ≡-Rel S → R ≡ S

{-
  Top and bottom
-}

  ⊤ : ∀{a}{A B : Set a} → (B ⟵ A)
  ⊤ x y = Top

  ⊥ : ∀{a}{A B : Set a} → (B ⟵ A)
  ⊥ x y = Bot

  R⊆⊤ : ∀{a}{A B : Set a}(R : A ⟵ B) → R ⊆ ⊤
  R⊆⊤ R _ = top

  ⊥⊆R : ∀{a}{A B : Set a}(R : A ⟵ B) → ⊥ ⊆ R
  ⊥⊆R R ()

{-
  Meet and Join with universsals
-}

  _∪_ : ∀{a}{A B : Set a}(R S : B ⟵ A) → B ⟵ A
  (R ∪ S) x y = R x y ⊎ S x y

  _∩_ : ∀{a}{A B : Set a}(R S : B ⟵ A) → B ⟵ A
  (R ∩ S) x y = R x y × S x y

  ∪-uni-l : ∀{a}{A B : Set a}(R S X : B ⟵ A)
          → R ∪ S ⊆ X → (R ⊆ X) × (S ⊆ X)
  ∪-uni-l R S X hip 
    = hip ∘ i1 , hip ∘ i2

  ∪-uni-r : ∀{a}{A B : Set a}(R S X : B ⟵ A)
          → R ⊆ X → S ⊆ X → R ∪ S ⊆ X
  ∪-uni-r R S X hip1 hip2
    = either-prelude hip1 hip2
  
  ∩-uni-l : ∀{a}{A B : Set a}(R S X : B ⟵ A)
          → X ⊆ (R ∩ S) → (X ⊆ R) × (X ⊆ S)
  ∩-uni-l R S X hip 
    = (p1 ∘ hip) , (p2 ∘ hip)

  ∩-uni-r : ∀{a}{A B : Set a}(R S X : B ⟵ A)
          → X ⊆ R → X ⊆ S → X ⊆ (R ∩ S)
  ∩-uni-r R S X hip1 hip2
    = split-prelude hip1 hip2

{- 
  Our bicategory follows:
-}

  _ᵒ : ∀{a}{A B : Set a} → (A ⟵ B) → (B ⟵ A)
  (R ᵒ) x y = R y x

  _∙_ : ∀{a}{A B C : Set a} → (C ⟵ B) → (B ⟵ A) → (C ⟵ A)
  (R ∙ S) c a = ∃ (λ b → R c b × S b a)

  ID : ∀{a}{A : Set a} → A ⟵ A
  ID x y = x ≡ y

  infix  40 _ᵒ 
  infixl 30 _∙_
  infixl 25 _∩_
  infixl 24 _∪_
  infix  20 _⊆_

{- 
  Every functions defines a relation:
-}

  fun : ∀{a}{A B : Set a}(f : A → B) → (B ⟵ A)
  fun f b a = b ≡ f a

{-

  Coproducts

-}

  ι₁ : ∀{a}{A B : Set a} → (A ⊎ B) ⟵ A
  ι₁ = fun i1

  ι₂ : ∀{a}{A B : Set a} → (A ⊎ B) ⟵ B
  ι₂ = fun i2

  either-def : ∀{a}{A B C : Set a} → (C ⟵ A) → (C ⟵ B) → C ⟵ (A ⊎ B)
  either-def R S = R ∙ ι₁ ᵒ ∪ S ∙ ι₂ ᵒ

  either : ∀{a}{A B C : Set a} → (C ⟵ A) → (C ⟵ B) → C ⟵ (A ⊎ B)
  either R S x (i1 y) = R x y
  either R S x (i2 y) = S x y

  _+-def_ : ∀{a}{A B C D : Set a} → (C ⟵ A) → (D ⟵ B) → (C ⊎ D) ⟵ (A ⊎ B)
  (R +-def S) = either (ι₁ ∙ R) (ι₂ ∙ S)

  _+_ : ∀{a}{A B C D : Set a} → (C ⟵ A) → (D ⟵ B) → (C ⊎ D) ⟵ (A ⊎ B)
  (R + S) (i1 x) (i1 y) = R x y
  (R + S) (i1 x) (i2 y) = Bot
  (R + S) (i2 x) (i1 y) = Bot
  (R + S) (i2 x) (i2 y) = S x y

{-

  Products

-}

  π₁ : ∀{a}{A B : Set a} → A ⟵ (A × B)
  π₁ = fun p1

  π₂ : ∀{a}{A B : Set a} → B ⟵ (A × B)
  π₂ = fun p2

  split-def : ∀{a}{A B C : Set a} → (A ⟵ C) → (B ⟵ C) → (A × B) ⟵ C 
  split-def R S = π₁ ᵒ ∙ R ∩ π₂ ᵒ ∙ S

  split : ∀{a}{A B C : Set a} → (A ⟵ C) → (B ⟵ C) → (A × B) ⟵ C 
  split R S (a , b) c = R a c × S b c

  _*-def_ : ∀{a}{A B C D : Set a} → (C ⟵ A) → (D ⟵ B) → (C × D) ⟵ (A × B)
  R *-def S = split (R ∙ π₁) (S ∙ π₂)

  _*_ : ∀{a}{A B C D : Set a} → (C ⟵ A) → (D ⟵ B) → (C × D) ⟵ (A × B)
  (R * S) (c , d) (a , b) = R c a × S d b
