open import Prelude
  hiding (⊥)

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

  ≡-Rel-refl : ∀{a}{A B : Set a}{R : B ⟵ A}
             → R ≡-Rel R
  ≡-Rel-refl = id , id

  ≡-Rel-sym : ∀{a}{A B : Set a}{R S : B ⟵ A}
            → R ≡-Rel S → S ≡-Rel R
  ≡-Rel-sym (ps , pr) = pr , ps

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
    = either hip1 hip2
  
  ∩-uni-l : ∀{a}{A B : Set a}(R S X : B ⟵ A)
          → X ⊆ (R ∩ S) → (X ⊆ R) × (X ⊆ S)
  ∩-uni-l R S X hip 
    = (p1 ∘ hip) , (p2 ∘ hip)

  ∩-uni-r : ∀{a}{A B : Set a}(R S X : B ⟵ A)
          → X ⊆ R → X ⊆ S → X ⊆ (R ∩ S)
  ∩-uni-r R S X hip1 hip2
    = split hip1 hip2

{- 
  Our bicategory follows:
-}

  record _∙_ {a}{A B C : Set a}(R : C ⟵ B)(S : B ⟵ A)(c : C)(x : A) : Set a
    where
      constructor _,_
      field
        witness  : B
        composes : (R c witness) × (S witness x)

  p1∙ : {A B C : Set}{R : C ⟵ B}{S : B ⟵ A}{c : C}{a : A} → (R ∙ S) c a → B
  p1∙ rs = _∙_.witness rs

  p2∙ : {A B C : Set}{R : C ⟵ B}{S : B ⟵ A}{c : C}{a : A}
      (prf : (R ∙ S) c a) → (R c (p1∙ prf)) × (S (p1∙ prf) a)
  p2∙ rs = _∙_.composes rs

  _ᵒ : ∀{a}{A B : Set a} → (A ⟵ B) → (B ⟵ A)
  (R ᵒ) x y = R y x

  ID : ∀{a}{A : Set a} → A ⟵ A
  ID x y = x ≡ y

  infix  40 _ᵒ 
  infixl 30 _∙_
  infixl 25 _∩_
  infixl 24 _∪_
  infix  20 _⊆_
  infix  10 _≡-Rel_

{- 
  Every functions defines a relation:
-}

  fun : ∀{a}{A B : Set a}(f : A → B) → (B ⟵ A)
  fun f b a = b ≡ f a

{-

  Knapkin rules

-}

  knapkin-ll
    : ∀{a}{A B C : Set a}(R : C ⟵ B)(f : A → B)
    → {c : C}{a : A}
    → R c (f a) → (R ∙ fun f) c a
  knapkin-ll R f {c} {a} hip = f a , hip , refl

  knapkin-lr
    : ∀{a}{A B C : Set a}(R : C ⟵ B)(f : A → C)
    → {a : A}{b : B}
    → R (f a) b → (fun f ᵒ ∙ R) a b
  knapkin-lr R f {a} {b} hip = (f a) , (refl , hip)

  knapkin-rl
    : ∀{a}{A B C : Set a}(R : C ⟵ B)(f : A → B)
    → {c : C}{a : A}
    → (R ∙ fun f) c a → R c (f a)
  knapkin-rl R f (_ , h1 , refl) = h1

  knapkin-rr
    : ∀{a}{A B C : Set a}(R : C ⟵ B)(f : A → C)
    → {a : A}{b : B}
    → (fun f ᵒ ∙ R) a b → R (f a) b
  knapkin-rr R f {a} {b} (_ , refl , h1) = h1
