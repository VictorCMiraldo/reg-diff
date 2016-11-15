open import Prelude
  hiding (_+_; _*_; ⊥)
open import Prelude.RelCalc.Core

module Prelude.RelCalc.Product where


  record <_∣_> {a}{A B C : Set a}(R : B ⟵ A)(S : C ⟵ A)(bc : B × C)(x : A) : Set a
    where constructor cons-split
          field un : (R (p1 bc) x) × (S (p2 bc) x)

  abstract
    π₁ : ∀{a}{A B : Set a} → A ⟵ (A × B)
    π₁ = fun p1

    π₂ : ∀{a}{A B : Set a} → B ⟵ (A × B)
    π₂ = fun p2

    prod-uni-r1 : ∀{a}{A B C : Set a}{X : (A × B) ⟵ C}
               → (R : A ⟵ C)(S : B ⟵ C)
               → X ⊆ < R ∣ S >
               → π₁ ∙ X ⊆ R
    prod-uni-r1 {X = X} R S hip {.a} {c} ((a , b) , refl , h1)
      = p1 (<_∣_>.un (hip h1))

    prod-uni-r2 : ∀{a}{A B C : Set a}{X : (A × B) ⟵ C}
               → (R : A ⟵ C)(S : B ⟵ C)
               → X ⊆ < R ∣ S >
               → π₂ ∙ X ⊆ S
    prod-uni-r2 {X = X} R S hip {.b} {c} ((a , b) , refl , h1)
      = p2 (<_∣_>.un (hip h1))

    prod-uni-l : ∀{a}{A B C : Set a}{X : (A × B) ⟵ C}
               → (R : A ⟵ C) → (S : B ⟵ C)
               → (π₁ ∙ X) ⊆ R → (π₂ ∙ X) ⊆ S
               → X ⊆ < R ∣ S >
    prod-uni-l {X = X} R S pr ps {a , b} {c} hip
      = cons-split ((pr ((a , b) , (refl , hip))) 
                   , ps ((a , b) , (refl , hip)))

  abstract
    _><_ : ∀{a}{A B C D : Set a} → (C ⟵ A) → (D ⟵ B) → (C × D) ⟵ (A × B)
    R >< S = < R ∙ π₁ ∣ S ∙ π₂ >
