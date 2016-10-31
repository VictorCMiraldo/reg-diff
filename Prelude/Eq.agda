open import Prelude

module Prelude.Eq where

  record Eq (A : Set) : Set where
    constructor eq
    field cmp : (x y : A) → Dec (x ≡ y)


  open Eq

  instance
    eq-Unit : Eq Unit
    eq-Unit = eq (λ { unit unit → yes refl })

    eq-Bool : Eq Bool
    eq-Bool = eq decide
      where 
        decide : (x y : Bool) → Dec (x ≡ y)
        decide true  true   = yes refl
        decide true  false  = no (λ ())
        decide false true  = no (λ ())
        decide false false = yes refl

    eq-ℕ : Eq ℕ
    eq-ℕ = eq _≟-ℕ_

    eq-⊥ : Eq ⊥
    eq-⊥ = eq (λ x → ⊥-elim x)

    eq-pair : ∀{A B} ⦃ eqA : Eq A ⦄ ⦃ eqB : Eq B ⦄ → Eq (A × B)
    eq-pair = eq decide
      where
        decide : {A B : Set}⦃ eqA : Eq A ⦄ ⦃ eqB : Eq B ⦄
               → (x y : A × B) → Dec (x ≡ y)
        decide {{eq cA}} {{eq cB}} (x1 , x2) (y1 , y2) 
          with cA x1 y1
        ...| no abs = no (abs ∘ p1 ∘ ×-inj)
        ...| yes h
          with cB x2 y2
        ...| no abs = no (abs ∘ p2 ∘ ×-inj)
        ...| yes i = yes (cong₂ _,_ h i)

    eq-sum : ∀{A B} ⦃ eqA : Eq A ⦄ ⦃ eqB : Eq B ⦄ → Eq (A ⊎ B)
    eq-sum = eq decide
      where
        decide : {A B : Set}⦃ eqA : Eq A ⦄ ⦃ eqB : Eq B ⦄
               → (x y : A ⊎ B) → Dec (x ≡ y)
        decide {{eq cA}} {{eq cB}} (i1 x) (i1 y)
          with cA x y
        ...| no abs = no (abs ∘ i1-inj)
        ...| yes h  = yes (cong i1 h)
        decide {{eq cA}} {{eq cB}} (i2 x) (i2 y)
          with cB x y
        ...| no abs = no (abs ∘ i2-inj)
        ...| yes h  = yes (cong i2 h)
        decide (i1 x) (i2 y) = no (λ ())
        decide (i2 x) (i1 y) = no (λ ())
          

    eq-Maybe : ∀{A} ⦃ eqA : Eq A ⦄ → Eq (Maybe A)
    eq-Maybe = eq decide
      where
        decide : {A : Set} ⦃ eqA : Eq A ⦄
               → (x y : Maybe A) → Dec (x ≡ y)
        decide nothing nothing   = yes refl
        decide nothing (just _)  = no (λ ())
        decide (just _) nothing  = no (λ ())
        decide ⦃ eq f ⦄ (just x) (just y) with f x y
        ...| yes x≡y = yes (cong just x≡y)
        ...| no  x≢y = no (x≢y ∘ just-inj)

    eq-List : {A : Set}{{eq : Eq A}} → Eq (List A)
    eq-List {A} {{eq _≟_}} = eq decide
      where
        open import Data.List.Properties
          renaming (∷-injective to ∷-inj)

        decide : (a b : List A) → Dec (a ≡ b)
        decide [] (_ ∷ _) = no (λ ())
        decide (_ ∷ _) [] = no (λ ())
        decide []   []    = yes refl
        decide (a ∷ as) (b ∷ bs)
          with a ≟ b | decide as bs
        ...| yes a≡b | yes as≡bs
          rewrite a≡b = yes (cong (_∷_ b) as≡bs)
        ...| no  a≢b | yes as≡bs = no (a≢b ∘ p1 ∘ ∷-inj)
        ...| yes a≡b | no  as≢bs = no (as≢bs ∘ p2 ∘ ∷-inj)
        ...| no  a≢b | no  as≢bs = no (a≢b ∘ p1 ∘ ∷-inj)
