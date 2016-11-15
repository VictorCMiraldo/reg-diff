open import Prelude
  hiding (_+_; _*_; ⊥)
open import Prelude.RelCalc.Core

module Prelude.RelCalc.Coproduct where

  record [_∣_] {a}{A B C : Set a}(R : C ⟵ A)(S : C ⟵ B)(c : C)(ab : A ⊎ B) : Set a
    where constructor cons-either
          field un : either (R c) (S c) ab

  abstract
    -- Coproduct constants
    ι₁ : ∀{a}{A B : Set a} → (A ⊎ B) ⟵ A
    ι₁ = fun i1

    ι₂ : ∀{a}{A B : Set a} → (A ⊎ B) ⟵ B
    ι₂ = fun i2

    coprod-uni-r1 : ∀{a}{A B C : Set a}{X : C ⟵ (A ⊎ B)}
                  → (R : C ⟵ A)(S : C ⟵ B)
                  → X ≡-Rel [ R ∣ S ] 
                  → R ≡-Rel X ∙ ι₁
    coprod-uni-r1 {X = X} r s (prf1 , prf2)
      = (λ {c} {a} hip → i1 a , prf2 (cons-either hip) , cons-fun refl) 
      , (λ {c} {a} hip → let wit , hprf = hip
                         in [_∣_].un (prf1 (subst (X c) (fun.un (p2 hprf)) (p1 hprf))))

    coprod-uni-r2 : ∀{a}{A B C : Set a}{X : C ⟵ (A ⊎ B)}
                  → (R : C ⟵ A)(S : C ⟵ B)
                  → X ≡-Rel [ R ∣ S ] 
                  → S ≡-Rel X ∙ ι₂
    coprod-uni-r2 {X = X} r s (prf1 , prf2)
      = (λ {c} {b} hip → i2 b , prf2 (cons-either hip) , cons-fun refl) 
      , (λ {c} {b} hip → let wit , hprf = hip
                         in [_∣_].un (prf1 (subst (X c) (fun.un (p2 hprf)) (p1 hprf))))

    private
      coprod-uni-l-aux1 : ∀{a}{A B C : Set a}{X : C ⟵ (A ⊎ B)}
                        → (R : C ⟵ A)(S : C ⟵ B)
                        → (X ∙ ι₁ ⊆ R) → (X ∙ ι₂ ⊆ S)
                        → X ⊆ [ R ∣ S ]
      coprod-uni-l-aux1  {X = X} R S pr ps {y} {i1 a} hip
        = cons-either (pr (knapkin-ll X i1 hip))
      coprod-uni-l-aux1  {X = X} R S pr ps {y} {i2 b} hip
        = cons-either (ps (knapkin-ll X i2 hip))

      coprod-uni-l-aux2 : ∀{a}{A B C : Set a}{X : C ⟵ (A ⊎ B)}
                        → (R : C ⟵ A)(S : C ⟵ B)
                        → (R ⊆ X ∙ ι₁) → (S ⊆ X ∙ ι₂)
                        → [ R ∣ S ] ⊆ X
      coprod-uni-l-aux2 {X = X} R S pr ps {c} {i1 a} (cons-either hip)
        = knapkin-rl X i1 (pr hip)
      coprod-uni-l-aux2 {X = X} R S pr ps {c} {i2 b} (cons-either hip)
        = knapkin-rl X i2 (ps hip)

    coprod-uni-l : ∀{a}{A B C : Set a}{X : C ⟵ (A ⊎ B)}
                 → (R : C ⟵ A)(S : C ⟵ B)
                 → (R ≡-Rel X ∙ ι₁) → (S ≡-Rel X ∙ ι₂)
                 → X ≡-Rel [ R ∣ S ]
    coprod-uni-l R S pr ps 
      = coprod-uni-l-aux1 R S (p2 pr) (p2 ps) 
      , coprod-uni-l-aux2 R S (p1 pr) (p1 ps)

  abstract
    _-|-_ : ∀{a}{A B C D : Set a} → (B ⟵ A) → (D ⟵ C) → (B ⊎ D) ⟵ (A ⊎ C)
    R -|- S = [ ι₁ ∙ R ∣ ι₂ ∙ S ]

    ι₁-natural : ∀{a}{A B C D : Set a}(R : B ⟵ A){S : D ⟵ C}
               → ι₁ ∙ R ≡-Rel (R -|- S) ∙ ι₁
    ι₁-natural R {S}
      = coprod-uni-r1 (ι₁ ∙ R) (ι₂ ∙ S) 
        ( (λ z → cons-either ([_∣_].un z)) 
        , (λ z → cons-either ([_∣_].un z)))

    ι₁-cancel : ∀{a}{A B C : Set a}(R : C ⟵ A){S : C ⟵ B}
              → [ R ∣ S ] ∙ ι₁ ≡-Rel R
    ι₁-cancel R {S} = ≡-Rel-sym (coprod-uni-r1 R S ≡-Rel-refl)

    ι₂-natural : ∀{a}{A B C D : Set a}{R : B ⟵ A}(S : D ⟵ C)
               → ι₂ ∙ S ≡-Rel (R -|- S) ∙ ι₂
    ι₂-natural {R = R} S
      = coprod-uni-r2 (ι₁ ∙ R) (ι₂ ∙ S) 
        ( (λ z → cons-either ([_∣_].un z)) 
        , (λ z → cons-either ([_∣_].un z)))

    ι₂-cancel : ∀{a}{A B C : Set a}{R : C ⟵ A}(S : C ⟵ B)
              → [ R ∣ S ] ∙ ι₂ ≡-Rel S
    ι₂-cancel {R = R} S = ≡-Rel-sym (coprod-uni-r2 R S ≡-Rel-refl)
