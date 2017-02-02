open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.PartialFuncs.Base
open import Prelude.List.All
open import RegDiff.Generic.Parms

open import RegDiff.Diff.Abstract.Base

module RegDiff.Diff.Abstract.Instances.Trivial
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_
  open import RegDiff.Diff.Trivial.Apply ks keqs A _≟-A_

  {-
    We will first abstract over which layer of the universe
    we are talking about, let it be P.

    We then later instantiate it for Sums, Products and Atoms.
  -}
  private 
    module Generic {A : Set}(⟦_⟧ : A → Set)
                   (eqA : (x y : A) → Dec (x ≡ y))
                   (eqP : (k : A)(x y : ⟦ k ⟧) → Dec (x ≡ y)) 
      where

      -- The general template for the trivial diff is:
      Trivial-delta : Diffable ⟦_⟧
      Trivial-delta = record 
        { P = trivial ⟦_⟧ 
        ; cands = λ x y → (x , y) ∷ [] 
        ; apply = Trivial-apply ⟦_⟧ eqA eqP 
        ; cost = cost-trivial ⟦_⟧ eqA eqP 
        }

      -- Now we prove a bunch of lemmas of delta, in general.
      lemma-singl-correct
        : {a b : A}(x : ⟦ a ⟧)(y : ⟦ b ⟧)
        → singl ⟦_⟧ eqP x y x ≡ just y
      lemma-singl-correct {a} x y 
        with eqP a x x 
      ...| no abs = ⊥-elim (abs refl)
      ...| yes _  = refl

      lemma-singl-correct-2
        : {a b : A}(x k : ⟦ a ⟧)(y z : ⟦ b ⟧)
        → singl ⟦_⟧ eqP x y k ≡ just z
        → x ≡ k × y ≡ z
      lemma-singl-correct-2 {a} x k y z hip 
        with eqP a x k
      ...| yes px = px , just-inj hip
      lemma-singl-correct-2 {a} x k y z ()
         | no _ 

      lemma-cands-1 : {a b : A}(x : ⟦ a ⟧)(y : ⟦ b ⟧) 
                    → IsCand Trivial-delta x y (x , y)
      lemma-cands-1 {a} {b} x y with eqA a b
      ...| no _ = lemma-singl-correct x y
      lemma-cands-1 {a} {.a} x y 
         | yes refl with eqP a x y
      ...| no  _ = lemma-singl-correct x y
      ...| yes p = cong just p

      lemma-cost-1 : {a b : A}(x : ⟦ a ⟧)(y : ⟦ b ⟧)(p q : P Trivial-delta a b)
                   → IsCand Trivial-delta x y p
                   → IsCand Trivial-delta x y q
                   → cost Trivial-delta p ≡ cost Trivial-delta q 
                   → apply Trivial-delta p ≡ apply Trivial-delta q
      lemma-cost-1 {a} {b} x y (px , py) (qx , qy) hP hQ hip
        with eqA a b
      ...| no _ with lemma-singl-correct-2 px x py y hP
                   | lemma-singl-correct-2 qx x qy y hQ
      ...| px≡x , py≡y | qx≡x , qy≡y 
         rewrite px≡x | py≡y | qx≡x | qy≡y = refl
      lemma-cost-1 {a} {.a} x y (px , py) (qx , qy) hP hQ hip
         | yes refl with eqP a px py
      ...| no _ with eqP a qx qy 
      ...| no _ with lemma-singl-correct-2 px x py y hP
                   | lemma-singl-correct-2 qx x qy y hQ
      ...| px≡x , py≡y | qx≡x , qy≡y 
         rewrite px≡x | py≡y | qx≡x | qy≡y = refl
      lemma-cost-1 {a} {.a} x y (px , py) (qx , qy) hP hQ () 
         | yes refl | no _ | yes _ 
      lemma-cost-1 {a} {.a} x y (px , py) (qx , qy) hP hQ hip 
         | yes refl | yes px≡py with eqP a qx qy
      lemma-cost-1 {a} {.a} x y (px , py) (qx , qy) hP hQ () 
         | yes refl | yes _ | no _ 
      ...| yes qx≡qy = refl

      lemma-cost-2 : {a b : A}(x : ⟦ a ⟧)(y : ⟦ b ⟧)(p q : P Trivial-delta a b)
                   → IsCand Trivial-delta x y p
                   → IsCand Trivial-delta x y q
                   → cost Trivial-delta p ≤ cost Trivial-delta q 
                   → apply Trivial-delta q ≼* apply Trivial-delta p
      lemma-cost-2 {a} {b} x y (px , py) (qx , qy) hP hQ hip
        with eqA a b
      ...| no _ with lemma-singl-correct-2 px x py y hP
                   | lemma-singl-correct-2 qx x qy y hQ
      ...| px≡x , py≡y | qx≡x , qy≡y 
         rewrite px≡x | py≡y | qx≡x | qy≡y = ≼-refl 
      lemma-cost-2 {a} {.a} x y (px , py) (qx , qy) hP hQ hip
         | yes refl with eqP a px py
      ...| no _ with eqP a qx qy 
      ...| no _ with lemma-singl-correct-2 px x py y hP
                   | lemma-singl-correct-2 qx x qy y hQ
      ...| px≡x , py≡y | qx≡x , qy≡y 
         rewrite px≡x | py≡y | qx≡x | qy≡y = ≼-refl
      lemma-cost-2 {a} {.a} x y (px , py) (qx , qy) hP hQ ()
         | yes refl | no _ | yes _ 
      lemma-cost-2 {a} {.a} x y (px , py) (qx , qy) hP hQ hip
         | yes refl | yes px≡py with eqP a qx qy
      lemma-cost-2 {a} {.a} x y (px , py) (qx , qy) hP hQ hip
         | yes refl | yes _ | no abs with lemma-singl-correct-2 qx x qy y hQ
      ...| qx≡x , qy≡y 
         = ⊥-elim (abs (trans qx≡x (trans (just-inj hP) (sym qy≡y))))
      lemma-cost-2 {a} {.a} x y (px , py) (qx , qy) hP hQ hip
         | yes refl | yes _ | yes qx≡qy = ≼-refl

      -- Finally,
      -- We can prove that the template we had is ok!
      Trivial-Correct
        : CandsCorrect ⟦_⟧ Trivial-delta
      Trivial-Correct = record
        { cands-correct = λ x y → lemma-cands-1 x y ∷ []
        ; cands-nonnil  = λ {a} {b} x y → s≤s z≤n
        }

      Trivial-CostCorrect 
        : CostCorrect ⟦_⟧ Trivial-delta
      Trivial-CostCorrect = record
        { cands-correct = Trivial-Correct
        ; cost-eq = lemma-cost-1
        ; cost-order = lemma-cost-2
        }

  -- Lastly, we instantiate to our specifics!

  --   ATOMS
  --   #####
  Trivialₐ-Diffable : Diffable ⟦_⟧ₐ
  Trivialₐ-Diffable = Trivial-delta
    where
      open Generic ⟦_⟧ₐ Atom-eq (dec-eqₐ _≟-A_) 

  Trivialₐ-Correct : CandsCorrect ⟦_⟧ₐ Trivialₐ-Diffable
  Trivialₐ-Correct = Trivial-Correct
    where
      open Generic ⟦_⟧ₐ Atom-eq (dec-eqₐ _≟-A_)

  Trivialₐ-CostCorrect : CostCorrect ⟦_⟧ₐ Trivialₐ-Diffable
  Trivialₐ-CostCorrect = Trivial-CostCorrect
    where
      open Generic ⟦_⟧ₐ Atom-eq (dec-eqₐ _≟-A_)

 
  --   PRODUCTS
  --   ########
  Trivialₚ-Diffable : Diffable ⟦_⟧ₚ
  Trivialₚ-Diffable = Trivial-delta
    where
      open Generic ⟦_⟧ₚ Prod-eq (dec-eqₚ _≟-A_)

  Trivialₚ-Correct : CandsCorrect ⟦_⟧ₚ Trivialₚ-Diffable
  Trivialₚ-Correct = Trivial-Correct
    where
      open Generic ⟦_⟧ₚ Prod-eq (dec-eqₚ _≟-A_) 

  Trivialₚ-CostCorrect : CostCorrect ⟦_⟧ₚ Trivialₚ-Diffable
  Trivialₚ-CostCorrect = Trivial-CostCorrect
    where
      open Generic ⟦_⟧ₚ Prod-eq (dec-eqₚ _≟-A_) 


  --   SUMS
  --   ####
  Trivialₛ-Diffable : Diffable ⟦_⟧
  Trivialₛ-Diffable = Trivial-delta
    where
      open Generic ⟦_⟧ Sum-eq (dec-eq _≟-A_)

  Trivialₛ-Correct : CandsCorrect ⟦_⟧ Trivialₛ-Diffable
  Trivialₛ-Correct = Trivial-Correct
    where
      open Generic ⟦_⟧ Sum-eq (dec-eq _≟-A_)

  Trivialₛ-CostCorrect : CostCorrect ⟦_⟧ Trivialₛ-Diffable
  Trivialₛ-CostCorrect = Trivial-CostCorrect
    where
      open Generic ⟦_⟧ Sum-eq (dec-eq _≟-A_)
