open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.PartialFuncs.Base

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
      D-delta : Diffable ⟦_⟧
      D-delta = record 
        { P = delta ⟦_⟧ 
        ; cands = λ x y → (x , y) ∷ [] 
        ; apply = Δ-apply ⟦_⟧ eqA eqP 
        ; cost = cost-delta ⟦_⟧ eqA eqP 
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
                    → IsCand D-delta x y (x , y)
      lemma-cands-1 {a} {b} x y with eqA a b
      ...| no _ = lemma-singl-correct x y
      lemma-cands-1 {a} {.a} x y 
         | yes refl with eqP a x y
      ...| no  _ = lemma-singl-correct x y
      ...| yes p = cong just p

      lemma-cost-1 : {a b : A}(x : ⟦ a ⟧)(y : ⟦ b ⟧)(p q : P D-delta a b)
                   → IsCand D-delta x y p
                   → IsCand D-delta x y q
                   → cost D-delta p ≡ cost D-delta q 
                   → apply D-delta p ≡ apply D-delta q
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

      lemma-cost-2 : {a b : A}(x : ⟦ a ⟧)(y : ⟦ b ⟧)(p q : P D-delta a b)
                   → IsCand D-delta x y p
                   → IsCand D-delta x y q
                   → cost D-delta p ≤ cost D-delta q 
                   → apply D-delta q ≼* apply D-delta p
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
      diffable-delta-ok 
        : IsDiff ⟦_⟧ D-delta
      diffable-delta-ok = record
        { candidates-ok = λ x y → lemma-cands-1 x y ∷ []
        ; candidates-nonnil = λ {a} {b} x y → s≤s z≤n
        ; cost-eq = lemma-cost-1
        ; cost-order = lemma-cost-2
        }

  -- Lastly, we instantiate to our specifics!

  --   ATOMS
  --   #####
  Δₐ-Diffable : Diffable ⟦_⟧ₐ
  Δₐ-Diffable = D-delta
    where
      open Generic ⟦_⟧ₐ Atom-eq (dec-eqₐ _≟-A_) 

  IsDiff-Δₐ : IsDiff ⟦_⟧ₐ Δₐ-Diffable
  IsDiff-Δₐ = diffable-delta-ok
    where
      open Generic ⟦_⟧ₐ Atom-eq (dec-eqₐ _≟-A_)

 
  --   PRODUCTS
  --   ########
  Δₚ-Diffable : Diffable ⟦_⟧ₚ
  Δₚ-Diffable = D-delta
    where
      open Generic ⟦_⟧ₚ π-eq (dec-eqₚ _≟-A_)

  IsDiff-Δₚ : IsDiff ⟦_⟧ₚ Δₚ-Diffable
  IsDiff-Δₚ = diffable-delta-ok
    where
      open Generic ⟦_⟧ₚ π-eq (dec-eqₚ _≟-A_) 


  --   SUMS
  --   ####
  Δₛ-Diffable : Diffable ⟦_⟧
  Δₛ-Diffable = D-delta
    where
      open Generic ⟦_⟧ σπ-eq (dec-eq _≟-A_)

  IsDiff-Δₛ : IsDiff ⟦_⟧ Δₛ-Diffable
  IsDiff-Δₛ = diffable-delta-ok
    where
      open Generic ⟦_⟧ σπ-eq (dec-eq _≟-A_)
