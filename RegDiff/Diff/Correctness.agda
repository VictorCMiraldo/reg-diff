open import Prelude hiding (_⊔_)
open import Prelude.Vector

open import RegDiff.Diff.Abstract

{-
  Here we prove basic correctness properties
  for our diff primitives.
-}

module RegDiff.Diff.Correctness
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)(tds : VecI Dₐ v)
    where

  open import RegDiff.Diff.Base v eqs tds

  open Dₐ

{- 
  diff source and destination lemmas.
-}

  diff-src-lemma
    : {A : Set}(ty : U)(x y : ⟦ ty ⟧ A)
    → D-src (diff ty x y) ≡ x
  diff-src-lemma I x y = refl
  diff-src-lemma u1 unit unit = refl
  diff-src-lemma (K k) x y = dₐ-src-lemma (ty-diffs k) x y
  diff-src-lemma (ty ⊕ tv) (i1 x) (i1 y) 
    = cong i1 (diff-src-lemma ty x y)
  diff-src-lemma (ty ⊕ tv) (i1 x) (i2 y) 
    = refl
  diff-src-lemma (ty ⊕ tv) (i2 x) (i1 y) 
    = refl
  diff-src-lemma (ty ⊕ tv) (i2 x) (i2 y) 
    = cong i2 (diff-src-lemma tv x y)
  diff-src-lemma (ty ⊗ tv) (x1 , x2) (y1 , y2)
    = cong₂ _,_ (diff-src-lemma ty x1 y1) 
                (diff-src-lemma tv x2 y2)

  diff-dst-lemma
    : {A : Set}(ty : U)(x y : ⟦ ty ⟧ A)
    → D-dst (diff ty x y) ≡ y
  diff-dst-lemma I x y = refl
  diff-dst-lemma u1 unit unit = refl
  diff-dst-lemma (K k) x y = dₐ-dst-lemma (ty-diffs k) x y
  diff-dst-lemma (ty ⊕ tv) (i1 x) (i1 y) 
    = cong i1 (diff-dst-lemma ty x y)
  diff-dst-lemma (ty ⊕ tv) (i1 x) (i2 y) 
    = refl
  diff-dst-lemma (ty ⊕ tv) (i2 x) (i1 y) 
    = refl
  diff-dst-lemma (ty ⊕ tv) (i2 x) (i2 y) 
    = cong i2 (diff-dst-lemma tv x y)
  diff-dst-lemma (ty ⊗ tv) (x1 , x2) (y1 , y2)
    = cong₂ _,_ (diff-dst-lemma ty x1 y1) 
                (diff-dst-lemma tv x2 y2)

{- 
  Application respects src and dst
-}

  apply-lemma 
    : {A : Set}{{eqA : Eq A}}{ty : U}(d : D ty A)
    → apply ty d (D-src d) ≡ just (D-dst d)
  apply-lemma D1 = refl
  apply-lemma {{eq _≟_}} (DA x y) 
    with x ≟ x
  ...| yes _ = refl
  ...| no ¬p = ⊥-elim (¬p refl)
  apply-lemma (DK k x) 
    = dₐ-app-lemma (ty-diffs k) x
  apply-lemma (D⊗ d e) 
    rewrite apply-lemma d
          | apply-lemma e
          = refl
  apply-lemma (Di1 d) 
    rewrite apply-lemma d = refl
  apply-lemma (Di2 d) 
    rewrite apply-lemma d = refl 
  apply-lemma {ty = ty ⊕ tv} (Ds1 x y) 
    with dec-eq ty x x
  ...| yes _ = refl 
  ...| no ¬p = ⊥-elim (¬p refl)
  apply-lemma {ty = ty ⊕ tv} (Ds2 x y)
    with dec-eq tv x x
  ...| yes _ = refl 
  ...| no ¬p = ⊥-elim (¬p refl)
