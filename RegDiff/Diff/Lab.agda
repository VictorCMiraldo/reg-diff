open import Prelude
open import Prelude.Vector

module RegDiff.Diff.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Subtype.Base konstants
    public
  open import RegDiff.Diff.Regular konstants keqs
    public
  open import RegDiff.Diff.Fixpoint konstants keqs
    as F1
  open import RegDiff.Diff.Fixpoint2 konstants keqs
    as F2
  open import RegDiff.Diff.Loc.Regular konstants keqs
    public
  open import RegDiff.Diff.Loc.Fixpoint konstants keqs
    public

  TREE-F : U
  TREE-F = u1 ⊕ (K kℕ) ⊗ I ⊗ I ⊕ (K kℕ) ⊗ I

  TreeNat : Set
  TreeNat = μ TREE-F

  Leaf : TreeNat
  Leaf = ⟨ i1 unit ⟩

  Node : ℕ → TreeNat → TreeNat → TreeNat
  Node e l r = ⟨ i2 (i1 (e , l , r)) ⟩

  Cons : ℕ → TreeNat → TreeNat
  Cons x l = ⟨ i2 (i2 (x , l)) ⟩

  t1 t2 t3 t4 t5 t6 : TreeNat
  t1 = Node 10 Leaf (Cons 5 Leaf)

  t2 = Node 13 (Node 10 Leaf Leaf)
               Leaf

  t3 = Node 1 Leaf (Cons 2 Leaf)
  
  t4 = Node 10 t2 (Cons 5 Leaf)
 
  t5 = Node 1 Leaf t4

  t6 = Cons 3 t4 
  

  p12 : F2.Dμ TREE-F
  p12 = F2.diffμ t1 t2

  p12-1 : F1.Dμ TREE-F
  p12-1 = F1.diffμ (t1 ∷ []) (t2 ∷ [])
{-
  .RegDiff.Diff.Fixpoint.Dμ.Dμ-ins (i2 (i1 (13 , unit , unit)))
(.RegDiff.Diff.Fixpoint.Dμ.Dμ-mod
 (Di2 (Di1 (D⊗ (DK fz 10 10) (D⊗ (DA unit unit) (DA unit unit)))))
 (.RegDiff.Diff.Fixpoint.Dμ.Dμ-mod (Di1 D1)
  (.RegDiff.Diff.Fixpoint.Dμ.Dμ-ins (i1 unit)
   (.RegDiff.Diff.Fixpoint.Dμ.Dμ-del (i2 (i2 (5 , unit)))
    (.RegDiff.Diff.Fixpoint.Dμ.Dμ-mod (Di1 D1)
     .RegDiff.Diff.Fixpoint.Dμ.Dμ-nil))))
-}

  p13 : F2.Dμ TREE-F
  p13 = F2.diffμ t1 t3

  p14 : F2.Dμ TREE-F
  p14 = F2.diffμ t1 t4

  p14-1 : F1.Dμ TREE-F
  p14-1 = F1.diffμ (t1 ∷ []) (t4 ∷ [])

{-
p14-1: 
Dμ.Dμ-mod
(Di2 (Di1 (D⊗ (DK fz 10 10) (D⊗ (DA unit unit) (DA unit unit)))))
(Dμ.Dμ-ins (i2 (i1 (13 , unit , unit)))
 (Dμ.Dμ-ins (i2 (i1 (10 , unit , unit)))
  (Dμ.Dμ-mod (Di1 D1)
   (Dμ.Dμ-ins (i1 unit)
    (Dμ.Dμ-ins (i1 unit)
     (Dμ.Dμ-mod
      (Di2 (Di2 (D⊗ (DK fz 5 5) (DA unit unit))))
      (Dμ.Dμ-mod (Di1 D1)
       Dμ.Dμ-nil)))))))

p14:
Dμ.Dμ-mod
(Di2 (Di1 (D⊗ (DK fz 10 10) (D⊗ (DA unit unit) (DA unit unit)))))
(Dμ.Dμ-ins (i2 (i1 (13 , unit , unit)))
 (Dμ.Dμ-ins (i2 (i1 (10 , unit , unit)))
  (Dμ.Dμ-mod (Di1 D1)
   (Dμ.Dμ-ins (i1 unit)
    (Dμ.Dμ-ins (i1 unit)
     (Dμ.Dμ-mod
      (Di2 (Di2 (D⊗ (DK fz 5 5) (DA unit unit))))
      (Dμ.Dμ-mod (Di1 D1)
       Dμ.Dμ-nil)))))))
-}

  p56 : F2.Dμ TREE-F
  p56 = F2.diffμ t5 t6

  p56-c1 : ℕ
  p56-c1 = F2.costμ p56 -- 67

  p56-manual : F2.Dμ TREE-F
  p56-manual = del (i2 (i1 (1 , unit , unit)))
              (⟨ i1 unit ⟩ ∷
               ⟨
               i2
               (i1
                (10 ,
                 ⟨
                 i2
                 (i1
                  (13 , ⟨ i2 (i1 (10 , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩)) ⟩ , ⟨ i1 unit ⟩))
                 ⟩
                 , ⟨ i2 (i2 (5 , ⟨ i1 unit ⟩)) ⟩))
               ⟩
               ∷ []
               , fs fz)
              (ins (i2 (i2 (3 , unit))) (t4 ∷ [] , fz) 
              (mod (i2 (i1 (10 , unit , unit))) (i2 (i1 (10 , unit , unit))) refl 
              ((mod (i2 (i1 (13 , unit , unit))) (i2 (i1 (13 , unit , unit))) refl 
                (mod (i2 (i1 (10 , unit , unit))) (i2 (i1 (10 , unit , unit))) refl 
                  ((mod (i1 unit) (i1 unit) refl []) ∷ (mod (i1 unit) (i1 unit) refl []) ∷ []) 
               ∷ (mod (i1 unit) (i1 unit) refl []) ∷ [])) 
              ∷ ((mod (i2 (i2 (5 , unit))) (i2 (i2 (5 , unit))) refl 
                ((mod (i1 unit) (i1 unit) refl []) ∷ [])) ∷ []))))

  p56-cM : ℕ
  p56-cM = F2.costμ p56-manual

{-
Dμ.Dμ-del (i2 (i1 (1 , unit , unit)))
(Dμ.Dμ-del (i1 unit)
 (Dμ.Dμ-del (i2 (i1 (10 , unit , unit)))
  (Dμ.Dμ-del (i2 (i1 (13 , unit , unit)))
   (Dμ.Dμ-del (i2 (i1 (10 , unit , unit)))
    (Dμ.Dμ-ins (i2 (i2 (3 , unit)))
     (Dμ.Dμ-ins (i2 (i1 (10 , unit , unit)))
      (Dμ.Dμ-ins (i2 (i1 (13 , unit , unit)))
       (Dμ.Dμ-ins (i2 (i1 (10 , unit , unit)))
        (Dμ.Dμ-mod (Di1 D1)
         (Dμ.Dμ-ins (i1 unit)
          (Dμ.Dμ-ins (i1 unit)
           (Dμ.Dμ-ins (i2 (i2 (5 , unit)))
            (Dμ.Dμ-ins (i1 unit)
             (Dμ.Dμ-del (i1 unit)
              (Dμ.Dμ-del (i1 unit)
               (Dμ.Dμ-del (i2 (i2 (5 , unit)))
                (Dμ.Dμ-del (i1 unit)
                 Dμ.Dμ-nil)))))))))))))))))
-}

  p56' : F1.Dμ TREE-F
  p56' = F1.diffμ (t5 ∷ []) (t6 ∷ [])

  gonutz : F1.Dμ TREE-F × F2.Dμ TREE-F
  gonutz = p56' , p56
