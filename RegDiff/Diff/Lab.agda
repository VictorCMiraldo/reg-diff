open import Prelude
open import Prelude.Vector

module RegDiff.Diff.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Subtype.Base konstants
    public
  open import RegDiff.Diff.Base 
      konstants 
      keqs
    public
  open import RegDiff.Diff.Loc.Base konstants keqs
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

  t1 t2 t3 : TreeNat
  t1 = Node 10 Leaf (Cons 5 Leaf)

  t2 = Node 13 (Node 10 Leaf Leaf)
               Leaf

  t3 = Node 1 Leaf (Cons 2 Leaf)

  

  p12 : Dμ TREE-F
  p12 = diffμ (t1 ∷ []) (t2 ∷ [])

  p13 : Dμ TREE-F
  p13 = diffμ (t1 ∷ []) (t3 ∷ [])

  p13-1 : Dμ TREE-F
  p13-1 = Dμ-ins (i2 (i1 (1 , unit , unit)))
          (Dμ-del (i2 (i1 (10 , unit , unit)))
          (Dμ-mod (Di1 D1)
            (Dμ-mod (Di2 (Di2 (D⊗ (DK fz 5 2) (DA unit unit))))
              (Dμ-mod (Di1 D1) Dμ-nil))))

  p13-hd : D TREE-F Unit
  p13-hd = (Di2 (Di1 (D⊗ (DK fz 1 10) (D⊗ (DA unit unit) (DA unit unit)))))
  p13-1' p13-2' : Dμ TREE-F
  p13-2' = (Dμ-mod (Di1 D1)
            (Dμ-mod (Di2 (Di2 (D⊗ (DK fz 5 2) (DA unit unit))))
              (Dμ-mod (Di1 D1) Dμ-nil)))
  p13-1' = Dμ-mod p13-hd
           p13-2'
          

  

  p13-1'' : Lμ TREE-F
  p13-1'' = goμ p13-1'

  p12-2 p12-3 : Dμ TREE-F
  
  p12-3 = (Dμ-mod
          (Di2 (Di1 (D⊗ (DK fz 10 10) (D⊗ (DA unit unit) (DA unit unit)))))
          (Dμ-mod (Di1 D1)
           (Dμ-ins (i1 unit)
            (Dμ-del (i2 (i2 (5 , unit))) (Dμ-mod (Di1 D1) Dμ-nil)))))

  p12-4 : Dμ TREE-F
  p12-4 = (Dμ-mod
          (Di2 (Di1 (D⊗ (DK fz 10 10) (D⊗ (DA unit unit) (DA unit unit)))))
          (Dμ-mod (Di1 D1)
           (Dμ-ins (i1 unit)
            (Dμ-del (i2 (i2 (5 , unit))) (Dμ-mod (Di1 D1) 
            (Dμ-ins (i1 unit) Dμ-nil))))))

  p12-2 = Dμ-ins (i2 (i1 (13 , unit , unit)))
          p12-3

  r3 : Maybe (List TreeNat)
  r3 = applyμ p12 (t1 ∷ [])
