open import Prelude
open import Prelude.Vector

module RegDiff.Diff.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Subtype.Base konstants
    public
  open import RegDiff.Diff.Regular
      konstants 
      keqs
    public
  open import RegDiff.Diff.Fixpoint2
      konstants 
      keqs
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
  p12 = diffμ t1 t2

  p13 : Dμ TREE-F
  p13 = diffμ t1 t3
