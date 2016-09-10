open import Prelude
open import Prelude.Vector

module RegDiff.Diff.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Diff.Base 
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

  t1 t2 : TreeNat
  t1 = Node 10 Leaf (Cons 5 Leaf)

  t2 = Node 13 (Node 10 Leaf Leaf)
               Leaf

  p12 : Dμ ⊥' TREE-F
  p12 = diffμ (t1 ∷ []) (t2 ∷ [])

  r3 : Maybe (List TreeNat)
  r3 = applyμ p12 (t1 ∷ [])
