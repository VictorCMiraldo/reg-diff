open import Prelude
open import Prelude.Vector

open import RegDiff.Diff.Abstract

module RegDiff.Diff.Lab where

  open import RegDiff.Generic.Lab
  open import RegDiff.Diff.Base 
      konstants 
      keqs
      (trivial-diff ∷ trivial-diff ∷ [])
    public

  TREE-F : U
  TREE-F = u1 ⊕ (K kℕ) ⊗ I ⊗ I

  TreeNat : Set
  TreeNat = μ TREE-F

  Leaf : TreeNat
  Leaf = ⟨ i1 unit ⟩

  Node : ℕ → TreeNat → TreeNat → TreeNat
  Node e l r = ⟨ i2 (e , l , r) ⟩

  t1 t2 : TreeNat
  t1 = Node 10 Leaf Leaf

  t2 = Node 13 (Node 10 Leaf Leaf)
               Leaf

  p12 : Dμ TREE-F
  p12 = diffμ (t1 ∷ []) (t2 ∷ [])

  r3 : Maybe (List TreeNat)
  r3 = applyμ p12 (t1 ∷ [])
