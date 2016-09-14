open import Prelude
open import Prelude.Vector

open import RegDiff.Generic.Konstants

module RegDiff.Generic.Lab where

  open import RegDiff.Generic.Base konstants
    public
  open import RegDiff.Generic.Subtype.Base konstants
    public
  open import RegDiff.Generic.Serialization.TypeSafe konstants
    public

  TREE-F : U
  TREE-F = u1 ⊕ (K kℕ) ⊗ I ⊗ I

  TreeNat : Set
  TreeNat = μ TREE-F

  Leaf : TreeNat
  Leaf = ⟨ i1 unit ⟩

  Node : ℕ → TreeNat → TreeNat → TreeNat
  Node e l r = ⟨ i2 (e , l , r) ⟩

  rootnat : Dirμ TREE-F (K kℕ)
  rootnat = hd (right (fst here))

  leftnat : Dirμ TREE-F (K kℕ)
  leftnat = tl (right (snd (fst here))) rootnat

  t1 t2 : TreeNat
  t1 = Node 10 Leaf Leaf

  t2 = Node 13 (Node 10 Leaf Leaf)
               Leaf

  t1s : μW TREE-F
  t1s = μ-w t1
