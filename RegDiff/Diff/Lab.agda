open import Prelude
open import Prelude.Vector

module RegDiff.Diff.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Subtype.Base konstants
    public
  open import RegDiff.Diff.Regular konstants keqs
    public
  open import RegDiff.Diff.Fixpoint konstants keqs
    public
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

  _==_ : TreeNat → Maybe TreeNat → Maybe Bool
  t == nothing = nothing
  t == just u  = just (dec-elim (const true) (const false)
                      (dec-eqμ t u))

  t1 t2 t3 t4 t5 t6 : TreeNat
  t1 = Node 10 Leaf Leaf

  t2 = Node 13 (Cons 3 Leaf) (Cons 2 Leaf)

  t3 = Node 1 Leaf (Cons 2 Leaf)
  
  t4 = Node 10 t2 (Cons 5 Leaf)
 
  t5 = Node 1 Leaf t4

  t6 = Cons 3 t4 
  
  d13 d32 d12 : Dμ TREE-F
  d13 = diffμ-⋁ t1 t3
  d32 = diffμ-⋁ t3 t2
  d12 = diffμ-⋁ t1 t2

  l13 l32 l12 : Lμ TREE-F
  l13 = goμ d13
  l32 = goμ d32
  l12 = goμ d12
