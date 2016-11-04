open import Prelude
open import Prelude.Eq

module RegDiff.Diff.Fixpoint.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Base konstants public
  open import RegDiff.Generic.Eq konstants keqs public

  import RegDiff.Diff.Fixpoint.Base konstants keqs 
    as DIFF
  -- import RegDiff.Diff.Fixpoint.Domains konstants keqs
  --  as DOMAINS

  LIST-F : U
  LIST-F = u1 ⊕ (K kℕ) ⊗ I

  list : Set
  list = μ LIST-F

  # : list
  # = ⟨ i1 unit ⟩

  infixr 20 _>_
  _>_ : ℕ → list → list
  x > xs = ⟨ i2 (x , xs) ⟩

  2-3-TREE-F : U
  2-3-TREE-F = u1 ⊕ (K kℕ) ⊗ I ⊗ I ⊕ (K kℕ) ⊗ I ⊗ I ⊗ I

  2-3-Tree : Set
  2-3-Tree = μ 2-3-TREE-F

  Leaf : 2-3-Tree
  Leaf = ⟨ i1 unit ⟩

  2-Node : ℕ → 2-3-Tree → 2-3-Tree → 2-3-Tree
  2-Node n l r = ⟨ i2 (i1 (n , l , r)) ⟩

  3-Node : ℕ → 2-3-Tree → 2-3-Tree → 2-3-Tree → 2-3-Tree
  3-Node n l m r = ⟨ i2 (i2 (n , l , m , r)) ⟩

  _==_ : 2-3-Tree → Maybe 2-3-Tree → Bool
  _ == nothing = false
  t == just u with dec-eqμ t u 
  ...| yes _ = true
  ...| no  _ = false

  module T1 where
    open DIFF.Internal LIST-F public

    l0 l1 l2 l3 : list
    l0 = (1 > #)
    l1 = (1 > 4 > #)
    l2 = (1 > 50 > 4 > #)
    l3 = (1 > 50 > 4 > 20 > #)

    s1 : List (Patchμ LIST-F)
    s1 = diffμ l2 l3

{-
  module T2 where
    open DIFF.Internal 2-3-TREE-F public

    k0 k1 k2 : 2-3-Tree
    k0 = Leaf
    k1 = 2-Node 1 Leaf Leaf
    k2 = 3-Node 5 Leaf Leaf Leaf
    k3 = 3-Node 3 k1 k2 k2

    t1 t2 : 2-3-Tree
    t1 = 2-Node 4 k1 k2
    t2 = 3-Node 5 k1 Leaf k2

    r1 r2 : List (Patchμ 2-3-TREE-F)
    r1 = diffμ t1 t2
    r2 = diffμ k1 k3
-}
  open T1 public
