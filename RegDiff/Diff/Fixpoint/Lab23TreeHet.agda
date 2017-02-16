open import Prelude hiding (⊥)
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.RelCalc.Base
open import Prelude.List.All

module RegDiff.Diff.Fixpoint.Lab23TreeHet where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Eq konstants keqs as EQ
  open import RegDiff.Generic.Multirec konstants
    renaming (I to I')
  import RegDiff.Diff.Multirec.Base konstants keqs 
    as DIFF
  import RegDiff.Diff.Multirec.Apply konstants keqs 
    as APPLY

  I : Atom 1
  I = I' fz

  2-3-TREE-F : Sum 1
  2-3-TREE-F = u1 
             ⊕ (K kBool) ⊗ I ⊗ I ⊗ [] 
             ⊕ (K kℕ) ⊗ I ⊗ I ⊗ I ⊗ [] ⊕ []

  2-3-Tree : Set
  2-3-Tree = Fix (2-3-TREE-F ∷ []) fz

  %leaf %2-node %3-node : Constr 2-3-TREE-F
  %leaf = fz
  %2-node = fs fz
  %3-node = fs (fs fz)

  Leaf : 2-3-Tree
  Leaf = ⟨ i1 unit ⟩

  2-Node : Bool → 2-3-Tree → 2-3-Tree → 2-3-Tree
  2-Node n l r = ⟨ i2 (i1 (n , l , r , unit)) ⟩

  3-Node : ℕ → 2-3-Tree → 2-3-Tree → 2-3-Tree → 2-3-Tree
  3-Node n l m r = ⟨ i2 (i2 (i1 (n , l , m , r , unit))) ⟩

  _==_ : 2-3-Tree → Maybe 2-3-Tree → Bool
  _ == nothing = false
  t == just u with t ≟ u 
  ...| yes _ = true
  ...| no  _ = false

  t1 t2 t3 : 2-3-Tree
  t1 = 2-Node true Leaf Leaf
  t2 = 3-Node 3 Leaf Leaf Leaf
  t3 = 3-Node 5 Leaf Leaf (2-Node false Leaf Leaf)

  k1 k2 k3 k4 : 2-3-Tree
  k1 = 2-Node false t1 t2
  k2 = 3-Node 3 t1 Leaf t2
  k3 = 2-Node false t3 t3
  k4 = 3-Node 3 t3 Leaf t3

  open DIFF.Internal  (2-3-TREE-F ∷ []) public
  open APPLY.Internal (2-3-TREE-F ∷ []) public

  d12 d12-expected : Patchμ (T fz) (T fz)
  d12 = diffμ k1 k2

  d12-expected
    = skel
      (Schg %2-node %3-node
        (Adel false
        (Ains 3
        (AX (fix (skel Scp))
        (Ains ⟨ i1 unit ⟩ (AX (fix (skel Scp)) A0))))))

  d12-correct : d12 ≡ d12-expected
  d12-correct = refl

  d12-apply : Patchμ-app d12 k3 ≡ just k4
  d12-apply = refl
