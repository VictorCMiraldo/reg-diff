open import Prelude
open import Prelude.Eq
open import Prelude.Vector

module RegDiff.Diff.Fixpoint.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Fixpoint konstants keqs public
  open import RegDiff.Generic.Eq konstants keqs public

  import RegDiff.Diff.Multirec.Base konstants keqs 
    as DIFF
  -- import RegDiff.Diff.Fixpoint.Domains konstants keqs
  --  as DOMAINS

  LIST-F : Uₙ 1
  LIST-F = u1 ⊕ (K kℕ) ⊗ I

  list : Set
  list = Fix LIST-F

  # : list
  # = ⟨ i1 unit ⟩

  infixr 20 _>_
  _>_ : ℕ → list → list
  x > xs = ⟨ i2 (x , xs) ⟩

  2-3-TREE-F : Uₙ 1
  2-3-TREE-F = u1 ⊕ (K kℕ) ⊗ I ⊗ I ⊕ (K kℕ) ⊗ I ⊗ I ⊗ I

  2-3-Tree : Set
  2-3-Tree = Fix 2-3-TREE-F

  Leaf : 2-3-Tree
  Leaf = ⟨ i1 unit ⟩

  2-Node : ℕ → 2-3-Tree → 2-3-Tree → 2-3-Tree
  2-Node n l r = ⟨ i2 (i1 (n , l , r)) ⟩

  3-Node : ℕ → 2-3-Tree → 2-3-Tree → 2-3-Tree → 2-3-Tree
  3-Node n l m r = ⟨ i2 (i2 (n , l , m , r)) ⟩

  _==_ : 2-3-Tree → Maybe 2-3-Tree → Bool
  _ == nothing = false
  t == just u with t ≟-Fix u 
  ...| yes _ = true
  ...| no  _ = false

  module T1 where
    open DIFF.Internal (LIST-F ∷ []) public

    l0 l1 l2 l3 : list
    l0 = (1 > #)
    l1 = (1 > 4 > #)
    l2 = (3 > 50 > 4 > #)
    l3 = (1 > 50 > 4 > 20 > #)

    s1 : Patchμ (T fz) (T fz)
    s1 = diffμ l0 l1 -- 6
    
  module T2 where
    open DIFF.Internal (2-3-TREE-F ∷ []) public

    k0 k1 k2 : 2-3-Tree
    k0 = Leaf
    k1 = 2-Node 1 Leaf Leaf
    k2 = 3-Node 5 Leaf Leaf Leaf
    k3 = 3-Node 3 k1 k2 k2

    t1 t2 : 2-3-Tree
    t1 = 2-Node 4 k1 k2
    t2 = 3-Node 5 k1 Leaf k2

    r1 r1-computed r2 r2-computed : Patchμ (T fz) (T fz)
    r1 = diffμ t1 t2

    r1-computed 
     = skel
        (Si2
         (SX
          (chng
           (Cmod
            (Ci2
             (CX
              (Ci1
               (CX
                (A⊗ (AX (set (4 , 5)))
                 (A⊗ (AX (fix (skel Scp)))
                  (Ap2 ⟨ i1 unit ⟩ (AX (fix (skel Scp))))))))))))))

    r2 = diffμ k1 k3

    r2-computed 
      = chng
        (Cins {k = fz} {k' = fz}
         (Ci2
          (Ci2
           (CX
            (Ap2 3
             (Ap1
              (⟨ i2 (i2 (5 , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩)) ⟩ ,
               ⟨ i2 (i2 (5 , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩)) ⟩)
              (AX (fix (skel Scp)))))))))

  open T2 public
