open import Prelude hiding (⊥)
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.RelCalc.Base
open import Prelude.ListI

module RegDiff.Diff.Fixpoint.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Fixpoint konstants keqs
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
    public
  open import RegDiff.Generic.Eq konstants keqs public

  import RegDiff.Diff.Multirec.Base konstants keqs 
    as DIFF

  LIST-F : σπ 1
  LIST-F = u1 ⊕ (K kℕ) ⊗ I ⊗ [] ⊕ []

  list : Set
  list = Fix LIST-F

  # : list
  # = ⟨ i1 unit ⟩

  infixr 20 _>_
  _>_ : ℕ → list → list
  x > xs = ⟨ i2 (i1 (x , xs , unit)) ⟩

  2-3-TREE-F : σπ 1
  2-3-TREE-F = u1 ⊕ (K kℕ) ⊗ I ⊗ I ⊗ [] ⊕ (K kℕ) ⊗ I ⊗ I ⊗ I ⊗ [] ⊕ []

  2-3-Tree : Set
  2-3-Tree = Fix 2-3-TREE-F

  Leaf : 2-3-Tree
  Leaf = ⟨ i1 unit ⟩

  2-Node : ℕ → 2-3-Tree → 2-3-Tree → 2-3-Tree
  2-Node n l r = ⟨ i2 (i1 (n , l , r , unit)) ⟩

  3-Node : ℕ → 2-3-Tree → 2-3-Tree → 2-3-Tree → 2-3-Tree
  3-Node n l m r = ⟨ i2 (i2 (i1 (n , l , m , r , unit))) ⟩

  _==_ : 2-3-Tree → Maybe 2-3-Tree → Bool
  _ == nothing = false
  t == just u with t ≟-Fix u 
  ...| yes _ = true
  ...| no  _ = false

  module T1 where
    open DIFF.Internal (LIST-F ∷ []) public

    l0 l0' l1 l2 l3 l4 : list
    l0 = (1 > #)
    l0' = (1 > 5 > #)
    l1 = (1 > 7 > #)
    l2 = (3 > 50 > 4 > #)
    l3 = (1 > 50 > 4 > 20 > #)
    l4 = (5 > 1 > #)

    s1 : Patchμ (T fz) (T fz)
    s1 = diffμ l3 l2 -- 6

    s2 : Patchμ (T fz) (T fz)
    s2 = diffμ l4 l0 -- 6

    cost1-ex1 cost1-ex2 : Patchμ (T fz) (T fz)
    cost1-ex1 = {!diffμ* l4 l0!}
    cost1-ex2 = {!!}
{-
    cost2-ex1 cost2-ex2 : Patchμ (T fz) (T fz)
    cost2-ex1 = skel
         (Scns (fs fz)
          (AX (set (i1 (1 , unit) , i1 (3 , unit))) A0 ∷
           (AX
            (fix
             (skel
              (Scns (fs fz)
               (AX (set (i1 (50 , unit) , i1 (50 , unit))) A0 ∷
                (AX
                 (fix
                  (skel
                   (Scns (fs fz)
                    (AX (set (i1 (4 , unit) , i1 (4 , unit))) A0 ∷
                     (AX (fix (del (fs fz) (Ap1 20 (AX (fix (skel Scp)) A0)))) A0 ∷
                      [])))))
                 A0
                 ∷ [])))))
            A0
            ∷ [])))
    cost2-ex2 = del (fs fz) (Ap1 5 (AX (fix (skel Scp)) A0))
-}
{-
  module T2 where
    open DIFF.Internal (2-3-TREE-F ∷ []) public
    -- open DOMAIN.Internal (2-3-TREE-F ∷ []) public

    k0 k1 k2 : 2-3-Tree
    k0 = Leaf
    k1 = 2-Node 1 Leaf Leaf
    k2 = 3-Node 5 Leaf Leaf Leaf
    k3 = 3-Node 3 k1 k2 k2

    t1 t2 : 2-3-Tree
    t1 = 2-Node 4 k1 k2
    t2 = 3-Node 5 k1 Leaf k2

    r1 r2 h1 h2 h3 : Patchμ (T fz) (T fz)
    r1 = diffμ t1 t2
    -- 460 with good align
    -- 3971 with bad align
    -- 40591 with horrible align (align-exp + heterogeneous set)

    -- 905 sop
    -- 853 new sop

    -- 2889 new sop2

    h1 = skel
     (Schg (fs fz) (fs (fs fz))
      (AX (set (i1 (4 , unit) , i1 (5 , unit)))
       (AX (fix (skel Scp)) (Ap1ᵒ ⟨ i1 unit ⟩ (AX (fix (skel Scp)) A0)))))

    h3 = {!diffμ k1 k3!}

    r2 = diffμ k1 k3
    -- 74  with good align
    -- 471 with bad align
    -- 4276 with horrible align

    -- 128 sop
    -- 128 new sop

    h2 = ins (fs (fs fz))
       (Ap1ᵒ 3
        (AX (fix (skel Scp))
         (Ap1ᵒ
          ⟨ i2 (i2 (i1 (5 , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩ , unit)))
          ⟩
          (Ap1ᵒ
           ⟨ i2 (i2 (i1 (5 , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩ , unit)))
           ⟩
           A0))))
-}
{-
    r1-computed
      = chng
        (Cmod
         (Si2
          (SX
           (Ci2
            (Ci1ᵒ
             (CX
              (A⊗ (AX (set (4 , 5)))
               (A⊗ (AX (fix (chng (Cmod Scp))))
                (Ap2 ⟨ i1 unit ⟩ (AX (fix (chng (Cmod Scp)))))))))))))

    r2-computed
      = chng
        (Cins
         (Ci2
          (Ci2
           (CX
            (Ap2 3
             (Ap1
              (⟨ i2 (i2 (5 , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩)) ⟩ ,
               ⟨ i2 (i2 (5 , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩)) ⟩)
              (AX (fix (chng (Cmod Scp))))))))))


    still-ok-1 : r1 ≡ r1-computed
    still-ok-1 = refl

    still-ok-2 : r2 ≡ r2-computed
    still-ok-2 = refl
-}
 
  open T1 public
