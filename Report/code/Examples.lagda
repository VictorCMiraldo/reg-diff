\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector

module Report.code.Examples where
\end{code}


\begin{code}
  module Examples1 where
    open import RegDiff.Generic.Konstants
    open import RegDiff.Generic.Fixpoint konstants keqs public
    open import RegDiff.Generic.Eq konstants keqs public

    LIST-F : Uₙ 1
    LIST-F = u1 ⊕ (K kℕ) ⊗ I

    list : Set
    list = Fix LIST-F

    # : list
    # = ⟨ i1 unit ⟩

    infixr 20 _>_
    _>_ : ℕ → list → list
    x > xs = ⟨ i2 (x , xs) ⟩

    import RegDiff.Diff.Fixpoint.Base konstants keqs 
      as DIFF
    open DIFF.Internal LIST-F public
\end{code}
%<*Example-list-2>
\begin{code}
    s0 : Patchμ LIST-F LIST-F
    s0 = diffμ (5 > 8 > 13 > 21 > #) (8 > 13 > 21 > #)

    s0-norm : Patchμ LIST-F LIST-F
    s0-norm = chng (Cdel (Ci2ᵒ (CX (Ap2ᵒ 5 (AX (fix (skel Scp)))))))
\end{code}
%</Example-list-2>
%<*Example-list-1>
\begin{code}
    l0 l1 : list
    l0 = (3 > 50 > 4 > #)
    l1 = (1 > 50 > 4 > 20 > #)

    s1 : Patchμ LIST-F LIST-F
    s1 = diffμ l0 l1

    s1-normalized : Patchμ LIST-F LIST-F
    s1-normalized 
      = skel
        (Si2
         (S⊗ (SX (chng (Cmod (CX (AX (set (3 , 1)))))))
          (SX
           (fix
            (skel
             (Si2
              (S⊗ Scp
               (SX
                (fix
                 (skel
                  (Si2
                   (S⊗ Scp
                    (SX
                     (fix
                      (chng
                       (Cins (Ci2 (CX (Ap2 20 (AX (fix (skel Scp))))))))))))))))))))))

\end{code}
%</Example-list-1>

%<*Example-2-3-tree-full>
\begin{code}
  module Examples2 where
    open import RegDiff.Generic.Konstants
    open import RegDiff.Generic.Fixpoint konstants keqs public
    open import RegDiff.Generic.Eq konstants keqs public

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

    import RegDiff.Diff.Fixpoint.Base konstants keqs 
      as DIFF
    open DIFF.Internal 2-3-TREE-F public

    k0 k1 k2 : 2-3-Tree
    k0 = Leaf
    k1 = 2-Node 1 Leaf Leaf
    k2 = 3-Node 5 Leaf Leaf Leaf
    k3 = 3-Node 3 k1 k2 k2

    t1 t2 : 2-3-Tree
    t1 = 2-Node 4 k1 k2
    t2 = 3-Node 5 k1 Leaf k2
\end{code}
%</Example-2-3-tree-full>
%<*Example-2-3-patches>
\begin{code}
    r1 r2 : Patchμ 2-3-TREE-F 2-3-TREE-F
    r1 = diffμ t1 t2
    r2 = diffμ k1 k3
\end{code}
%</Example-2-3-patches>
%<*Example-2-3-tree-norm1>
\begin{code}
    r1-normalized : Patchμ 2-3-TREE-F  2-3-TREE-F
    r1-normalized
      = skel
        (Si2
         (SX
          (chng
           (Cmod
            (Ci2
             (Ci1ᵒ
              (CX
               (A⊗ (AX (set (4 , 5)))
                (A⊗ (AX (fix (skel Scp)))
                 (Ap2 ⟨ i1 unit ⟩ (AX (fix (skel Scp)))))))))))))
\end{code}
%</Example-2-3-tree-norm1>
%<*Example-2-3-tree-norm2>
\begin{code}
    r2-normalized : Patchμ 2-3-TREE-F 2-3-TREE-F
    r2-normalized
      = chng
        (Cins
         (Ci2
          (Ci2
           (CX
            (Ap2 3
             (Ap1
              (⟨ i2 (i2 (5 , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩)) ⟩ ,
               ⟨ i2 (i2 (5 , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩ , ⟨ i1 unit ⟩)) ⟩)
              (AX (fix (skel Scp)))))))))
\end{code}
%</Example-2-3-tree-norm2>


\begin{code}
  module Examples3 where
    open import RegDiff.Generic.Konstants
    open import RegDiff.Generic.Multirec konstants public
    open import RegDiff.Generic.Eq konstants keqs public

    import RegDiff.Diff.Multirec.Base konstants keqs 
      as DIFF
    import RegDiff.Diff.Multirec.Apply konstants keqs
      as APPLY

    RTREE-NAT : Fam 2
    RTREE-NAT
      = u1 ⊕ I (fs fz) ⊗ I fz  
      ∷ K kℕ ⊗ I fz 
      ∷ []

    list : Set
    list = Fix RTREE-NAT fz

    rtreeᵢ : Fin 2
    rtreeᵢ = fs fz

    rtree : Set
    rtree = Fix RTREE-NAT rtreeᵢ

    # : list
    # = ⟨ i1 unit ⟩

    _>_ : rtree → list → list
    x > xs = ⟨ i2 (x , xs) ⟩

    infixr 20 _>_

    fork : ℕ → list → rtree
    fork n xs = ⟨ n , xs ⟩

    open DIFF.Internal RTREE-NAT public
    open APPLY.Internal RTREE-NAT public

    t1 t2 : rtree
    t1 = fork 3 
           ( fork 4 #
           > fork 5 #
           > # )

    t2 = fork 1 
           ( fork 4 #
           > fork 8 (fork 5 # > #)
           > # )

    r1 : Patchμ (T rtreeᵢ) (T rtreeᵢ)
    r1 = diffμ t1 t2

    r1-normalized : Patchμ (T rtreeᵢ) (T rtreeᵢ)
    r1-normalized
      = {!!}

    r1-expected : Patchμ (T rtreeᵢ) (T rtreeᵢ)
    r1-expected 
      = {!!}

    res : Maybe rtree
    res = Patchμ-apply-famₗ r1-expected t1

    good : Patchμ-apply-famₗ r1-expected t1 ≡ Patchμ-apply-famₗ r1-normalized t1
    good = {!res!}
\end{code}
