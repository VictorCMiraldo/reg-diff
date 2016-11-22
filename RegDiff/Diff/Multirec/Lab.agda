open import Prelude hiding (⊥)
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.RelCalc.Base

module RegDiff.Diff.Multirec.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Multirec konstants public
  open import RegDiff.Generic.Eq konstants keqs public

  import RegDiff.Diff.Multirec.Base konstants keqs 
    as DIFF
  import RegDiff.Diff.Multirec.Apply konstants keqs
    as APPLY
  import RegDiff.Diff.Multirec.Domain konstants keqs
    as DOMAIN

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
  rtree = Fix RTREE-NAT (fs fz)

  # : list
  # = ⟨ i1 unit ⟩

  _%_ : rtree → list → list
  x % xs = ⟨ i2 (x , xs) ⟩

  infixr 20 _%_

  fork : ℕ → list → rtree
  fork n xs = ⟨ n , xs ⟩

  open DIFF.Internal RTREE-NAT public
  open APPLY.Internal RTREE-NAT public
  open import RegDiff.Diff.Regular.Domain konstants keqs (Fix RTREE-NAT) DIFF.WB-FAM
    public
  open DOMAIN.Internal RTREE-NAT public

  t1 t3 : rtree

  t1 = fork 3 
         ( fork 4 #
         % fork 5 #
         % # )

  t3 = fork 3 
         ( fork 4 #
         % fork 1 (fork 5 # % #)
         % # )


  t1t3 t1t3-norm t1t3-computed : Patchμ (T (fs fz)) (T (fs fz))
  t1t3 = diffμ t1 t3

  t1t3-norm = skel
               (S⊗ Scp
                (SX
                 (fix {k = fz} {k' = fz}
                  (skel
                   (Si2
                    (S⊗ Scp
                     (SX
                      (fix {k = fz} {k' = fz}
                       (skel
                        (Si2
                         (S⊗
                          (SX
                           (fix {k = fs fz} {k' = fs fz}
                            (chng
                             (Cins {k = fs fz} {k' = fs fz}
                              (CX
                               (Ap2 {ty = I (fs fz)} {tv = I fz} {tw = K kℕ} 1
                                (AX
                                 (fix {k = fs fz} {k' = fz}
                                  (chng
                                   (Cins {k = fs fz} {k' = fz}
                                     (Ci2 (CX (Ap1 {ty = I (fs fz)} {tv = I (fs fz)} {tw = I fz}
                                       ⟨ i1 unit ⟩ (AX (fix (skel Scp))))))))))))))))
                          Scp)))))))))))

  t1t3-computed
    = skel
      (S⊗ Scp
       (SX
        (fix
         (skel
          (Si2
           (S⊗ Scp
            (SX
             (fix
              (skel
               (Si2
                (S⊗
                 (SX
                  (fix
                   (skel
                    (S⊗ (SX (chng (Cmod (CX (AX (set (5 , 1)))))))
                     (SX
                      (fix
                       (chng
                        (Cins {k = fz} {fz}
                         (Ci2 (CX (Ap2 {ty = I fz} {tv = I fz} {tw = I (fs fz)}
                           ⟨ 5 , ⟨ i1 unit ⟩ ⟩ (AX (fix (skel Scp))))))))))))))
                 Scp)))))))))))

  lemma : Patchμ-apply-famₗ t1t3-norm t1 ≡ just t3
  lemma = refl

  lemma' : Patchμ-apply-famᵣ t1t3-norm t3 ≡ just t1
  lemma' = refl

  w1 w3 : rtree

  w1 = fork 3 #

  w3 = fork 4 (fork 3 # % #)


  w1w3 w1w3-norm w1w3-computed : Patchμ (T (fs fz)) (T (fs fz))
  w1w3 = diffμ w1 w3

  w1w3-norm 
    = chng
       (Cins {k = fs fz} {k' = fs fz}
        (CX
         (Ap2 {ty = I (fs fz)} {tv = I fz} {tw = K kℕ} 4
          (AX
           (fix {k = fs fz} {k' = fz}
            (chng
             (Cins {k = fs fz} {k' = fz}
               (Ci2 (CX (Ap1 {ty = I (fs fz)} {tv = I (fs fz)} {tw = I fz}
                 ⟨ i1 unit ⟩ (AX (fix (skel Scp)))))))))))))


  -- Note the (skel (S⊗ (SX ...) (SX ...))) this is a pointless spine!
  -- we don't want to allow such a spine. If both target and source are
  -- a product with no common parts, this product should be handled
  -- by alignment!
  w1w3-computed
    = skel
      (S⊗ (SX (chng (Cmod (CX (AX (set (3 , 4)))))))
       (SX
        (fix
         (chng
          (Cins {k = fz} {fz}
           (Ci2 (CX (Ap2 ⟨ 3 , ⟨ i1 unit ⟩ ⟩ (AX (fix (skel Scp)))))))))))

  wlemma : Patchμ-apply-famₗ w1w3-norm w1 ≡ just w3
  wlemma = refl

  wlemma' : Patchμ-apply-famᵣ w1w3-norm w3 ≡ just w1
  wlemma' = refl

{-  
  w1 w3 : rtree

  w1 = fork 3 ( fork 4 # % # )

  w3 = fork 3 ( fork 1 (fork 4 # % #) % # )


  w1w3 w1w3-norm w1w3-computed : Patchμ (T (fs fz)) (T (fs fz))
  w1w3 = diffμ w1 w3

  w1w3-norm 
    = skel (S⊗ Scp (SX (fix (skel (Si2 (S⊗ ss Scp))))))
    where
      ss : S Patchμ (I (fs fz))
      ss = SX (fix (chng (Cins {k = fs fz} {fs fz}
           (CX (Ap2 1 (AX (fix (chng (Cins {k = fs fz} {fz}
           (Ci2 (CX (Ap1 # (AX (fix (skel (Scp {ty = T (fs fz)}))))))))))))))))

  w1w3-computed
    = skel
      (S⊗ Scp
       (SX
        (fix
         (skel
          (Si2
           (S⊗
            (SX
             (fix
              (skel
               (S⊗ (SX (chng (Cmod (CX (AX (set (4 , 1)))))))
                (SX
                 (fix
                  (chng
                   (Cins {k = fz} {fz}
                    (Ci2 (CX (Ap2 ⟨ 4 , ⟨ i1 unit ⟩ ⟩ 
                         (AX (fix (skel (Scp {ty = T fz}))))))))
                    )))))))
            Scp))))))

  wlemma : Patchμ-apply-famₗ w1w3-norm w1 ≡ just w3
  wlemma = refl

  wlemma' : Patchμ-apply-famᵣ w1w3-norm w3 ≡ just w1
  wlemma' = refl
-}
  
