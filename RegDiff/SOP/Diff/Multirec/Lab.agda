open import Prelude
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

  w1 w3 w2 : rtree

  w1 = fork 3 #

  w3 = fork 1 (fork 3 # % #)

  w2 = fork 4 (fork 1 # % #)


  w1w3 w1w3-norm : Patchμ (T (fs fz)) (T (fs fz))
  w1w3 = diffμ w1 w3

  w1w3-norm 
    = chng
      (Cins {k = fs fz} {fs fz}
       (CX
        (Ap2 1
         (AX
          (fix
           (chng
            (Cins {k = fs fz} {fz}
             (Ci2 (CX (Ap1 ⟨ i1 unit ⟩ (AX (fix (chng (Cmod Scp))))))))))))))


  wlemma : Patchμ-apply-famₗ w1w3-norm w1 ≡ just w3
  wlemma = refl

  wlemma' : Patchμ-apply-famᵣ w1w3-norm w3 ≡ just w1
  wlemma' = refl

  t1 t3 : rtree

  t1 = fork 3 
         ( fork 4 #
         % fork 5 #
         % # )

  t3 = fork 3 
         ( fork 4 #
         % fork 1 (fork 5 # % #)
         % # )


  t1t3 t1t3-norm : Patchμ (T (fs fz)) (T (fs fz))
  t1t3 = diffμ t1 t3
  -- 1652 better diff!
  -- 2185 good align
  -- 4996 bad align
  -- 52545 horrible align

  t1t3-norm
    = chng
     (Cmod
      (S⊗ Scp
       (SX (CX (AX (fix
           (chng
            (Cmod
             (Si2
              (S⊗ Scp
               (SX (CX (AX (fix
                   (chng
                    (Cmod
                     (Si2
                      (S⊗ (SX (CX (AX (fix w1w3-norm))))
                       Scp))))))))))))))))))


  lemma : Patchμ-apply-famₗ t1t3-norm t1 ≡ just t3
  lemma = refl

  lemma' : Patchμ-apply-famᵣ t1t3-norm t3 ≡ just t1
  lemma' = refl
