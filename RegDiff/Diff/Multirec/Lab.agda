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
  -- open APPLY.Internal RTREE-NAT public
  open import RegDiff.Diff.Regular.Domain konstants keqs (Fix RTREE-NAT) DIFF.WB-FAM
    public
  open DOMAIN.Internal RTREE-NAT public

  t1 t2 t3 : rtree
  t1 = fork 3 
         ( fork 4 #
         % fork 5 #
         % # )

  t2 = fork 1 
         ( fork 4 #
         % fork 8 #
         % # )

  t3 = fork 3 
         ( fork 4 #
         % fork 6 #
         % fork 5 (fork 1 # % #)
         % # )
