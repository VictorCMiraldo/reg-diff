open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.RelCalc.Base
open import Prelude.ListI

module RegDiff.Diff.Multirec.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Multirec konstants 
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
    public
  open import RegDiff.Generic.Eq konstants keqs public

  import RegDiff.Diff.Multirec.Base konstants keqs 
    as DIFF
{-
  import RegDiff.Diff.Multirec.Apply konstants keqs
    as APPLY
  import RegDiff.Diff.Multirec.Domain konstants keqs
    as DOMAIN
-}
  RTREE-NAT : Fam 2
  RTREE-NAT
    = u1 ⊕ I (fs fz) ⊗ I fz ⊗ [] ⊕ []
    ∷ K kℕ ⊗ I fz ⊗ [] ⊕ []
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
  x % xs = ⟨ i2 (i1 (x , xs , unit)) ⟩

  infixr 20 _%_

  fork : ℕ → list → rtree
  fork n xs = ⟨ i1 (n , xs , unit) ⟩

  open DIFF.Internal RTREE-NAT public

{-
  open APPLY.Internal RTREE-NAT public
  open import RegDiff.Diff.Regular.Domain konstants keqs (Fix RTREE-NAT) DIFF.WB-FAM
    public
  open DOMAIN.Internal RTREE-NAT public
-}
  w1 w3 w2 : rtree

  w1 = fork 3 #

  w3 = fork 1 (fork 3 # % #)

  w2 = fork 4 (fork 1 # % #)


  w1w3 w1w3-norm : Patchμ (T (fs fz)) (T (fs fz))
  w1w3 = diffμ w1 w3

  w1w3-norm 
    = {!!}

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

  -- 7303 SOP type-heterogeneous set.
  -- 6415 SOP with cpy
  -- 2727 SOP with spine

  t1t3-norm
    = {!!}

{-
  ABS : Fam 2
  ABS = (K kBool ⊗ []) ⊕ []
      ∷ (K kℕ ⊗ []) ⊕ []
      ∷ []

  open DIFF.Internal ABS public

  d1 : Patchμ (T fz) (T (fs fz))
  d1 = diffμ {fz} {fs fz} ⟨ i1 (true , unit) ⟩ ⟨ i1 (10 , unit) ⟩

  al : List (Al Δₐ (K kBool ⊗ []) (K kℕ ⊗ []))
  al = align* (true , unit) (10 , unit)
-}
