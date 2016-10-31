open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Diff.Lab where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Base konstants public
  open import RegDiff.Generic.Eq konstants keqs public
  import RegDiff.Diff.Spine konstants keqs as SPINE
  open import RegDiff.Diff.Fixpoint konstants keqs

  QOOL : U
  QOOL = u1 ⊕ I ⊕ I ⊗ I

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
  
    open SPINE ℕ (const 1) public

    r1 : S Δ QOOL QOOL
    r1 = diff1 (i2 (i1 5)) (i2 (i2 (1 , 5)))

    app : S Δ QOOL QOOL → ⟦ QOOL ⟧ ℕ → Maybe (⟦ QOOL ⟧ ℕ)
    app s el = applyₗ apply-Δ s el

    

  module T2 where

    l1 l2 l3 : list
    l1 = (1 > 4 > #)
    l2 = (1 > 50 > 4 > #)
    l3 = (1 > 50 > 4 > 20 > #)

    open Internal LIST-F public

    r1 r2 r3 : S (SI Δ) LIST-F LIST-F
    r1 = diffμ l1 l2
    r2 = diffμ l1 l3 -- 12

    r3 = Si2 (Ssym (Si2 (S⊗ (SX (SY (1 , 1))) 
             (SX (Svar (SX (Sins (Ssym (Si2 
             (Ssnd 50 (SX (Svar (Si2 (Ssym 
               (Si2 (S⊗ (SX (SY (4 , 4))) 
             (SX (Svar (SX (Sins (Ssym 
               (Si2 (Ssnd 20 Scp))))))))))))) 
             ))))))))))
  
  module T3 where

    k0 k1 k2 : 2-3-Tree
    k0 = Leaf
    k1 = 2-Node 1 Leaf Leaf
    k2 = 3-Node 5 Leaf Leaf Leaf
    k3 = 3-Node 3 k1 k2 k2

    t1 t2 : 2-3-Tree
    t1 = 2-Node 4 k1 k2
    t2 = 3-Node 5 k1 Leaf k2

    open Internal 2-3-TREE-F public

    r1 r2 r3 : S (SI Δ) 2-3-TREE-F 2-3-TREE-F
    r1 = diffμ t1 t2

    r2 = diffμ k1 k3 -- 30

    r3 = SX (Sins (Ssym (Si2 (Si2 (Ssnd 1 (Sfst (k2 , k2) (SX (Svar (diffμ k1 k1)))))))))

  open T3 public


