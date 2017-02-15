open import Prelude hiding (⊥)
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.PartialFuncs.Base
open import Prelude.List.All
open import Prelude.Monad

module RegDiff.Diff.Fixpoint.Lab23TreeHeuristic where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Eq konstants keqs as EQ
  import RegDiff.Diff.Multirec.Base konstants keqs 
    as DIFF
  import RegDiff.Diff.Multirec.Apply konstants keqs 
    as APPLY

  module Defs where

    
    open import RegDiff.Generic.Multirec konstants
      renaming (I to I')

    I : Atom 1
    I = I' fz

    2-3-TREE-F : Sum 1
    2-3-TREE-F = u1 
               ⊕ (K kℕ) ⊗ I ⊗ I ⊗ [] 
               ⊕ (K kℕ) ⊗ I ⊗ I ⊗ I ⊗ [] ⊕ []

    fam : Fam 1
    fam = 2-3-TREE-F ∷ []

    fixfam : Fin 1 → Set
    fixfam = Fix fam

    2-3-Tree : Set
    2-3-Tree = fixfam fz

    %leaf %2-node %3-node : Constr 2-3-TREE-F
    %leaf = fz
    %2-node = fs fz
    %3-node = fs (fs fz)

    Leaf : 2-3-Tree
    Leaf = ⟨ i1 unit ⟩

    2-Node : ℕ → 2-3-Tree → 2-3-Tree → 2-3-Tree
    2-Node n l r = ⟨ i2 (i1 (n , l , r , unit)) ⟩

    3-Node : ℕ → 2-3-Tree → 2-3-Tree → 2-3-Tree → 2-3-Tree
    3-Node n l m r = ⟨ i2 (i2 (i1 (n , l , m , r , unit))) ⟩

    _==_ : 2-3-Tree → Maybe 2-3-Tree → Bool
    _ == nothing = false
    t == just u with t EQ.≟ u 
    ...| yes _ = true
    ...| no  _ = false

    -- Now, let's pretend that the labels in a 2-3-Tree
    -- represent function names. We know for a fact that
    -- if two functions have the same name, they are
    -- the same function! So we can already say that
    -- trying to insert or delete one of them is
    -- a bad idea, we go straight for modify!

    fun-name : 2-3-Tree → Maybe ℕ
    fun-name ⟨ i1 _ ⟩                  = nothing
    fun-name ⟨ i2 (i1 (n , _)) ⟩       = just n
    fun-name ⟨ i2 (i2 (i1 (n , _))) ⟩  = just n
    fun-name ⟨ i2 (i2 (i2 ())) ⟩  
  
  open Defs
  open DIFF.Internal fam public
  open APPLY.Internal fam public
  open import RegDiff.Diff.Universe konstants keqs 
        fixfam EQ._≟_
    hiding (Fix)

  -- This is just copy pasted from RegDiff.Diff.Multirec.Base.Naive
  -- with the intention of making it call the heuristic definition
  -- instead of the original one.
  mutual
    diffμh*-atoms : {ty tv : Atom} → ⟦ ty ⟧ₐ → ⟦ tv ⟧ₐ → List (UU→AA Patchμ ty tv)
    diffμh*-atoms {I fz} {I fz} x y  = fix <$> diffμ-heu* x y
    diffμh*-atoms {I (fs ())} {I _} x y  
    diffμh*-atoms {I _} {I (fs ())} x y  
    diffμh*-atoms {K ty} {K tv} x y  = return (set (to-α {K ty} x , to-α {K tv} y))
    diffμh*-atoms {K ty} {I tv} x y  = []
    diffμh*-atoms {I ty} {K tv} x y  = []

    alignμh  : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ
            → List (Al (UU→AA Patchμ) ty tv)
    alignμh x y = align* x y >>= Al-mapM (uncurry diffμh*-atoms)

    alignμh'  : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ
             → List (Al (UU→AA Patchμ) ty tv)
    alignμh' {[]}     {_}      _ _  = []
    alignμh' {_}      {[]}     _ _  = []
    alignμh' {_ ∷ _}  {_ ∷ _}  x y  = alignμh x y

    diffμh*-mod : {ty tv : U} → ⟦ ty ⟧ → ⟦ tv ⟧ → List (Patchμ ty tv)
    diffμh*-mod {ty} {tv} x y with EQ.Sum-eq ty tv
    ...| no _ = []
    diffμh*-mod x y
       | yes refl 
       = skel <$> S-mapM (uncurry alignμh) (spine x y)

    diffμh*-ins : {ty : U} → 2-3-Tree → ⟦ ty ⟧ → List (Patchμ 2-3-TREE-F ty)
    diffμh*-ins x y with sop y
    diffμh*-ins x _ | strip cy dy 
      = ins cy <$> alignμh' (x , unit) dy

    diffμh*-del : {ty : U} → ⟦ ty ⟧ → 2-3-Tree → List (Patchμ ty 2-3-TREE-F)
    diffμh*-del x y with sop x
    diffμh*-del _ y | strip cx dx
      = del cx <$> alignμh' dx (y , unit) 



    -- Finally, we can define a diffμ with our heuristic builtin
    --
    {-# TERMINATING #-}
    diffμ-heu* : 2-3-Tree → 2-3-Tree → List (Patchμ 2-3-TREE-F 2-3-TREE-F)
    diffμ-heu* x y with Maybe-δ (fun-name x , fun-name y)
    ...| nothing 
      =  diffμh*-ins x (unmu y) 
      ++ diffμh*-del (unmu x) y
    ...| just (nx , ny) 
      with nx ≟-ℕ ny 
    ...| no _  = diffμh*-ins x (unmu y) 
              ++ diffμh*-del (unmu x) y
    ...| yes _ = diffμh*-mod (unmu x) (unmu y)

  t1 t2 : 2-3-Tree
  t1 = 2-Node 1 Leaf Leaf
  t2 = 3-Node 2 Leaf Leaf t1

  d12*-heu d12* : List (Patchμ 2-3-TREE-F 2-3-TREE-F)
  d12*-heu = diffμ-heu* t2 t1
  d12* = diffμ* t2 t1

  -- d12* has 18 elements, while with the heuristic there
  -- is only one possibility!

  -- Let's scale this up a bit.

  k1 k2 : 2-3-Tree
  k1 = 3-Node 3 t1 Leaf t2
  k2 = 2-Node 3 (3-Node 4 t1 Leaf Leaf) t2

  k12*-heu k12* : List (Patchμ 2-3-TREE-F 2-3-TREE-F)
  k12*-heu = diffμ-heu* k2 k1 -- length == 4
  k12* = diffμ* k2 k1 -- length == 1428
