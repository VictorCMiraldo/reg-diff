open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.Lemmas
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.ES.SamplePatch where

  open Monad {{...}}
  open Applicative {{...}}

  ks# : ℕ
  ks# = 2

  ks : Vec Set ks#
  ks = Bool ∷ ℕ ∷ []

  keqs : VecI Eq ks
  keqs = eq-Bool ∷ eq-ℕ ∷ []

  open import RegDiff.Generic.Multirec ks
  import RegDiff.Generic.Eq ks keqs as EQ

  fam# : ℕ
  fam# = 2

  listT : Sum fam#
  listT = []
        ∷ (I (fs fz) ∷ I fz ∷ [])
        ∷ []

  forkT : Sum fam#
  forkT = (K (fs fz) ∷ I fz ∷ [])
        ∷ []

  fam : Fam fam#
  fam = listT ∷ forkT ∷ []

  list rose : Set
  list = Fix fam fz
  rose = Fix fam (fs fz)

  c-nil : list
  c-nil = ⟨ i1 unit ⟩
  
  c-cons : rose → list → list
  c-cons x xs = ⟨ i2 (i1 (x , xs , unit)) ⟩

  c-fork : ℕ → list → rose
  c-fork n xs = ⟨ i1 (n , xs , unit) ⟩

  nil cons : Constr listT
  nil = fz
  cons = fs fz

  t1 : rose
  t1 = c-fork 10 (c-cons (c-fork 5 c-nil) 
                 (c-cons (c-fork 8 c-nil)
                  c-nil))

  t2 : rose 
  t2 = c-fork 10 (c-cons (c-fork 5 (c-cons (c-fork 8 c-nil) c-nil))
                  c-nil)

  import RegDiff.Diff.ES.Base as BASE
  open BASE.Internal ks keqs fam

  RosePatch : Set
  RosePatch = ES (I (fs fz) ∷ []) (I (fs fz) ∷ [])

  p12 : RosePatch
  p12 = cpy fz 
       (cpy 10 
       (cpy cons
       (cpy fz (cpy 5 (del nil 
       (cpy cons (cpy fz (cpy 8 (cpy nil 
       (ins nil (cpy nil 
       end)))))))))))

{-
  module Internal {fam# : ℕ}(fam : MREC.Fam fam#) where

    open import RegDiff.Diff.Universe ks keqs (MREC.Fix fam) EQ._≟_
    open import RegDiff.Diff.Trivial.Base ks keqs (MREC.Fix fam) EQ._≟_
    open BASE.Internal ks keqs fam
      renaming (ES to BaseES)
-}
