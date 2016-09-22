open import Prelude
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.NatProperties

{-
  Here we exploit the connection between patches
  and lists of locations!
-}

module RegDiff.Diff.Properties.Correctness.Loc
      {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open Monad {{...}}

  open import RegDiff.Generic.Subtype.Base v
  open import RegDiff.Diff.Regular v eqs
  open import RegDiff.Diff.Fixpoint2 v eqs
  open import RegDiff.Diff.Loc.Regular v eqs
  open import RegDiff.Diff.Loc.Fixpoint v eqs

  applyμ-correct
    : {ty : U}(d : Dμ ty)
    → applyμ (goμ d) (Dμ-src d) ≡ just (Dμ-dst d)
  applyμ-correct (ins x al d) 
    with onμ (hd here) (applyμ-open (goμ d)) (Dμ-src d)
  ...| just k = {!!}
  ...| nothing = {!!}
  applyμ-correct (del x al d) = {!!}
  applyμ-correct (mod x y hip d) = {!!}
