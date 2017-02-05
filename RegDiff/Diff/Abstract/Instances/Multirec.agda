open import Prelude
open import Prelude.Eq
open import Prelude.Vector using (Vec ; VecI)
open import Prelude.Monad
open import Prelude.List.All
open import Prelude.List.Lemmas
open import Prelude.Nat.Lemmas
open import Prelude.PartialFuncs.Base

open import RegDiff.Generic.Parms

open import RegDiff.Diff.Abstract.Base

module RegDiff.Diff.Abstract.Instances.Multirec
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
    where

open Monad {{...}}
open Applicative {{...}}

import RegDiff.Generic.Multirec ks as MREC
import RegDiff.Generic.Eq ks keqs as EQ
import RegDiff.Diff.Multirec.Base ks keqs as BASE
import RegDiff.Diff.Multirec.Apply ks keqs as APPLY

module Internal {fam# : ℕ}(fam : MREC.Fam fam#) where

  open import RegDiff.Diff.Universe ks keqs (MREC.Fix fam) EQ._≟_
  open import RegDiff.Diff.Trivial.Base ks keqs (MREC.Fix fam) EQ._≟_
  open BASE.Internal fam
  open APPLY.Internal fam

  Fix-Diffable : Diffable (Fix fam)
  Fix-Diffable = record 
    { P = λ a b → Patchμ (T a) (T b)
    ; cands = diffμ* 
    ; apply = Patchμ-app 
    ; cost = Patchμ-cost 
    }

  
