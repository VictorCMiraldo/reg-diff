module AllFiles where

-- "Standard" library
open import Prelude.List.All
open import Prelude.Monad
open import Prelude.Monad.Decl
open import Prelude.Monad.Instances
open import Prelude.PartialFuncs.PartialOrder
open import Prelude.PartialFuncs.PCat
open import Prelude.PartialFuncs.Base
open import Prelude.Functor.Decl
open import Prelude.Functor.Instances
open import Prelude.RelCalc.Coproduct
open import Prelude.RelCalc.Core
open import Prelude.RelCalc.Product
open import Prelude.RelCalc.Base
open import Prelude.List.All
open import Prelude.List.Lemmas
open import Prelude.Nat.Lemmas
open import Prelude.Functor
open import Prelude.Vector
open import Prelude.Eq

-- Universe of sums-of-products datatypes
open import RegDiff.Generic.Parms
open import RegDiff.Generic.Regular
open import RegDiff.Generic.Multirec
open import RegDiff.Generic.Eq
open import RegDiff.Generic.Fixpoint
open import RegDiff.Generic.Konstants
open import RegDiff.Generic.Lemmas

-- Re-exporting the universe with more suitable names
open import RegDiff.Diff.Universe

-- Trivial diff
open import RegDiff.Diff.Trivial.Base
open import RegDiff.Diff.Trivial.Apply
open import RegDiff.Diff.Trivial.Lemmas

-- Specification of diff-ability (extensional)
open import RegDiff.Diff.Abstract.Base
open import RegDiff.Diff.Abstract.Instances.Trivial
open import RegDiff.Diff.Abstract.Instances.Patch
-- TODO: needs finishing
-- open import RegDiff.Diff.Abstract.Instances.Multirec

-- Lempsink's diff:
open import RegDiff.Diff.ES.Base

-- Diff of sums-of-products (intensional)
open import RegDiff.Diff.Regular.Base
open import RegDiff.Diff.Regular.Apply
open import RegDiff.Diff.Regular.Grupoid
open import RegDiff.Diff.Regular.Lab
open import RegDiff.Diff.Regular.Lemmas

-- Diff of mutual fixpoints
open import RegDiff.Diff.Multirec.Base
open import RegDiff.Diff.Multirec.Apply
-- open import RegDiff.Diff.Multirec.Grupoid
open import RegDiff.Diff.Multirec.LabJson
-- open import RegDiff.Diff.Multirec.Lab

-- Diff of fixpoints (specialized from Multirec)
open import RegDiff.Diff.Fixpoint.Base
open import RegDiff.Diff.Fixpoint.Apply
-- open import RegDiff.Diff.Fixpoint.Lab
