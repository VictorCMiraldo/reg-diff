  Here we try to tie the knot for a mutually recursive family
  of datatypes.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.Multirec.Base
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  import RegDiff.Generic.Multirec ks as MREC
  import RegDiff.Generic.Eq ks keqs as EQ
\end{code}

  The idea is almost the same as for fixpoints,
  but now, we parametrize over a family of datatypes.

\begin{code}
  module Internal {fam# : ℕ}(fam : MREC.Fam fam#) where
\end{code}

\begin{code}
    open import RegDiff.Diff.Universe ks keqs (MREC.Fix fam) EQ._≟_
    open import RegDiff.Diff.Trivial.Base ks keqs (MREC.Fix fam) EQ._≟_
    open import RegDiff.Diff.Regular.Base ks keqs (MREC.Fix fam) EQ._≟_
      public

    import RegDiff.Diff.Multirec.Base.Type ks keqs as TYPE
    open TYPE.Internal fam public

    import RegDiff.Diff.Multirec.Base.Optimized ks keqs as ALGO
    open ALGO.Internal fam public
\end{code}

\begin{code}
    _<μ>_ : {ty tv : U} → Patchμ ty tv → List (Patchμ ty tv) → Patchμ ty tv
    s <μ> []       = s
    s <μ> (o ∷ os) with Patchμ-cost s ≤?-ℕ Patchμ-cost o
    ...| yes _ = s <μ> os
    ...| no  _ = o <μ> os

    Patchμ* : U → U → Set
    Patchμ* ty tv = List (Patchμ ty tv)

    Patchμ& : U → U → Set
    Patchμ& ty tv = List (ℕ × Patchμ ty tv)

    addCostsμ : {ty tv : U} → Patchμ* ty tv → Patchμ& ty tv
    addCostsμ = map (λ x → Patchμ-cost x , x)

    filterCostsμ : {ty tv : U} → ℕ → Patchμ* ty tv → Patchμ* ty tv
    filterCostsμ n = filter (cmp n ∘ Patchμ-cost)
      where
        cmp : ℕ → ℕ → Bool
        cmp zero zero = true
        cmp (suc n) (suc m) = cmp n m
        cmp _ _ = false
\end{code}
%<*diffmu-det>
\begin{code}
    diffμ : {k k' : Famᵢ} → Fix fam k → Fix fam k' → Patchμ (T k) (T k')
    diffμ {k} x y with diffμ* x y
    ...| s ∷ ss  = s <μ> ss
    ...| []      = set (unmu x , unmu y)
\end{code}
%</diffmu-det>
