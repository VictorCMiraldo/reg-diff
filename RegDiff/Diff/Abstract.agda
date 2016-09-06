open import Prelude
open import Prelude.Vector

{-
  This provides a "hack" to be able to
  run our algorithm with some types:

  Make a Abstract-Diffing-Structure, Dₐ,
  available for arbitrary sets A,

  A vector of these structures is passed as
  a module-parameter to the diff-function.
-}

module RegDiff.Diff.Abstract where

  record Dₐ (A : Set) : Set₁ where
    field
      Patchₐ : Set
      srcₐ   : Patchₐ → A
      dstₐ   : Patchₐ → A
      diffₐ  : A → A → Patchₐ
      appₐ   : Patchₐ → A → Maybe A
      costₐ  : Patchₐ → ℕ

  open Dₐ

{-
  The Oh!-so-famous trivial diff can be implemented
  for any type with equality.
-}

  trivial-diff : {A : Set}{{eq : Eq A}}
               → Dₐ A
  trivial-diff {A} {{eq _≟_}}
    = record
        { Patchₐ = A × A
        ; srcₐ = p1
        ; dstₐ = p2
        ; diffₐ = _,_
        ; appₐ = λ d x → dec-elim (const (just (p2 d))) (const nothing) (p1 d ≟ x)
        ; costₐ = λ p → dec-elim (const 0) (const 1) (p1 p ≟ p2 p)
        }

{-
  We postulate this lemmas as their proof is irrelevant.
  On the universe of RTT we don't need it.
-}

  postulate
    dₐ-src-lemma
      : {A : Set}(d : Dₐ A)(x y : A)
      → srcₐ d (diffₐ d x y) ≡ x

    dₐ-dst-lemma
      : {A : Set}(d : Dₐ A)(x y : A)
      → dstₐ d (diffₐ d x y) ≡ y

    dₐ-app-lemma
      : {A : Set}(d : Dₐ A)(p : Patchₐ d)
      → appₐ d p (srcₐ d p) ≡ just (dstₐ d p)

