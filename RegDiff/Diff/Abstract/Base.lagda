\begin{code}
open import Prelude
open import Prelude.PartialFuncs.Base
open import Prelude.List.All

module RegDiff.Diff.Abstract.Base where
\end{code}

  We need to pack up information about
  our diff algorithms in a record, otherwise
  reasoning about it will be impossible.

  We will have homo- and hetero-geneous
  variants.

  We begin by a record that encapsulates the general lines
  of a (heterogeneous) diff:

\begin{code}
  record Diffable {A : Set}(⟦_⟧ : A → Set) : Set₁ where
    field
      P      : A → A → Set
      cands  : ∀{a b} → ⟦ a ⟧ → ⟦ b ⟧ → List (P a b)
      apply  : ∀{a b} → P a b → (⟦ a ⟧ ⇀ ⟦ b ⟧)
      cost   : ∀{a b} → P a b → ℕ

  open Diffable public
\end{code}

  And a predicate about candidates.

\begin{code}
  IsCand : {A : Set}{⟦_⟧ : A → Set}(D : Diffable ⟦_⟧)
          → {a b : A}(x : ⟦ a ⟧)(y : ⟦ b ⟧)(p : P D a b)
          → Set
  IsCand D x y p = apply D p x ≡ just y
\end{code}

  Now, we could come up with plenty of inhabitants
  for the record above. We only want the Diffables that
  obey certain laws!

\begin{code}
  record IsDiff {A : Set}(⟦_⟧ : A → Set)(D : Diffable ⟦_⟧) : Set₁ where
    field
      candidates-ok
        : ∀{a b}(x : ⟦ a ⟧)(y : ⟦ b ⟧) 
        → All (IsCand D x y) (cands D x y)

      candidates-nonnil
        : ∀{a b}(x : ⟦ a ⟧)(y : ⟦ b ⟧)
        → 1 ≤ length (cands D x y)
      
      cost-eq
        : ∀{a b}(x : ⟦ a ⟧)(y : ⟦ b ⟧)(p q : P D a b)
          (hp : IsCand D x y p)(hq : IsCand D x y q)
        → cost D p ≡ cost D q → apply D p ≡ apply D q

      cost-order
        : ∀{a b}(x : ⟦ a ⟧)(y : ⟦ b ⟧)(p q : P D a b)
          (hp : IsCand D x y p)(hq : IsCand D x y q)
        → cost D p ≤ cost D q → apply D q ≼* apply D p
\end{code}
  
  Now we repeat everything for homogeneous patches!

\begin{code}

  record Diffable₀ {A : Set}(⟦_⟧ : A → Set) : Set₁ where
    field
      P₀      : A → Set
      cands₀  : ∀{a} → ⟦ a ⟧ → ⟦ a ⟧ → List (P₀ a)
      apply₀  : ∀{a} → P₀ a → (⟦ a ⟧ ⇀ ⟦ a ⟧)
      cost₀   : ∀{a} → P₀ a → ℕ
  
  open Diffable₀ public

  IsCand₀ : {A : Set}{⟦_⟧ : A → Set}(D : Diffable₀ ⟦_⟧)
          → {a : A}(x y : ⟦ a ⟧)(p : P₀ D a)
          → Set
  IsCand₀ D x y p = apply₀ D p x ≡ just y

  record IsDiff₀ {A : Set}(⟦_⟧ : A → Set)(D : Diffable₀ ⟦_⟧) : Set₁ where
    field
      candidates-ok₀
        : ∀{a}(x y : ⟦ a ⟧)
        → All (IsCand₀ D x y) (cands₀ D x y)

      candidates-nonnil₀
        : ∀{a}(x y : ⟦ a ⟧)
        → 1 ≤ length (cands₀ D x y)
      
      cost-eq
        : ∀{a}(x y : ⟦ a ⟧)(p q : P₀ D a)
          (hp : IsCand₀ D x y p)(hq : IsCand₀ D x y q)
        → cost₀ D p ≡ cost₀ D q → apply₀ D p ≡ apply₀ D q

      cost-order₀
        : ∀{a}(x y : ⟦ a ⟧)(p q : P₀ D a)
          (hp : IsCand₀ D x y p)(hq : IsCand₀ D x y q)
        → cost₀ D p ≤ cost₀ D q → apply₀ D q ≼* apply₀ D p
\end{code}

