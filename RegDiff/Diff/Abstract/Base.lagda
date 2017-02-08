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

  Here are some interesting predicates:

\begin{code}
  CandsCorrect : {A : Set}(⟦_⟧ : A → Set)(D : Diffable ⟦_⟧) → Set
  CandsCorrect ⟦_⟧ D = ∀{a b}(x : ⟦ a ⟧)(y : ⟦ b ⟧) 
                     → All (IsCand D x y) (cands D x y)

  CandsNonNil : {A : Set}(⟦_⟧ : A → Set)(D : Diffable ⟦_⟧) → Set
  CandsNonNil ⟦_⟧ D = ∀{a b}(x : ⟦ a ⟧)(y : ⟦ b ⟧) 
                    → 1 ≤ length (cands D x y)

  CostEq : {A : Set}(⟦_⟧ : A → Set)(D : Diffable ⟦_⟧) → Set
  CostEq ⟦_⟧ D = ∀{a b}(x : ⟦ a ⟧)(y : ⟦ b ⟧)(p q : P D a b)
               → (hp : IsCand D x y p)(hq : IsCand D x y q)
               → cost D p ≡ cost D q → apply D p ≡ apply D q

  CostOrdered : {A : Set}(⟦_⟧ : A → Set)(D : Diffable ⟦_⟧) → Set
  CostOrdered ⟦_⟧ D = ∀{a b}(x : ⟦ a ⟧)(y : ⟦ b ⟧)(p q : P D a b)
                    → (hp : IsCand D x y p)(hq : IsCand D x y q)
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

  CandsCorrect₀ : {A : Set}(⟦_⟧ : A → Set)(D : Diffable₀ ⟦_⟧) → Set
  CandsCorrect₀ ⟦_⟧ D = ∀{a}(x y : ⟦ a ⟧) 
                      → All (IsCand₀ D x y) (cands₀ D x y)

  CandsNonNil₀ : {A : Set}(⟦_⟧ : A → Set)(D : Diffable₀ ⟦_⟧) → Set
  CandsNonNil₀ ⟦_⟧ D = ∀{a}(x y : ⟦ a ⟧)
                     → 1 ≤ length (cands₀ D x y)

  CostEq₀ : {A : Set}(⟦_⟧ : A → Set)(D : Diffable₀ ⟦_⟧) → Set
  CostEq₀ ⟦_⟧ D = ∀{a}(x y : ⟦ a ⟧)(p q : P₀ D a)
                → (hp : IsCand₀ D x y p)(hq : IsCand₀ D x y q)
                → cost₀ D p ≡ cost₀ D q → apply₀ D p ≡ apply₀ D q

  CostOrdered₀ : {A : Set}(⟦_⟧ : A → Set)(D : Diffable₀ ⟦_⟧) → Set
  CostOrdered₀ ⟦_⟧ D = ∀{a}(x y : ⟦ a ⟧)(p q : P₀ D a)
                     → (hp : IsCand₀ D x y p)(hq : IsCand₀ D x y q)
                     → cost₀ D p ≤ cost₀ D q → apply₀ D q ≼* apply₀ D p
\end{code}

