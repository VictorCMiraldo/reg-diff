\begin{code}
open import Prelude
open import Prelude.Vector
open import Prelude.ListI
open import RegDiff.Generic.Parms

module RegDiff.SOP.Generic.Regular {ks# : ℕ}(ks : Vec Set ks#) where

  infixr 25 _⊗_
  infixr 22 _⊕_

  _⊗_ _⊕_ : ∀{a}{A : Set a} → A → List A → List A
  _⊗_ = _∷_
  _⊕_ = _∷_

  u1 : ∀{a}{A : Set a} → List A
  u1 = []
\end{code}
\begin{code}
  data Atom (n : ℕ) : Set where
    I : Fin n    → Atom n
    K : Fin ks#  → Atom n

  Prod : ℕ → Set
  Prod = List ∘ Atom

  Uₙ : ℕ → Set
  Uₙ = List ∘ Prod

  𝓐 : {n : ℕ} → Atom n → Uₙ n
  𝓐 a = (a ∷ []) ∷ []
\end{code}
\begin{code}
  ⟦_⟧ₐ : {n : ℕ} → Atom n → Parms n → Set
  ⟦ I x ⟧ₐ     A = A x
  ⟦ K x ⟧ₐ     A = lookup x ks

  ⟦_⟧ₚ : {n : ℕ} → Prod n → Parms n → Set
  ⟦ []     ⟧ₚ  A = Unit
  ⟦ a ∷ as ⟧ₚ  A = ⟦ a ⟧ₐ A × ⟦ as ⟧ₚ A

  ⟦_⟧ : {n : ℕ} → Uₙ n → Parms n → Set
  ⟦ []     ⟧   A = ⊥
  ⟦ p ∷ ps ⟧   A = ⟦ p ⟧ₚ A ⊎ ⟦ ps ⟧ A
\end{code}
\begin{code}
  cons# : {n : ℕ} → Uₙ n → ℕ
  cons# = length

  Constr : {n : ℕ}(ty : Uₙ n) → Set
  Constr ty = Fin (cons# ty)

  typeOf : {n : ℕ}(ty : Uₙ n) → Constr ty → Prod n
  typeOf [] ()
  typeOf (x ∷ ty) fz     = x
  typeOf (x ∷ ty) (fs c) = typeOf ty c
\end{code}
\begin{code}
  inject : {n : ℕ}{A : Parms n}{ty : Uₙ n}
         → (i : Constr ty) → ⟦ typeOf ty i ⟧ₚ A
         → ⟦ ty ⟧ A
  inject {ty = []} () cs
  inject {ty = x ∷ ty} fz cs     = i1 cs
  inject {ty = x ∷ ty} (fs i) cs = i2 (inject i cs)

  data SOP {n : ℕ}{A : Parms n}{ty : Uₙ n} : ⟦ ty ⟧ A → Set where
    strip : (i : Constr ty)(ls : ⟦ typeOf ty i ⟧ₚ A)
          → SOP (inject i ls)

  sop : {n : ℕ}{A : Parms n}{ty : Uₙ n}
      → (x : ⟦ ty ⟧ A) → SOP x
  sop {ty = []} ()
  sop {ty = x ∷ ty} (i1 k) = strip fz k
  sop {ty = x ∷ ty} (i2 k) with sop k
  sop {ty = x ∷ ty} (i2 _) | strip i k' = strip (fs i) k'

  constrOf : {n : ℕ}{A : Parms n}{ty : Uₙ n}
           → (x : ⟦ ty ⟧ A) → Constr ty
  constrOf x with sop x
  constrOf _ | strip i _ = i

  dataOf   : {n : ℕ}{A : Parms n}{ty : Uₙ n}
           → (x : ⟦ ty ⟧ A) → ⟦ typeOf ty (constrOf x) ⟧ₚ A
  dataOf x with sop x
  dataOf _ | strip _ k = k
\end{code}
\begin{code}
  size1ₚ : {n : ℕ}{A : Parms n}(f : ∀{k} → A k → ℕ)(ty : Prod n)
         → ⟦ ty ⟧ₚ A → ℕ
  size1ₚ f [] x = 1
  size1ₚ f (I x ∷ as) (⟦x⟧ , xs) = f ⟦x⟧ + size1ₚ f as xs
  size1ₚ f (K x ∷ as) (⟦x⟧ , xs) = 1 + size1ₚ f as xs

  size1 : {n : ℕ}{A : Parms n}(f : ∀{k} → A k → ℕ)(ty : Uₙ n)
        → ⟦ ty ⟧ A → ℕ
  size1 f [] ()
  size1 f (ty ∷ tys) (i1 x) = size1ₚ  f ty x
  size1 f (ty ∷ tys) (i2 y) = size1   f tys y

  size-const : {n : ℕ}{A : Parms n}(ty : Uₙ n) → ⟦ ty ⟧ A → ℕ
  size-const = size1 (const 1)
\end{code}
