\begin{code}
open import Prelude
open import Prelude.Vector
open import Prelude.ListI
open import RegDiff.Generic.Parms

module RegDiff.Generic.Regular {ks# : ℕ}(ks : Vec Set ks#) where

  infixr 25 _⊗_
  infixr 22 _⊕_

\end{code}
%<*sop-synonyms-def>
\begin{code}
  _⊗_ _⊕_ : ∀{a}{A : Set a} → A → List A → List A
  _⊗_ = _∷_
  _⊕_ = _∷_

  u1 : ∀{a}{A : Set a} → List A
  u1 = []
\end{code}
%</sop-synonyms-def>
%<*atom-def>
\begin{code}
  data Atom (n : ℕ) : Set where
    I : Fin n    → Atom n
    K : Fin ks#  → Atom n
\end{code}
%</atom-def>
%<*prod-def>
\begin{code}
  π : ℕ → Set
  π = List ∘ Atom
\end{code}
%</prod-def>
%<*sum-of-prod-def>
\begin{code}
  σπ : ℕ → Set
  σπ = List ∘ π
\end{code}
%</sum-of-prod-def>
%<*into-sop-def>
\begin{code}
  α : {n : ℕ} → Atom n → σπ n
  α a = (a ∷ []) ∷ []

  β : {n : ℕ} → Atom n → π n
  β x = x ∷ [] 
\end{code}
%</into-sop-def>
%<*sop-denotation-def>
\begin{code}
  ⟦_⟧ₐ : {n : ℕ} → Atom n → Parms n → Set
  ⟦ I x ⟧ₐ     A = A x
  ⟦ K x ⟧ₐ     A = lookup x ks

  ⟦_⟧ₚ : {n : ℕ} → π n → Parms n → Set
  ⟦ []     ⟧ₚ  A = Unit
  ⟦ a ∷ as ⟧ₚ  A = ⟦ a ⟧ₐ A × ⟦ as ⟧ₚ A

  ⟦_⟧ : {n : ℕ} → σπ n → Parms n → Set
  ⟦ []     ⟧   A = ⊥
  ⟦ p ∷ ps ⟧   A = ⟦ p ⟧ₚ A ⊎ ⟦ ps ⟧ A
\end{code}
%</sop-denotation-def>
\begin{code}
  injₐ : {n : ℕ}{k : Atom n}{P : Parms n} → ⟦ k ⟧ₐ P → ⟦ α k ⟧ P
  injₐ k = i1 (k , unit)
\end{code}
%<*Constr-def>
\begin{code}
  cons# : {n : ℕ} → σπ n → ℕ
  cons# = length

  Constr : {n : ℕ}(ty : σπ n) → Set
  Constr ty = Fin (cons# ty)
\end{code}
%</Constr-def>
%<*typeOf-def>
\begin{code}
  typeOf : {n : ℕ}(ty : σπ n) → Constr ty → π n
  typeOf [] ()
  typeOf (x ∷ ty) fz     = x
  typeOf (x ∷ ty) (fs c) = typeOf ty c
\end{code}
%</typeOf-def>
%<*injection-def>
\begin{code}
  inject : {n : ℕ}{A : Parms n}{ty : σπ n}
         → (i : Constr ty) → ⟦ typeOf ty i ⟧ₚ A
         → ⟦ ty ⟧ A
  inject {ty = []} () cs
  inject {ty = x ∷ ty} fz cs     = i1 cs
  inject {ty = x ∷ ty} (fs i) cs = i2 (inject i cs)
\end{code}
%</injection-def>
%<*SOP-view>
\begin{code}
  data SOP {n : ℕ}{A : Parms n}{ty : σπ n} : ⟦ ty ⟧ A → Set where
    strip : (i : Constr ty)(ls : ⟦ typeOf ty i ⟧ₚ A)
          → SOP (inject i ls)
\end{code}
%</SOP-view>
\begin{code}
  sop : {n : ℕ}{A : Parms n}{ty : σπ n}
      → (x : ⟦ ty ⟧ A) → SOP x
  sop {ty = []} ()
  sop {ty = x ∷ ty} (i1 k) = strip fz k
  sop {ty = x ∷ ty} (i2 k) with sop k
  sop {ty = x ∷ ty} (i2 _) | strip i k' = strip (fs i) k'

  constrOf : {n : ℕ}{A : Parms n}{ty : σπ n}
           → (x : ⟦ ty ⟧ A) → Constr ty
  constrOf x with sop x
  constrOf _ | strip i _ = i

  dataOf   : {n : ℕ}{A : Parms n}{ty : σπ n}
           → (x : ⟦ ty ⟧ A) → ⟦ typeOf ty (constrOf x) ⟧ₚ A
  dataOf x with sop x
  dataOf _ | strip _ k = k
\end{code}
\begin{code}
  size1ₚ : {n : ℕ}{A : Parms n}(f : ∀{k} → A k → ℕ)(ty : π n)
         → ⟦ ty ⟧ₚ A → ℕ
  size1ₚ f [] x = 1
  size1ₚ f (I x ∷ as) (⟦x⟧ , xs) = f ⟦x⟧ + size1ₚ f as xs
  size1ₚ f (K x ∷ as) (⟦x⟧ , xs) = 1 + size1ₚ f as xs

  size1 : {n : ℕ}{A : Parms n}(f : ∀{k} → A k → ℕ)(ty : σπ n)
        → ⟦ ty ⟧ A → ℕ
  size1 f [] ()
  size1 f (ty ∷ tys) (i1 x) = size1ₚ  f ty x
  size1 f (ty ∷ tys) (i2 y) = size1   f tys y

  size-const : {n : ℕ}{A : Parms n}(ty : σπ n) → ⟦ ty ⟧ A → ℕ
  size-const = size1 (const 1)
\end{code}
