  Here we define a refinement over the trivial diff.
  Instead of storing both values as a whole,
  we will store a bunch of transformations that
  could transform one into the other.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Base
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open Monad {{...}}

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_
    public

  -- Now the spine is just re-exported
  open import RegDiff.Diff.Regular.Base.Spine ks keqs A _≟-A_
    public

  -- And the alignment too!
  open import RegDiff.Diff.Regular.Base.AlignmentType ks keqs A _≟-A_
    public
\end{code}


%<*Al-mapM-def>
\begin{code}
  Al-mapM : {ty tv : Π}{M : Set → Set}{{m : Monad M}}
            {P Q : AASet}(X : ∀{k v} → P k v → M (Q k v))
          → Al P ty tv → M (Al Q ty tv)
  Al-mapM f A0 = return A0
  Al-mapM f (Ap1 x a) = Al-mapM f a >>= return ∘ (Ap1 x) 
  Al-mapM f (Ap1ᵒ x a) = Al-mapM f a >>= return ∘ (Ap1ᵒ x)
  Al-mapM f (AX x a) = f x >>= λ x' → Al-mapM f a >>= return ∘ (AX x') 
\end{code}
%</Al-mapM-def>
%<*Al-cost-def>
\begin{code}
  Al-cost : {ty tv : Π}{P : AASet}(doP : {k v : Atom} → P k v → ℕ)
          → Al P ty tv → ℕ
  Al-cost doP A0         = 0
  Al-cost doP (Ap1 x a)  = 1 + Al-cost doP a
  Al-cost doP (Ap1ᵒ x a) = 1 + Al-cost doP a
  Al-cost doP (AX x a)   = doP x + Al-cost doP a
\end{code}
%</Al-cost-def>
\begin{code}
  is-ap1 : {ty tv : Π} → Al Trivialₐ ty tv → Bool
  is-ap1 (Ap1 _ _) = true
  is-ap1 _         = false

  is-ap1ᵒ : {ty tv : Π} → Al Trivialₐ ty tv → Bool
  is-ap1ᵒ (Ap1ᵒ _ _) = true
  is-ap1ᵒ _          = false 
\end{code}
%<*align-star-def>
\begin{code}
  align* : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ → List (Al Trivialₐ ty tv)
  align* {[]}     {[]}     m n = return A0
  align* {[]}     {v ∷ tv} m (n , nn) 
    = Ap1ᵒ n <$> align* m nn
  align* {y ∷ ty} {[]}     (m , mm) n 
    = Ap1 m <$> align* mm n
  align* {y ∷ ty} {v ∷ tv} (m , mm) (n , nn)
    =  align? m n (align* mm nn)
    ++ Ap1  m       <$> filter (not ∘ is-ap1ᵒ)  (align* mm (n , nn))
    ++ Ap1ᵒ n       <$> filter (not ∘ is-ap1)   (align* (m , mm) nn)
    where
      align? : {ty tv : Atom}{tys tvs : Π} 
             → ⟦ ty ⟧ₐ → ⟦ tv ⟧ₐ → List (Al Trivialₐ tys tvs)
             → List (Al Trivialₐ (ty ∷ tys) (tv ∷ tvs))
      align? {I _} {I _} x y xys = AX (x , y) <$> xys
      align? {K _} {K _} x y xys = AX (x , y) <$> xys
      align? {I _} {K _} x y xys = []
      align? {K _} {I _} x y xys = []
      
\end{code}
%</align-star-def>

%<*Patch-def>
\begin{code}
  Patch : AASet → U → Set
  Patch P = S (Al P)
\end{code}
%</Patch-def>
\begin{code}
  Patch-cost : {ty : U}{P : AASet}(doP : ∀{k v} → P k v → ℕ)
             → Patch P ty → ℕ
  Patch-cost doP = S-cost (Al-cost doP)

  Patch-mapM : {ty : U}{M : Set → Set}{{m : Monad M}}
               {P Q : AASet}(X : ∀{k v} → P k v → M (Q k v))
             → Patch P ty → M (Patch Q ty)
  Patch-mapM X = S-mapM (Al-mapM X)
\end{code}
\begin{code}
  Patch-cost-Trivialₐ : {ty : U} → Patch Trivialₐ ty → ℕ
  Patch-cost-Trivialₐ = Patch-cost (λ {k} {v} → cost-Trivialₐ {k} {v})

  Patch* : U → Set
  Patch* = List ∘ Patch Trivialₐ

  Patch& : U → Set
  Patch& = List ∘ (ℕ ×_) ∘ Patch Trivialₐ

  addCosts : {ty : U} → Patch* ty → Patch& ty
  addCosts = map (λ k → Patch-cost-Trivialₐ k , k)

  choose : {ty : U} → Patch Trivialₐ ty → Patch Trivialₐ ty → Patch Trivialₐ ty
  choose c d with Patch-cost-Trivialₐ c ≤?-ℕ Patch-cost-Trivialₐ d
  ...| yes _ = d
  ...| no  _ = c

  _<>_ : {ty : U} → Patch Trivialₐ ty → List (Patch Trivialₐ ty) → Patch Trivialₐ ty
  c <> [] = c
  c <> (d ∷ ds) = (choose c d) <> ds
\end{code}
%<*diff1-star-def>
\begin{code}
  diff1* : {ty : U}(x y : ⟦ ty ⟧) → Patch* ty
  diff1* x y = S-mapM (uncurry align*) (spine x y)
\end{code}
%</diff1-star-def>
%<*diff1-def>
\begin{code}
  diff1 : {ty : U} → ⟦ ty ⟧ → ⟦ ty ⟧ → Patch Trivialₐ ty
  diff1 x y with diff1* x y
  ...| s ∷ ss = s <> ss
  ...| []     = impossible
     where postulate impossible : {ty : U} → Patch Trivialₐ ty
\end{code}
%</diff1-def>


 TODO: Prove that diff1* is NEVER the empty list.
