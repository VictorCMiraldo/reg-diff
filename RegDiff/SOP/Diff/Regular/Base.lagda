  Here we define a refinement over the trivial diff.
  Instead of storing both values as a whole,
  we will store a bunch of transformations that
  could transform one into the other.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.ListI
open import RegDiff.Generic.Parms

module RegDiff.SOP.Diff.Regular.Base
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where

  open Monad {{...}}

  open import RegDiff.SOP.Generic.Multirec ks
  open import RegDiff.SOP.Generic.Eq ks keqs
  open import RegDiff.SOP.Diff.Trivial.Base ks keqs A WBA
    public
\end{code}

%<*S1-def>
\begin{code}
  data S (P : UUSet) : U → Set where
    SX  : {ty : U} → P ty ty → S P ty
    Scp : {ty : U} → S P ty

  data C (P : ΠΠSet) : U → U → Set where
    CX  : {ty tv : U}
        → (i : Constr ty)(j : Constr tv)
        → P (typeOf ty i) (typeOf tv j) 
        → C P ty tv

  data Al (P : AASet) : Π → Π → Set where
    A0   :                                             Al P [] []
    Ap1  : ∀{a ty tv}     → ⟦ a ⟧ₐ A   → Al P ty tv →  Al P (a ∷ ty) tv
    Ap1ᵒ : ∀{a ty tv}     → ⟦ a ⟧ₐ A   → Al P ty tv →  Al P ty       (a ∷ tv)
    AX   : ∀{a a' ty tv}  → P a a'     → Al P ty tv →  Al P (a ∷ ty) (a' ∷ tv)
\end{code}
%</S1-def>

\begin{code}
  S-map : {ty : U}
          {P Q : UUSet}(X : ∀{k v} → P k v → Q k v)
        → S P ty → S Q ty
  S-map f (SX x) = SX (f x)
  S-map f Scp    = Scp

  S-mapM : {ty : U}{M : Set → Set}{{m : Monad M}}
           {P Q : UUSet}(X : ∀{k v} → P k v → M (Q k v))
         → S P ty → M (S Q ty)
  S-mapM f (SX x) = f x >>= return ∘ SX
  S-mapM f Scp    = return Scp

  C-map : {ty tv : U}
          {P Q : ΠΠSet}(X : ∀{k v} → P k v → Q k v)
        → C P ty tv → C Q ty tv
  C-map f (CX i j x) = CX i j (f x)

  C-mapM : {ty tv : U}{M : Set → Set}{{m : Monad M}}
           {P Q : ΠΠSet}(X : ∀{k v} → P k v → M (Q k v))
         → C P ty tv → M (C Q ty tv)
  C-mapM f (CX i j x) = f x >>= return ∘ CX i j

  Al-mapM : {ty tv : Π}{M : Set → Set}{{m : Monad M}}
            {P Q : AASet}(X : ∀{k v} → P k v → M (Q k v))
          → Al P ty tv → M (Al Q ty tv)
  Al-mapM f A0 = return A0
  Al-mapM f (Ap1 x a) = Al-mapM f a >>= return ∘ (Ap1 x) 
  Al-mapM f (Ap1ᵒ x a) = Al-mapM f a >>= return ∘ (Ap1ᵒ x)
  Al-mapM f (AX x a) = f x >>= λ x' → Al-mapM f a >>= return ∘ (AX x') 
\end{code}


\begin{code}
  S-cost : {ty : U}{P : UUSet}(doP : {k v : U} → P k v → ℕ)
         → S P ty → ℕ
  S-cost doP (SX x) = doP x
  S-cost doP Scp = 0

  C-cost : {ty tv : U}{P : ΠΠSet}(doP : {k v : Π} → P k v → ℕ)
         → C P ty tv → ℕ
  C-cost doP (CX i j x) = doP x

  Al-cost : {ty tv : Π}{P : AASet}(doP : {k v : Aty} → P k v → ℕ)
          → Al P ty tv → ℕ
  Al-cost doP A0         = 0
  Al-cost doP (Ap1 x a)  = 1 + Al-cost doP a
  Al-cost doP (Ap1ᵒ x a) = 1 + Al-cost doP a
  Al-cost doP (AX x a)   = doP x + Al-cost doP a
\end{code}

\begin{code}
  Δ' : UUSet
  Δ' ty tv = ⟦ ty ⟧ A × ⟦ tv ⟧ A

  Δₚ : ΠΠSet
  Δₚ ty tv = ⟦ ty ⟧ₚ A × ⟦ tv ⟧ₚ A

  zipₚ : {ty : Π}
       → ⟦ ty ⟧ₚ A  → ⟦ ty ⟧ₚ A → ListI (λ k → Δ' (𝓐 k) (𝓐 k)) ty
  zipₚ {[]}     _        _         = []
  zipₚ {_ ∷ ty} (x , xs) (y , ys)  
    = (i1 (x , unit) , i1 (y , unit)) ∷ zipₚ xs ys

  spine : {ty : U}(x y : ⟦ ty ⟧ A) → S Δ' ty
  spine {ty} x y with dec-eq _≟-A_ ty x y 
  ...| yes _ = Scp
  ...| no  _ = SX (x , y)

  change : {ty tv : U} → ⟦ ty ⟧ A → ⟦ tv ⟧ A → C Δₚ ty tv
  change x y with sop x | sop y
  change _ _ | strip cx dx | strip cy dy = CX cx cy (dx , dy)


  align* : {ty tv : Π} → ⟦ ty ⟧ₚ A → ⟦ tv ⟧ₚ A → List (Al Δ ty tv)
  align* {[]}     {[]}     m n = return A0
  align* {[]}     {v ∷ tv} m (n , nn) 
    = Ap1ᵒ n <$> align* m nn
  align* {y ∷ ty} {[]}     (m , mm) n 
    = Ap1 m <$> align* mm n
  align* {y ∷ ty} {v ∷ tv} (m , mm) (n , nn)
    =  AX (m , n)   <$> align* mm nn
    ++ Ap1  m       <$> filter (not ∘ is-ap1ᵒ)  (align* mm (n , nn))
    ++ Ap1ᵒ n       <$> filter (not ∘ is-ap1)   (align* (m , mm) nn)
    where
      is-ap1 : {ty tv : Π} → Al Δ ty tv → Bool
      is-ap1 (Ap1 _ _) = true
      is-ap1 _         = false

      is-ap1ᵒ : {ty tv : Π} → Al Δ ty tv → Bool
      is-ap1ᵒ (Ap1ᵒ _ _) = true
      is-ap1ᵒ _          = false 
\end{code}
\begin{code}
  Patch : U → Set
  Patch = S (C (Al Δ))

  Patch* : U → Set
  Patch* = List ∘ Patch

  Patch& : U → Set
  Patch& = List ∘ (ℕ ×_) ∘ Patch

  Patch-cost : {ty : U} → Patch ty → ℕ
  Patch-cost = S-cost (C-cost (Al-cost (λ {k} {v} → cost-Δ {k} {v})))

  addCosts : {ty : U} → Patch* ty → Patch& ty
  addCosts = map (λ k → Patch-cost k , k)

  choose : {ty : U} → Patch ty → Patch ty → Patch ty
  choose c d with Patch-cost c ≤?-ℕ Patch-cost d
  ...| yes _ = d
  ...| no  _ = c

  _<>_ : {ty : U} → Patch ty → List (Patch ty) → Patch ty
  c <> [] = c
  c <> (d ∷ ds) = (choose c d) <> ds

  diff1* : {ty : U}(x y : ⟦ ty ⟧ A) → Patch* ty
  diff1* x y = S-mapM (C-mapM (uncurry align*) ∘ uncurry change) (spine x y)
\end{code}
%<*diff1-def>
\begin{code}
  diff1 : {ty : U} → ⟦ ty ⟧ A → ⟦ ty ⟧ A → Patch ty
  diff1 x y with diff1* x y
  ...| s ∷ ss = s <> ss
  ...| []     = impossible
     where postulate impossible : {ty : U} → Patch ty
\end{code}
%</diff1-def>
