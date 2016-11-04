  Here we define a refinement over the trivial diff.
  Instead of storing both values as a whole,
  we will store a bunch of transformations that
  could transform one into the other.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Diff.Regular.Base
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)(A : Set)
       {{eqA : Eq A}}(sized : A → ℕ)
    where

  open Monad {{...}}

  open import RegDiff.Generic.Base v
  open import RegDiff.Generic.Eq v eqs
  open import RegDiff.Diff.Trivial.Base v eqs A sized
    public
\end{code}

  An inhabitant of S represents a list of instructions on how
  to transform one thing into another.

  This transformation works in two phases: Here, we the phases
  are identifying common parts, then proceeding to change them.

%<*S-def>
\begin{code}
  data S (P : UUSet) : U → Set where
    SX   : {ty : U} → P ty ty → S P ty
    Scp  : {ty : U} → S P ty
    S⊗   : {ty tv : U} 
         → S P ty → S P tv → S P (ty ⊗ tv)
    Si1  : {ty tv : U} 
         → S P ty → S P (ty ⊕ tv)
    Si2  : {ty tv : U} 
         → S P ty → S P (tv ⊕ ty)
\end{code}
%</S-def>

  As expected, S makes an indexed functor.
  It will be especially usefull to monadically map over it later on.

\begin{code}
  S-mapM : {ty : U}{M : Set → Set}{{m : Monad M}}{P Q : UUSet}
         → (f : ∀{k} → P k k → M (Q k k))
         → S P ty → M (S Q ty)
  S-mapM f (SX x) = f x >>= return ∘ SX
  S-mapM f Scp = return Scp
  S-mapM f (S⊗ s o) = S-mapM f s >>= λ s' → S-mapM f o >>= return ∘ (S⊗ s')
  S-mapM f (Si1 s) = S-mapM f s >>= return ∘ Si1
  S-mapM f (Si2 s) = S-mapM f s >>= return ∘ Si2
\end{code}

  Computing the inhabitants of S is fairly simple:

\begin{code}
  mutual
    spine-cp : {ty : U} → ⟦ ty ⟧ A → ⟦ ty ⟧ A → List (S Δ ty)
    spine-cp {ty} x y
      with dec-eq ty x y 
    ...| no  _ = spine x y
    ...| yes _ = return Scp
    
    spine : {ty : U} → ⟦ ty ⟧ A → ⟦ ty ⟧ A → List (S Δ ty)
    spine {ty ⊗ tv} (x1 , x2) (y1 , y2) 
      = S⊗ <$> (spine-cp x1 y1) <*> (spine-cp x2 y2)
    spine {tv ⊕ tw} (i1 x) (i1 y) = Si1 <$> (spine-cp x y) 
    spine {tv ⊕ tw} (i2 x) (i2 y) = Si2 <$> (spine-cp x y)
    spine {ty}      x      y      = return (SX (x , y))
\end{code}

  But we eventually need to choose one of them! In fact, the patch between
  (x : ⟦ ty ⟧ A) and (y : ⟦ tv ⟧ A) is the one with the lowest cost!

\begin{code}
  S-cost : {ty : U}{P : UUSet}
         → (costP : ∀{ty} → P ty ty → ℕ)
         → S P ty → ℕ
  S-cost c (SX x) = c x
  S-cost c Scp = 0
  S-cost c (S⊗ s o) = S-cost c s + S-cost c o
  S-cost c (Si1 s) = 1 + S-cost c s
  S-cost c (Si2 s) = 1 + S-cost c s

  SΔ-cost : {ty : U} → S Δ ty → ℕ
  SΔ-cost = S-cost (λ {ty} xy → cost-Δ {ty} {ty} xy)
\end{code}

  Here we add some binary operators to choose
  between S's

\begin{code} 
  private
    chooseS : {ty : U}{P : UUSet}(costP : ∀{k} → P k k → ℕ)
            → (s1 s2 : S P ty) → S P ty
    chooseS c s o with S-cost c s ≤?-ℕ S-cost c o 
    ...| yes _ = s
    ...| no  _ = o

    chooseS* : {ty : U}{P : UUSet}(costP : ∀{k} → P k k → ℕ)
             → S P ty → List (S P ty)  → S P ty
    chooseS* c s []       = s
    chooseS* c s (o ∷ os) = chooseS* c (chooseS c s o) os
\end{code}

  And finally, we can diff things! Note that spine-cp will NEVER be empty.
  In the worst case scenario, it gives a (SX (x , y)).

  But now, we need to be able to change things!

\begin{code}
  data C (P : UUSet) : U → U → Set where
    CX   : {ty tv : U}   → P ty tv → C P ty tv
    Ci1  : {ty tv k : U} → C P ty tv → C P ty (tv ⊕ k)
    Ci2  : {ty tv k : U} → C P ty tv → C P ty (k ⊕ tv)
    Cfst : {ty tv k : U} → ⟦ k ⟧ A → C P ty tv → C P ty (tv ⊗ k)
    Csnd : {ty tv k : U} → ⟦ k ⟧ A → C P ty tv → C P ty (k ⊗ tv)
    C⊗   : {ty tv tw tz : U}
         → C P ty tw → C P tv tz → C P (ty ⊗ tv) (tw ⊗ tz)

  Sym : UUSet → UUSet
  Sym P ty tv = P tv ty
\end{code}

\begin{code}
  C-mapM : {ty tv : U}{M : Set → Set}{{m : Monad M}}{P Q : UUSet}
         → (f : ∀{k v} → P k v → M (Q k v))
         → C P ty tv → M (C Q ty tv)
  C-mapM f (CX x) = f x >>= return ∘ CX
  C-mapM f (C⊗ s o) = C-mapM f s >>= λ s' → C-mapM f o >>= return ∘ (C⊗ s')
  C-mapM f (Cfst k s) = C-mapM f s >>= return ∘ (Cfst k)
  C-mapM f (Csnd k s) = C-mapM f s >>= return ∘ (Csnd k)
  C-mapM f (Ci1 s) = C-mapM f s >>= return ∘ Ci1
  C-mapM f (Ci2 s) = C-mapM f s >>= return ∘ Ci2
\end{code}

\begin{code}
  change : {ty tv : U} → ⟦ ty ⟧ A → ⟦ tv ⟧ A → List (C Δ ty tv)
  change {ty ⊗ tv} {tw ⊗ tz} (x1 , x2) (y1 , y2)
    = C⊗ <$> (change x1 y1) <*> (change x2 y2)
  change {ty} {tv ⊕ tw} x (i1 y) = Ci1 <$> (change x y) 
  change {ty} {tv ⊕ tw} x (i2 y) = Ci2 <$> (change x y)
  change {ty} {tw ⊗ tz} x (y1 , y2)
    =  {- return (CX (x , (y1 , y2)))
    ++ -} (Cfst y2 <$> change x y1) 
    ++ (Csnd y1 <$> change x y2)
  change {ty}      x      y      = return (CX (x , y))

  change-sym : {ty tv : U} → ⟦ ty ⟧ A → ⟦ tv ⟧ A → List (C (Sym (C Δ)) ty tv)
  change-sym x y = change x y >>= C-mapM (uncurry (flip change))
\end{code}

\begin{code}
  C-cost : {ty tv : U}{P : UUSet}
         → (costP : ∀{ty tv} → P ty tv → ℕ)
         → C P ty tv → ℕ
  C-cost c (CX x) = c x
  C-cost c (Ci1 s) = 1 + C-cost c s
  C-cost c (Ci2 s) = 1 + C-cost c s
  C-cost c (C⊗ s o) = C-cost c s + C-cost c o
  C-cost c (Cfst {k = k} x s) = size1 sized k x + C-cost c s
  C-cost c (Csnd {k = k} x s) = size1 sized k x + C-cost c s

  CΔ-cost : {ty tv : U} → C Δ ty tv → ℕ
  CΔ-cost = C-cost (λ {ty} {tv} xy → cost-Δ {ty} {tv} xy)

  CSymCΔ-cost : {ty tv : U} → C (Sym (C Δ)) ty tv → ℕ
  CSymCΔ-cost = C-cost CΔ-cost
\end{code}

\begin{code} 
  private
    chooseC : {ty tv : U}{P : UUSet}(costP : ∀{k v} → P k v → ℕ)
            → (s1 s2 : C P ty tv) → C P ty tv
    chooseC c s o with C-cost c s ≤?-ℕ C-cost c o 
    ...| yes _ = s
    ...| no  _ = o

    chooseC* : {ty tv : U}{P : UUSet}(costP : ∀{k v} → P k v → ℕ)
             → C P ty tv → List (C P ty tv) → C P ty tv
    chooseC* c s []       = s
    chooseC* c s (o ∷ os) = chooseC* c (chooseC c s o) os
\end{code}

\begin{code}
  Patch : U → Set
  Patch ty = S (C (Sym (C Δ))) ty

  infixl 20 _<>_ _<>'_
  _<>_ : {ty : U} → Patch ty → Patch ty → Patch ty
  s <> o = chooseS CSymCΔ-cost s o

  _<>'_ : {ty : U} → Patch ty → List (Patch ty) → Patch ty
  s <>' []       = s
  s <>' (o ∷ os) = (s <> o) <>' os

  diff1* : {ty : U} → ⟦ ty ⟧ A → ⟦ ty ⟧ A → List (Patch ty)
  diff1* x y = spine-cp x y 
           >>= S-mapM (uncurry change-sym)

  diff1 : {ty : U} → ⟦ ty ⟧ A → ⟦ ty ⟧ A → Patch ty
  diff1 x y with diff1* x y
  ...| []     = SX (CX (CX (y , x)))
  ...| s ∷ ss = s <>' ss
\end{code}

begin{code}
  diff1 : {ty tv : U} → ⟦ ty ⟧ A → ⟦ tv ⟧ A → S Δ ty tv
  diff1 x y with spine-cp x y
  ...| []     = SX (x , y)
  ...| s ∷ ss = s <>' ss
end{code}
