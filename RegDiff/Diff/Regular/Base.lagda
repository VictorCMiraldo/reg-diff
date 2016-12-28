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
\end{code}

  We begin with the definition of a spine. The spine is 
  responsible for agressively copying structure.
 
  Scp copies the whole structure where Scns copies only
  the top most constructor. Note that we do NOT align
  values comming from the same constructor.

%<*Spine-def>
\begin{code}
  data S (P : UUSet) : U → Set where
    SX   : {ty : U} → P ty ty → S P ty
    Scp  : {ty : U} → S P ty
    Scns : {ty : U}(i : Constr ty)
         → ListI (contr P ∘ α) (typeOf ty i)
         → S P ty
\end{code}
%</Spine-def>

%<*S-map-def>
\begin{code}
  S-map  :  {ty : U}
            {P Q : UUSet}(X : ∀{k v} → P k v → Q k v)
         → S P ty → S Q ty
  S-map f (SX x)       = SX (f x)
  S-map f Scp          = Scp
  S-map f (Scns i xs)  = Scns i (mapᵢ f xs)
\end{code}
%</S-map-def>
%<*S-mapM-def>
\begin{code}
  S-mapM  :  {ty : U}{M : Set → Set}{{m : Monad M}}
             {P Q : UUSet}(X : ∀{k v} → P k v → M (Q k v))
          → S P ty → M (S Q ty)
  S-mapM f (SX x)       = f x >>= return ∘ SX
  S-mapM f Scp          = return Scp
  S-mapM f (Scns i xs)  = mapMᵢ f xs >>= return ∘ (Scns i)
\end{code}
%</S-mapM-def>

%<*S-cost-def>
\begin{code}
  S-cost : {ty : U}{P : UUSet}(doP : {k v : U} → P k v → ℕ)
         → S P ty → ℕ
  S-cost doP (SX x)      = doP x
  S-cost doP Scp         = 0
  S-cost doP (Scns i xs) = foldrᵢ (λ h r → doP h + r) 0 xs
\end{code}
%</S-cost-def>

%<*zip-product-def>
\begin{code}
  zipₚ : {ty : Π}
       → ⟦ ty ⟧ₚ → ⟦ ty ⟧ₚ → ListI (λ k → Δₛ (α k) (α k)) ty
  zipₚ {[]}     _        _         
    = []
  zipₚ {_ ∷ ty} (x , xs) (y , ys)  
    = (i1 (x , unit) , i1 (y , unit)) ∷ zipₚ xs ys
\end{code}
%</zip-product-def>
%<*spine-def>
\begin{code}
  spine-cns : {ty : U}(x y : ⟦ ty ⟧) → S Δₛ ty
  spine-cns x y  with sop x | sop y
  spine-cns _ _ | strip cx dx | strip cy dy
    with cx ≟-Fin cy
  ...| no  _     = SX (inject cx dx , inject cy dy)
  spine-cns _ _ | strip _ dx | strip cy dy
     | yes refl  = Scns cy (zipₚ dx dy)
  
  spine : {ty : U}(x y : ⟦ ty ⟧) → S Δₛ ty
  spine {ty} x y 
    with dec-eq _≟-A_ ty x y 
  ...| yes _     = Scp
  ...| no  _     = spine-cns x y
\end{code}
%</spine-def>

  Unsurprisingly, when a spine can't copy anything
  we gotta perform a change!

%<*C-def>
\begin{code}
  data C (P : ΠΠSet) : U → U → Set where
    CX  : {ty tv : U}
        → (i : Constr ty)(j : Constr tv)
        → P (typeOf ty i) (typeOf tv j) 
        → C P ty tv
\end{code}
%</C-def>
%<*C-map-def>
\begin{code}
  C-map  :  {ty tv : U}
            {P Q : ΠΠSet}(X : ∀{k v} → P k v → Q k v)
         → C P ty tv → C Q ty tv
  C-map f (CX i j x) = CX i j (f x)
\end{code}
%</C-map-def>
%<*C-mapM-def>
\begin{code}
  C-mapM  :  {ty tv : U}{M : Set → Set}{{m : Monad M}}
             {P Q : ΠΠSet}(X : ∀{k v} → P k v → M (Q k v))
          → C P ty tv → M (C Q ty tv)
  C-mapM f (CX i j x) = f x >>= return ∘ CX i j
\end{code}
%</C-mapM-def>
%<*C-cost>
\begin{code}
  C-cost  : {ty tv : U}{P : ΠΠSet}(doP : {k v : Π} → P k v → ℕ)
          → C P ty tv → ℕ
  C-cost doP (CX i j x) = doP x
\end{code}
%</C-cost>
%<*change-def>
\begin{code}
  change : {ty tv : U} → ⟦ ty ⟧ → ⟦ tv ⟧ → C Δₚ ty tv
  change x y with sop x | sop y
  change _ _ | strip cx dx | strip cy dy = CX cx cy (dx , dy)
\end{code}
%</change-def>

  Last but not least, we are left with products that need some alignment!

%<*Al-def>
\begin{code}
  data Al (P : AASet) : Π → Π → Set where
    A0   :                                          Al P [] []
    Ap1  : ∀{a ty tv}     → ⟦ a ⟧ₐ  → Al P ty tv →  Al P (a ∷ ty) tv
    Ap1ᵒ : ∀{a ty tv}     → ⟦ a ⟧ₐ  → Al P ty tv →  Al P ty       (a ∷ tv)
    AX   : ∀{a a' ty tv}  → P a a'  → Al P ty tv →  Al P (a ∷ ty) (a' ∷ tv)
\end{code}
%</Al-def>

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
  is-ap1 : {ty tv : Π} → Al Δₐ ty tv → Bool
  is-ap1 (Ap1 _ _) = true
  is-ap1 _         = false

  is-ap1ᵒ : {ty tv : Π} → Al Δₐ ty tv → Bool
  is-ap1ᵒ (Ap1ᵒ _ _) = true
  is-ap1ᵒ _          = false 
\end{code}
%<*align-star-def>
\begin{code}
  align* : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ → List (Al Δₐ ty tv)
  align* {[]}     {[]}     m n = return A0
  align* {[]}     {v ∷ tv} m (n , nn) 
    = Ap1ᵒ n <$> align* m nn
  align* {y ∷ ty} {[]}     (m , mm) n 
    = Ap1 m <$> align* mm n
  align* {y ∷ ty} {v ∷ tv} (m , mm) (n , nn)
    =  AX (m , n)   <$> align* mm nn
    ++ Ap1  m       <$> filter (not ∘ is-ap1ᵒ)  (align* mm (n , nn))
    ++ Ap1ᵒ n       <$> filter (not ∘ is-ap1)   (align* (m , mm) nn)
\end{code}
%</align-star-def>

%<*Patch-def>
\begin{code}
  Patch : AASet → U → Set
  Patch P = S (C (Al P))
\end{code}
%</Patch-def>
\begin{code}
  Patch-cost : {ty : U}{P : AASet}(doP : ∀{k v} → P k v → ℕ)
             → Patch P ty → ℕ
  Patch-cost doP = S-cost (C-cost (Al-cost doP))

  Patch-mapM : {ty : U}{M : Set → Set}{{m : Monad M}}
               {P Q : AASet}(X : ∀{k v} → P k v → M (Q k v))
             → Patch P ty → M (Patch Q ty)
  Patch-mapM X = S-mapM (C-mapM (Al-mapM X))
\end{code}
\begin{code}
  Patch-cost-Δₐ : {ty : U} → Patch Δₐ ty → ℕ
  Patch-cost-Δₐ = Patch-cost (λ {k} {v} → cost-Δₐ {k} {v})

  Patch* : U → Set
  Patch* = List ∘ Patch Δₐ

  Patch& : U → Set
  Patch& = List ∘ (ℕ ×_) ∘ Patch Δₐ

  addCosts : {ty : U} → Patch* ty → Patch& ty
  addCosts = map (λ k → Patch-cost-Δₐ k , k)

  choose : {ty : U} → Patch Δₐ ty → Patch Δₐ ty → Patch Δₐ ty
  choose c d with Patch-cost-Δₐ c ≤?-ℕ Patch-cost-Δₐ d
  ...| yes _ = d
  ...| no  _ = c

  _<>_ : {ty : U} → Patch Δₐ ty → List (Patch Δₐ ty) → Patch Δₐ ty
  c <> [] = c
  c <> (d ∷ ds) = (choose c d) <> ds
\end{code}
%<*diff1-star-def>
\begin{code}
  diff1* : {ty : U}(x y : ⟦ ty ⟧) → Patch* ty
  diff1* x y = S-mapM (C-mapM (uncurry align*) ∘ uncurry change) (spine x y)
\end{code}
%</diff1-star-def>
%<*diff1-def>
\begin{code}
  diff1 : {ty : U} → ⟦ ty ⟧ → ⟦ ty ⟧ → Patch Δₐ ty
  diff1 x y with diff1* x y
  ...| s ∷ ss = s <> ss
  ...| []     = impossible
     where postulate impossible : {ty : U} → Patch Δₐ ty
\end{code}
%</diff1-def>
