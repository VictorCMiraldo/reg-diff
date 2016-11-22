  Here we define a refinement over the trivial diff.
  Instead of storing both values as a whole,
  we will store a bunch of transformations that
  could transform one into the other.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Base
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where

  open Monad {{...}}

  open import RegDiff.Generic.Multirec ks
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Trivial.Base ks keqs A WBA
    public
\end{code}

  An inhabitant of S represents a spine. 
  A Spine intuitively is the maximal shared prefix between two
  elements of the same type.

  Here we also add a Copy (Scp) instruction, representing
  the fact that both elements are propositionally equal.

  It is unsure to us, at this point, whether Scp should belong
  here or to Δ.

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
  S-mapM  : {ty : U}{M : Set → Set}{{m : Monad M}}{P Q : UUSet}
          → (f : ∀{k} → P k k → M (Q k k))
          → S P ty → M (S Q ty)
  S-mapM f (SX x)    = f x >>= return ∘ SX
  S-mapM f Scp       = return Scp
  S-mapM f (S⊗ s o)  = S-mapM f s >>= λ s' → S-mapM f o >>= return ∘ (S⊗ s')
  S-mapM f (Si1 s)   = S-mapM f s >>= return ∘ Si1
  S-mapM f (Si2 s)   = S-mapM f s >>= return ∘ Si2

  S-map  : {ty : U}{P Q : UUSet}
          → (f : ∀{k} → P k k → Q k k)
          → S P ty → S Q ty
  S-map f (SX x)    = SX (f x)
  S-map f Scp       = Scp
  S-map f (S⊗ s o)  = S⊗ (S-map f s) (S-map f o)
  S-map f (Si1 s)   = Si1 (S-map f s)
  S-map f (Si2 s)   = Si2 (S-map f s)
\end{code}

  Computing the inhabitants of S is fairly simple:

%<*spine-def>
\begin{code}
  mutual
    spine-cp : {ty : U} → ⟦ ty ⟧ A → ⟦ ty ⟧ A → S Δ ty
    spine-cp {ty} x y
      with dec-eq _≟-A_ ty x y 
    ...| no  _ = spine x y
    ...| yes _ = Scp
    
    spine : {ty : U} → ⟦ ty ⟧ A → ⟦ ty ⟧ A → S Δ ty
    spine {ty ⊗ tv}  (x1 , x2)  (y1 , y2) 
      = S⊗ (spine-cp x1 y1) (spine-cp x2 y2)
    spine {tv ⊕ tw}  (i1 x)     (i1 y)  = Si1 (spine-cp x y) 
    spine {tv ⊕ tw}  (i2 x)     (i2 y)  = Si2 (spine-cp x y)
    spine {ty}       x          y       = SX (delta {ty} {ty} x y)
\end{code}
%</spine-def>

\begin{code}
  spine-list : {ty : U} → ⟦ ty ⟧ A → ⟦ ty ⟧ A → List (S Δ ty)
  spine-list x = return ∘ spine-cp x
\end{code}

  But we eventually need to choose one of them! In fact, the patch between
  (x : ⟦ ty ⟧ A) and (y : ⟦ tv ⟧ A) is the one with the lowest cost!

%<*S-cost-def>
\begin{code}
  S-cost : {ty : U}{P : UUSet}
         → (costP : ∀{ty} → P ty ty → ℕ)
         → S P ty → ℕ
  S-cost c (SX x)   = c x
  S-cost c Scp      = 0
  S-cost c (S⊗ s o) = S-cost c s + S-cost c o
  S-cost c (Si1 s)  = S-cost c s
  S-cost c (Si2 s)  = S-cost c s
\end{code}
%</S-cost-def>

\begin{code}
  SΔ-cost : {ty : U} → S Δ ty → ℕ
  SΔ-cost = S-cost (λ {ty} xy → cost-Δ {ty} {ty} xy)
\end{code}

  Here we add some binary operators to choose
  between S's as long as we can compute the cost
  of P's inside of S.

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

  Now that we can extract the shared prefix between an (x , y : ⟦ ty ⟧ A),
  we need to be able to change the non-agreeing parts.
  
  First we start by adapting coproducts. Here we are making the symmetric nature of this
  step explicit.

  An inhabitant of C tells us which coproducts to insert or pattern-match
  in order to bet the best candidate for alignment.

%<*C-def>
\begin{code}
  data C (P : UUSet) : U → U → Set where
    CX    : {ty tv : U}   → P ty tv → C P ty tv
    Ci1   : {ty tv k : U} → C P ty tv → C P ty (tv ⊕ k)
    Ci2   : {ty tv k : U} → C P ty tv → C P ty (k ⊕ tv)
    Ci1ᵒ  : {ty tv k : U} → C P ty tv → C P (ty ⊕ k) tv
    Ci2ᵒ  : {ty tv k : U} → C P ty tv → C P (k ⊕ ty) tv
\end{code}
%</C-def>

  Just like S, we can map over these guys.

\begin{code}
  C-mapM : {ty tv : U}{M : Set → Set}{{m : Monad M}}{P Q : UUSet}
         → (f : ∀{k v} → P k v → M (Q k v))
         → C P ty tv → M (C Q ty tv)
  C-mapM f (CX x) = f x >>= return ∘ CX
  C-mapM f (Ci1 s) = C-mapM f s >>= return ∘ Ci1
  C-mapM f (Ci2 s) = C-mapM f s >>= return ∘ Ci2
  C-mapM f (Ci1ᵒ s) = C-mapM f s >>= return ∘ Ci1ᵒ 
  C-mapM f (Ci2ᵒ s) = C-mapM f s >>= return ∘ Ci2ᵒ

  C-map : {ty tv : U}{P Q : UUSet}
         → (f : ∀{k v} → P k v → Q k v)
         → C P ty tv → C Q ty tv
  C-map f (CX x)  = CX (f x)
  C-map f (Ci1 s) = Ci1 (C-map f s)
  C-map f (Ci2 s) = Ci2 (C-map f s)
  C-map f (Ci1ᵒ s) = Ci1ᵒ (C-map f s)
  C-map f (Ci2ᵒ s) = Ci2ᵒ (C-map f s)
\end{code}

%<*change-def>
\begin{code}
  change : {ty tv : U} → ⟦ ty ⟧ A → ⟦ tv ⟧ A → C Δ ty tv
  change {ty} {tv ⊕ tw} x (i1 y) = Ci1  (change x y) 
  change {ty} {tv ⊕ tw} x (i2 y) = Ci2  (change x y)
  change {ty ⊕ tw} {tv} (i1 x) y = Ci1ᵒ (change x y) 
  change {ty ⊕ tw} {tv} (i2 x) y = Ci2ᵒ (change x y)
  change {ty} {tv}      x      y = CX (delta {ty} {tv} x y)
\end{code}
\begin{code}
  change-list : {ty tv : U} → ⟦ ty ⟧ A → ⟦ tv ⟧ A → List (C Δ ty tv)
  change-list x = return ∘ change x
\end{code}
%</change-def>

  We can also assign costs to them, in order to choose the
  best one.

%<*C-cost-def>
\begin{code}
  C-cost : {ty tv : U}{P : UUSet}
         → (costP : ∀{ty tv} → P ty tv → ℕ)
         → C P ty tv → ℕ
  C-cost c (CX x)    = c x
  C-cost c (Ci1 s)   = 1 + C-cost c s
  C-cost c (Ci2 s)   = 1 + C-cost c s
  C-cost c (Ci1ᵒ s)  = 1 + C-cost c s
  C-cost c (Ci2ᵒ s)  = 1 + C-cost c s
\end{code}
%</C-cost-def>

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

  Finally, we will be left with with two different products.
  And this is where the notion of alignment comes into play.

  An inhabitnat of Al represents a product alignment.
  The workflow is the same as with S and C; Al makes
  an indexed functor; we can compute it's cost, and
  we can compute it's inhabitants.

%<*Al-def>
\begin{code}
  data Al (P : UUSet) : U → U → Set where
    AX    : {ty tv : U}     → P ty tv → Al P ty tv
    Ap1   : {ty tv tw : U}  → ⟦ tw ⟧ A → Al P ty tv → Al P ty (tv ⊗ tw)
    Ap1ᵒ  : {ty tv tw : U}  → ⟦ tw ⟧ A → Al P ty tv → Al P (ty ⊗ tw) tv
    Ap2   : {ty tv tw : U}  → ⟦ tw ⟧ A → Al P ty tv → Al P ty (tw ⊗ tv)
    Ap2ᵒ  : {ty tv tw : U}  → ⟦ tw ⟧ A → Al P ty tv → Al P (tw ⊗ ty) tv
    A⊗    : {ty tv tw tz : U}
          → Al P ty tw → Al P tv tz → Al P (ty ⊗ tv) (tw ⊗ tz)
\end{code}
%</Al-def>

\begin{code}
  Al-mapM : {ty tv : U}{M : Set → Set}{{m : Monad M}}{P Q : UUSet}
          → (f : ∀{k v} → P k v → M (Q k v))
          → Al P ty tv → M (Al Q ty tv)
  Al-mapM f (AX x) = f x >>= return ∘ AX
  Al-mapM f (A⊗ al bl)
    = Al-mapM f al >>= λ al' → Al-mapM f bl >>= return ∘ (A⊗ al')
  Al-mapM f (Ap1 x al) = Al-mapM f al >>= return ∘ (Ap1 x)
  Al-mapM f (Ap1ᵒ x al) = Al-mapM f al >>= return ∘ (Ap1ᵒ x)
  Al-mapM f (Ap2 x al) = Al-mapM f al >>= return ∘ (Ap2 x)
  Al-mapM f (Ap2ᵒ x al) = Al-mapM f al >>= return ∘ (Ap2ᵒ x)
\end{code}

  Producing an alignment is where our options are really open.
  We could check for permutations, or allow for different
  types of alignments.

  Obviusly, the more expressive the alignment, the more
  expensive it's computation.

%<*align-all-paths-def>
\begin{code}
  align : {ty tv : U} → ⟦ ty ⟧ A → ⟦ tv ⟧ A → List (Al Δ ty tv)
  align {ty ⊗ ty'} {tv ⊗ tv'} (x1 , x2) (y1 , y2) 
    =  A⊗ <$> align x1 y1 <*> align x2 y2
    ++ Ap1  y2 <$> align (x1 , x2) y1
    ++ Ap2  y1 <$> align (x1 , x2) y2
    ++ Ap1ᵒ x2 <$> align x1 (y1 , y2)
    ++ Ap2ᵒ x1 <$> align x2 (y1 , y2)
\end{code}
%</align-all-paths-def>
%<*align-rest-def>
\begin{code}
  align {ty ⊗ ty'} {tv} (x1 , x2) y 
    =  Ap1ᵒ x2 <$> align x1 y
    ++ Ap2ᵒ x1 <$> align x2 y
  align {ty} {tv ⊗ tv'} x (y1 , y2) 
    =  Ap1  y2 <$> align x y1
    ++ Ap2  y1 <$> align x y2
  align {ty} {tv} x y = return (AX (x , y))
\end{code}
%</align-rest-def>
%<*Al-cost-def>
\begin{code}
  Al-cost : {ty tv : U}{P : UUSet}
          → (costP : ∀{ty tv} → P ty tv → ℕ)
          → Al P ty tv → ℕ
  Al-cost c (AX xy) = c xy
  Al-cost c (A⊗ s o) = Al-cost c s + Al-cost c o
  Al-cost c (Ap1  {tw = k} x s) = size1 sized k x + Al-cost c s
  Al-cost c (Ap2  {tw = k} x s) = size1 sized k x + Al-cost c s
  Al-cost c (Ap1ᵒ {tw = k} x s) = size1 sized k x + Al-cost c s
  Al-cost c (Ap2ᵒ {tw = k} x s) = size1 sized k x + Al-cost c s
\end{code}
%</Al-cost-def>

\begin{code}
  AlΔ-cost : {ty tv : U} → Al Δ ty tv → ℕ
  AlΔ-cost = Al-cost (λ {ty} {tv} xy → cost-Δ {ty} {tv} xy)
\end{code}

  Finally, we can diff values of regular types!

  A Patch then is a skeleton followed by some pattern matching;
  followed by some injections followed by some alignment.

  Note that we could have made the symmetry of C internal
  to it's definition. We are still not sure
  which one to use.

%<*Patch-def>
\begin{code}
  Patch : U → Set
  Patch ty = S (C (Al Δ)) ty
\end{code}
%</Patch-def>

\begin{code}
  infixl 20 _<>_ _<>'_
  _<>_ : {ty : U} → Patch ty → Patch ty → Patch ty
  s <> o = chooseS (C-cost AlΔ-cost) s o

  _<>'_ : {ty : U} → Patch ty → List (Patch ty) → Patch ty
  s <>' []       = s
  s <>' (o ∷ os) = (s <> o) <>' os
\end{code}

  Here is the final algorithm.
  
%<*diff1-nondet-def>
\begin{code}
  diff1* : {ty : U} → ⟦ ty ⟧ A → ⟦ ty ⟧ A → List (Patch ty)
  diff1* x y = S-mapM (C-mapM (uncurry align) ∘ uncurry change) (spine-cp x y)
\end{code}
%</diff1-nondet-def>
%<*diff1-def>
\begin{code}
  diff1 : {ty : U} → ⟦ ty ⟧ A → ⟦ ty ⟧ A → Patch ty
  diff1 x y with diff1* x y
  ...| []     = SX (CX (AX (x , y)))
  ...| s ∷ ss = s <>' ss
\end{code}
%</diff1-def>
