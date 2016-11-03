  Here we define the base notion of the spine of two values.

  First we set the stage:

    We will be getting a spine of elements of type (⟦ ty ⊗ tv ⟧ A)
    Here, we require that A is a setoid equipped with a measure
    function over it's elements.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Diff.Spine
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)(A : Set)
       {{eqA : Eq A}}(sized : A → ℕ)
    where

  open Monad {{...}}
\end{code}

  First, we import the universe constructions
  for the correct parameters.

  We also initialize some synonyms for convenience.

\begin{code}
  open import RegDiff.Generic.Base v
  open import RegDiff.Generic.Eq v eqs
  open import RegDiff.Diff.Base v eqs A sized
    public
\end{code}

  As we already know, Δ models the trivial diff
  algorithm. Henceforth, we will use it as a primitive.


  
  Now, an S is something that describes a way of transforming
  an element (x : ⟦ ty ⟧ A) into and element (y : ⟦ tv ⟧ A).

  This transformation happens in two cyclic phases: pattern
  matching on the right or adding information to the left.
  We keep repeating this until we are left with matching things.
  The change of phase happens by Ssym.

  The full datatype is as follows:

%<*S-def>
\begin{code}
  data S (P : UUSet) : U → U → Set where
    SX   : {ty tv : U} → P ty tv → S P ty tv
    Ssym : {ty tv : U} → S P ty tv → S P tv ty
    Scp  : {ty : U} → S P ty ty
    S⊗   : {ty tv tw tz : U} 
         → S P ty tw → S P tv tz → S P (ty ⊗ tv) (tw ⊗ tz)
    Sfst : {ty tv k : U}
         → ⟦ k ⟧ A → S P ty tv → S P ty (tv ⊗ k)
    Ssnd : {ty tv k : U}
         → ⟦ k ⟧ A → S P ty tv → S P ty (k ⊗ tv)
    Si1  : {ty tv k : U} 
         → S P ty tv → S P ty (tv ⊕ k)
    Si2  : {ty tv k : U} 
         → S P ty tv → S P ty (k ⊕ tv)
\end{code}
%</S-def>

  Note that each inhabitant s of (S P ty tv) is specifying a partial
  function, trₛ : ⟦ ty ⟧ A → ⟦ tv ⟧ A. 

  As expected, We can map over S:

\begin{code}
  S-mapM : {ty tv : U}{M : Set → Set}{{m : Monad M}}{P Q : UUSet}
         → (f : ∀{k v} → P k v → M (Q k v))
         → S P ty tv → M (S Q ty tv)
  S-mapM f (SX x) = f x >>= return ∘ SX
  S-mapM f (Ssym s) = S-mapM f s >>= return ∘ Ssym
  S-mapM f Scp = return Scp
  S-mapM f (S⊗ s o) = S-mapM f s >>= λ s' → S-mapM f o >>= return ∘ (S⊗ s')
  S-mapM f (Sfst x s) = S-mapM f s >>= return ∘ (Sfst x)
  S-mapM f (Ssnd x s) = S-mapM f s >>= return ∘ (Ssnd x)
  S-mapM f (Si1 s) = S-mapM f s >>= return ∘ Si1
  S-mapM f (Si2 s) = S-mapM f s >>= return ∘ Si2
\end{code}

  And we can compute the set of all ways of changing the first
  element into the second element of a pair:

  This can be seen as an arrow, in the category of relations,
  between (for all A)

    ⟦ ty ⊗ tv ⟧ ---> S Δ ty tv

\begin{code}
  mutual
    spine-cp : {ty tv : U} → ⟦ ty ⟧ A → ⟦ tv ⟧ A → List (S Δ ty tv)
    spine-cp {ty} {tv} x y with U-eq ty tv
    ...| no _ = spine x y
    spine-cp {ty} {.ty} x y | yes refl
      with dec-eq ty x y 
    ...| no  _ = spine x y
    ...| yes _ = return Scp
    
    spine : {ty tv : U} → ⟦ ty ⟧ A → ⟦ tv ⟧ A → List (S Δ ty tv)
    spine {ty ⊗ tv} {tw ⊗ tz} (x1 , x2) (y1 , y2) 
      = S⊗ <$> (spine-cp x1 y1) <*> (spine-cp x2 y2)
    -- spine {ty ⊕ tv} {tw ⊕ tz} (i1 x) (i1 y) = (Si1 ∘ Ssym ∘ Si1) <$> (spine-cp y x)
    -- spine {ty ⊕ tv} {tw ⊕ tz} (i2 x) (i2 y) = (Si2 ∘ Ssym ∘ Si2) <$> (spine-cp y x)
    spine {ty} {tv ⊕ tw} x (i1 y) = Si1 <$> (spine-cp x y) 
    spine {ty} {tv ⊕ tw} x (i2 y) = Si2 <$> (spine-cp x y)
    spine {ty ⊕ tv} {tw} (i1 x) y = (Ssym ∘ Si1) <$> (spine-cp y x) 
    spine {ty ⊕ tv} {tw} (i2 x) y = (Ssym ∘ Si2) <$> (spine-cp y x)
    spine {ty ⊗ tv} {tw} (x1 , x2) y
      = Ssym <$> ((Sfst x2 <$> (spine-cp y x1)) ++ (Ssnd x1 <$> (spine-cp y x2)))
    spine {ty} {tv ⊗ tw} x (y1 , y2)
      = (Sfst y2 <$> (spine-cp x y1)) ++ (Ssnd y1 <$> (spine-cp x y2))
    spine {ty} {tv} x y 
      = return (SX (x , y))
\end{code}

  But we eventually need to choose one of them! In fact, the patch between
  (x : ⟦ ty ⟧ A) and (y : ⟦ tv ⟧ A) is the spine with the lowest cost!

\begin{code}
  S-cost : {ty tv : U}{P : UUSet}
         → (costP : ∀{ty tv} → P ty tv → ℕ)
         → S P ty tv → ℕ
  S-cost c (SX x) = c x
  S-cost c (Ssym s) = S-cost c s
  S-cost c Scp = 0
  S-cost c (S⊗ s o) = S-cost c s + S-cost c o
  S-cost c (Sfst {k = k} x s) = size1 sized k x + S-cost c s
  S-cost c (Ssnd {k = k} x s) = size1 sized k x + S-cost c s
  -- S-cost c (Si1 (Ssym (Si1 s))) = S-cost c s
  -- S-cost c (Si2 (Ssym (Si2 s))) = S-cost c s
  S-cost c (Si1 s) = 1 + S-cost c s
  S-cost c (Si2 s) = 1 + S-cost c s

  SΔ-cost : {ty tv : U} → S Δ ty tv → ℕ
  SΔ-cost = S-cost (λ {ty} {tv} xy → cost-Δ {ty} {tv} xy)
\end{code}


\begin{code}      
  infixr 20 _<>_ _<>'_
  _<>_ : {ty tv : U}(s1 s2 : S Δ ty tv) → S Δ ty tv
  s <> o with SΔ-cost s ≤?-ℕ SΔ-cost o 
  ...| yes _ = s
  ...| no  _ = o

  _<>'_ : {ty tv : U} → S Δ ty tv → List (S Δ ty tv) → S Δ ty tv
  s <>' [] = s
  s <>' (o ∷ os) = (s <> o) <>' os

  
\end{code}

  And finally, we can diff things! Note that spine-cp will NEVER be empty.
  In the worst case scenario, it gives a (SX (x , y)).

\begin{code}
  diff1 : {ty tv : U} → ⟦ ty ⟧ A → ⟦ tv ⟧ A → S Δ ty tv
  diff1 x y with spine-cp x y
  ...| []     = SX (x , y)
  ...| s ∷ ss = s <>' ss
\end{code}

  Now, this is all too nice, but S is in fact defining two Prisms!
  We can see this through the apply functions:

  First we need our parameter type to be "appliable"



  Now we can define applyₗ and applyᵣ. One adds constructors,
  the other pattern-matches. The phase change happens with Ssym.

  Note that (applyₗ s) is the partial bijection defined by (s : S P ty tv).
  We say that the PATCH between x and y is the s that defines
  (applyₗ s) x ≡ y and maximizes the domain of (applyₗ s).
