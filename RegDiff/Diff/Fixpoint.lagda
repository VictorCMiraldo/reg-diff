\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

module RegDiff.Diff.Fixpoint
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  -- open Monad {{...}}
  open Applicative {{...}}

  open import RegDiff.Generic.Base v
  open import RegDiff.Generic.Eq v eqs

  instance
    μ-eq : {T : U} → Eq (μ T)
    μ-eq = eq dec-eqμ
\end{code}

  Tying the know for fixpoints is not so hard.
  The important insight is that the parameter A
  is going to be (μ T) now.

  We hence abstract T as a module parameter.

\begin{code}
  module Internal (T : U) where
\end{code}

  Now we open the spine module with the correct parameters

\begin{code}
    open import RegDiff.Diff.Spine v eqs (μ T) μ-size
      hiding (_<>_)
      public
\end{code}

  And declare a relation between U's that will let us tie the
  final knot. Remember that a value of a fixedpoint allows
  for recursing into it's variables or inserting something
  on a variable.

  We keep carrying around a parameter P for convenience.

%<*SI-def>
\begin{code}
    data SI (P : UUSet) : U → U → Set where
      Svar : S (SI P) T T → SI P I I
      Sins : S (SI P) T I → SI P T T
      SY   : {ty tv : U} → P ty tv → SI P ty tv
\end{code}
%</SI-def>

  Just like with spines, we can define costs for (S ∘ SI)

\begin{code}
    Sμ : U → U → Set
    Sμ ty tv = List (S (SI Δ) ty tv)

    {-# TERMINATING #-}
    SI-cost : {ty tv : U}{P : UUSet}
            → (costP : ∀{ty tv} → P ty tv → ℕ)
            → SI P ty tv → ℕ
    SI-cost c (Svar x) = S-cost (SI-cost c) x
    SI-cost c (Sins x) = 1 + S-cost (SI-cost c) x
    SI-cost c (SY x) = c x

    Sμ1-cost : {ty tv : U} → S (SI Δ) ty tv → ℕ
    Sμ1-cost = S-cost (SI-cost (λ {ty} {tv} xy → cost-Δ {ty} {tv} xy))

    infixr 20 _<>_
    _<>_ : {ty tv : U} → S (SI Δ) ty tv → List (S (SI Δ) ty tv) →  S (SI Δ) ty tv
    s <> [] = s
    s <> (o ∷ os) with Sμ1-cost s ≤?-ℕ Sμ1-cost o 
    ...| yes _ = s <> os
    ...| no  _ = o <> os
\end{code}

  We also need a monadic map over S.

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

  Diffing a value of a fixed point is defined next.

  Note how it is important to NOT get out of the list monad until
  we have computed everything. Otherwise we will not be exploring
  every possibility.

\begin{code}
    mutual
      {-# TERMINATING #-}
      refine : {ty tv : U} → Δ ty tv → List (SI Δ ty tv)
      refine {I} {I} (x , y)   = Svar <$> (spineμ x y)
      refine {ty} {tv} (x , y) = return (SY (x , y))

      spineμ' : {ty tv : U} → ⟦ ty ⟧ (μ T) → ⟦ tv ⟧ (μ T) → Sμ ty tv
      spineμ' x y = spine x y >>= S-mapM refine

      spineμ : μ T → μ T → Sμ T T
      spineμ ⟨ x ⟩ ⟨ y ⟩ 
        =  spineμ' x y
        ++ ((SX ∘ Sins)        <$> (spineμ' x ⟨ y ⟩))
        ++ ((Ssym ∘ SX ∘ Sins) <$> (spineμ' y ⟨ x ⟩))
\end{code}

  Finally, we can choose the actual patch between all possibilities when we have computed
  all of them.

  We have to stay in the List monad in order to guarantee that the algorithm
  is exploring all possiblities.

\begin{code}
    diffμ : μ T → μ T → S (SI Δ) T T
    diffμ x y with spineμ x y
    ...| []     = SX (SY (unmu x , unmu y))
    ...| s ∷ ss = s <> ss
\end{code}

  Application is trivial.

\begin{code}
    mutual
      applyₗ-SI : {ty tv : U} → SI Δ ty tv → ⟦ ty ⟧ (μ T) → Maybe (⟦ tv ⟧ (μ T))
      applyₗ-SI (Svar x) el = ⟨_⟩ <$> applyμₗ x (unmu el)
      applyₗ-SI (Sins x) el = unmu <$> applyμₗ x el
      applyₗ-SI {ty} {tv} (SY x) el = goₗ apply-Δ {ty} {tv} x el

      applyᵣ-SI : {ty tv : U} → SI Δ ty tv → ⟦ tv ⟧ (μ T) → Maybe (⟦ ty ⟧ (μ T))
      applyᵣ-SI (Svar x) el = ⟨_⟩ <$> applyμᵣ x (unmu el)
      applyᵣ-SI (Sins x) el = applyμᵣ x ⟨ el ⟩
      applyᵣ-SI {ty} {tv} (SY x) el = goᵣ apply-Δ {ty} {tv} x el

      {-# TERMINATING #-}
      applyμₗ : {ty tv : U} → S (SI Δ) ty tv → ⟦ ty ⟧ (μ T) → Maybe (⟦ tv ⟧ (μ T))
      applyμₗ s x = applyₗ (apply applyₗ-SI applyᵣ-SI) s x

      applyμᵣ : {ty tv : U} → S (SI Δ) ty tv → ⟦ tv ⟧ (μ T) → Maybe (⟦ ty ⟧ (μ T))
      applyμᵣ s x = applyᵣ (apply applyₗ-SI applyᵣ-SI) s x

    applyμ♭ : S (SI Δ) T T → μ T → Maybe (μ T)
    applyμ♭ s ⟨ x ⟩ = ⟨_⟩ <$> applyμₗ s x
\end{code}

  Domains and Ranges:

\begin{code}
    open import RegDiff.Diff.DomRan v eqs (μ T) μ-size
      public

    mutual
      {-# TERMINATING #-}
      SI-dom : {ty tv : U} → SI Δ ty tv → (⟦ ty ⟧ (μ T) → Set)
      SI-dom (Svar x)     = dom SI-domran x ∘ unmu 
      SI-dom (Sins x)     = dom SI-domran x
      SI-dom (SY (x , _)) = (x ≡_)

      SI-ran : {ty tv : U} → SI Δ ty tv → (⟦ tv ⟧ (μ T) → Set)
      SI-ran (Svar x)     = ran SI-domran x ∘ unmu
      SI-ran (Sins x)     = ran SI-domran x ∘ ⟨_⟩ 
      SI-ran (SY (_ , y)) = (y ≡_)

      SI-domran : HasDomRan (SI Δ)
      SI-domran = hasdomran SI-dom SI-ran

    domμ : {ty tv : U} → S (SI Δ) ty tv → ⟦ ty ⟧ (μ T) → Set
    domμ = dom SI-domran

    ranμ : {ty tv : U} → S (SI Δ) ty tv → ⟦ tv ⟧ (μ T) → Set
    ranμ = ran SI-domran
\end{code}
