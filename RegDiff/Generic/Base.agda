open import Prelude
open import Prelude.Vector
open import Prelude.ListProperties using (length-++)

module RegDiff.Generic.Base {n : ℕ}(parms : Vec Set n)  where

{-
  Here we define the universe of regular types and the
  generic functions we need to perform diffing over them.

  Constants will be handled by the vector passed around
  as a module parameter.
-}

  data U : Set where
    I   : U
    u1  : U
    K   : (k : Fin n) → U
    _⊕_ : (ty : U) → (tv : U) → U
    _⊗_ : (ty : U) → (tv : U) → U

  infixr 25 _⊗_
  infixr 22 _⊕_

  ⟦_⟧ : U → Set → Set
  ⟦ I       ⟧ A = A
  ⟦ u1       ⟧ A = Unit
  ⟦ K x     ⟧ A = lookup x parms
  ⟦ ty ⊕ tv ⟧ A = ⟦ ty ⟧ A ⊎ ⟦ tv ⟧ A
  ⟦ ty ⊗ tv ⟧ A = ⟦ ty ⟧ A × ⟦ tv ⟧ A

  data μ (ty : U) : Set where
    ⟨_⟩ : ⟦ ty ⟧ (μ ty) → μ ty

{-
  Generic map
-}

  gmap : {A B : Set}(ty : U)(f : A → B)
       → ⟦ ty ⟧ A → ⟦ ty ⟧ B
  gmap I         f x       = f x
  gmap u1        f x       = unit
  gmap (K k)     f x       = x
  gmap (ty ⊕ tv) f (i1 x)  = i1 (gmap ty f x)
  gmap (ty ⊕ tv) f (i2 y)  = i2 (gmap tv f y)
  gmap (ty ⊗ tv) f (x , y) = gmap ty f x , gmap tv f y

  fgt : {A : Set}(ty : U) → ⟦ ty ⟧ A → ⟦ ty ⟧ Unit
  fgt ty = gmap ty (const unit)

{-
  First we need an arity notion!
-}

  ar : {A : Set}(ty : U) → ⟦ ty ⟧ A → ℕ
  ar I         x       = 1
  ar u1        x       = 0
  ar (K k)     x       = 0
  ar (ty ⊕ tv) (i1 x)  = ar ty x
  ar (ty ⊕ tv) (i2 y)  = ar tv y
  ar (ty ⊗ tv) (x , y) = ar ty x + ar tv y

{-
  A proof that mapping respects arity will be welcome
-}

  gmap-ar-lemma : {A B : Set}(ty : U)(f : A → B)
          → (x : ⟦ ty ⟧ A)
          → ar ty x ≡ ar ty (gmap ty f x)
  gmap-ar-lemma I f x = refl
  gmap-ar-lemma u1 f x = refl
  gmap-ar-lemma (K k) f x = refl
  gmap-ar-lemma (ty ⊕ tv) f (i1 x) = gmap-ar-lemma ty f x
  gmap-ar-lemma (ty ⊕ tv) f (i2 y) = gmap-ar-lemma tv f y
  gmap-ar-lemma (ty ⊗ tv) f (x , y) = cong₂ _+_ (gmap-ar-lemma ty f x) (gmap-ar-lemma tv f y)

{-
  We also need a children's notion, which is basically extracting the
  parameters of our functor
-}

  ch : {A : Set}(ty : U) → ⟦ ty ⟧ A → List A
  ch I         x       = x ∷ []
  ch u1        x       = []
  ch (K k)     x       = []
  ch (ty ⊕ tv) (i1 x)  = ch ty x
  ch (ty ⊕ tv) (i2 y)  = ch tv y
  ch (ty ⊗ tv) (x , y) = ch ty x ++ ch tv y

{-
  It obviously respects arity modulo length
-}

  ch-ar-lemma : {A : Set}(ty : U)
              → (x : ⟦ ty ⟧ A)
              → length (ch ty x) ≡ ar ty x
  ch-ar-lemma I         x       = refl
  ch-ar-lemma u1        x       = refl
  ch-ar-lemma (K k)     x       = refl
  ch-ar-lemma (ty ⊕ tv) (i1 x)  = ch-ar-lemma ty x
  ch-ar-lemma (ty ⊕ tv) (i2 y)  = ch-ar-lemma tv y
  ch-ar-lemma (ty ⊗ tv) (x , y) 
    = trans (length-++ (ch ty x)) 
            (cong₂ _+_ (ch-ar-lemma ty x) (ch-ar-lemma tv y))

  ch-ar-fgt-lemma : {A : Set}(ty : U)
                  → (x : ⟦ ty ⟧ A)
                  → length (ch ty x) ≡ ar ty (fgt ty x)
  ch-ar-fgt-lemma ty x = trans (ch-ar-lemma ty x) (gmap-ar-lemma ty (const unit) x)

{-
  Now a few vector-variants with some fancier types
  to make the typechecker happy
-}

  chv : {A : Set}(ty : U)
      → (x : ⟦ ty ⟧ A) → Vec A (ar ty (fgt ty x))
  chv ty x = vec (ch ty x) (ch-ar-fgt-lemma ty x)

{-
  And finally our plug function, in it's total variant
-}

  plugₜ : {A : Set}(ty : U)
       → (x : ⟦ ty ⟧ Unit) → Vec A (ar ty x) → ⟦ ty ⟧ A
  plugₜ I _ (x ∷ []) = x
  plugₜ u1 x v = unit
  plugₜ (K k) x v = x
  plugₜ (ty ⊕ tv) (i1 x) v = i1 (plugₜ ty x v)
  plugₜ (ty ⊕ tv) (i2 y) v = i2 (plugₜ tv y v)
  plugₜ (ty ⊗ tv) (x , y) v
    = let v0 , v1 = vsplit (ar ty x) v
         in plugₜ ty x v0 , plugₜ tv y v1

  plugₜ-correct
    : {A : Set}(ty : U)
    → (x : ⟦ ty ⟧ A)
    → plugₜ ty (fgt ty x) (chv ty x) ≡ x
  plugₜ-correct I x = refl
  plugₜ-correct u1 unit = refl
  plugₜ-correct (K k) x = refl
  plugₜ-correct (ty ⊕ tv) (i1 x) = cong i1 (plugₜ-correct ty x)
  plugₜ-correct (ty ⊕ tv) (i2 y) = cong i2 (plugₜ-correct tv y)
  plugₜ-correct (ty ⊗ tv) (x , y) 
    with vsplit-elim (ch ty x) (ch tv y) 
                     {(trans (trans (length-++ (ch ty x))
                             (cong₂ _+_ (ch-ar-lemma ty x) (ch-ar-lemma tv y)))
                             (cong₂ _+_ (gmap-ar-lemma ty (λ _ → unit) x)
                             (gmap-ar-lemma tv (λ _ → unit) y)))} 
                     {ch-ar-fgt-lemma ty x} 
                     {ch-ar-fgt-lemma tv y}
  ...| prf rewrite prf = cong₂ _,_ (plugₜ-correct ty x) (plugₜ-correct tv y)

{- 
  Writing the partial is now trivial!
-}

  plug : {A : Set}(ty : U)
       → ⟦ ty ⟧ Unit → List A → Maybe (⟦ ty ⟧ A)
  plug ty x as with length as ≟-ℕ ar ty x
  ...| yes p = just (plugₜ ty x (vec as p))
  ...| no  _ = nothing

  plug-correct
    : {A : Set}(ty : U)
    → (x : ⟦ ty ⟧ A)
    → plug ty (fgt ty x) (ch ty x) ≡ just x
  plug-correct ty x with length (ch ty x) ≟-ℕ ar ty (fgt ty x)
  ...| yes p = cong just (trans (cong (plugₜ ty (fgt ty x)) (vec-reduce (ch ty x))) 
                                (plugₜ-correct ty x))
  ...| no ¬p = ⊥-elim (¬p (ch-ar-fgt-lemma ty x))
  

{-
  Specialized versions for fixedpoints
-}

  μ-ch : {ty : U} → μ ty → List (μ ty)
  μ-ch {ty} ⟨ x ⟩ = ch ty x

  μ-ar : {ty : U} → μ ty → ℕ
  μ-ar {ty} ⟨ x ⟩ = ar ty x
  
