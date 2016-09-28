open import Prelude
open import Prelude.Vector
open import Prelude.Monad

{-
  Here we exploit the connection between patches
  and lists of locations!
-}

module RegDiff.Diff.Views.Loc.Fixpoint
      {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open Monad {{...}}

  open import RegDiff.Generic.Subtype.Base v
  open import RegDiff.Diff.Regular v eqs
  open import RegDiff.Diff.Fixpoint v eqs
  open import RegDiff.Diff.Loc.Regular v eqs

  Ctxμ : U → Set
  Ctxμ ty = Σ (⟦ ty ⟧ Unit) (Al (μ ty) ∘ ar ty)

  _▸_ : {ty : U} → μ ty → Ctxμ ty → ⟦ ty ⟧ (μ ty)
  _▸_ {ty} x (el , (v , n)) = plugₜ ty el (swap n v x)

  extr : {ty : U} → Ctxμ ty → μ ty → Maybe (μ ty)
  extr {ty} (el , (v , n)) x 
    with dec-eqμ ⟨ plugₜ ty el v ⟩ x
  ...| yes _ = just (lookup n v)
  ...| no  _ = nothing

  data Changeμ (ty : U) : Set where
    loc : (k : U) → Dirμ ty k → L Unit k → Changeμ ty
    ins : Dirμ ty ty → Ctxμ ty → List (Changeμ ty) → Changeμ ty
    del : Dirμ ty ty → Ctxμ ty → List (Changeμ ty) → Changeμ ty

  Lμ : U → Set
  Lμ = List ∘ Changeμ

  relocate : {ty : U} → Dir ty I → Changeμ ty → Changeμ ty
  relocate t (loc k d ls) = loc k (tl t d) ls
  relocate t (ins d ctx r) = ins (tl t d) ctx r
  relocate t (del d ctx r) = del (tl t d) ctx r

  vcat : {A : Set}{n : ℕ} → Vec (List A) n → List A
  vcat [] = []
  vcat (x ∷ xs) = x ++ vcat xs

  mutual
    goμ* : {ty : U} → Dir ty I → Dμ ty → Lμ ty
    goμ* r d = map (relocate r) (goμ d)

    {-# TERMINATING #-}
    goμ : {ty : U} → Dμ ty → Lμ ty
    goμ (Dμ.ins x al d) 
      = ins (hd here) (x , al) (goμ d) ∷ []
    goμ (Dμ.del x al d) 
      = del (hd here) (x , al) (goμ d) ∷ []
    goμ {ty} (Dμ.mod x y hip d) 
      with romeᵢ ty x
    ...| ds
      with go1 (diff ty x y)
    ...| []       = vcat (vmap (λ dd → goμ* (p1 dd) (p2 dd)) (vzip refl ds d))
    ...| (l ∷ ls) = loc ty (hd here) (l ∷ ls) 
                  ∷ vcat (vmap (λ dd → goμ* (p1 dd) (p2 dd)) (vzip refl ds d))

{-
  And now, applying these changes
-}

  L-on-hd : {A : Set}{ty : U}
          → L Unit ty → ⟦ ty ⟧ A → Maybe (⟦ ty ⟧ A)
  L-on-hd {ty = ty} l x 
    with applyAll l (fgt ty x)
  ...| nothing   = nothing
  ...| just hdX' = plug ty hdX' (ch ty x)

  mutual
    applyμ1 : {ty : U} → Changeμ ty → μ ty → Maybe (μ ty)
    applyμ1 (loc k dir ls) el 
      = onμ dir (L-on-hd ls) el
    applyμ1 (ins x al d) el 
      = onμ x (((_▸ al) <M>_) ∘ applyμ-open d) el
    applyμ1 (del x al d) el
      = onμ x (λ k → extr al ⟨ k ⟩ >>= applyμ d >>= just ∘ unmu) el

    applyμ-open
      : {ty : U} → Lμ ty → ⟦ ty ⟧ (μ ty) 
      → Maybe (μ ty)
    applyμ-open l x = applyμ l ⟨ x ⟩

    applyμ : {ty : U} → Lμ ty → μ ty → Maybe (μ ty)
    applyμ [] x = just x
    applyμ (l ∷ ls) x = applyμ1 l x >>= applyμ ls
