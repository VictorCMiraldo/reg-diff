open import Prelude
open import Prelude.Vector

{-
  Here we exploit the connection between patches
  and lists of locations!
-}

module RegDiff.Diff.Loc.Fixpoint
      {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Generic.Subtype.Base v
  open import RegDiff.Diff.Regular v eqs
  open import RegDiff.Diff.Fixpoint2 v eqs
  open import RegDiff.Diff.Loc.Regular v eqs

  Ctxμ : U → Set
  Ctxμ ty = Σ (⟦ ty ⟧ Unit) (Al (μ ty) ∘ ar ty)

  data Changeμ (ty : U) : Set where
    loc : (k : U) → Dirμ ty k → L Unit ty → Changeμ ty
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
      
