{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.List.All
open import Prelude.PartialFuncs.Base
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Lemmas
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Regular.Base ks keqs A _≟-A_
  open import RegDiff.Diff.Regular.Apply ks keqs A _≟-A_

  _* : ∀{a b}{A : Set a} → (A → A → Set b) → (A → A → Set b)
  (R *) x y = List (R x y)

  S-list-distr
    : {ty : U}{P : ΠΠSet}
    → S (P *) ty → List (S P ty)
  S-list-distr Scp = Scp ∷ []
  S-list-distr (Schg i j x) = map (Schg i j) x
  S-list-distr (Scns i x) = Scns i {!!} ∷ []

  spine-cns≢Scp : {ty : U}(x y : ⟦ ty ⟧)
               → spine-cns x y ≡ Scp → ⊥
  spine-cns≢Scp x y hip with sop x | sop y
  spine-cns≢Scp _ _ hip
    | strip cx dx | strip cy dy 
    with cx ≟-Fin cy
  spine-cns≢Scp _ _ () | strip _ _ | strip _ _ 
     | yes refl
  spine-cns≢Scp _ _ () | strip _ _ | strip _ _ 
     | no  _ 


  Scp-elim : {ty : U}(x y : ⟦ ty ⟧)
           → spine x y ≡ Scp → x ≡ y
  Scp-elim {ty} x y hip 
    with dec-eq _≟-A_ ty x y 
  ...| yes p     = p
  ...| no  _     = ⊥-elim (spine-cns≢Scp x y hip)

  unzipₚ
    : {ty : Π}
    → All (contr Trivialₚ ∘ β) ty
    → ⟦ ty ⟧ₚ × ⟦ ty ⟧ₚ
  unzipₚ [] = unit , unit
  unzipₚ (((x , unit) , (y , unit)) ∷ xys) 
    = let (xs , ys) = unzipₚ xys
       in (x , xs) , (y , ys)

  
