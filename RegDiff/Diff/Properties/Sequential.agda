open import Prelude
open import Prelude.Vector

module RegDiff.Diff.Properties.Sequential
      {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Diff.Regular v eqs
  open import RegDiff.Diff.Fixpoint v eqs
  
  infix 30 _⟶_ _⟶μ_

  _⟶_ : {A : Set}{ty : U}
      → D ty A → D ty A → Set
  p ⟶ q = D-dst p ≡ D-src q

  _⟶μ_ : {ty : U}
       → Dμ ty → Dμ ty → Set
  p ⟶μ q = Dμ-dst p ≡ Dμ-src q

  postulate
    ⟶μ-ins-del
      : {ty : U}(x y : ⟦ ty ⟧ Unit)(al : Al (μ ty) (ar ty x))
        (am : Al (μ ty) (ar ty y))(p q : Dμ ty)
      → ins x al p ⟶μ del y am q
      → p ⟶μ q
  {- We need plug-elimination lemmas here. such as
     ch (plug x xs) ≡ xs and hd (plug x xs) ≡ x
    ⟶μ-ins-del p q hip 
      with Dμ-dst p | inspect Dμ-dst p
    ...| dp | [ DP ]
      with Dμ-src q | inspect Dμ-src q
    ...| sq | [ SQ ]
       = {!!}
  -}

  ⟶μ-ins-mod
    : {ty : U}(x y0 y1 : ⟦ ty ⟧ Unit)(al : Al (μ ty) (ar ty x))
      (hip : ar ty y0 ≡ ar ty y1)(p : Dμ ty)(qs : Vec (Dμ ty) (ar ty y0))
    → ins x al p ⟶μ mod y0 y1 hip qs
    → Σ (x ≡ y0) (λ prf → p ⟶μ (lookup (Al-idx al) (vec-reindx (cong (ar ty) (sym prf)) qs)))
  ⟶μ-ins-mod x y0 y1 al hip p qs hip₀
    = {!!}
