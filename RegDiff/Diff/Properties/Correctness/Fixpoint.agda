open import Prelude hiding (_⊔_)
open import Prelude.Vector

module RegDiff.Diff.Properties.Correctness.Fixpoint
    {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where
{-
  The fixpoint variants
-}

{-

  ⊔μ-elim3 : {ty : U}(P : Dμ ty → Set)(d e f : Dμ ty)
          → P d → P e → P f → P (d ⊔μ (e ⊔μ f))
  ⊔μ-elim3 P d e f pd pe pf with costμ e ≤?-ℕ costμ f
  ...| yes _ with costμ d ≤?-ℕ costμ e
  ...| yes _ = pd
  ...| no  _ = pe
  ⊔μ-elim3 P d e f pd pe pf | no  _ 
    with costμ d ≤?-ℕ costμ f
  ...| yes _ = pd
  ...| no  _ = pf

  private
    lsplit-ar-ch
      : {ty : U}(x : μ ty)(xs : List (μ ty))
      → lsplit (ar ty (μ-hd x)) (μ-ch x ++ xs) ≡ (μ-ch x , xs)
    lsplit-ar-ch {ty} ⟨ x ⟩ xs 
      = trans (cong (λ P → lsplit P (ch ty x ++ xs)) 
                    (sym (ch-ar-fgt-lemma ty x))) 
              (lsplit-++-lemma (ch ty x) xs)

  unmu : {ty : U} → μ ty → ⟦ ty ⟧ (μ ty)
  unmu ⟨ x ⟩ = x

  mutual
    Dμ-del-src-lemma
      : {ty : U}(x : μ ty)(xs ys : List (μ ty))
      → Dμ-src (Dμ-del (μ-hd x) (diffμ (μ-ch x ++ xs) ys)) ≡ x ∷ xs
    Dμ-del-src-lemma {ty} x xs ys
      rewrite diffμ-src-lemma (μ-ch x ++ xs) ys
            | lsplit-ar-ch x xs
         with length (μ-ch x) ≟-ℕ ar ty (μ-hd x)
    ...| no ¬p = ⊥-elim (¬p (μ-ch-ar-hd-lemma x))
    ...| yes p with x
    ...| ⟨ x' ⟩ rewrite ≡-pi p (ch-ar-fgt-lemma ty x') 
       = cong (λ P → ⟨ P ⟩ ∷ xs) (plugₜ-correct ty x')

    Dμ-ins-dst-lemma
      : {ty : U}(y : μ ty)(xs ys : List (μ ty))
      → Dμ-dst (Dμ-ins (μ-hd y) (diffμ xs (μ-ch y ++ ys))) ≡ y ∷ ys
    Dμ-ins-dst-lemma {ty} y xs ys
      rewrite diffμ-dst-lemma xs (μ-ch y ++ ys)
            | lsplit-ar-ch y ys
         with length (μ-ch y) ≟-ℕ ar ty (μ-hd y)
    ...| no ¬p = ⊥-elim (¬p (μ-ch-ar-hd-lemma y))
    ...| yes p with y
    ...| ⟨ y' ⟩ rewrite ≡-pi p (ch-ar-fgt-lemma ty y') 
       = cong (λ P → ⟨ P ⟩ ∷ ys) (plugₜ-correct ty y')

    Dμ-mod-src-lemma
      : {ty : U}(x y : μ ty)(xs ys : List (μ ty))
      → Dμ-src (Dμ-mod (diff ty (μ-hd x) (μ-hd y))
               (diffμ (μ-ch x ++ xs) (μ-ch y ++ ys)))
      ≡ (x ∷ xs)
    Dμ-mod-src-lemma {ty} x y xs ys
      rewrite diff-src-lemma ty (μ-hd x) (μ-hd y)
            | diffμ-src-lemma (μ-ch x ++ xs) (μ-ch y ++ ys)
            | lsplit-ar-ch x xs
         with length (μ-ch x) ≟-ℕ ar ty (μ-hd x)
    ...| no ¬p = ⊥-elim (¬p (μ-ch-ar-hd-lemma x))
    ...| yes p with x
    ...| ⟨ x' ⟩ rewrite ≡-pi p (ch-ar-fgt-lemma ty x') 
       = cong (λ P → ⟨ P ⟩ ∷ xs) (plugₜ-correct ty x')

    Dμ-mod-dst-lemma
      : {ty : U}(x y : μ ty)(xs ys : List (μ ty))
      → Dμ-dst (Dμ-mod (diff ty (μ-hd x) (μ-hd y))
               (diffμ (μ-ch x ++ xs) (μ-ch y ++ ys)))
      ≡ (y ∷ ys)
    Dμ-mod-dst-lemma {ty} x y xs ys
      rewrite diff-dst-lemma ty (μ-hd x) (μ-hd y)
            | diffμ-dst-lemma (μ-ch x ++ xs) (μ-ch y ++ ys)
            | lsplit-ar-ch y ys
         with length (μ-ch y) ≟-ℕ ar ty (μ-hd y)
    ...| no ¬p = ⊥-elim (¬p (μ-ch-ar-hd-lemma y))
    ...| yes p with y
    ...| ⟨ y' ⟩ rewrite ≡-pi p (ch-ar-fgt-lemma ty y') 
       = cong (λ P → ⟨ P ⟩ ∷ ys) (plugₜ-correct ty y')

    {-# TERMINATING #-}
    diffμ-src-lemma 
      : {ty : U}(xs ys : List (μ ty))
      → Dμ-src (diffμ xs ys) ≡ xs
    diffμ-src-lemma [] [] = refl
    diffμ-src-lemma [] (y ∷ ys) 
      = diffμ-src-lemma [] (μ-ch y ++ ys)
    diffμ-src-lemma {ty} (x ∷ xs) [] 
      = Dμ-del-src-lemma x xs []
    diffμ-src-lemma {ty} (x ∷ xs) (y ∷ ys) 
      = ⊔μ-elim3 (λ d → Dμ-src d ≡ x ∷ xs) 
                 (Dμ-mod (diff ty (μ-hd x) (μ-hd y))
                    (diffμ (μ-ch x ++ xs) (μ-ch y ++ ys))) 
                 (Dμ-ins (μ-hd y) (diffμ (x ∷ xs) (μ-ch y ++ ys)))
                 (Dμ-del (μ-hd x) (diffμ (μ-ch x ++ xs) (y ∷ ys))) 
                 (Dμ-mod-src-lemma x y xs ys) 
                 (diffμ-src-lemma (x ∷ xs) (μ-ch y ++ ys)) 
                 (Dμ-del-src-lemma x xs (y ∷ ys))

    {-# TERMINATING #-}
    diffμ-dst-lemma 
      : {ty : U}(xs ys : List (μ ty))
      → Dμ-dst (diffμ xs ys) ≡ ys
    diffμ-dst-lemma [] [] = refl
    diffμ-dst-lemma [] (y ∷ ys) 
      = Dμ-ins-dst-lemma y [] ys
    diffμ-dst-lemma {ty} (x ∷ xs) [] 
      = diffμ-dst-lemma (μ-ch x ++ xs) []
    diffμ-dst-lemma {ty} (x ∷ xs) (y ∷ ys) 
      = ⊔μ-elim3 (λ d → Dμ-dst d ≡ y ∷ ys) 
                 (Dμ-mod (diff ty (μ-hd x) (μ-hd y))
                    (diffμ (μ-ch x ++ xs) (μ-ch y ++ ys))) 
                 (Dμ-ins (μ-hd y) (diffμ (x ∷ xs) (μ-ch y ++ ys)))
                 (Dμ-del (μ-hd x) (diffμ (μ-ch x ++ xs) (y ∷ ys))) 
                 (Dμ-mod-dst-lemma x y xs ys) 
                 (Dμ-ins-dst-lemma y (x ∷ xs) ys)
                 (diffμ-dst-lemma (μ-ch x ++ xs) (y ∷ ys)) 
  
-}
