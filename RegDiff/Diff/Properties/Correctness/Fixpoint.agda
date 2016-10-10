open import Prelude hiding (_⊔_)
open import Prelude.Vector

module RegDiff.Diff.Properties.Correctness.Fixpoint
    {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where
{-
  The fixpoint variants
-}

  open import RegDiff.Diff.Regular v eqs
  open import RegDiff.Diff.Fixpoint v eqs

  ifd-elim
    : {A B : Set}{f : A → B}{g : ¬ A → B}
    → (P : B → Set)
    → (x : Dec A)
    → ((a : A)   → P (f a))
    → ((a : ¬ A) → P (g a))
    → P (ifd x then f else g)
  ifd-elim P (yes x) pf pg = pf x
  ifd-elim P (no  x) pf pg = pg x

  ⊔μ-elim
    : {ty : U}{P : Dμ' ty → Set}{d e : Dμ' ty}
    → P d → P e → P (d ⊔μ e)
  ⊔μ-elim {ty} {P} {d} {e} pd pe
    with costμ d ≤?-ℕ costμ e
  ...| yes _ = pd
  ...| no  _ = pe

  mutual
    Dμ-mod-src
      : {O : Oracle}{ty : U}(x y : μ ty)(hip : ar ty (μ-hd x) ≡ ar ty (μ-hd y))
      → Dμ-src (mod (μ-hd x) (μ-hd y) hip (diffμ* {O} hip (μ-chv x) (μ-chv y)))
      ≡ x
    Dμ-mod-src {O} {ty} ⟨ x ⟩ y hip 
      = cong ⟨_⟩ (trans (cong (λ P → plugₜ ty (μ-hd {ty = ty} ⟨ x ⟩) P) 
                        (diffμ*-src-lemma (μ-chv ⟨ x ⟩) (μ-chv y) hip)) 
                        (plugₜ-correct ty x))

    Dμ-ins-src
      : {O : Oracle}{ty : U}(x y : μ ty)(hip : ¬ (ar ty (μ-hd y) ≡ 0))
      → Dμ-src (ins (μ-hd y) (p1 (do-ins {O} x (μ-chv y) hip)) (p2 (do-ins {O} x (μ-chv y) hip)))
      ≡ x
    Dμ-ins-src {O} {ty} x y hip = aux0 (μ-chv y) hip
      where
        aux0 : {k : ℕ}(v : Vec (μ ty) k)(h : ¬ k ≡ 0) → Dμ-src (p2 (do-ins x v h)) ≡ x
        aux0 [] h = ⊥-elim (h refl)
        aux0 (v ∷ vs) h = diffμ-src-lemma x (lookup (O x (v ∷ vs)) (v ∷ vs))

    Dμ-del-src
      : {O : Oracle}{ty : U}(x y : μ ty)(hip : ¬ (ar ty (μ-hd x) ≡ 0))
      → Dμ-src (del (μ-hd x) (p1 (do-del {O} (μ-chv x) hip y)) (p2 (do-del {O} (μ-chv x) hip y)))
      ≡ x
    Dμ-del-src {O} {ty} ⟨ x ⟩ y hip 
      with do-del {O} (μ-chv ⟨ x ⟩) hip y | inspect (do-del {O} (μ-chv ⟨ x ⟩) hip) y
    ...| (vs , k) , d | [ DEL ] 
      = cong ⟨_⟩ (trans (cong (plugₜ ty (μ-hd {ty = ty} ⟨ x ⟩)) 
                        (aux1 (ar ty (μ-hd {ty = ty} ⟨ x ⟩)) vs k d (μ-chv ⟨ x ⟩) hip DEL)) 
                 (plugₜ-correct ty x))
      where
        aux0 : {n : ℕ}(vs vs' : Vec (μ ty) (suc n))(k j : Fin (suc n))
             → (vs' , j) ≡ (vs , k)
             → swap k vs (lookup j vs') ≡ vs'
        aux0 .vs' vs' .j j refl = swap-uni j vs'
    
        aux1 : (n : ℕ)(vs : Vec (μ ty) n)(k : Fin n)(d : Dμ' ty)
            → (vs' : Vec (μ ty) n)(hip : ¬ n ≡ 0)
            → do-del {O} vs' hip y ≡ ((vs , k) , d)
            → swap k vs (Dμ-src d) ≡ vs'
        aux1 .0 vs k d [] hip0 hip1 = ⊥-elim (hip0 refl)
        aux1 (suc n) vs k d (v ∷ vs') hip0 hip1
          rewrite sym (p2 (×-inj hip1))
                | diffμ-src-lemma {O} (lookup (O y (v ∷ vs')) (v ∷ vs')) y
                = aux0 vs (v ∷ vs') k (O y (v ∷ vs')) (p1 (×-inj hip1))

    diffμ*-src-lemma
      : {O : Oracle}{ty : U}{n k : ℕ}(xs : Vec (μ ty) n)(ys : Vec (μ ty) k)
      → (hip : n ≡ k)
      → vmap Dμ-src (diffμ* {O} hip xs ys) ≡ xs
    diffμ*-src-lemma [] [] refl = refl
    diffμ*-src-lemma [] (y ∷ ys) ()
    diffμ*-src-lemma (x ∷ xs) [] ()
    diffμ*-src-lemma (x ∷ xs) (y ∷ ys) refl 
      = cong₂ _∷_ (diffμ-src-lemma x y) (diffμ*-src-lemma xs ys refl)

    {-# TERMINATING #-}
    diffμ-src-lemma
      : {O : Oracle}{ty : U}(x y : μ ty)
      → Dμ-src (diffμ {O} x y) ≡ x
    diffμ-src-lemma {O} {ty} x y 
      = ifd-elim (λ k → Dμ-src k ≡ x) (ar ty (μ-hd x) ≟-ℕ ar ty (μ-hd y)) 
        (λ hip₀ → ifd-elim (λ k → Dμ-src k ≡ x) (ar ty (μ-hd x) ≟-ℕ 0) 
            (λ hip₁ → Dμ-mod-src x y hip₀)
            (λ hip₁ → ⊔μ-elim {P = λ k → Dμ-src k ≡ x} 
                              {mod _ _ _ _}
                              {ins _ _ _ ⊔μ del _ _ _}
                              (Dμ-mod-src x y hip₀) 
                      (⊔μ-elim {P = λ k → Dμ-src k ≡ x}
                               {ins _ _ _} {del _ _ _}
                               (Dμ-ins-src x y (hip₁ ∘ trans hip₀)) 
                               (Dμ-del-src x y hip₁)))) 
        (λ hip₀ → ifd-elim (λ k → Dμ-src k ≡ x) (ar ty (μ-hd x) ≟-ℕ 0) 
            (λ hip₁ → Dμ-ins-src x y (hip₀ ∘ trans hip₁ ∘ sym))
            (λ hip₁ → ifd-elim (λ k → Dμ-src k ≡ x) (ar ty (μ-hd y) ≟-ℕ 0) 
              (λ hip₂ → Dμ-del-src x y hip₁) 
              (λ hip₂ → (⊔μ-elim {P = λ k → Dμ-src k ≡ x}
                               {ins _ _ _} {del _ _ _}
                               (Dμ-ins-src x y hip₂) 
                               (Dμ-del-src x y hip₁)))))


  mutual
    Dμ-mod-dst
      : {O : Oracle}{ty : U}(x y : μ ty)(hip : ar ty (μ-hd x) ≡ ar ty (μ-hd y))
      → Dμ-dst (mod (μ-hd x) (μ-hd y) hip (diffμ* {O} hip (μ-chv x) (μ-chv y)))
      ≡ y
    Dμ-mod-dst {O} {ty} x ⟨ y ⟩ hip 
      = cong ⟨_⟩ (trans (cong (λ P → plugₜ ty (μ-hd {ty = ty} ⟨ y ⟩) P) 
                        (trans (cong (vec-reindx hip)
                                     (diffμ*-dst-lemma (μ-chv x) (μ-chv ⟨ y ⟩) hip)) 
                               (vec-reindx-uni hip (chv ty y)) )) 
                        (plugₜ-correct ty y))

    Dμ-del-dst
      : {O : Oracle}{ty : U}(x y : μ ty)(hip : ¬ (ar ty (μ-hd x) ≡ 0))
      → Dμ-dst (del (μ-hd x) (p1 (do-del {O} (μ-chv x) hip y)) (p2 (do-del {O} (μ-chv x) hip y)))
      ≡ y
    Dμ-del-dst {O} {ty} x y hip = aux0 (μ-chv x) hip
      where
        aux0 : {k : ℕ}(v : Vec (μ ty) k)(h : ¬ k ≡ 0) → Dμ-dst (p2 (do-del v h y)) ≡ y
        aux0 [] h = ⊥-elim (h refl)
        aux0 (v ∷ vs) h = diffμ-dst-lemma {O} (lookup (O y (v ∷ vs)) (v ∷ vs)) y

    Dμ-ins-dst
      : {O : Oracle}{ty : U}(x y : μ ty)(hip : ¬ (ar ty (μ-hd y) ≡ 0))
      → Dμ-dst (ins (μ-hd y) (p1 (do-ins {O} x (μ-chv y) hip)) (p2 (do-ins {O} x (μ-chv y) hip)))
      ≡ y
    Dμ-ins-dst {O} {ty} x ⟨ y ⟩ hip 
      with do-ins {O} x (μ-chv ⟨ y ⟩) hip | inspect (λ k → do-ins {O} k (μ-chv ⟨ y ⟩) hip) x
    ...| (vs , k) , d | [ INS ] 
      = cong ⟨_⟩ (trans (cong (plugₜ ty (μ-hd {ty = ty} ⟨ y ⟩)) 
                        (aux1 (ar ty (μ-hd {ty = ty} ⟨ y ⟩)) vs k d (μ-chv ⟨ y ⟩) hip INS)) 
                 (plugₜ-correct ty y))
      where
        aux0 : {n : ℕ}(vs vs' : Vec (μ ty) (suc n))(k j : Fin (suc n))
             → (vs' , j) ≡ (vs , k)
             → swap k vs (lookup j vs') ≡ vs'
        aux0 .vs' vs' .j j refl = swap-uni j vs'
    
        aux1 : (n : ℕ)(vs : Vec (μ ty) n)(k : Fin n)(d : Dμ' ty)
            → (vs' : Vec (μ ty) n)(hip : ¬ n ≡ 0)
            → do-ins {O} x vs' hip ≡ ((vs , k) , d)
            → swap k vs (Dμ-dst d) ≡ vs'
        aux1 .0 vs k d [] hip0 hip1 = ⊥-elim (hip0 refl)
        aux1 (suc n) vs k d (v ∷ vs') hip0 hip1
          rewrite sym (p2 (×-inj hip1))
                | diffμ-dst-lemma {O} x (lookup (O x (v ∷ vs')) (v ∷ vs'))
                = aux0 vs (v ∷ vs') k (O x (v ∷ vs')) (p1 (×-inj hip1))

    diffμ*-dst-lemma
      : {O : Oracle}{ty : U}{n k : ℕ}(xs : Vec (μ ty) n)(ys : Vec (μ ty) k)
      → (hip : n ≡ k)
      → vmap Dμ-dst (diffμ* {O} hip xs ys) ≡ vec-reindx (sym hip) ys
    diffμ*-dst-lemma [] [] refl = refl
    diffμ*-dst-lemma [] (y ∷ ys) ()
    diffμ*-dst-lemma (x ∷ xs) [] ()
    diffμ*-dst-lemma {O} (x ∷ xs) (y ∷ ys) refl 
      = cong₂ _∷_ (diffμ-dst-lemma {O} x y) (diffμ*-dst-lemma {O} xs ys refl)

    {-# TERMINATING #-}
    diffμ-dst-lemma
      : {O : Oracle}{ty : U}(x y : μ ty)
      → Dμ-dst (diffμ x y) ≡ y
    diffμ-dst-lemma {O} {ty} x y 
      = ifd-elim (λ k → Dμ-dst k ≡ y) (ar ty (μ-hd x) ≟-ℕ ar ty (μ-hd y)) 
        (λ hip₀ → ifd-elim (λ k → Dμ-dst k ≡ y) (ar ty (μ-hd x) ≟-ℕ 0) 
            (λ hip₁ → Dμ-mod-dst x y hip₀)
            (λ hip₁ → ⊔μ-elim {P = λ k → Dμ-dst k ≡ y} 
                              {mod _ _ _ _}
                              {ins _ _ _ ⊔μ del _ _ _}
                              (Dμ-mod-dst x y hip₀) 
                      (⊔μ-elim {P = λ k → Dμ-dst k ≡ y}
                               {ins _ _ _} {del _ _ _}
                               (Dμ-ins-dst x y (hip₁ ∘ trans hip₀)) 
                               (Dμ-del-dst x y hip₁)))) 
        (λ hip₀ → ifd-elim (λ k → Dμ-dst k ≡ y) (ar ty (μ-hd x) ≟-ℕ 0) 
            (λ hip₁ → Dμ-ins-dst x y (hip₀ ∘ trans hip₁ ∘ sym))
            (λ hip₁ → ifd-elim (λ k → Dμ-dst k ≡ y) (ar ty (μ-hd y) ≟-ℕ 0) 
              (λ hip₂ → Dμ-del-dst x y hip₁) 
              (λ hip₂ → (⊔μ-elim {P = λ k → Dμ-dst k ≡ y}
                               {ins _ _ _} {del _ _ _}
                               (Dμ-ins-dst x y hip₂) 
                               (Dμ-del-dst x y hip₁)))))

