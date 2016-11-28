open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import RegDiff.Generic.Parms

module RegDiff.SOP.Generic.Eq 
    {ks# : ℕ}(ks : Vec Set ks#)(eqs : VecI Eq ks) where

  open import RegDiff.SOP.Generic.Multirec ks

  I-inj : {n : ℕ}{k l : Fin n} → I k ≡ I l → k ≡ l
  I-inj refl = refl

  K-inj : {n : ℕ}{i j : Fin ks#} → K {n = n} i ≡ K j → i ≡ j
  K-inj refl = refl

  Atom-eq : {n : ℕ}(ty tv : Atom n) → Dec (ty ≡ tv)
  Atom-eq (I x) (K y) = no (λ ())
  Atom-eq (K x) (I y) = no (λ ())
  Atom-eq (I x) (I y) 
    = ifd (x ≟-Fin y)
      then yes ∘ cong I
      else (no ∘ ¬-inv I-inj)
  Atom-eq (K x) (K y)
    = ifd (x ≟-Fin y)
      then yes ∘ cong K
      else (no ∘ ¬-inv K-inj)

  U-eq : {n : ℕ}(ty tv : Uₙ n) → Dec (ty ≡ tv)
  U-eq = Eq.cmp (eq-List {{ eq-List {{ eq Atom-eq }} }})

  dec-eqₐ : {n : ℕ}{A : Parms n}
          → (eqA : ∀{k}(x y : A k) → Dec (x ≡ y))
          → (ty : Atom n)(x y : ⟦ ty ⟧ₐ A)
          → Dec (x ≡ y)
  dec-eqₐ eqA (I k) x y = eqA x y
  dec-eqₐ eqA (K k) x y = Eq.cmp (lookupᵢ k eqs) x y

  dec-eqₚ : {n : ℕ}{A : Parms n}
          → (eqA : ∀{k}(x y : A k) → Dec (x ≡ y))
          → (ty : List (Atom n))(x y : ⟦ ty ⟧ₚ A)
          → Dec (x ≡ y)
  dec-eqₚ eqA [] unit unit = yes refl
  dec-eqₚ eqA (a ∷ as) (xa , xs) (ya , ys) 
    = ifd dec-eqₐ eqA a xa ya 
      then ifd dec-eqₚ eqA as xs ys 
           then (λ hb ha → yes (cong₂ _,_ ha hb)) 
           else flip (const (no ∘ ¬-inv (p2 ∘ ×-inj))) 
      else (no ∘ ¬-inv (p1 ∘ ×-inj))

  dec-eq : {n : ℕ}{A : Parms n}
         → (eqA : ∀{k}(x y : A k) → Dec (x ≡ y))
         → (ty : Uₙ n)(x y : ⟦ ty ⟧ A)
         → Dec (x ≡ y)
  dec-eq eqA [] () ()
  dec-eq eqA (p ∷ ps) (i1 x) (i2 y) = no (λ ())
  dec-eq eqA (p ∷ ps) (i2 x) (i1 y) = no (λ ())
  dec-eq eqA (p ∷ ps) (i1 x) (i1 y) 
    = ifd dec-eqₚ eqA p x y 
      then yes ∘ cong i1 
      else (no ∘ ¬-inv i1-inj)
  dec-eq eqA (p ∷ ps) (i2 x) (i2 y) 
    = ifd dec-eq eqA ps x y 
      then yes ∘ cong i2 
      else (no ∘ ¬-inv i2-inj)

  {-# TERMINATING #-}
  _≟_ : {n : ℕ}{F : Fam n}{k : Fin n}
      → (x y : Fix F k) 
      → Dec (x ≡ y)
  _≟_ {n} {F} {k} ⟨ x ⟩ ⟨ y ⟩ 
    with dec-eq _≟_ (lookup k F) x y
  ...| yes h0  = yes (cong ⟨_⟩ h0)
  ...| no  abs = no (abs ∘ ⟨⟩-inj)
