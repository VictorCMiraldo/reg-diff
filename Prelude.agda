module Prelude where

  open import Level
    renaming (zero to lz; suc to ls)
    public

  open import Data.Unit.NonEta
    using (Unit; unit)
    public

  open import Data.Empty
    using (⊥; ⊥-elim)
    public

  open import Function
    using (_∘_; _$_; flip; id; const; _on_)
    public

  open import Data.Nat
    using (ℕ; suc; zero; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
    renaming (_≟_ to _≟-ℕ_; _≤?_ to _≤?-ℕ_
             ; compare to compareℕ; Ordering to Ordℕ
             ; less to LE ; greater to GE ; equal to EQ)
    public

  open import Data.Fin
    using (Fin; fromℕ; fromℕ≤; toℕ)
    renaming (zero to fz; suc to fs;
              inject+ to finject; raise to fraise)
    public

  open import Data.Fin.Properties
    using ()
    renaming (_≟_ to _≟-Fin_)
    public

  open import Data.Product
    using (∃; Σ; _×_; _,_; uncurry; curry)
    renaming (proj₁ to p1; proj₂ to p2
           ; <_,_> to split
           ; map to _×'_)
    public

  open import Data.Sum
    using (_⊎_; [_,_]′)
    renaming (inj₁ to i1; inj₂ to i2
           ; [_,_] to either)
    public

  open import Data.Bool
    using (Bool; true; false; if_then_else_; not)
    renaming (_∧_ to _and_; _∨_ to _or_)
    public

  open import Relation.Nullary
    using (Dec; yes; no; ¬_)
    public

  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect; [_])
    renaming (proof-irrelevance to ≡-pi)
    public

  open import Data.Maybe
    using (Maybe; just; nothing)
    renaming (maybe′ to maybe)
    public

  open import Data.List
    using (List; _∷_; []; map; _++_; zip; filter;
           all; any; concat; foldr; reverse; length;
           sum; zipWith)
    public

  postulate
    fun-ext : ∀{a b}{A : Set a}{B : Set b}{f g : A → B}
            → (∀ x → f x ≡ g x)
            → f ≡ g

  ×-inj : ∀{a b}{A : Set a}{B : Set b}{a1 a2 : A}{b1 b2 : B}
        → (a1 , b1) ≡ (a2 , b2)
        → a1 ≡ a2 × b1 ≡ b2
  ×-inj refl = refl , refl

  i1-inj : ∀{a b}{A : Set a}{B : Set b}{a1 a2 : A}
         → i1 {B = B} a1 ≡ i1 a2
         → a1 ≡ a2
  i1-inj refl = refl

  i2-inj : ∀{a b}{A : Set a}{B : Set b}{b1 b2 : B}
         → i2 {A = A} b1 ≡ i2 b2
         → b1 ≡ b2
  i2-inj refl = refl

  just-inj : ∀{a}{A : Set a}{x y : A}
           → _≡_ {a} {Maybe A} (just x) (just y) → x ≡ y
  just-inj refl = refl

  ifd_then_else_ : ∀{a b}{A : Set a}{B : Set b} 
                 → Dec A → (A → B) → (¬ A → B) → B
  ifd (yes p) then f else _ = f p
  ifd (no ¬p) then _ else g = g ¬p

  ¬-inv : ∀{a b}{A : Set a}{B : Set b}
        → (A → B) → (¬ B → ¬ A)
  ¬-inv f ¬B a = ¬B (f a)
