open import Prelude
open import Prelude.Monad

module Prelude.List.All where

  open Monad {{...}} 

  open import Data.List.All 
    using (All; [] ; _∷_; tabulate) 
    public

  ∷ᵢ-inj : ∀{a p}{A : Set a}{P : A → Set p}{l : List A}
            {k : A}{x y : P k}{xs ys : All P l}
         → _≡_ {A = All P (k ∷ l)} (x ∷ xs) (y ∷ ys) 
         → x ≡ y × xs ≡ ys
  ∷ᵢ-inj refl = refl , refl

  mapᵢ : ∀{a b}{A : Set a}{P Q : A → Set b}{l : List A}
        → (f : ∀{k} → P k → Q k)
        → All P l → All Q l
  mapᵢ f [] = []
  mapᵢ f (x ∷ xs) = f x ∷ mapᵢ f xs

  foldrᵢ : ∀{a b c}{A : Set a}{B : Set b}{P : A → Set c}{l : List A}
         → (cons : ∀{k} → P k → B → B ) → B → All P l → B
  foldrᵢ cons nil []        = nil
  foldrᵢ cons nil (l ∷ ls)  = cons l (foldrᵢ cons nil ls)

  mapMᵢ : ∀{a}{A : Set a}{M : Set a → Set a}{{m : Monad M}}
           {P Q : A → Set a}{l : List A}
        → (f : ∀{k} → P k → M (Q k))
        → All P l → M (All Q l)
  mapMᵢ f []       = return []
  mapMᵢ f (i ∷ li) = f i >>= (λ qi → mapMᵢ f li >>= return ∘ (qi ∷_))

  zipWithᵢ : ∀{a b}{A : Set a}{P Q : A → Set b}{l : List A}
           → (f : ∀{k} → P k → P k → Q k) → (m n : All P l) → All Q l
  zipWithᵢ f []       []       = []
  zipWithᵢ f (m ∷ ms) (n ∷ ns) = f m n ∷ zipWithᵢ f ms ns

  zipWithMᵢ : ∀{a}{A : Set a}{M : Set a → Set a}{{m : Monad M}}
               {P Q : A → Set a}{l : List A}
           → (f : ∀{k} → P k → P k → M (Q k)) → (m n : All P l) → M (All Q l)
  zipWithMᵢ f []       []       = return []
  zipWithMᵢ f (m ∷ ms) (n ∷ ns) = f m n >>= λ fmn → zipWithMᵢ f ms ns >>= return ∘ (fmn ∷_)
