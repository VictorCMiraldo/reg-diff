open import Prelude
open import Prelude.Monad

module Prelude.ListI where

  open import Data.List.All 
    using (All; [] ; _∷_; tabulate) 
    public

  open Monad {{...}}

  ListI : ∀{a b}{A : Set a}(P : A → Set b) → List A → Set (b ⊔ a)
  ListI P = All P
 
{-
  data ListI {a b}{A : Set a}(P : A → Set b) : List A → Set b where
    []   : ListI P []
    _∷_  : ∀{x xs} → P x → ListI P xs → ListI P (x ∷ xs)
-}
  mapᵢ : ∀{a b}{A : Set a}{P Q : A → Set b}{l : List A}
        → (f : ∀{k} → P k → Q k)
        → ListI P l → ListI Q l
  mapᵢ f [] = []
  mapᵢ f (x ∷ xs) = f x ∷ mapᵢ f xs

  foldrᵢ : ∀{a b c}{A : Set a}{B : Set b}{P : A → Set c}{l : List A}
         → (cons : ∀{k} → P k → B → B ) → B → ListI P l → B
  foldrᵢ cons nil []        = nil
  foldrᵢ cons nil (l ∷ ls)  = cons l (foldrᵢ cons nil ls)

  mapMᵢ : ∀{a}{A : Set a}{M : Set a → Set a}{{m : Monad M}}
           {P Q : A → Set a}{l : List A}
        → (f : ∀{k} → P k → M (Q k))
        → ListI P l → M (ListI Q l)
  mapMᵢ f []       = return []
  mapMᵢ f (i ∷ li) = f i >>= (λ qi → mapMᵢ f li >>= return ∘ (qi ∷_))

  zipWithᵢ : ∀{a b}{A : Set a}{P Q : A → Set b}{l : List A}
           → (f : ∀{k} → P k → P k → Q k) → (m n : ListI P l) → ListI Q l
  zipWithᵢ f []       []       = []
  zipWithᵢ f (m ∷ ms) (n ∷ ns) = f m n ∷ zipWithᵢ f ms ns

  zipWithMᵢ : ∀{a}{A : Set a}{M : Set a → Set a}{{m : Monad M}}
               {P Q : A → Set a}{l : List A}
           → (f : ∀{k} → P k → P k → M (Q k)) → (m n : ListI P l) → M (ListI Q l)
  zipWithMᵢ f []       []       = return []
  zipWithMᵢ f (m ∷ ms) (n ∷ ns) = f m n >>= λ fmn → zipWithMᵢ f ms ns >>= return ∘ (fmn ∷_)
