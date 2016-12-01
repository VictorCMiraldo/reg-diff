open import Prelude
open import Prelude.Monad

module Prelude.ListI where

  open Monad {{...}}
 
  data ListI {a b}{A : Set a}(P : A → Set b) : List A → Set b where
    []   : ListI P []
    _∷_  : ∀{x xs} → P x → ListI P xs → ListI P (x ∷ xs)

  mapᵢ : ∀{a b}{A : Set a}{P Q : A → Set b}{l : List A}
        → (f : ∀{k} → P k → Q k)
        → ListI P l → ListI Q l
  mapᵢ f [] = []
  mapᵢ f (x ∷ xs) = f x ∷ mapᵢ f xs

  foldrᵢ : ∀{a b c}{A : Set a}{B : Set b}{P : A → Set c}{l : List A}
         → (cons : ∀{k} → P k → B → B ) → B → ListI P l → B
  foldrᵢ cons nil []        = nil
  foldrᵢ cons nil (l ∷ ls)  = cons l (foldrᵢ cons nil ls)

  mapMᵢ : ∀{a b}{A : Set a}{M : Set b → Set b}{{m : Monad M}}
           {P Q : A → Set b}{l : List A}
        → (f : ∀{k} → P k → M (Q k))
        → ListI P l → M (ListI Q l)
  mapMᵢ f []       = return []
  mapMᵢ f (i ∷ li) = f i >>= (λ qi → mapMᵢ f li >>= return ∘ (qi ∷_))
