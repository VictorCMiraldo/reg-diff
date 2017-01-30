open import Prelude
open import Prelude.Monad

module Prelude.List.All where

  open import Data.List.All 
    using (All; [] ; _∷_; tabulate) 
    public

  open Monad {{...}} 

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


  -- Possibly temporary lemmas (Jan-30, being used by 
  --     RegDiff.Diff.Abstract.Instances.Spine)
  --
  --
  all-list-commute
    : ∀{a b}{A : Set a}{P : A → Set b}{l : List A}
    → All (List ∘ P) l
    → List (All P l)
  all-list-commute [] 
    = [] ∷ []
  all-list-commute (px ∷ xs) 
    = foldr (λ h r → map (_∷ h) px ++ r) [] (all-list-commute xs)

  all-map-commute 
    : ∀{a b c}{A : Set a}{B : Set b}{P : B → Set c}
    → {l : List A}{f : A → B}
    → All (P ∘ f) l 
    → All P (map f l)
  all-map-commute {l = []}     [] = []
  all-map-commute {l = l ∷ ls} (x ∷ xs) = x ∷ all-map-commute xs

  
