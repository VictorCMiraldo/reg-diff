{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude
open import Prelude.Monad

module Prelude.List.All where

  open import Data.List.All 
    using (All; [] ; _∷_)
    renaming ( tabulate to All-tabulate
             ; lookup   to All-lookup
             ) 
    public

  open import Data.List.Any as Any using (here; there)
    public
  open Any.Membership-≡ using (_∈_; _⊆_) 
    public

  open Monad {{...}} 

  mapᵢ : ∀{a b c}{A : Set a}{P : A → Set b}{Q : A → Set c}{l : List A}
        → (f : ∀{k} → P k → Q k)
        → All P l → All Q l
  mapᵢ f [] = []
  mapᵢ f (x ∷ xs) = f x ∷ mapᵢ f xs

  foldrᵢ : ∀{a b c}{A : Set a}{B : Set b}{P : A → Set c}{l : List A}
         → (cons : ∀{k} → P k → B → B ) → B → All P l → B
  foldrᵢ cons nil []        = nil
  foldrᵢ cons nil (l ∷ ls)  = cons l (foldrᵢ cons nil ls)

  mapMᵢ : ∀{a p}{A : Set a}{M : Set a → Set a}{{m : Monad M}}
           {P : A → Set p}{Q : A → Set a}{l : List A}
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
  -- They are also equivalences, we are just
  -- proving one way of them, though. If this works out,
  -- would be nice to reengineer this.
  all-list-commute
    : ∀{a b}{A : Set a}{P : A → Set b}{l : List A}
    → All (List ∘ P) l
    → List (All P l)
  all-list-commute [] 
    = [] ∷ []
  all-list-commute (px ∷ xs) 
    = foldr (λ h r → map (_∷ h) px ++ r) [] (all-list-commute xs)

  _++ₐ_ : ∀{a p}{A : Set a}{P : A → Set p}
        → {l1 l2 : List A}
        → All P l1 → All P l2 → All P (l1 ++ l2)
  []       ++ₐ n = n
  (px ∷ m) ++ₐ n = px ∷ (m ++ₐ n)

  ++ₐ-split : ∀{a p}{A : Set a}{P : A → Set p}
            → {l1 l2 : List A}
            → All P (l1 ++ l2) → (All P l1 × All P l2)
  ++ₐ-split {l1 = []} hip = [] , hip
  ++ₐ-split {l1 = x ∷ xs} (px ∷ hip)
    = let pl1 , pl2 = ++ₐ-split hip
       in px ∷ pl1 , pl2

  All-concat-commute
    : ∀{a p}{A : Set a}{P : A → Set p}
    → {x : List (List A)}
    → All (All P) x
    → All P (concat x)
  All-concat-commute [] = []
  All-concat-commute (hip ∷ hips) 
    = hip ++ₐ All-concat-commute hips

  All-map-commute
    : ∀{a p}{A B : Set a}{P : B → Set p}
    → {x : List A}(f : A → B)
    → All (P ∘ f) x
    → All P (map f x)
  All-map-commute f [] = []
  All-map-commute f (px ∷ hip) 
    = px ∷ All-map-commute f hip

  All-concat-uncommute
    : ∀{a p}{A : Set a}{P : A → Set p}
    → {x : List (List A)}
    → All P (concat x)
    → All (All P) x
  All-concat-uncommute {x = []} [] = []
  All-concat-uncommute {x = x ∷ xs} hip 
    = let h0 , h1 = ++ₐ-split {l1 = x} hip
       in h0 ∷ All-concat-uncommute h1

  All-map-uncommute
    : ∀{a p}{A B : Set a}{P : B → Set p}
    → {x : List A}(f : A → B)
    → All P (map f x)
    → All (P ∘ f) x
  All-map-uncommute {x = []} f [] = []
  All-map-uncommute {x = x ∷ xs} f (px ∷ hip) 
    = px ∷ All-map-uncommute f hip

  All-bind-commute
    : ∀{a p}{A B : Set a}
    → {P : B → Set p}{x : List A}
    → (f : A → List B)
    → All (All P ∘ f) x
    → All P (x >>= f)
  All-bind-commute f hip 
    = All-concat-commute (All-map-commute f hip)

  All-bind-uncommute
    : ∀{a p}{A B : Set a}
    → {P : B → Set p}{x : List A}
    → (f : A → List B)
    → All P (x >>= f)
    → All (All P ∘ f) x
  All-bind-uncommute f hip 
    = All-map-uncommute f (All-concat-uncommute hip)

  All-<$>-commute
    : ∀{a p}{A B : Set a}
    → {P : B → Set p}{x : List A}
    → (f : A → B)
    → All (P ∘ f) x
    → All P (f <$> x)
  All-<$>-commute f hip 
    = All-bind-commute (return ∘ f) (mapᵢ (_∷ []) hip)

  All-<$>->>=-commute
    : ∀{a p}{A B C : Set a}
    → {P : C → Set p}{x : List A}
    → (f : A → B)
    → (m : B → List C)
    → All (All P ∘ m ∘ f) x
    → All P ((f <$> x) >>= m)
  All-<$>->>=-commute f m hip
    = All-bind-commute m (All-<$>-commute f hip)

  x∈[]-abs : ∀{a}{A : Set a}{x : A}
           → x ∈ [] → ⊥
  x∈[]-abs ()

  All-⊆ : ∀{a p}{A : Set a}{P : A → Set p}
        → {l1 l2 : List A}
        → (l1 ⊆ l2)
        → All P l2
        → All P l1
  All-⊆ {l1 = []} hip _ = []
  All-⊆ {l1 = x ∷ l1} hip pxs
    = All-lookup pxs (hip (here refl)) 
    ∷ All-⊆ (hip ∘ there) pxs

{-
  data ALL {a p q}{A : Set a}{P : A → Set p}
           (Q : ∀{x} → P x → Set q) 
           : {l : List A} → All P l → Set (a ⊔ p ⊔ q) where
    []   : ALL Q []
    _∷_  : {l : A}{ls : List A}{xs : All P ls}
         → {x : P l} → Q x → ALL Q xs → ALL Q (x ∷ xs)

  All-mapMᵢ-commute
    : ∀{a p r}{A : Set a}{P : A → Set p}{Q : A → Set a}
    → {l : List A}
    → {R : All Q l → Set r}
    → (f : ∀{k} → P k → List (Q k))
    → (x : All P l)
    → R {!!}
    → All R (mapMᵢ f x)
  All-mapMᵢ-commute = {!!}
-}
{-
: ∀{a}{A : Set a}{M : Set a → Set a}{{m : Monad M}}
           {P Q : A → Set a}{l : List A}
        → (f : ∀{k} → P k → M (Q k))
        → All P l → M (All Q l)
-}
