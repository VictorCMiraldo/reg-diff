open import Prelude
open import Prelude.Monad
open import Prelude.Nat.Lemmas

module Prelude.List.Lemmas where

  open Monad {{...}}

  open import Data.List.Properties
    using ( map-++-commute
          ; concat-map
          ; map-id
          ; map-compose
          ; foldr-cong
          ; map-cong
          ; length-map
          ; length-++
          )
    renaming (∷-injective to ∷-inj)
    public

  ++-assoc : ∀{a}{A : Set a}(x y z : List A)
           → x ++ (y ++ z) ≡ (x ++ y) ++ z
  ++-assoc []       y z = refl
  ++-assoc (x ∷ xs) y z = cong (x ∷_) (++-assoc xs y z)

  length-concat : ∀{a}{A : Set a}(xs : List (List A))
                → length (concat xs) ≡ sum (map length xs)
  length-concat []         = refl
  length-concat (xs ∷ xss) 
    = trans (length-++ xs)
            (cong (length xs +_) (length-concat xss))

  1≤length-witness 
    : ∀{a}{A : Set a}{l : List A}
    → 1 ≤ length l
    → ∃ (λ {(x , xs) → l ≡ x ∷ xs})
  1≤length-witness {l = []} ()
  1≤length-witness {l = x ∷ xs} w = (x , xs) , refl

  length-<$>-≤
    : ∀{a}{A B : Set a}
    → {f : A → B}(l : List A)
    → length l ≤ length (f <$> l)
  length-<$>-≤ []      = z≤n
  length-<$>-≤ (x ∷ l) = s≤s (length-<$>-≤ l)

  length-<$>-≡
    : ∀{a}{A B : Set a}
    → {f : A → B}(l : List A)
    → length l ≡ length (f <$> l)
  length-<$>-≡ []      = refl
  length-<$>-≡ (x ∷ l) = cong suc (length-<$>-≡ l)

  length-++-≤
    : ∀{a}{A : Set a}(l1 : List A){l2 : List A}
    → length l1 ≤ length (l1 ++ l2)
  length-++-≤ l1 {l2} 
    rewrite length-++ l1 {l2}
          = m≤m+n (length l1) (length l2) 
    
  ++->>=-commute
    : ∀{a}{A B : Set a}
    → (l₁ : List A){l₂ : List A}
    → (f : A → List B)
    → ((l₁ ++ l₂) >>= f) ≡ (l₁ >>= f) ++ (l₂ >>= f)
  ++->>=-commute [] f = refl
  ++->>=-commute (x ∷ xs) {l2} f 
    rewrite ++->>=-commute xs {l2} f
          = ++-assoc (f x) (concat (map f xs))
                           (concat (map f l2))
