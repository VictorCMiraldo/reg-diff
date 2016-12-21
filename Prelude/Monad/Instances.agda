open import Prelude
open import Prelude.Monad.Decl
open import Data.List.Properties

module Prelude.Monad.Instances where

  open import Prelude.Functor.Instances

  private
    maybe-μ : ∀{a}{A : Set a} → Maybe (Maybe A) → Maybe A
    maybe-μ (just k) = k
    maybe-μ nothing  = nothing

    ++-id : ∀{a}{A : Set a}(x : List A)
          → x ++ [] ≡ x
    ++-id [] = refl
    ++-id (x ∷ xs) = cong (x ∷_) (++-id xs)

    cat-map-∷ : ∀{a}{A : Set a}(x : List A)
              → concat (map (_∷ []) x) ≡ x
    cat-map-∷ [] = refl
    cat-map-∷ (x ∷ xs) 
      = cong₂ _∷_ refl (cat-map-∷ xs)

    postulate
      cat-cat-cat : ∀{a}{A : Set a}(x : List (List (List A)))
                  →  concat (concat x) ≡ concat (map concat x)

  List-<*> : ∀{a}{A B : Set a} → List (A → B) → List A → List B
  List-<*> []       xs = []
  List-<*> (g ∷ gs) xs = map g xs ++ List-<*> gs xs

  Maybe-<*> : ∀{a}{A B : Set a} → Maybe (A → B) → Maybe A → Maybe B
  Maybe-<*> (just f) (just x) = just (f x)
  Maybe-<*> nothing  (just x) = nothing
  Maybe-<*> (just f) nothing  = nothing
  Maybe-<*> nothing  nothing  = nothing

  Maybe-δ  : ∀{a b}{A : Set a}{B : Set b}
           → Maybe A × Maybe B → Maybe (A × B)
  Maybe-δ (just x  , just y)   = just (x , y)
  Maybe-δ (nothing , just _)   = nothing
  Maybe-δ (just _  , nothing)  = nothing
  Maybe-δ (nothing , nothing)  = nothing

  instance
    MonadMaybe : ∀{a} → Monad {a} Maybe
    MonadMaybe {a} 
      = monad 
        FunctorMaybe 
        just 
        maybe-μ 
        (λ x f → refl) 
        (λ { (just x) f → refl
           ; nothing  f → refl
           }) 
        refl 
        (λ { {x = just x}  → refl
           ; {x = nothing} → refl
           }) 
        (λ { {x = just x}  → refl
           ; {x = nothing} → refl
           })


    MonadList : ∀{a} → Monad {a} List
    MonadList {a} 
      = monad 
        FunctorList 
        (_∷ []) 
        concat 
        (λ x f → refl) 
        (λ x f → concat-map x) 
        (λ {A} {x} → ++-id x) 
        (λ {A} {x} → sym (cat-map-∷ x)) 
        (λ {A} {x} → cat-cat-cat x)


    ApplicativeMaybe : ∀{a} → Applicative {a} Maybe
    ApplicativeMaybe = applicative MonadMaybe Maybe-<*>

    ApplicativeList : ∀{a} → Applicative {a} List
    ApplicativeList = applicative MonadList List-<*>
