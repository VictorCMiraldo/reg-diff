open import Prelude
open import Prelude.Functor.Decl

module Prelude.Monad.Decl where

  record Monad {a}(M : Set a → Set a) : Set (ls a) where
    constructor monad
    field
      isFunctor : Functor M
      η : {A : Set a} → A → M A
      μ : {A : Set a} → M (M A) → M A
      
      η-natural : {A B : Set a}(x : A)(f : A → B)
                → η (f x) ≡ fmap isFunctor f (η x)
      μ-natural : {A B : Set a}(x : M (M A))(f : A → B)
                → μ (fmap isFunctor (fmap isFunctor f) x) ≡ fmap isFunctor f (μ x)
      μ-η-id  : {A : Set a}{x : M A} → μ (η x) ≡ x
      id-μ-η  : {A : Set a}{x : M A} → x ≡ μ (fmap isFunctor η x)
      μ-assoc : {A : Set a}{x : M (M (M A))}
                → μ (μ x) ≡ μ (fmap isFunctor μ x)

  open Monad

  mmap : ∀{a}{M : Set a → Set a}{{_ : Monad M}}{A B : Set a}
       → (f : A → B) → M A → M B
  mmap {{m}} f = fmap (isFunctor m) f

  return : ∀{a}{M : Set a → Set a}{{_ : Monad M}}{A : Set a}
         → A → M A
  return {{m}} = η m

  infixl 1 _>>=_ _>>_
  _>>=_ : ∀{a}{M : Set a → Set a}{{_ : Monad M}}{A B : Set a} 
        → M A → (A → M B) → M B
  _>>=_ {{m}} x f = μ m (mmap f x)

  _>>_ : ∀{a}{M : Set a → Set a}{{ _ : Monad M }}{A B : Set a}
       → M A → M B → M B
  f >> g = f >>= λ _ → g

  infixl 20 _<$>_
  _<$>_ : ∀{a}{M : Set a → Set a}{{_ : Monad M}}{A B : Set a}
        → (A → B) → M A → M B
  f <$> x = x >>= return ∘ f

  infixr 9 _∙_
  _∙_ : ∀{a}{M : Set a → Set a}{{_ : Monad M}}{A B C : Set a}
      → (B → M C) → (A → M B) → A → M C
  (f ∙ g) x = g x >>= f


  record Applicative {a}(M : Set a → Set a) : Set (ls a) where
    constructor applicative
    field
      isMonad : Monad M
      app     : {A B : Set a} → M (A → B) → M A → M B

  open Applicative
  
  infixl 20 _<*>_
  _<*>_ : ∀{a}{M : Set a → Set a}{{_ : Applicative M}}{A B : Set a}
        → M (A → B) → M A → M B
  _<*>_ {{a}} mab ma = app a mab ma

  
  module Properties where

    mmap-return : ∀{a}{M : Set a → Set a}{{m : Monad M}}{A B : Set a}
                → (x : A)(f : A → B)
                → (mmap {{m}} f (return x)) ≡ return (f x)
    mmap-return {{m}} x f = sym (η-natural m x f)

    return->>= : ∀{a}{M : Set a → Set a}{{_ : Monad M}}{A B : Set a}
               → (x : A)(f : A → M B)
               → (return x >>= f) ≡ f x
    return->>= {{m}} x f = trans (cong (μ m) (mmap-return x f)) 
                                 (μ-η-id m)

    >>=-return : ∀{a}{M : Set a → Set a}{{_ : Monad M}}{A B : Set a}
               → (x : M A)
               → (x >>= return) ≡ x
    >>=-return {{m}} x = sym (id-μ-η m)

{-
    >>=-assoc  : ∀{a}{M : Set a → Set a}{{_ : Monad M}}{A B C : Set a}
               → (x : M A)(f : A → M B)(g : B → M C)
               → ((x >>= f) >>= g) ≡ (x >>= (λ x' → f x' >>= g))
    >>=-assoc {{m}} x f g = trans (cong (μ m) (sym (μ-natural m (mmap f x) g))) 
                           (trans (μ-assoc m) {!!})
-}

  
