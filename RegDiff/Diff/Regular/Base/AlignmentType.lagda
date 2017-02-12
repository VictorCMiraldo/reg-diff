\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Base.AlignmentType
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open Monad {{...}}

  open import RegDiff.Diff.Universe ks keqs A _≟-A_
  open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_
\end{code}


%<*Al-def>
\begin{code}
  data Al (P : Atom → Atom → Set) : Π → Π → Set where
    A0   :                                          Al P [] []
    Adel : ∀{a ty tv}     → ⟦ a ⟧ₐ  → Al P ty tv →  Al P (a ∷ ty) tv
    Ains : ∀{a ty tv}     → ⟦ a ⟧ₐ  → Al P ty tv →  Al P ty       (a ∷ tv)
    AX   : ∀{a a' ty tv}  → P a a   → Al P ty tv →  Al P (a ∷ ty) (a' ∷ tv)
\end{code}
%</Al-def>
%<*Al-mapM-def>
\begin{code}
  Al-map : {ty tv : Π}
            {P Q : AASet}(X : ∀{k v} → P k v → Q k v)
          → Al P ty tv → Al Q ty tv
  Al-map f A0 = A0
  Al-map f (Adel x a) = Adel x (Al-map f a)
  Al-map f (Ains x a) = Ains x (Al-map f a)
  Al-map f (AX x a) = AX (f x) (Al-map f a)

  Al-map1 : {ty tv : Π}
            {P Q : AASet}(X : ∀{k} → P k k → Q k k)
          → Al P ty tv → Al Q ty tv
  Al-map1 f A0 = A0
  Al-map1 f (Adel x a) = Adel x (Al-map1 f a)
  Al-map1 f (Ains x a) = Ains x (Al-map1 f a)
  Al-map1 f (AX x a) = AX (f x) (Al-map1 f a)

  Al-mapM : {ty tv : Π}{M : Set → Set}{{m : Monad M}}
            {P Q : AASet}(X : ∀{k v} → P k v → M (Q k v))
          → Al P ty tv → M (Al Q ty tv)
  Al-mapM f A0 = return A0
  Al-mapM f (Adel x a) = Adel x <$> Al-mapM f a 
  Al-mapM f (Ains x a) = Ains x <$> Al-mapM f a
  Al-mapM f (AX x a) = f x >>= λ x' → AX x' <$> Al-mapM f a
\end{code}
%</Al-mapM-def>
%<*Al-cost-def>
\begin{code}
  Al-cost : {ty tv : Π}{P : AASet}(doP : {k v : Atom} → P k v → ℕ)
          → Al P ty tv → ℕ
  Al-cost doP A0         = 0
  Al-cost doP (Adel x a)  = 1 + Al-cost doP a
  Al-cost doP (Ains x a) = 1 + Al-cost doP a
  Al-cost doP (AX x a)   = doP x + Al-cost doP a
\end{code}
3
