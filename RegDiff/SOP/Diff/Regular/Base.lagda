  Here we define a refinement over the trivial diff.
  Instead of storing both values as a whole,
  we will store a bunch of transformations that
  could transform one into the other.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import RegDiff.Generic.Parms

module RegDiff.SOP.Diff.Regular.Base
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where

  open Monad {{...}}

  open import RegDiff.SOP.Generic.Multirec ks
  open import RegDiff.SOP.Generic.Eq ks keqs
  open import RegDiff.SOP.Diff.Trivial.Base ks keqs A WBA
    public

  data ListI {a b}{A : Set a}(P : A → Set b) : List A → Set b where
    []   : ListI P []
    _∷_  : ∀{x xs} → P x → ListI P xs → ListI P (x ∷ xs)

  mapᵢ : ∀{a b}{A : Set a}{P Q : A → Set b}{l : List A}
        → (f : ∀{k} → P k → Q k)
        → ListI P l → ListI Q l
  mapᵢ f [] = []
  mapᵢ f (x ∷ xs) = f x ∷ mapᵢ f xs

  mapMᵢ : ∀{a b}{A : Set a}{M : Set b → Set b}{{m : Monad M}}
           {P Q : A → Set b}{l : List A}
        → (f : ∀{k} → P k → M (Q k))
        → ListI P l → M (ListI Q l)
  mapMᵢ f []       = return []
  mapMᵢ f (i ∷ li) = f i >>= (λ qi → mapMᵢ f li >>= return ∘ (qi ∷_))
  
\end{code}

  An inhabitant of S represents a spine. 
  A Spine intuitively is the maximal shared prefix between two
  elements of the same type.

  Here we also add a Copy (Scp) instruction, representing
  the fact that both elements are propositionally equal.

  It is unsure to us, at this point, whether Scp should belong
  here or to Δ.

%<*S1-def>
\begin{code}
  data Al (P : AASet) : Prod parms# → Prod parms# → Set where
    Ap1  : ∀{a ty tv}     → ⟦ a ⟧ₐ A  → Al P ty tv → Al P (a ∷ ty) tv
    Ap1ᵒ : ∀{a ty tv}     → ⟦ a ⟧ₐ A  → Al P ty tv → Al P ty (a ∷ tv)
    AX   : ∀{a a' ty tv}  → P a a'    → Al P ty tv → Al P (a ∷ ty) (a' ∷ tv)

  data C (P : AASet) : U → U → Set where
    same   : {ty : U}{i : Constr ty} 
           → ListI (λ k → P k k) (typeOf ty i) → C P ty ty 
    change : {ty tv : U}
           → (i : Constr ty)(j : Constr tv)
           → Al P (typeOf ty i) (typeOf tv j) 
           → C P ty tv
\end{code}
%</S1-def>
