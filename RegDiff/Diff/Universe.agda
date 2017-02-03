open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import RegDiff.Generic.Parms

module RegDiff.Diff.Universe
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open import RegDiff.Generic.Multirec ks
    renaming ( Atom to Atom'
             ; ⟦_⟧ₐ to interpₐ
             ; ⟦_⟧ₚ to interpₚ
             ; ⟦_⟧ to interpₛ
             )
    public
  open import RegDiff.Generic.Eq ks keqs
    public

-- First we define a few synonyms without
-- having to pass parms# around everywhere.
  Atom : Set
  Atom = Atom' parms#

  U : Set
  U = Sum parms#

  Π : Set
  Π = Prod parms#

-- Same for the interpretation functions!
  ⟦_⟧ₐ : Atom → Set
  ⟦ a ⟧ₐ = interpₐ a A

  ⟦_⟧ₚ : Π → Set
  ⟦ p ⟧ₚ = interpₚ p A

  ⟦_⟧ : U → Set
  ⟦ u ⟧ = interpₛ u A

-- Useful to have relations over the different levels of our universe
  UUSet : Set₁
  UUSet = U → U → Set

  AASet : Set₁
  AASet = Atom → Atom → Set

  ΠΠSet : Set₁
  ΠΠSet = Π → Π → Set

-- Finally, a bunch of general purpose functionality.
  contr : ∀{a b}{A : Set a}{B : Set b}
        → (A → A → B) → A → B
  contr p x = p x x

  UU→AA : UUSet → AASet
  UU→AA P a a' = P (α a) (α a')

  to-α : {a : Atom} → ⟦ a ⟧ₐ → ⟦ α a ⟧
  to-α k = i1 (k , unit)

  from-α : {a : Atom} → ⟦ α a ⟧ → ⟦ a ⟧ₐ
  from-α (i1 (k , unit)) = k
  from-α (i2 ())

  →α : {a : Atom} → ⟦ a ⟧ₐ → ⟦ α a ⟧
  →α k = i1 (k , unit)

  to-β : {a : Atom} → ⟦ a ⟧ₐ → ⟦ β a ⟧ₚ
  to-β k = (k , unit)

  from-β : {a : Atom} → ⟦ β a ⟧ₚ → ⟦ a ⟧ₐ
  from-β (k , unit) = k
