open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad

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
  open import RegDiff.Generic.Lemmas ks keqs A _≟-A_
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

-- And we borrow some relation functionality from
-- Agda
  open import Relation.Binary.Core
    using (REL; _⇒_)
    public

  -- composes a monad with a relation.
  -- Makes the types of the mapM guys much simpler
  _∘₂_ : ∀{a b c}{A : Set a}{B : Set b}
       → (M : Set c → Set c){{_ : Monad M}} 
       → REL A B c
       → REL A B c
  (M ∘₂ R) x y = M (R x y)

  -- We are specially intereste in "measurable" relations
  Measurable : ∀{a b c}{A : Set a}{B : Set b}
             → REL A B c → Set (c ⊔ (b ⊔ a))
  Measurable R = ∀{i j} → R i j → ℕ


-- Finally, a bunch of general purpose functionality.
  contr : ∀{a b}{A : Set a}{B : Set b}
        → (A → A → B) → A → B
  contr p x = p x x

  UU→AA : UUSet → AASet
  UU→AA P a a' = P (α a) (α a')

  to-β : {a : Atom} → ⟦ a ⟧ₐ → ⟦ β a ⟧ₚ
  to-β k = (k , unit)

  from-β : {a : Atom} → ⟦ β a ⟧ₚ → ⟦ a ⟧ₐ
  from-β (k , unit) = k

  to-α : {a : Atom} → ⟦ a ⟧ₐ → ⟦ α a ⟧
  to-α {a} k = i1 (to-β {a} k)

  from-α : {a : Atom} → ⟦ α a ⟧ → ⟦ a ⟧ₐ
  from-α {a} (i1 k) = from-β {a} k
  from-α (i2 ())

  to-α-elim : {a : Atom}(x : ⟦ a ⟧ₐ)
            → to-α {a} x ≡ i1 (x , unit)
  to-α-elim x = refl
