open import Prelude 
open import Prelude.Vector

module RegDiff.Generic.Subtype.Base
      {n : ℕ}(v : Vec Set n) -- (eqs : VecI Eq v)
    where

  open import RegDiff.Generic.Base v 

  data Dir : U → U → Set where
    here  : {ty : U} → Dir ty ty
    left  : {k ty tv : U} → Dir ty k → Dir (ty ⊕ tv) k
    right : {k ty tv : U} → Dir tv k → Dir (ty ⊕ tv) k
    fst   : {k ty tv : U} → Dir ty k → Dir (ty ⊗ tv) k
    snd   : {k ty tv : U} → Dir tv k → Dir (ty ⊗ tv) k
  
  data Dirμ (ty : U) : U → Set where
    hd : {k : U} → Dir ty k → Dirμ ty k
    tl : {k : U} → Dir ty I → Dirμ ty k → Dirμ ty k
    

  fetch : {A : Set}{ty tv : U}
        → Dir ty tv 
        → ⟦ ty ⟧ A → Maybe (⟦ tv ⟧ A)
  fetch here x = just x
  fetch (left d) (i1 x) = fetch d x
  fetch (left d) (i2 y) = nothing
  fetch (right d) (i1 x) = nothing
  fetch (right d) (i2 y) = fetch d y
  fetch (fst d) x = fetch d (p1 x)
  fetch (snd d) x = fetch d (p2 x)

  on : {A : Set}{ty tv : U}
      → Dir ty tv → (⟦ tv ⟧ A → Maybe (⟦ tv ⟧ A))
      → ⟦ ty ⟧ A → Maybe (⟦ ty ⟧ A)
  on here el x = el x
  on (left d) el (i1 x) = i1 <M> on d el x
  on (left d) el (i2 y) = nothing
  on (right d) el (i1 x) = nothing
  on (right d) el (i2 y) = i2 <M> on d el y
  on (fst d) el (x , y) = (_, y) <M> on d el x
  on (snd d) el (x , y) = (x ,_) <M> on d el y

  fetchμ : {tv ty : U}
         → Dirμ ty tv
         → μ ty
         → Maybe (⟦ tv ⟧ (μ ty))
  fetchμ (hd k) ⟨ x ⟩ = fetch k x
  fetchμ (tl k d) ⟨ x ⟩ 
    = maybe (fetchμ d) nothing (fetch k x)

  onμ : {ty tv : U}
       → Dirμ ty tv
       → (⟦ tv ⟧ (μ ty) → Maybe (⟦ tv ⟧ (μ ty))) 
       → μ ty → Maybe (μ ty)
  onμ (hd c) el ⟨ x ⟩ = ⟨_⟩ <M> on c el x
  onμ (tl c dir) el ⟨ x ⟩ 
    = ⟨_⟩ <M> on c (onμ dir el) x

  rome : {A : Set}(ty : U)
       → ⟦ ty ⟧ A → List (Dir ty I)
  rome I x = here ∷ []
  rome u1 x = []
  rome (K k) x = []
  rome (ty ⊕ tv) (i1 x) = map left (rome ty x)
  rome (ty ⊕ tv) (i2 y) = map right (rome tv y)
  rome (ty ⊗ tv) (x , y) = map fst (rome ty x) ++ map snd (rome tv y)
