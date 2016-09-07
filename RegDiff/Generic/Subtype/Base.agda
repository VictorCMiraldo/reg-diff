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

  fetchμ : {tv ty : U}
         → Dirμ ty tv
         → μ ty
         → Maybe (⟦ tv ⟧ (μ ty))
  fetchμ (hd k) ⟨ x ⟩ = fetch k x
  fetchμ (tl k d) ⟨ x ⟩ 
    = maybe (fetchμ d) nothing (fetch k x)
