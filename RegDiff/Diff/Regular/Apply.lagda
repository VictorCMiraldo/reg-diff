  Here we define application for
  Regular-type patches.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.List.All
open import Prelude.Monad
open import Prelude.PartialFuncs.Base
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Apply
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open import RegDiff.Diff.Universe ks keqs A _≟-A_
  open import RegDiff.Diff.Regular.Base ks keqs A _≟-A_
  open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_
  open import RegDiff.Diff.Trivial.Apply ks keqs A _≟-A_
\end{code}

  The application functions in both directions makes it easy
  to see how the two phases of the algorithm play together.

\begin{code}
  β-app : {a b : Atom}{P : ΠΠSet}
        → (doP : HasAppₚ P)
        → P (β a) (β b)
        → ⟦ a ⟧ₐ ↦ ⟦ b ⟧ₐ
  β-app {a} {b} doP wit = (return ∘ from-β {b}) 
                        ∙ doP wit 
                        ∙ (return ∘ to-β {a}) 

  S-app-prod : {P : ΠΠSet}
             → (doP : HasAppₚ P){l : List Atom}
             → All ((contr P) ∘ β) l
             → ⟦ l ⟧ₚ ↦ ⟦ l ⟧ₚ
  S-app-prod doP {[]}     []       = !
  S-app-prod doP {x ∷ xs} (l ∷ ls) = β-app doP l >< S-app-prod doP ls
\end{code}
\begin{code}
  S-app : {ty : U}{P : ΠΠSet}(doP : HasAppₚ P) → S P ty → ⟦ ty ⟧ ↦ ⟦ ty ⟧
  S-app doP Scp           = id ♭
  S-app doP (Scns i sx)   = to-inj {i = i} ∙ S-app-prod doP sx ∙ from-inj
  S-app doP (Schg i j p)  = to-inj ∙ doP p ∙ from-inj
\end{code}
\begin{code}
  guard♯ : {a : Atom}{ty : Π}
         → ⟦ a ⟧ₐ → ⟦ a ∷ ty ⟧ₚ ↦ ⟦ ty ⟧ₚ
  guard♯ {a} x (y , ys) 
    with dec-eqₐ _≟-A_ a x y
  ...| no  _ = nothing
  ...| yes _ = just ys

  Al-app : {P : AASet}(doP : HasAppₐ P)
         → ∀{ty tv} → Al P ty tv → ⟦ ty ⟧ₚ ↦ ⟦ tv ⟧ₚ
  Al-app doP A0          = !
  Al-app doP (Adel {a = ta} x a)  = Al-app doP a ∙ guard♯ {a = ta} x
  Al-app doP (Ains x a)  = split♯ ((const x) ♭) (Al-app doP a)
  Al-app doP (AX   x a)  = doP x >< Al-app doP a
\end{code}
\begin{code}
  Patch-app : {ty : U}{P : AASet}(doP : HasAppₐ P) 
            → Patch P ty → ⟦ ty ⟧ ↦ ⟦ ty ⟧
  Patch-app doP = S-app (Al-app doP)
\end{code}
\begin{code}
  PatchΔ-app : {ty : U} → Patch Trivialₐ ty → ⟦ ty ⟧ ↦ ⟦ ty ⟧
  PatchΔ-app = Patch-app (λ {ty} {tv} → Trivialₐ-apply {ty} {tv})
\end{code}


  Alignment application function is correct!

begin{code}
  module Al-app-correct 
           {P : AASet}(doP : HasAppₐ P)
           (costP : ∀{ty tv} → P ty tv → ℕ)
           (hipP : ∀{ty tv}(p₁ p₂ : P ty tv)
                 → costP p₁ ≤ costP p₂
                 → (doP p₂) ≼* (doP p₁))
      where
  
    proof : ∀{ty tv}(a₁ a₂ : Al P ty tv)
          → Al-cost costP a₁ ≤ Al-cost costP a₂
          → Al-app doP a₂ ≼* Al-app doP a₁
    proof A0 A0 hip {x} = up refl
    proof (Ap1 {a = ta} x a1) (Ap1  y a2) hip = {!!}
    proof (Ap1 {a = ta} x a1) (Ap1ᵒ {a = tb} y a2) hip = {!!}
    proof (Ap1 {a = ta} x a1) (AX yz a2) hip = {!!}
    proof a1 a2 hip = {!!}
\end{code}
