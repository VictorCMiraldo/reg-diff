  Here we define application for
  Regular-type patches.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.ListI
open import Prelude.Monad
open import Prelude.PartialFuncs.Base
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Apply
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Regular.Base ks keqs A WBA
\end{code}

  The application functions in both directions makes it easy
  to see how the two phases of the algorithm play together.

\begin{code}
  HasApp : UUSet → Set
  HasApp Q = ∀{ty tv} → Q ty tv → ⟦ ty ⟧ ↦ ⟦ tv ⟧
\end{code}

\begin{code}
  HasAppₐ : AASet → Set
  HasAppₐ Q = ∀{ty tv} → Q ty tv → ⟦ ty ⟧ₐ ↦ ⟦ tv ⟧ₐ
\end{code}

\begin{code}
  HasAppₚ : ΠΠSet → Set
  HasAppₚ Q = ∀{ty tv} → Q ty tv → ⟦ ty ⟧ₚ ↦ ⟦ tv ⟧ₚ
\end{code}
\begin{code}
  from-inj : {ty : U}{i : Constr ty} → ⟦ ty ⟧ ↦ ⟦ typeOf ty i ⟧ₚ
  from-inj x with sop x
  from-inj {ty} {i} _ | strip cx dx 
    with cx ≟-Fin i
  ...| no _ = nothing
  from-inj _ | strip cx dx
     | yes refl = just dx

  to-inj : {ty : U}{i : Constr ty} → ⟦ typeOf ty i ⟧ₚ ↦ ⟦ ty ⟧
  to-inj {ty} {i} = return ∘ inject i
\end{code}
\begin{code}
  singl   : ∀{α}{A : Set α}{ty tv : A}(P : A → Set)
            (eqP : (k : A)(x y : P k) → Dec (x ≡ y))
          → P ty → P tv → (P ty ↦ P tv)
  singl {ty = ty} P eqP pa pb x
    with eqP ty pa x
  ...| yes _ = just pb
  ...| no  _ = nothing
\end{code}
\begin{code}
  Δ-apply : ∀{α}{A : Set α}{ty tv : A}(P : A → Set)
            (eqA : (x y : A) → Dec (x ≡ y))
            (eqP : (k : A)(x y : P k) → Dec (x ≡ y))
          → delta P ty tv → (P ty ↦ P tv)
  Δ-apply {ty = ty} {tv = tv} P eqA eqP (pa1 , pa2)
    with eqA ty tv
  ...| no _ = singl P eqP pa1 pa2
  Δ-apply {ty = ty} P eqA eqP (pa1 , pa2) 
     | yes refl with eqP ty pa1 pa2
  ...| no  _ = singl P eqP pa1 pa2
  ...| yes _ = id♯
\end{code}
\begin{code}
  Δₐ-apply : {ty tv : Atom} → Δₐ ty tv → (⟦ ty ⟧ₐ ↦ ⟦ tv ⟧ₐ)
  Δₐ-apply {ty} {tv} = Δ-apply {ty = ty} {tv} ⟦_⟧ₐ Atom-eq (dec-eqₐ _≟-A_)

  Δₚ-apply : {ty tv : Π} → Δₚ ty tv → (⟦ ty ⟧ₚ ↦ ⟦ tv ⟧ₚ)
  Δₚ-apply {ty} {tv} = Δ-apply {ty = ty} {tv} ⟦_⟧ₚ π-eq (dec-eqₚ _≟-A_)

  Δₛ-apply : {ty tv : U} → Δₛ ty tv → (⟦ ty ⟧ ↦ ⟦ tv ⟧)
  Δₛ-apply {ty} {tv} = Δ-apply {ty = ty} {tv} ⟦_⟧ σπ-eq (dec-eq _≟-A_)
\end{code}
\begin{code}
  α-app : {a b : Atom}{P : UUSet}
        → (doP : HasApp P)
        → P (α a) (α b)
        → ⟦ a ⟧ₐ ↦ ⟦ b ⟧ₐ
  α-app {a} {b} doP wit = (return ∘ from-α {b}) ∙ doP wit ∘ to-α {a}

  S-app-prod : {P : UUSet}
             → (doP : HasApp P){l : List Atom}
             → ListI ((contr P) ∘ α) l
             → ⟦ l ⟧ₚ ↦ ⟦ l ⟧ₚ
  S-app-prod doP {[]}     []       = !
  S-app-prod doP {x ∷ xs} (l ∷ ls) = α-app doP l >< S-app-prod doP ls
\end{code}
\begin{code}
  S-app : {ty : U}{P : UUSet}(doP : HasApp P) → S P ty → ⟦ ty ⟧ ↦ ⟦ ty ⟧
  S-app doP Scp          = id♯
  S-app doP (Scns i sx)  = to-inj {i = i} ∙ S-app-prod doP sx ∙ from-inj
  S-app doP (SX p)       = doP p
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
  Al-app doP (Ap1 {a = ta} x a)  = Al-app doP a ∙ guard♯ {a = ta} x
  Al-app doP (Ap1ᵒ x a)  = split♯ (const♯ x) (Al-app doP a)
  Al-app doP (AX   x a)  = doP x >< Al-app doP a
\end{code}
\begin{code}
  C-app : {P : ΠΠSet}(doP : HasAppₚ P)
        → ∀{ty tv} → C P ty tv → ⟦ ty ⟧ ↦ ⟦ tv ⟧
  C-app doP (CX i j k) = to-inj ∙ doP k ∙ from-inj
\end{code}
\begin{code}
  Patch-app : {ty : U}{P : AASet}(doP : HasAppₐ P) 
            → Patch P ty → ⟦ ty ⟧ ↦ ⟦ ty ⟧
  Patch-app doP = S-app (C-app (Al-app doP))
\end{code}
\begin{code}
  PatchΔ-app : {ty : U} → Patch Δₐ ty → ⟦ ty ⟧ ↦ ⟦ ty ⟧
  PatchΔ-app = Patch-app (λ {ty} {tv} → Δₐ-apply {ty} {tv})
\end{code}
