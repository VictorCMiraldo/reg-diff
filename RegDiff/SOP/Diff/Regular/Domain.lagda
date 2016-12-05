\begin{code}
open import Prelude hiding (⊥)
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.RelCalc.Base
open import RegDiff.Generic.Parms

module RegDiff.SOP.Diff.Regular.Domain
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where

  open import RegDiff.SOP.Generic.Multirec ks
  open import RegDiff.SOP.Generic.Eq ks keqs
  open import RegDiff.SOP.Diff.Regular.Base ks keqs A WBA
\end{code}

\begin{code}
  HasRel : UUSet → Set₁
  HasRel Q = ∀{ty tv} → Q ty tv → ⟦ tv ⟧ A ⟵ ⟦ ty ⟧ A
\end{code}

\begin{code}
  HasRelₐ : AASet → Set₁
  HasRelₐ Q = ∀{ty tv} → Q ty tv → ⟦ tv ⟧ₐ A ⟵ ⟦ ty ⟧ₐ A
\end{code}

\begin{code}
  HasRelₚ : ΠΠSet → Set₁
  HasRelₚ Q = ∀{ty tv} → Q ty tv → ⟦ tv ⟧ₚ A ⟵ ⟦ ty ⟧ₚ A
\end{code}

\begin{code}
  ≣ₗ : ∀{a}{A B : Set a} → A → (B ⟵ A)
  ≣ₗ a = fun (const a) ᵒ

  ≣ᵣ : ∀{a}{A B : Set a} → B → (B ⟵ A)
  ≣ᵣ b = fun (const b)

  inj : ∀{ty i} → ⟦ ty ⟧ A ⟵ ⟦ typeOf ty i ⟧ₚ A
  inj {ty} {i} = fun (inject i)
\end{code}

\begin{code}
  Δ-rel : ∀{ty tv} → Δ ty tv → ⟦ tv ⟧ₐ A ⟵ ⟦ ty ⟧ₐ A
  Δ-rel {ty} {tv} (x , y) 
    with Atom-eq ty tv
  ...| no _ = _∙_ {B = Unit} (≣ᵣ y) (≣ₗ x)
  Δ-rel {ty} {.ty} (x , y) | yes refl
    with dec-eqₐ _≟-A_ ty x y
  ...| no  _ = _∙_ {B = Unit} (≣ᵣ y) (≣ₗ x)
  ...| yes _ = ID
\end{code}

\begin{code}
  Al-rel : {P : AASet}(doP : HasRelₐ P)
         → ∀{ty tv} → Al P ty tv → ⟦ tv ⟧ₚ A ⟵ ⟦ ty ⟧ₚ A
  Al-rel doP A0          = ⊤
  Al-rel doP (Ap1  x a)  = Al-rel doP a ∙ π₂ ∙ (≣ₗ {B = Unit} x >< ID)
  Al-rel doP (Ap1ᵒ x a)  = < ≣ᵣ x ∣ Al-rel doP a >
  Al-rel doP (AX   x a)  = doP x >< Al-rel doP a

  C-rel : {P : ΠΠSet}(doP : HasRelₚ P)
        → ∀{ty tv} → C P ty tv → ⟦ tv ⟧ A ⟵ ⟦ ty ⟧ A
  C-rel doP (CX i j k) = inj ∙ doP k ∙ inj ᵒ
\end{code}
