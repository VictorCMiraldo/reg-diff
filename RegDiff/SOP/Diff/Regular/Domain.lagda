\begin{code}
open import Prelude hiding (⊥)
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.ListI
open import Prelude.RelCalc.Base
open import RegDiff.Generic.Parms

module RegDiff.SOP.Diff.Regular.Domain
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where

  open import RegDiff.SOP.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.SOP.Generic.Eq ks keqs
  open import RegDiff.SOP.Diff.Regular.Base ks keqs A WBA
\end{code}

\begin{code}
  HasRel : UUSet → Set₁
  HasRel Q = ∀{ty tv} → Q ty tv → ⟦ tv ⟧ ⟵ ⟦ ty ⟧
\end{code}

\begin{code}
  HasRelₐ : AASet → Set₁
  HasRelₐ Q = ∀{ty tv} → Q ty tv → ⟦ tv ⟧ₐ ⟵ ⟦ ty ⟧ₐ
\end{code}

\begin{code}
  HasRelₚ : ΠΠSet → Set₁
  HasRelₚ Q = ∀{ty tv} → Q ty tv → ⟦ tv ⟧ₚ ⟵ ⟦ ty ⟧ₚ
\end{code}

\begin{code}
  ≣ₗ : ∀{a}{A B : Set a} → A → (B ⟵ A)
  ≣ₗ a = fun (const a) ᵒ

  ≣ᵣ : ∀{a}{A B : Set a} → B → (B ⟵ A)
  ≣ᵣ b = fun (const b)

  abstract
    singl : {A B : Set} → A → B → (B ⟵ A)
    singl x y = _∙_ {B = Unit} (≣ᵣ y) (≣ₗ x)

  inj : ∀{ty i} → ⟦ ty ⟧ ⟵ ⟦ typeOf ty i ⟧ₚ
  inj {ty} {i} = fun (inject i)
\end{code}
\begin{code}
  Δ-rel : ∀{α}{A : Set α}{ty tv : A}(P : A → Set)
          (eqA : (x y : A) → Dec (x ≡ y))
          (eqP : (k : A)(x y : P k) → Dec (x ≡ y))
        → delta P ty tv → (P tv ⟵ P ty)
  Δ-rel {ty = ty} {tv = tv} P eqA eqP (pa1 , pa2) 
    with eqA ty tv
  ...| no _ = singl pa1 pa2
  Δ-rel {ty = ty} P eqA eqP (pa1 , pa2) 
     | yes refl with eqP ty pa1 pa2
  ...| no  _ = singl pa1 pa2
  ...| yes _ = ID
\end{code}
\begin{code}
  Δₐ-rel : {ty tv : Atom} → Δₐ ty tv → (⟦ tv ⟧ₐ ⟵ ⟦ ty ⟧ₐ)
  Δₐ-rel {ty} {tv} = Δ-rel {ty = ty} {tv} ⟦_⟧ₐ Atom-eq (dec-eqₐ _≟-A_)

  Δₚ-rel : {ty tv : Π} → Δₚ ty tv → (⟦ tv ⟧ₚ ⟵ ⟦ ty ⟧ₚ)
  Δₚ-rel {ty} {tv} = Δ-rel {ty = ty} {tv} ⟦_⟧ₚ π-eq (dec-eqₚ _≟-A_)

  Δₛ-rel : {ty tv : U} → Δₛ ty tv → (⟦ tv ⟧ ⟵ ⟦ ty ⟧)
  Δₛ-rel {ty} {tv} = Δ-rel {ty = ty} {tv} ⟦_⟧ σπ-eq (dec-eq _≟-A_)
\end{code}
\begin{code}
  α-rel : {a b : Atom}{P : UUSet}
        → (doP : HasRel P)
        → P (α a) (α b)
        → ⟦ b ⟧ₐ ⟵ ⟦ a ⟧ₐ
  α-rel {a} {b} doP wit = fun (→α {b}) ᵒ ∙ doP wit ∙ fun (→α {a})

  S-rel-prod : {P : UUSet}
             → (doP : HasRel P){l : List Atom}
             → ListI ((contr P) ∘ α) l
             → EndoRel ⟦ l ⟧ₚ
  S-rel-prod doP {[]}     []       = ⊤
  S-rel-prod doP {x ∷ xs} (l ∷ ls) = α-rel doP l >< S-rel-prod doP ls
\end{code}
\begin{code}
  S-rel : {ty : U}{P : UUSet}(doP : HasRel P) → S P ty → EndoRel ⟦ ty ⟧
  S-rel doP Scp          = ID
  S-rel doP (Scns i sx)  = inj {i = i} ∙ S-rel-prod doP sx ∙ inj {i = i} ᵒ
  S-rel doP (SX p)       = doP p
\end{code}
\begin{code}
  Al-rel : {P : AASet}(doP : HasRelₐ P)
         → ∀{ty tv} → Al P ty tv → ⟦ tv ⟧ₚ ⟵ ⟦ ty ⟧ₚ
  Al-rel doP A0          = ⊤
  Al-rel doP (Ap1  x a)  = Al-rel doP a ∙ π₂ ∙ (≣ₗ {B = Unit} x >< ID)
  Al-rel doP (Ap1ᵒ x a)  = < ≣ᵣ x ∣ Al-rel doP a >
  Al-rel doP (AX   x a)  = doP x >< Al-rel doP a
\end{code}
\begin{code}
  C-rel : {P : ΠΠSet}(doP : HasRelₚ P)
        → ∀{ty tv} → C P ty tv → ⟦ tv ⟧ ⟵ ⟦ ty ⟧
  C-rel doP (CX i j k) = inj ∙ doP k ∙ inj ᵒ
\end{code}
