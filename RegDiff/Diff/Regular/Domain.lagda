\begin{code}
open import Prelude hiding (⊥)
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.RelCalc.Base
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Domain
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where

  open import RegDiff.Generic.Multirec ks
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Regular.Base ks keqs A WBA
\end{code}

\begin{code}
  HasRel : UUSet → Set₁
  HasRel Q = ∀{ty tv} → Q ty tv → ⟦ tv ⟧ A ⟵ ⟦ ty ⟧ A
\end{code}

\begin{code}
  ≣ₗ : ∀{a}{A B : Set a} → A → (B ⟵ A)
  ≣ₗ a = fun (const a) ᵒ

  ≣ᵣ : ∀{a}{A B : Set a} → B → (B ⟵ A)
  ≣ᵣ b = fun (const b)
\end{code}

\begin{code}
  Δ-rel : HasRel Δ
  Δ-rel {ty} {tv} (x , y) 
    with U-eq ty tv
  ...| no _ = _∙_ {B = Unit} (≣ᵣ y) (≣ₗ x)
  Δ-rel {ty} {.ty} (x , y) | yes refl
    with dec-eq _≟-A_ ty x y
  ...| no  _ = _∙_ {B = Unit} (≣ᵣ y) (≣ₗ x)
  ...| yes _ = ID
\end{code}

\begin{code}
  S-rel  : {ty : U}{P : UUSet}
         → (doP : HasRel P)
         → S P ty → EndoRel (⟦ ty ⟧ A)
  S-rel doP (SX x)   = doP x
  S-rel doP Scp      = ID
  S-rel doP (S⊗ s o) = S-rel doP s >< S-rel doP o
  S-rel doP (Si1 s)  = S-rel doP s -|- ⊥
  S-rel doP (Si2 s)  = ⊥ -|- S-rel doP s

  C-rel : {P : UUSet}(doP : HasRel P) → HasRel (C P)
  C-rel doP (CX x)  = doP x 
  C-rel doP (Ci1 c) = ι₁ ∙ C-rel doP c
  C-rel doP (Ci2 c) = ι₂ ∙ C-rel doP c

  Sym-rel : {P : UUSet}(doP : HasRel P) → HasRel (Sym P)
  Sym-rel doP s = (doP s) ᵒ

  Al-rel : {P : UUSet}(doP : HasRel P) → HasRel (Al P)
  Al-rel doP (AX x)     = doP x
  Al-rel doP (A⊗ a a')  = Al-rel doP a >< Al-rel doP a'
  Al-rel doP (Ap1  x a) = < Al-rel doP a ∣ ≣ᵣ x         >
  Al-rel doP (Ap2  x a) = < ≣ᵣ x         ∣ Al-rel doP a >
  Al-rel doP (Ap1ᵒ x a) = π₁ ∙ (Al-rel doP a >< ≣ᵣ x)
  Al-rel doP (Ap2ᵒ x a) = π₂ ∙ (≣ᵣ x         >< Al-rel doP a)
\end{code}

\begin{code}
  CSymCSym-rel : {P : UUSet} → HasRel P →  HasRel (C (Sym (C (Sym P))))
  CSymCSym-rel doP
    = C-rel (λ k → Sym-rel (λ {ty} {tv} k → 
                   C-rel   (λ {ty} {tv} k → 
                   Sym-rel (λ {ty} {tv} k → 
                              doP {ty} {tv} k) {ty} {tv} k) {ty} {tv} k) k)
   

  CSymCSymAlΔ-rel : HasRel (C (Sym (C (Sym (Al (Δ))))))
  CSymCSymAlΔ-rel = CSymCSym-rel (Al-rel (λ {ty} {tv} → Δ-rel {ty} {tv}))

  Patch-rel : ∀{ty} → Patch ty → EndoRel (⟦ ty ⟧ A)
  Patch-rel p = S-rel CSymCSymAlΔ-rel p
\end{code}
