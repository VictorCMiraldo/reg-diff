\begin{code}
open import Prelude hiding (⊥)
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.RelCalc.Base
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Domains
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where

  open Monad {{...}}

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
  ≣ₗ a _ a' = a ≡ a'

  ≣ᵣ : ∀{a}{A B : Set a} → B → (B ⟵ A)
  ≣ᵣ b b' _ = b ≡ b'
\end{code}

\begin{code}
  Δ-rel : HasRel Δ
  Δ-rel (x , y) = λ y' x' → y' ≡ y × x ≡ x' 
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

  C-rel : {ty tv : U}{P : UUSet}(doP : HasRel P)
        → C P ty tv → (⟦ tv ⟧ A ⟵ ⟦ ty ⟧ A)
  C-rel doP (CX x)  = doP x 
  C-rel doP (Ci1 c) = ι₁ ∙ C-rel doP c
  C-rel doP (Ci2 c) = ι₂ ∙ C-rel doP c

  Sym-rel : {ty tv : U}{P : UUSet}(doP : HasRel P)
          → Sym P ty tv → (⟦ tv ⟧ A ⟵ ⟦ ty ⟧ A)
  Sym-rel doP s = (doP s) ᵒ

  Al-rel : {ty tv : U}{P : UUSet}(doP : HasRel P)
         → Al P ty tv → (⟦ tv ⟧ A ⟵ ⟦ ty ⟧ A)  
  Al-rel doP (AX x)     = doP x
  Al-rel doP (A⊗ a a')  = Al-rel doP a >< Al-rel doP a'
  Al-rel doP (Ap1  x a) = < Al-rel doP a ∣ ≣ᵣ x         >
  Al-rel doP (Ap2  x a) = < ≣ᵣ x         ∣ Al-rel doP a >
  Al-rel doP (Ap1ᵒ x a) = π₁ ∙ (Al-rel doP a >< ≣ᵣ x)
  Al-rel doP (Ap2ᵒ x a) = π₂ ∙ (≣ᵣ x         >< Al-rel doP a)
\end{code}

\begin{code}
  CSymCSymAlΔ-rel : HasRel (C (Sym (C (Sym (Al (Δ))))))
  CSymCSymAlΔ-rel 
    = λ {ty} {tv} → C-rel   {ty} {tv} (
      λ {ty} {tv} → Sym-rel {ty} {tv} (
      λ {ty} {tv} → C-rel   {ty} {tv} (
      λ {ty} {tv} → Sym-rel {ty} {tv} (
      λ {ty} {tv} → Al-rel  {ty} {tv} (
      λ {ty} {tv} → Δ-rel   {ty} {tv}))))) 

  Patch-rel : ∀{ty} → Patch ty → EndoRel (⟦ ty ⟧ A)
  Patch-rel p = S-rel CSymCSymAlΔ-rel p
\end{code}
