\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.All
open import RegDiff.Generic.Parms
open import Prelude.PartialFuncs.Base

module RegDiff.Diff.Regular.Grupoid
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Regular.Base ks keqs A _≟-A_
  open import RegDiff.Diff.Regular.Apply ks keqs A _≟-A_
\end{code}

\begin{code}
  HasInv : {X : Set} → (X → X → Set) → Set
  HasInv Q = ∀{x₁ x₂} → Q x₁ x₂ → Q x₂ x₁
\end{code}
\begin{code}
  Trivialₐ-inv : HasInv Trivialₐ
  Trivialₐ-inv (x , y) = (y , x)

  Trivialₚ-inv : HasInv Trivialₚ
  Trivialₚ-inv (x , y) = (y , x)

  Trivialₛ-inv : HasInv Trivialₛ
  Trivialₛ-inv (x , y) = (y , x)
\end{code}
\begin{code}
  S-inv : {P : ΠΠSet}(doP : HasInv P){ty : U} → S P ty → S P ty
  S-inv doP Scp           = Scp
  S-inv doP (Schg i j p)  = Schg j i (doP p)
  S-inv doP (Scns i ps)   = Scns i (mapᵢ doP ps)
\end{code}
\begin{code}
  Al-inv : {P : AASet}(doP : HasInv P) → HasInv (Al P)
  Al-inv doP A0         = A0
  Al-inv doP (Ap1  x a) = Ap1ᵒ x (Al-inv doP a)
  Al-inv doP (Ap1ᵒ x a) = Ap1  x (Al-inv doP a)
  Al-inv doP (AX   x a) = AX (doP x) (Al-inv doP a)
\end{code}
\begin{code}
  Patch-inv : {P : AASet}(doP : HasInv P){ty : U} → Patch P ty → Patch P ty
  Patch-inv doP = S-inv (Al-inv doP)
\end{code}
\begin{code}
  PatchTrivial-inv : {ty : U} → Patch Trivialₐ ty → Patch Trivialₐ ty
  PatchTrivial-inv = Patch-inv (λ {ty} {tv} → Trivialₐ-inv {ty} {tv})
\end{code}


\begin{code}
  HasCmp : {X : Set} → (X → X → Set) → Set
  HasCmp Q = ∀{x₁ x₂ x₃} → Q x₂ x₃ → Q x₁ x₂ → Maybe (Q x₁ x₃)
\end{code}
\begin{code}
  Trivialₐ-cmp : HasCmp Trivialₐ
  Trivialₐ-cmp {_} {a} (w , z) (x , w') 
    with dec-eqₐ _≟-A_ a w w' 
  ...| yes _ = just (x , z)
  ...| no  _ = nothing

  Trivialₚ-cmp : HasCmp Trivialₚ
  Trivialₚ-cmp {_} {p} (w , z) (x , w')
    with dec-eqₚ _≟-A_ p w w' 
  ...| yes _ = just (x , z)
  ...| no  _ = nothing

  Trivialₛ-cmp : HasCmp Trivialₛ
  Trivialₛ-cmp {_} {s} (w , z) (x , w')
    with dec-eq _≟-A_ s w w' 
  ...| yes _ = just (x , z)
  ...| no  _ = nothing
\end{code}
begin{code}
  S-cmp : {P : UUSet}(doP : HasCmp P){ty : U} → S P ty → S P ty → Maybe (S P ty)
  S-cmp doP Scp s'         = just s'
  S-cmp doP s Scp          = just s
  S-cmp doP (SX p) (SX p') = SX <$> doP p p'
  S-cmp doP (Scns i ps) (Scns j qs)
    with i ≟-Fin j
  ...| no  _    = nothing
  S-cmp doP (Scns _ ps) (Scns j qs) 
     | yes refl = Scns j <$> zipWithMᵢ doP ps qs 
  S-cmp doP (SX p) (Scns i ps') = nothing
  S-cmp doP (Scns i ps) (SX p)  = nothing
\end{code}
begin{code}
  Al-cmp : {P : AASet}(doP : HasCmp P) → HasCmp (Al P)
  Al-cmp doP A0 b = just b
  Al-cmp doP a A0 = just a
  Al-cmp doP a (Ap1 y b)  = Ap1 y <$> Al-cmp doP a b
  Al-cmp doP (Ap1ᵒ x a) b = Ap1ᵒ x <$> Al-cmp doP a b
  Al-cmp doP (Ap1 x a) (Ap1ᵒ y b) = Al-cmp doP a b
  Al-cmp doP (AX x a) (AX y b) = AX <$> doP x y <*> Al-cmp doP a b

  {-
    We could still do better at these cases!
    Ideally, we can invert and apply P instead of
    only composing P.
  -}
  Al-cmp doP (AX x a) (Ap1ᵒ y b) = nothing
  Al-cmp doP (Ap1 x a) (AX y b) = nothing
\end{code}
begin{code}
  Patch-cmp : {P : AASet}(doP : HasCmp P){ty : U}
            → Patch P ty → Patch P ty → Maybe (Patch P ty)
  Patch-cmp doP = S-cmp (C-cmp (Al-cmp doP))
\end{code}
begin{code}
  PatchTrivial-cmp : {ty : U} → Patch Trivialₐ ty → Patch Trivialₐ ty → Maybe (Patch Trivialₐ ty)
  PatchTrivial-cmp = Patch-cmp (λ {ty} {tv} {tw} → Trivialₐ-cmp {ty} {tv} {tw})
\end{code}

  Ideally, we want to prove the following:

  Which will involve some serious Agda!

begin{code}
  S-inv-lemma₁ : {P : UUSet}(appP : HasApp P)(invP : HasInv P)
               → {ty : U}(s : S P ty)
               → (S-app appP s ∙ S-app appP (S-inv invP s)) ≼* (id ♭)
  S-inv-lemma₁ appP invP Scp = ≼-refl
  S-inv-lemma₁ appP invP (SX x) = {!s!}
  S-inv-lemma₁ appP invP (Scns i sx) = {!!}

  PatchTrivial-inv-lemma₁
    : {ty : U}(p : Patch Trivialₐ ty)
    → (PatchTrivial-app p ∙ PatchTrivial-app (PatchTrivial-inv p)) ≼* (id ♭)
  PatchTrivial-inv-lemma₁ p = {!!}

  

\end{code}
