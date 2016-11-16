\begin{code}
open import Prelude
open import Prelude.Eq

module RegDiff.Generic.Parms where
\end{code}

%<*Parms-def>
\begin{code}
  Parms : ℕ → Set₁
  Parms n = Fin n → Set
\end{code}
%</Parms-def>

\begin{code}
  _⇉_ : {n : ℕ} → Parms n → Parms n → Set
  P ⇉ Q = ∀{k} → P k → Q k
\end{code}

  Well behaved parameters are those that
  have a size function and decidable equality!

%<*WBParms-def>
\begin{code}
  record WBParms {n : ℕ}(A : Parms n) : Set where
    constructor wb-parms
    field 
      parm-size : ∀{k} → A k → ℕ
      parm-cmp  : ∀{k}(x y : A k) → Dec (x ≡ y)
\end{code}
%</WBParms-def>

\begin{code}
  open WBParms public

{-
  Here we provide some toy parameters
-}
  module ToyParms where

    parms# : ℕ
    parms# = 3

    x₁ x₂ x₃ : Fin parms#
    x₁ = fz
    x₂ = (fs fz)
    x₃ = fs (fs fz)

    data RGB : Set where
      R G B : RGB

    rgb-eq : (x y : RGB) → Dec (x ≡ y)
    rgb-eq R R = yes refl
    rgb-eq R G = no (λ ())
    rgb-eq R B = no (λ ())
    rgb-eq G R = no (λ ())
    rgb-eq G G = yes refl
    rgb-eq G B = no (λ ())
    rgb-eq B R = no (λ ())
    rgb-eq B G = no (λ ())
    rgb-eq B B = yes refl

    data Heavy : Set where
      weighted : ℕ → Heavy

    weighted-inj : {x y : ℕ} → weighted x ≡ weighted y → x ≡ y
    weighted-inj refl = refl

    heavy-eq : (x y : Heavy) → Dec (x ≡ y)
    heavy-eq (weighted x) (weighted y)
      with x ≟-ℕ y
    ...| yes h = yes (cong weighted h)
    ...| no  h = no (h ∘ weighted-inj)

    PARMS : Fin parms# → Set
    PARMS fz           = ℕ
    PARMS (fs fz)      = RGB
    PARMS (fs (fs fz)) = Heavy
    PARMS (fs (fs (fs ())))

    WB-PARMS : WBParms PARMS
    WB-PARMS 
      = wb-parms 
        (λ { {fz}         p → 1 
           ; {fs fz}      p → 1
           ; {fs (fs fz)} (weighted k) → k
           ; {fs (fs (fs ()))} _
           }) 
        (λ { {fz}         → _≟-ℕ_
           ; {fs fz}      → rgb-eq
           ; {fs (fs fz)} → heavy-eq
           ; {fs (fs (fs ()))} _
           }) 
\end{code}
