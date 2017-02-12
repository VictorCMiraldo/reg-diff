\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Base.Spine
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open Monad {{...}}

  open import RegDiff.Diff.Universe ks keqs A _≟-A_
  open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_
\end{code}

  We begin with the definition of a spine. The spine is 
  responsible for agressively copying structure.
 
  Scp copies the whole structure where Scns copies only
  the top most constructor. Note that we do NOT align
  values comming from the same constructor.

%<*Spine-def>
\begin{code}
  data S (Al : ΠΠSet)(At : AASet)(ty : U) : Set where
    Scp  : S Al At ty
    Schg : (i j : Constr ty)
         → Al (typeOf ty i) (typeOf ty j)
         → S Al At ty
    Scns : (i : Constr ty)
         → All (contr At) (typeOf ty i)
         → S Al At ty
\end{code}
%</Spine-def>

%<*S-map-def>
\begin{code}
  S-map  : {ty : U}{P Q : ΠΠSet}{A B : AASet}
         → (X : P ⇒ Q)(Y : A ⇒ B)
         → S P A ty → S Q B ty
  S-map f g Scp          = Scp
  S-map f g (Schg i j x) = Schg i j (f x)
  S-map f g (Scns i xs)  = Scns i (mapᵢ g xs)
\end{code}
%</S-map-def>
%<*S-mapM-def>
\begin{code}
  S-mapM  :  {ty : U}{M : Set → Set}{{m : Monad M}}
             {P Q : ΠΠSet}{A B : AASet}
          → (X : P ⇒ M ∘₂ Q)
          → (Y : A ⇒ M ∘₂ B)
          → S P A ty → M (S Q B ty)
  S-mapM f g Scp          = return Scp
  S-mapM f g (Schg i j x) = Schg i j <$> f x
  S-mapM f g (Scns i xs)  = Scns i   <$> mapMᵢ g xs
\end{code}
%</S-mapM-def>

%<*S-cost-def>
\begin{code}
  S-cost : {ty : U}{P : ΠΠSet}{At : AASet}
           (doP : Measurable P)
           (doA : Measurable At)
         → S P At ty → ℕ
  S-cost doP doAt Scp         = 0
  S-cost doP doAt (Schg i j x) = doP x
  S-cost doP doAt (Scns i xs) = foldrᵢ (λ h r → doAt h + r) 0 xs
\end{code}
%</S-cost-def>

%<*zip-product-def>
\begin{code}
  zipₚ : {ty : Π}
       → ⟦ ty ⟧ₚ → ⟦ ty ⟧ₚ → All (λ k → Trivialₐ k k) ty
  zipₚ {[]}     _        _         
    = []
  zipₚ {_ ∷ ty} (x , xs) (y , ys)  
    = (x , y) ∷ zipₚ xs ys
\end{code}
%</zip-product-def>
%<*spine-def>
\begin{code}
  spine-cns : {ty : U}(x y : ⟦ ty ⟧) → S Trivialₚ Trivialₐ ty
  spine-cns x y  with sop x | sop y
  spine-cns _ _ | strip cx dx | strip cy dy
    with cx ≟-Fin cy
  ...| no  _     = Schg cx cy (dx , dy)
  spine-cns _ _ | strip _ dx | strip cy dy
     | yes refl  = Scns cy (zipₚ dx dy)
  
  spine : {ty : U}(x y : ⟦ ty ⟧) → S Trivialₚ Trivialₐ ty
  spine {ty} x y 
    with dec-eq _≟-A_ ty x y 
  ...| yes _     = Scp
  ...| no  _     = spine-cns x y
\end{code}
%</spine-def>

  Last but not least, we are left with products that need some alignment!
