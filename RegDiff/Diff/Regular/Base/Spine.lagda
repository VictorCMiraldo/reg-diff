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
  data S (P : ΠΠSet) : U → Set where
    Scp  : {ty : U} → S P ty
    Schg : {ty : U}(i j : Constr ty)
         → P (typeOf ty i) (typeOf ty j)
         → S P ty
    Scns : {ty : U}(i : Constr ty)
         → All (contr P ∘ β) (typeOf ty i)
         → S P ty
\end{code}
%</Spine-def>

%<*S-map-def>
\begin{code}
  S-map  :  {ty : U}
            {P Q : ΠΠSet}(X : ∀{k v} → P k v → Q k v)
         → S P ty → S Q ty
  S-map f Scp          = Scp
  S-map f (Schg i j x) = Schg i j (f x)
  S-map f (Scns i xs)  = Scns i (mapᵢ f xs)
\end{code}
%</S-map-def>
%<*S-mapM-def>
\begin{code}
  S-mapM  :  {ty : U}{M : Set → Set}{{m : Monad M}}
             {P Q : ΠΠSet}(X : ∀{k v} → P k v → M (Q k v))
          → S P ty → M (S Q ty)
  S-mapM f Scp          = return Scp
  S-mapM f (Schg i j x) = Schg i j <$> f x
  S-mapM f (Scns i xs)  = Scns i   <$> mapMᵢ f xs
\end{code}
%</S-mapM-def>

%<*S-cost-def>
\begin{code}
  S-cost : {ty : U}{P : ΠΠSet}(doP : {k v : Π} → P k v → ℕ)
         → S P ty → ℕ
  S-cost doP Scp         = 0
  S-cost doP (Schg i j x) = doP x
  S-cost doP (Scns i xs) = foldrᵢ (λ h r → doP h + r) 0 xs
\end{code}
%</S-cost-def>

%<*zip-product-def>
\begin{code}
  zipₚ : {ty : Π}
       → ⟦ ty ⟧ₚ → ⟦ ty ⟧ₚ → All (λ k → Trivialₚ (β k) (β k)) ty
  zipₚ {[]}     _        _         
    = []
  zipₚ {_ ∷ ty} (x , xs) (y , ys)  
    = ((x , unit) , (y , unit)) ∷ zipₚ xs ys
\end{code}
%</zip-product-def>
%<*spine-def>
\begin{code}
  spine-cns : {ty : U}(x y : ⟦ ty ⟧) → S Trivialₚ ty
  spine-cns x y  with sop x | sop y
  spine-cns _ _ | strip cx dx | strip cy dy
    with cx ≟-Fin cy
  ...| no  _     = Schg cx cy (dx , dy)
  spine-cns _ _ | strip _ dx | strip cy dy
     | yes refl  = Scns cy (zipₚ dx dy)
  
  spine : {ty : U}(x y : ⟦ ty ⟧) → S Trivialₚ ty
  spine {ty} x y 
    with dec-eq _≟-A_ ty x y 
  ...| yes _     = Scp
  ...| no  _     = spine-cns x y
\end{code}
%</spine-def>

  Last but not least, we are left with products that need some alignment!
