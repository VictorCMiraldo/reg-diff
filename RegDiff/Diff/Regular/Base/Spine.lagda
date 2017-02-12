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
  data S (Al : ΠΠSet)(At : AASet) : U → Set where
    Scp  : {ty : U} → S Al At ty
    Schg : {ty : U}(i j : Constr ty)
         → Al (typeOf ty i) (typeOf ty j)
         → S Al At ty
    Scns : {ty : U}(i : Constr ty)
         → All (contr At) (typeOf ty i)
         → S Al At ty
\end{code}
%</Spine-def>

%<*S-map-def>
\begin{code}
  S-map  :  {ty : U}
            {P Q : ΠΠSet}{At : AASet}(X : ∀{k v} → P k v → Q k v)
         → S P At ty → S Q At ty
  S-map f Scp          = Scp
  S-map f (Schg i j x) = Schg i j (f x)
  S-map f (Scns i xs)  = Scns i xs
\end{code}
%</S-map-def>
%<*S-mapM-def>
\begin{code}
  S-mapM  :  {ty : U}{M : Set → Set}{{m : Monad M}}
             {P Q : ΠΠSet}{At : AASet}(X : ∀{k v} → P k v → M (Q k v))
          → S P At ty → M (S Q At ty)
  S-mapM f Scp          = return Scp
  S-mapM f (Schg i j x) = Schg i j <$> f x
  S-mapM f (Scns i xs)  = return (Scns i xs)
\end{code}
%</S-mapM-def>

%<*S-cost-def>
\begin{code}
  S-cost : {ty : U}{P : ΠΠSet}{At : AASet}
           (doAt : {k k' : Atom} → At k k' → ℕ)
           (doP : {k v : Π} → P k v → ℕ)
         → S P At ty → ℕ
  S-cost doAt doP Scp         = 0
  S-cost doAt doP (Schg i j x) = doP x
  S-cost doAt doP (Scns i xs) = foldrᵢ (λ h r → doAt h + r) 0 xs
\end{code}
%</S-cost-def>

%<*zip-product-def>
\begin{code}
  zipₚ : {ty : Π}
       → ⟦ ty ⟧ₚ → ⟦ ty ⟧ₚ → All (λ k → Trivialₐ k k) ty
  zipₚ {[]}     _        _         
    = []
  zipₚ {_ ∷ ty} (x , xs) (y , ys)  
    = (x , y ) ∷ zipₚ xs ys
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
