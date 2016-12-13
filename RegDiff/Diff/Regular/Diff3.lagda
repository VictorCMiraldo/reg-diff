\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.ListI
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Diff3
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(WBA  : WBParms A)
    where

  open Monad {{...}}

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Regular.Base ks keqs A WBA
    public
\end{code}
\begin{code}
  Parallel : {A : Set}(P : A → A → Set) → Set₁
  Parallel {A} P = {a b : A} → P a b → P a b → Set


  data PLs (P : UUSet)(plp : Parallel P) : {ty : U} → S P ty → S P ty → Set where
    pscpₗ : {ty : U}{s : S P ty} → PLs P plp Scp s
    pscpᵣ : {ty : U}{s : S P ty} → PLs P plp s Scp
    psx   : {ty : U}(r s : P ty ty)
          → plp r s → PLs P plp (SX r) (SX s)
    pscns : {ty : U}(i : Constr ty)(rs ss : ListI (contr P ∘ α) (typeOf ty i))
          → foldrᵢ (λ h r → uncurry plp h × r) Unit (zipWithᵢ _,_ rs ss)
          → PLs P plp {ty} (Scns i rs) (Scns i ss)

  data PLc (P : ΠΠSet)(plp : Parallel P) : {ty tv : U} → C P ty tv → C P ty tv → Set where 
    pcx   : {ty tv : U}(i : Constr ty)(j : Constr tv)
          → (rs ss : P (typeOf ty i) (typeOf tv j))
          → plp rs ss
          → PLc P plp {ty} {tv} (CX i j rs) (CX i j ss)
          
  
\end{code}
