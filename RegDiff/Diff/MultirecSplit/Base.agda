open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.MultirecSplit.Base
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  import RegDiff.Generic.Multirec ks as MREC
  import RegDiff.Generic.Eq ks keqs as EQ

  module Internal {fam# : ℕ}(fam : MREC.Fam fam#) where

    open import RegDiff.Diff.Universe ks keqs (MREC.Fix fam) EQ._≟_
    open import RegDiff.Diff.Trivial.Base ks keqs (MREC.Fix fam) EQ._≟_
    open import RegDiff.Diff.Regular.Base ks keqs (MREC.Fix fam) EQ._≟_
      public

    Famᵢ : Set
    Famᵢ = Fin fam#

    T : Famᵢ → Sum fam#
    T k = lookup k fam

    data Sμ (Rec : AASet) : UUSet where
      skel  : {ty : U} → Patch Rec ty → Sμ Rec ty ty
      ins   : {ty : U}{k : Famᵢ}(i : Constr ty)
              → Al Rec (I k ∷ []) (typeOf ty i) 
              → Sμ Rec (T k) ty
      del   : {ty : U}{k : Famᵢ}(i : Constr ty)
              → Al Rec (typeOf ty i) (I k ∷ [])  
              → Sμ Rec ty (T k)

    data Rec : AASet where
        fix : {k k'   : Famᵢ}  
            → Sμ Rec (T k) (T k')      
            → Rec (I k) (I k')
        set : {k k' : Fin ks#} 
            → Trivialₐ (K k) (K k')
            → Rec (K k) (K k')

    Patchμ = Sμ Rec

    CostFor : {A : Set}→ (A → A → Set) → Set
    CostFor P = ∀{ty tv} → P ty tv → ℕ

    mutual
      {-# TERMINATING #-}
      Patchμ-cost : CostFor Patchμ 
      Patchμ-cost (skel x) = Patch-cost Rec-cost x
      Patchμ-cost (ins x a) = Al-cost Rec-cost a
      Patchμ-cost (del x a) = Al-cost Rec-cost a

      Rec-cost : CostFor Rec
      Rec-cost (fix i) = Patchμ-cost i
      Rec-cost (set {k} {k'} s) = cost-Trivialₐ {K k} {K k'} s

    mutual
      diffμ*-atoms : {ty tv : Atom} → ⟦ ty ⟧ₐ → ⟦ tv ⟧ₐ → List (Rec ty tv)
      diffμ*-atoms {I ty} {I tv} x y  = fix <$> diffμ* x y
      diffμ*-atoms {K ty} {K tv} x y  = return (set (x , y))
      diffμ*-atoms {K ty} {I tv} x y  = []
      diffμ*-atoms {I ty} {K tv} x y  = []

      alignμ  : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ
              → List (Al Rec ty tv)
      alignμ x y = align* x y >>= Al-mapM (uncurry diffμ*-atoms)
      
      alignμ'  : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ
               → List (Al Rec ty tv)
      alignμ' {[]}     {_}      _ _  = []
      alignμ' {_}      {[]}     _ _  = []
      alignμ' {_ ∷ _}  {_ ∷ _}  x y  = alignμ x y

      diffμ*-mod : {ty tv : U} → ⟦ ty ⟧ → ⟦ tv ⟧ → List (Patchμ ty tv)
      diffμ*-mod {ty} {tv} x y with Sum-eq ty tv
      ...| no _ = []
      ...| yes refl = skel <$> S-mapM (uncurry alignμ) (spine x y)

      diffμ*-ins : {ty : U}{k : Famᵢ} → Fix fam k → ⟦ ty ⟧ → List (Patchμ (T k) ty)
      diffμ*-ins x y with sop y
      diffμ*-ins {k = k} x _ | strip cy dy 
        = ins {k = k} cy <$> alignμ' (x , unit) dy

      diffμ*-del : {ty : U}{k : Famᵢ} → ⟦ ty ⟧ → Fix fam k → List (Patchμ ty (T k))
      diffμ*-del x y with sop x
      diffμ*-del {k = k} _ y | strip cx dx
        = del {k = k} cx <$> alignμ' dx (y , unit)

      {-# TERMINATING #-}
      diffμ* : {k k' : Famᵢ} → Fix fam k → Fix fam k' → List (Patchμ (T k) (T k'))
      diffμ* {k} {k'} ⟨ x ⟩ ⟨ y ⟩ 
          =  diffμ*-mod {T k}            {T k'}    x      y
          ++ diffμ*-ins {lookup k' fam}  {k}    ⟨  x ⟩    y
          ++ diffμ*-del {lookup k fam}   {k'}      x   ⟨  y ⟩


    module Unstratified where

      infixr 20 _⊔μ_ _⊔a_
      _⊔μ_ : {ty tv : U} → (p q : Patchμ ty tv) → Patchμ ty tv
      p ⊔μ q with Patchμ-cost p ≤?-ℕ Patchμ-cost q
      ...| yes _ = p
      ...| no  _ = q

      _⊔a_ : {ty tv : Π} → (p q : Al Rec ty tv) → Al Rec ty tv
      p ⊔a q with Al-cost Rec-cost p ≤?-ℕ Al-cost Rec-cost q
      ...| yes _ = p
      ...| no  _ = q

      mutual
        ualign : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ → Al Rec ty tv
        ualign {[]}    {[]}    unit     unit     = A0
        ualign {_ ∷ _} {[]}    (x , xs) unit     = Adel x (ualign xs unit)
        ualign {[]}    {_ ∷ _} unit     (y , ys) = Ains y (ualign unit ys)
        ualign {I _ ∷ _} {K _ ∷ _} (x , xs) (y , ys) 
          =  Adel x (ualign xs (y , ys)) 
          ⊔a Ains y (ualign (x , xs) ys)
        ualign {K _ ∷ _} {I _ ∷ _} (x , xs) (y , ys) 
          =  Adel x (ualign xs (y , ys))
          ⊔a Ains y (ualign (x , xs) ys)
        ualign {I _ ∷ _} {I _ ∷ _} (x , xs) (y , ys) 
          =  Adel x (ualign xs (y , ys))
          ⊔a Ains y (ualign (x , xs) ys)
          ⊔a AX (fix (udiffμ x y)) (ualign xs ys)
        ualign {K _ ∷ _} {K _ ∷ _} (x , xs) (y , ys)
          =  Adel x (ualign xs (y , ys))
          ⊔a Ains y (ualign (x , xs) ys)
          ⊔a AX (set (x , y)) (ualign xs ys)

        {-# TERMINATING #-}
        udiffμ : {k k' : Famᵢ} → Fix fam k → Fix fam k' → Patchμ (T k) (T k')
        udiffμ {k} {k'} ⟨ x ⟩ ⟨ y ⟩ with k ≟-Fin k'
        ...| no  _ 
          =  udiffμ-ins {lookup k' fam}  {k}    ⟨  x ⟩    y
          ⊔μ udiffμ-del {lookup k fam}   {k'}      x   ⟨  y ⟩
        ...| yes refl
          =  udiffμ-mod {T k}                      x      y
          ⊔μ udiffμ-ins {lookup k' fam}  {k}    ⟨  x ⟩    y
          ⊔μ udiffμ-del {lookup k fam}   {k'}      x   ⟨  y ⟩

        udiffμ-mod : {ty : U} → ⟦ ty ⟧ → ⟦ ty ⟧ → Patchμ ty ty
        udiffμ-mod {ty} x y = skel (S-map (uncurry ualign) (spine x y))

        udiffμ-ins : {ty : U}{k : Famᵢ} → Fix fam k → ⟦ ty ⟧ → Patchμ (T k) ty
        udiffμ-ins x y with sop y
        udiffμ-ins {k = k} x _ | strip cy dy 
          = ins cy (ualign (x , unit) dy)

        udiffμ-del : {ty : U}{k : Famᵢ} → ⟦ ty ⟧ → Fix fam k → Patchμ ty (T k)
        udiffμ-del x y with sop x
        udiffμ-del {k = k} _ y | strip cx dx
          = del cx (ualign dx (y , unit))
