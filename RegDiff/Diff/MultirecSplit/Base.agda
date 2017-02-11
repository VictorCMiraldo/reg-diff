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

    mutual
      data Patchμ : U → U → Set where
        skel  : {ty : U} → Patch Rec ty → Patchμ ty ty
        ins   : {ty : U}{k : Famᵢ}(i : Constr ty)
              → Al Rec (I k ∷ []) (typeOf ty i) 
              → Patchμ (T k) ty
        del   : {ty : U}{k : Famᵢ}(i : Constr ty)
              → Al Rec (typeOf ty i) (I k ∷ [])  
              → Patchμ ty (T k)

      data Rec : Atom → Atom → Set where
        fix : {k k'   : Famᵢ}  
            → Patchμ (T k) (T k')      
            → Rec (I k) (I k')
        set : {k k' : Fin ks#} 
            → Trivialₐ (K k) (K k')
            → Rec (K k) (K k')

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
