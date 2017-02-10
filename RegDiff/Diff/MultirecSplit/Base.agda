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

    data Sμ (P : U → U → Set) : U → U → Set where
      share  : {ty : U} → S (Al (UU→AA P)) ty → Sμ P ty ty
      empty  : {ty tv : U} → P ty tv → Sμ P ty tv

    data Alμ (P : U → U → Set) : U → U → Set where
      ins   : {ty : U}{k : Famᵢ}(i : Constr ty)
            → Al (UU→AA P) (I k ∷ []) (typeOf ty i) 
            → Alμ P (T k) ty
      del   : {ty : U}{k : Famᵢ}(i : Constr ty)
            → Al (UU→AA P) (typeOf ty i) (I k ∷ [])  
            → Alμ P ty (T k)
      nil   : {ty tv : U} → P ty tv → Alμ P ty tv

    data Rec (P : U → U → Set) : U → U → Set where
      fix : {k k'   : Famᵢ}  
          → P (T k) (T k')      
          → Rec P (α (I k)) (α (I k'))
      set : {ty tv : U} 
          → Trivialₛ ty tv
          → Rec P ty tv

{-
  I'll define a bunch of synonyms to make life easier
-}
    MapMFor : ((U → U → Set) → U → U → Set) → Set₁
    MapMFor F = ∀{ty tv}{P Q : U → U → Set}{M : Set → Set}{{_ : Monad M}}
              → (∀{k v} → P k v → M (Q k v))
              → F P ty tv → M (F Q ty tv)

    CostFor : (U → U → Set) → Set
    CostFor P = ∀{ty tv} → P ty tv → ℕ

    AlgoFor : (U → U → Set) → Set
    AlgoFor P = ∀{ty tv}(x : ⟦ ty ⟧)(y : ⟦ tv ⟧) → List (P ty tv)

{-
  Now, our cost functions
-}
    Sμ-cost : ∀{P} → CostFor P → CostFor (Sμ P)
    Sμ-cost doP (empty x) = doP x
    Sμ-cost doP (share x) = Patch-cost doP x

    Alμ-cost : ∀{P} → CostFor P → CostFor (Alμ P)
    Alμ-cost doP (nil a) = doP a
    Alμ-cost doP (ins x a) = Al-cost doP a
    Alμ-cost doP (del x a) = Al-cost doP a

    Rec-cost : ∀{P} → CostFor P → CostFor (Rec P)
    Rec-cost doP (fix i) = doP i
    Rec-cost doP (set s) = cost-Trivialₛ s
    

    Patchμ₀ : (U → U → Set) → U → U → Set
    Patchμ₀ P = Sμ (Alμ (Rec P))

    data Patchμ : U → U → Set where
      roll : {ty tv : U} → Patchμ₀ Patchμ ty tv → Patchμ ty tv
    

    {-# TERMINATING #-}
    Patchμ-cost : CostFor Patchμ
    Patchμ-cost (roll p) = Sμ-cost (Alμ-cost (Rec-cost Patchμ-cost)) p

    mutual
{-
      diffμ*-atoms : {ty tv : Atom} → Phase → ⟦ ty ⟧ₐ → ⟦ tv ⟧ₐ → List (UU→AA Patchμ ty tv)
      diffμ*-atoms {I ty} {I tv} p x y  = fix <$> diffμp* p x y
      diffμ*-atoms {K ty} {K tv} p x y  = return (set (to-α {K ty} x , to-α {K tv} y))
      diffμ*-atoms {K ty} {I tv} p x y  = []
      diffμ*-atoms {I ty} {K tv} p x y  = []
-}

      alignμ  : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ
              → List (Al (UU→AA Patchμ) ty tv)
      alignμ x y = align* x y >>= Al-mapM (uncurry {!!})
      
      alignμ'  : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ
               → List (Al (UU→AA Patchμ) ty tv)
      alignμ' {[]}     {_}      _ _  = []
      alignμ' {_}      {[]}     _ _  = []
      alignμ' {_ ∷ _}  {_ ∷ _}  x y  = alignμ x y

      diffμ*-mod : {ty tv : U} → ⟦ ty ⟧ → ⟦ tv ⟧ → List (Patchμ₀ Patchμ ty tv)
      diffμ*-mod {ty} {tv} x y with Sum-eq ty tv
      ...| no _ = []
      ...| yes refl = share <$> S-mapM (uncurry {!alignμ!}) (spine x y)

      diffμ*-ins : {ty : U}{k : Famᵢ} → Fix fam k → ⟦ ty ⟧ → List (Patchμ₀ Patchμ (T k) ty)
      diffμ*-ins x y with sop y
      diffμ*-ins {k = k} x _ | strip cy dy 
        = (empty ∘ ins {k = k} cy) <$> {!!}

      diffμ*-del : {ty : U}{k : Famᵢ} → ⟦ ty ⟧ → Fix fam k → List (Patchμ₀ Patchμ ty (T k))
      diffμ*-del x y with sop x
      diffμ*-del {k = k} _ y | strip cx dx
        = (empty ∘ del {k = k} cx) <$> {!alignμ' dx (y , unit)!}

      diffμ* : {k k' : Famᵢ} → Fix fam k → Fix fam k' → List (Patchμ (T k) (T k'))
      diffμ* {k} {k'} ⟨ x ⟩ ⟨ y ⟩ 
          = roll <$> (diffμ*-mod {T k}            {T k'}    x      y
                  ++  diffμ*-ins {lookup k' fam}  {k}    ⟨  x ⟩    y
                  ++  diffμ*-del {lookup k fam}   {k'}      x   ⟨  y ⟩)
