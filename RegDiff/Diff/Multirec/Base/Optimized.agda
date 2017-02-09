open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.Multirec.Base.Optimized
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

    import RegDiff.Diff.Multirec.Base.Type ks keqs as TYPE
    open TYPE.Internal fam

{- Optimization is the same as performed for alignments
-}
    data Phase : Set where
      L M R : Phase

    mutual
      diffμ*-atoms : {ty tv : Atom} → Phase → ⟦ ty ⟧ₐ → ⟦ tv ⟧ₐ → List (UU→AA Patchμ ty tv)
      diffμ*-atoms {I ty} {I tv} p x y  = fix <$> diffμp* p x y
      diffμ*-atoms {K ty} {K tv} p x y  = return (set (to-α {K ty} x , to-α {K tv} y))
      diffμ*-atoms {K ty} {I tv} p x y  = []
      diffμ*-atoms {I ty} {K tv} p x y  = []

      alignμ  : {ty tv : Π} → Phase → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ
              → List (Al (UU→AA Patchμ) ty tv)
      alignμ p x y = align* x y >>= Al-mapM (uncurry (diffμ*-atoms p))
      
      alignμ'  : {ty tv : Π} → Phase → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ
               → List (Al (UU→AA Patchμ) ty tv)
      alignμ' {[]}     {_}      _ _ _  = []
      alignμ' {_}      {[]}     _ _ _  = []
      alignμ' {_ ∷ _}  {_ ∷ _}  p x y  = alignμ p x y

      diffμ*-mod : {ty tv : U} → ⟦ ty ⟧ → ⟦ tv ⟧ → List (Patchμ ty tv)
      diffμ*-mod {ty} {tv} x y with Sum-eq ty tv
      ...| no _ = []
      diffμ*-mod x y
         | yes refl 
         = skel <$> S-mapM (uncurry (alignμ M)) (spine x y)

      diffμ*-ins : {ty : U}{k : Famᵢ} → Fix fam k → ⟦ ty ⟧ → List (Patchμ (T k) ty)
      diffμ*-ins x y with sop y
      diffμ*-ins x _ | strip cy dy 
        = ins cy <$> alignμ' L (x , unit) dy

      diffμ*-del : {ty : U}{k : Famᵢ} → ⟦ ty ⟧ → Fix fam k → List (Patchμ ty (T k))
      diffμ*-del x y with sop x
      diffμ*-del _ y | strip cx dx
        = del cx <$> alignμ' R dx (y , unit) 


      {-# TERMINATING #-}
      diffμp* : {k k' : Famᵢ} → Phase → Fix fam k → Fix fam k' → List (Patchμ (T k) (T k'))
      diffμp* {k} {k'} M ⟨ x ⟩ ⟨ y ⟩ 
        =   diffμ*-mod {T k}            {T k'}    x      y
        ++  diffμ*-ins {lookup k' fam}  {k}    ⟨  x ⟩    y
        ++  diffμ*-del {lookup k fam}   {k'}      x   ⟨  y ⟩
      diffμp* {k} {k'} L ⟨ x ⟩ ⟨ y ⟩ 
        =   diffμ*-mod {T k}            {T k'}   x      y
        ++  diffμ*-ins {lookup k' fam}  {k}    ⟨  x ⟩    y
      diffμp* {k} {k'} R ⟨ x ⟩ ⟨ y ⟩ 
        =   diffμ*-mod {T k}            {T k'}    x      y
        ++  diffμ*-del {lookup k fam}   {k'}      x   ⟨  y ⟩
