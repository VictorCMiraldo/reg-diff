open import Prelude hiding (⊥)
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.RelCalc.Base
open import Prelude.List.All
open import Prelude.Monad
open import Data.String

module RegDiff.Diff.Fixpoint.LabSExp where

  open Monad {{...}}

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Eq konstants keqs as EQ
  open import RegDiff.Generic.Multirec konstants
    renaming (I to I')
  import RegDiff.Diff.Multirec.Base konstants keqs 
    as DIFF
  import RegDiff.Diff.Multirec.Apply konstants keqs 
    as APPLY

  I : Atom 1
  I = I' fz

  SExpF : Sum 1
  SExpF = u1 
        ⊕ (K kString) ⊗ [] 
        ⊕ (K kℕ) ⊗ [] 
        ⊕ (K kString) ⊗ I ⊗ I ⊗ []
        ⊕ (I ⊗ I ⊗ [])
        ⊕ (I ⊗ (K kString) ⊗ (K kString) ⊗ I ⊗ I ⊗ [])
        ⊕ I ⊗ []
        ⊕ []

  SExp : Set
  SExp = Fix (SExpF ∷ []) fz

  %nil %name %int %def %cons %elim : Constr SExpF
  %nil = fz
  %name = fs fz
  %int = fs (fs fz)
  %def = fs (fs (fs fz))
  %cons = fs (fs (fs (fs fz)))
  %elim = fs (fs (fs (fs (fs fz))))
  %parens = fs (fs (fs (fs (fs (fs (fz {n = 0}))))))

  # : SExp
  # = ⟨ i1 unit ⟩

  Name : String → SExp
  Name s = ⟨ i2 (i1 (s , unit)) ⟩

  Int : ℕ → SExp
  Int n = ⟨ i2 (i2 (i1 (n , unit))) ⟩

  Def : String → SExp → SExp → SExp
  Def func parms body = ⟨ i2 (i2 (i2 (i1 (func , parms , body , unit)))) ⟩

  _!>_ : SExp → SExp → SExp
  p !> q = ⟨ i2 (i2 (i2 (i2 (i1 (p , q , unit))))) ⟩

  Elim : SExp → String → String → SExp → SExp → SExp
  Elim arg s s' nil nnil = ⟨ i2 (i2 (i2 (i2 (i2 (i1 (arg , s , s' , nil , nnil , unit)))))) ⟩

  Parens : SExp → SExp 
  Parens s = ⟨ i2 (i2 (i2 (i2 (i2 (i2 (i1 (s , unit))))))) ⟩

  infixr 20 _!>_

  _=s=_ : SExp → Maybe SExp → Bool
  _ =s= nothing = false
  t =s= just u with t EQ.≟ u 
  ...| yes _ = true
  ...| no  _ = false

  k1 k2 k3 k4 k5 k6 : SExp
  k1 = Def "head" (Name "s") 
                  (Elim (Name "s") "sHD" "sTL" 
                    (Name "error" !> (Int 10)) 
                    (Name "sHD") 
                  )

  k2 = Def "head" (Name "s" !> Name "d") 
                  (Elim (Name "s") "sHD" "sTL" 
                    (Name "d") 
                    (Name "sHD") 
                  )

  k5 = Def "tail" (Name "s") 
                  (Elim (Name "s") "sHD" "sTL" 
                    (Name "error" !> (Int 10)) 
                    (Elim  (Name "sTL") "_" "_" 
                           (Name "sHD")
                           (Name "last" !> Name "sTL")
                    )
                  )


  k3 = Def "length" (Name "k") 
                    (Elim (Name "k") "kHD" "kTL" 
                      (Name "error" !> (Int 10)) 
                      (Name "+" !> (Name "1" !> Parens (Name "length" !> Name "kTL")))
                    )

  k4 = Def "length" (Name "k" !> Name "d") 
                    (Elim (Name "k") "kHD" "kTL" 
                      (Name "d") 
                      (Name "+" !> (Name "1" !> Parens (Name "length" !> Name "kTL")))
                    )

  k6 = Def "tail" (Name "s" !> Name "d") 
                  (Elim (Name "s") "sHD" "sTL" 
                    (Name "d") 
                    (Elim  (Name "sTL") "_" "_" 
                           (Name "sHD")
                           (Name "last" !> Name "sTL")
                    )
                  )

  open DIFF.Internal  (SExpF ∷ []) public
  open APPLY.Internal (SExpF ∷ []) public

  d12 d12-expected : Patchμ (T fz) (T fz)
  d12 = diffμ k1 k2

  d15 d15-expected : Patchμ (T fz) (T fz)
  d15 = diffμ k1 k5

  d12-expected
    = skel
      (Scns %def
       (AX (set (i1 ("head" , unit) , i1 ("head" , unit))) A0 ∷
        AX
        (fix
         (ins {k = fz} %cons
          (AX (fix (skel Scp)) (Ains ⟨ i2 (i1 ("d" , unit)) ⟩ A0))))
        A0
        ∷
        AX
        (fix
         (skel
          (Scns %elim
           (AX (fix (skel Scp)) A0 ∷
            AX (set (i1 ("sHD" , unit) , i1 ("sHD" , unit))) A0 ∷
            AX (set (i1 ("sTL" , unit) , i1 ("sTL" , unit))) A0 ∷
            AX
            (fix
             (del {k = fz} %cons
              (AX
               (fix
                (skel
                 (Scns %name
                  (AX (set (i1 ("error" , unit) , i1 ("d" , unit))) A0 ∷ []))))
               (Adel ⟨ i2 (i2 (i1 (10 , unit))) ⟩ A0))))
            A0
            ∷ AX (fix (skel Scp)) A0 ∷ []))))
        A0
        ∷ []))

  d15-expected = skel
     (Scns %def
      (AX (set (i1 ("head" , unit) , i1 ("tail" , unit))) A0 ∷
       AX (fix (skel Scp)) A0 ∷
       AX
       (fix
        (skel
         (Scns %elim
          (AX (fix (skel Scp)) A0 ∷
           AX (set (i1 ("sHD" , unit) , i1 ("sHD" , unit))) A0 ∷
           AX (set (i1 ("sTL" , unit) , i1 ("sTL" , unit))) A0 ∷
           AX (fix (skel Scp)) A0 ∷
           AX
           (fix
            (ins {k = fz} %elim
             (Ains ⟨ i2 (i1 ("sTL" , unit)) ⟩
              (Ains "_"
               (Ains "_"
                (AX (fix (skel Scp))
                 (Ains (Name "last" !> Name "sTL")
                  A0)))))))
           A0
           ∷ []))))
       A0
       ∷ []))

  d12-apply : Patchμ-app d12-expected k3 ≡ just k4
  d12-apply = refl

  d12-15-apply : (Patchμ-app {k' = fz} d12-expected k1 
                   >>= Patchμ-app d15-expected) 
                 ≡ just k6   
  d12-15-apply = refl

  d15-12-apply : (Patchμ-app {k' = fz} d15-expected k1 
                   >>= Patchμ-app d12-expected) 
                 ≡ just k6   
  d15-12-apply = refl

  expected-ok-12 : d12 ≡ d12-expected
  expected-ok-12 = refl

  expected-ok-15 : d15 ≡ d15-expected
  expected-ok-15 = refl
