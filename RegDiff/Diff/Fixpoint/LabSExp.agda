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
        ⊕ I ⊗ []
        ⊕ []

  SExp : Set
  SExp = Fix (SExpF ∷ []) fz

  %nil %name %int %def %cons %parens : Constr SExpF
  %nil = fz
  %name = fs fz
  %int = fs (fs fz)
  %def = fs (fs (fs fz))
  %cons = fs (fs (fs (fs fz)))
  %parens = fs (fs (fs (fs (fs fz))))

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

  Parens : SExp → SExp 
  Parens s = ⟨ (i2 (i2 (i2 (i2 (i2 (i1 (s , unit))))))) ⟩

  infixr 20 _!>_

  _=s=_ : SExp → Maybe SExp → Bool
  _ =s= nothing = false
  t =s= just u with t EQ.≟ u 
  ...| yes _ = true
  ...| no  _ = false

  k1 k2 k3 k4 k5 k6 : SExp
  k1 = Def "head" (Name "s")
                  (Name "if" !> (Parens (Name "null") !> (Name "s"))
                             !> (Parens (Name "error" !> (Int 10)))
                             !> (Parens (Name "car" !> (Name "s")))
                  )

  k2 = Def "head" (Name "s" !> Name "d")
                  (Name "if" !> (Parens (Name "null") !> (Name "s"))
                             !> (Parens (Name "d"))
                             !> (Parens (Name "car" !> (Name "s")))
                  )

  k3 = Def "init" (Name "s")
                  (Name "if" !> (Parens (Name "null") !> (Name "s"))
                             !> (Parens (Name "error" !> (Int 10)))
                             !> (Parens (Name "if" 
                               !> Parens (Name "null" !> Parens (Name "cdr" !> Name "s"))
                               !> Parens #
                               !> Parens (Parens (Name "car" !> Name "s") 
                                  !> Parens (Name "init" 
                                    !> Parens (Name "cdr" !> Name "s")))))
                  )

  k4 = Def "init" (Name "s" !> Name "d")
                  (Name "if" !> (Parens (Name "null") !> (Name "s"))
                             !> (Parens (Name "d"))
                             !> (Parens (Name "if" 
                               !> Parens (Name "null" !> Parens (Name "cdr" !> Name "s"))
                               !> Parens #
                               !> Parens (Parens (Name "car" !> Name "s") 
                                  !> Parens (Name "init" 
                                    !> Parens (Name "cdr" !> Name "s")))))
                  )


  k5 = Def "tail" (Name "s")
                  (Name "if" !> (Parens (Name "null") !> (Name "s"))
                             !> (Parens (Name "error" !> (Int 10)))
                             !> (Parens (Name "if" 
                               !> Parens (Name "null" !> Parens (Name "cdr" !> Name "s"))
                               !> Parens (Name "car" !> (Name "s"))
                               !> Parens (Name "tail" 
                                         !> Parens (Name "cdr" !> Name "s"))))
                  )


  k6 = Def "tail" (Name "s" !> Name "d")
                  (Name "if" !> (Parens (Name "null") !> (Name "s"))
                             !> (Parens (Name "d"))
                             !> (Parens (Name "if" 
                               !> Parens (Name "null" !> Parens (Name "cdr" !> Name "s"))
                               !> Parens (Name "car" !> (Name "s"))
                               !> Parens (Name "tail" 
                                         !> Parens (Name "cdr" !> Name "s"))))
                  )

  open DIFF.Internal  (SExpF ∷ []) public
  open APPLY.Internal (SExpF ∷ []) public

  d12 d12-expected : Patchμ (T fz) (T fz)
  d12 = diffμ k1 k2

  -- WARNING: Takes about 3h to compute.
  d15 d15-expected : Patchμ (T fz) (T fz)
  d15 = diffμ k1 k5

  d12-expected
    = skel
      (Scns %def
       ( AX (set (i1 ("head" , unit) , i1 ("head" , unit))) A0 
       ∷ AX (fix (ins {k = fz} %cons
          (AX (fix (skel Scp)) (Ains (Name "d") A0)))) 
         A0
       ∷ AX (fix (skel (Scns %cons
            ( AX (fix (skel Scp)) A0 
            ∷ AX (fix (skel (Scns %cons
               ( AX (fix (skel Scp)) A0 
               ∷ AX (fix (ins {k = fz} %cons
                  (Ains (Parens (Name "d"))
                  (AX (fix (skel (Schg %cons %parens
                      (Adel (Parens (Name "error" !> (Int 10)))
                      (AX (fix (del {k = fz} %parens (AX (fix (skel Scp)) A0)))
                       A0)))))
                   A0)))) A0
               ∷ [])))) A0
            ∷ [])))) A0
       ∷ []))


  d15-expected 
    = skel (Scns %def
      ( AX (set (i1 ("head" , unit) , i1 ("tail" , unit))) A0 
      ∷ AX (fix (skel Scp)) A0
      ∷ AX (fix (skel (Scns %cons
           ( AX (fix (skel Scp)) A0 
           ∷ AX (fix (skel (Scns %cons
                ( AX (fix (skel Scp)) A0 
                ∷ AX (fix (ins %cons
                     (AX (fix {k = fz} (skel (Schg %cons %parens
                          (AX (fix (del {k = fz} %parens (AX (fix (skel Scp)) A0)))
                          (Adel (Parens (Name "car" !> (Name "s")))
                           A0)))))
                     (Ains (Parens (Name "if" 
                            !> (Parens (Name "null" !> Parens (Name "cdr" !> Name "s")))
                            !> ((Parens (Name "car" !> Name "s")
                                  !> Parens (Name "tail" 
                                  !> Parens (Name "cdr" !> Name "s"))))))
                     A0)))) A0
                ∷ [])))) A0
           ∷ [])))) A0
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
{-
  expected-ok-12 : d12 ≡ d12-expected
  expected-ok-12 = refl

  expected-ok-15 : d15 ≡ d15-expected
  expected-ok-15 = refl
-}
