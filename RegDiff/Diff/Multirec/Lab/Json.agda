open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.RelCalc.Base
open import Prelude.List.All

module RegDiff.Diff.Multirec.Lab.Json where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Multirec konstants 
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
    public
  open import RegDiff.Generic.Eq konstants keqs public

  import RegDiff.Diff.Multirec.Base konstants keqs 
    as DIFF
  import RegDiff.Diff.Multirec.Apply konstants keqs
    as APPLY

  jsonᵢ jsArrᵢ : Fin 2
  jsonᵢ    = fz
  jsArrᵢ   = fs fz

  json-type : Sum 2
  json-type = (I jsArrᵢ ⊗ u1) ⊕ (K kℕ ⊗ u1) ⊕ []

  jsArr-type : Sum 2
  jsArr-type = u1 ⊕ (I jsonᵢ ⊗ I jsArrᵢ ⊗ u1) ⊕ []

  JSON : Fam 2
  JSON = json-type ∷ (jsArr-type ∷ [])

  json : Set
  json = Fix JSON jsonᵢ

  jsArr : Set
  jsArr = Fix JSON jsArrᵢ

  # : jsArr
  # = ⟨ i1 unit ⟩

  _%_ : json → jsArr → jsArr
  x % xs = ⟨ i2 (i1 (x , xs , unit)) ⟩

  fork : jsArr → json
  fork x = ⟨ i1 (x , unit) ⟩

  info : ℕ → json
  info x = ⟨ i2 (i1 (x , unit)) ⟩

  infixr 20 _%_

  open DIFF.Internal JSON public
  open APPLY.Internal JSON public
  open import RegDiff.Diff.Universe konstants keqs (Fix JSON) _≟_
    using (⟦_⟧)

  js1 js2 js3 : json
  
  js1 = fork (info 1 
             % fork (info 2 % info 3 % #) 
             % #)

  js3 = fork (info 10 
             % fork (info 20 % info 30 % #) 
             % #)

  js2 = fork (info 1 % info 2 % info 3 % #)

  -- 2427 branches.
  -- constructors js1 = 11
  -- constructors js2 = 8
  j12 j12-nf : Patchμ (T jsonᵢ) (T jsonᵢ)
  j12 = diffμ js1 js2

{-
     Here is a table with all different optimization combinations (align and diffμ)
     representing (length (diffμ* js1 js2))

     AO = Align Optimized
     AN = Align Naive
     DO = Diffμ optimized
     DN = Diffμ naive

        | DN    | DO    
     -------------
     AN | 84619 | 7037
     -------------
     AO | 2427  | 55
-}

  j12-nf = skel
        (Scns fz
         (AX
          (fix
           (skel
            (Scns (fs fz)
             (AX (fix (skel Scp)) A0 ∷
              (AX
               (fix
                (del {k = fs fz} (fs fz)
                 (AX (fix (del {k = fs fz} fz (AX (fix (skel Scp)) A0))) 
                 (Adel ⟨ i1 unit ⟩ A0))))
               A0
               ∷ [])))))
          A0
          ∷ []))

  -- This patch amounts to the function:
  {-
    f : json -> Maybe json
    f (fork (x % fork y % #)) = just (fork (x % y))
    f _                       = nothing
  -}

  _==_ : json → Maybe json → Bool
  _ == nothing = false
  t == just u with t ≟ u 
  ...| yes _ = true
  ...| no  _ = false

  test : json → Maybe json
  test x = Patchμ-app j12-nf x

  
