\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.List.All
open import RegDiff.Generic.Parms

module RegDiff.Diff.Regular.Base.AlignmentOptimized
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open Monad {{...}}

  open import RegDiff.Diff.Universe ks keqs A _≟-A_
  open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_

  -- Our alignment datatype is just reexported
  open import RegDiff.Diff.Regular.Base.AlignmentType ks keqs A _≟-A_
    public
\end{code}

%<*align-star-def>
\begin{code}
  mutual
    align* : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ → List (Al Trivialₐ ty tv)
    align* {[]}     {[]}     m n = return A0
    align* {[]}     {v ∷ tv} m (n , nn)
      = Ains n <$> align* m nn
    align* {y ∷ ty} {[]}     (m , mm) n
      = Adel m <$> align* mm n
    align* {y ∷ ty} {v ∷ tv} (m , mm) (n , nn)
      =  align? m n (align* mm nn)
      ++ Adel  m       <$> (align*-no-ins mm (n , nn))
      ++ Ains n        <$> (align*-no-del (m , mm) nn)

    align*-no-ins : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ → List (Al Trivialₐ ty tv)
    align*-no-ins {[]}     {[]}     m n = return A0
    align*-no-ins {[]}     {v ∷ tv} m (n , nn)
      = []
    align*-no-ins {y ∷ ty} {[]}     (m , mm) n
      = Adel m <$> align* mm n
    align*-no-ins {y ∷ ty} {v ∷ tv} (m , mm) (n , nn)
      =  align? m n (align* mm nn)
      ++ Adel  m       <$> (align*-no-ins mm (n , nn))

    align*-no-del : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ → List (Al Trivialₐ ty tv)
    align*-no-del {[]}     {[]}     m n = return A0
    align*-no-del {[]}     {v ∷ tv} m (n , nn)
      = Ains n <$> align* m nn
    align*-no-del {y ∷ ty} {[]}     (m , mm) n
      = []
    align*-no-del {y ∷ ty} {v ∷ tv} (m , mm) (n , nn)
      =  align? m n (align* mm nn)
      ++ Ains n       <$> (align*-no-del (m , mm) nn)

    align? : {ty tv : Atom}{tys tvs : Π}
                 → ⟦ ty ⟧ₐ → ⟦ tv ⟧ₐ → List (Al Trivialₐ tys tvs)
                 → List (Al Trivialₐ (ty ∷ tys) (tv ∷ tvs))
    align? {I _} {I _} x y xys = AX (x , y) <$> xys
    align? {K _} {K _} x y xys = AX (x , y) <$> xys
    align? {I _} {K _} x y xys = []
    align? {K _} {I _} x y xys = []


  lift-Adel :  ∀{P ty}     → ⟦ ty ⟧ₚ →  Al P ty []
  lift-Adel {ty = []} v = A0
  lift-Adel {ty = y ∷ ty} (v , vv) = Adel v (lift-Adel vv)

  lift-Ains : ∀{P tv}     → ⟦ tv ⟧ₚ  → Al P [] tv
  lift-Ains {tv = []} v = A0
  lift-Ains {tv = x ∷ tv} (v , vv) = Ains v (lift-Ains vv)

  -- Remark: this is an (inefficient!) LCS at the type level
  -- Efficient Haskell implem: [http://urchin.earth.li/~ian/cabal/lcs/]
  alignh*-help : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ → ℕ × Al Trivialₐ ty tv
  alignh*-help {[]} {[]} m n = 0 , A0
  alignh*-help {[]} {v ∷ tv} m n = 0 , lift-Ains n
  alignh*-help {y ∷ ty} {[]} m n = 0 , lift-Adel m
  alignh*-help {y ∷ ty} {v ∷ tv} (m , mm) (n , nn) with Atom-eq y v
  ... | no ¬p with  alignh*-help {y ∷ ty} {tv} (m , mm) nn
                  | alignh*-help {ty} {v ∷ tv} mm (n , nn)
  ... |  (n1 , r1) | (n2 , r2) with n1 ≤?-ℕ n2
  ... | yes _ = n1 , Ains n r1
  ... | no _ = n2 , Adel m r2
  alignh*-help {y ∷ ty} {v ∷ tv} (m , mm) (n , nn)
      | yes p with alignh*-help mm nn
  ... | (sc , t) = sc + 1 , AX (m , n) t

  alignh* : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ → Al Trivialₐ ty tv
  alignh* xs ys = p2 (alignh*-help xs ys)

  open import Data.List.Any as Any using (here; there)
  open Any.Membership-≡ using (_∈_; _⊆_)

  -- Conjecture: the above heuristic finds a valid alignment, as per the above spec.
  postulate
    alignh-valid : {ty tv : Π} → (y : ⟦ ty ⟧ₚ)(v : ⟦ tv ⟧ₚ) → alignh* y v ∈ align* y v


\end{code}
%</align-star-def>
