open import Prelude
open import Prelude.Eq
open import Prelude.Vector using (Vec ; VecI)
open import Prelude.Monad
open import Prelude.List.All
open import Prelude.List.Lemmas
open import Prelude.Nat.Lemmas
open import Prelude.PartialFuncs.Base

open import RegDiff.Generic.Parms

open import RegDiff.Diff.Abstract.Base

module RegDiff.Diff.Abstract.Instances.AlignmentNaive
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

open import RegDiff.Diff.Universe ks keqs A _≟-A_
open import RegDiff.Diff.Trivial.Base ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Base.AlignmentNaive ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Apply ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Lemmas ks keqs A _≟-A_

open Monad {{...}}

-- The same as we did for Spines, we now do for alignments.
Al-Diffable : Diffable ⟦_⟧ₐ → Diffable ⟦_⟧ₚ
Al-Diffable doP = record 
  { P     = Al (P doP) 
  ; cands = λ x y → align* x y >>= Al-mapM (uncurry (cands doP))
  ; apply = Al-app (apply doP) 
  ; cost  = Al-cost (cost doP) 
  }


private 
  module CandsCorrect 
           (doP : Diffable ⟦_⟧ₐ)
           (okP : CandsCorrect ⟦_⟧ₐ doP)
      where

    Ains-correct
      : {ty : Atom}{tys tvs : Π}(y : ⟦ ty ⟧ₐ)(xs : ⟦ tvs ⟧ₚ)(ys : ⟦ tys ⟧ₚ)
      → {k : P (Al-Diffable doP) tvs tys}
      → IsCand (Al-Diffable doP) xs ys k
      → IsCand (Al-Diffable doP) {b = ty ∷ tys} xs (y , ys) (Ains y k)
    Ains-correct y xs ys hip 
      rewrite hip = refl

    lemma-cands-ins
      : {ty : Atom}{tys tvs : Π}(y : ⟦ ty ⟧ₐ)(xs : ⟦ tvs ⟧ₚ)(ys : ⟦ tys ⟧ₚ)
      → {k : Al Trivialₐ tvs tys}
      → All (IsCand (Al-Diffable doP) xs ys) 
            (Al-mapM (uncurry (cands doP)) k)
      → All (IsCand (Al-Diffable doP) {b = ty ∷ tys} xs (y , ys)) 
            (Ains y <$> Al-mapM (uncurry (cands doP)) k)
    lemma-cands-ins {ty} {tys} y xs ys hip
      = All-<$>-commute (Ains y) (mapᵢ (λ {k} → Ains-correct {ty} {tys} y xs ys {k}) hip)

    Adel-correct
      : {tv : Atom}{tys tvs : Π}(x : ⟦ tv ⟧ₐ)(xs : ⟦ tvs ⟧ₚ)(ys : ⟦ tys ⟧ₚ)
      → {k : P (Al-Diffable doP) tvs tys}
      → IsCand (Al-Diffable doP) xs ys k
      → IsCand (Al-Diffable doP) {a = tv ∷ tvs} (x , xs) ys (Adel x k)
    Adel-correct {tv} x xs ys hip 
      with dec-eqₐ _≟-A_ tv x x
    ...| no abs = ⊥-elim (abs refl)
    ...| yes _  = hip

    lemma-cands-del
      : {tv : Atom}{tys tvs : Π}(x : ⟦ tv ⟧ₐ)(xs : ⟦ tvs ⟧ₚ)(ys : ⟦ tys ⟧ₚ)
      → {k : Al Trivialₐ tvs tys}
      → All (IsCand (Al-Diffable doP) xs ys) 
            (Al-mapM (uncurry (cands doP)) k)
      → All (IsCand (Al-Diffable doP) {a = tv ∷ tvs} (x , xs) ys) 
            (Adel x <$> Al-mapM (uncurry (cands doP)) k)
    lemma-cands-del {ty} {tys} x xs ys hip
      = All-<$>-commute (Adel x) (mapᵢ (λ {k} → Adel-correct {ty} {tys} x xs ys {k}) hip)

    AX-correct
      : {tv ty : Atom}{tys tvs : Π}(x : ⟦ tv ⟧ₐ)(xs : ⟦ tvs ⟧ₚ)(y : ⟦ ty ⟧ₐ)(ys : ⟦ tys ⟧ₚ)
      → {k : P doP tv ty}{ks : P (Al-Diffable doP) tvs tys}
      → IsCand doP x y k
      → IsCand (Al-Diffable doP) xs ys ks
      → IsCand (Al-Diffable doP) {tv ∷ tvs} {ty ∷ tys} (x , xs) (y , ys) (AX k ks)
    AX-correct {tv} x xs y ys hip0 hip1
      rewrite hip0 | hip1 = refl

    lemma-cands-AX
      : {tv ty : Atom}{tys tvs : Π}(x : ⟦ tv ⟧ₐ)(xs : ⟦ tvs ⟧ₚ)(y : ⟦ ty ⟧ₐ)(ys : ⟦ tys ⟧ₚ)
      → {k : Al Trivialₐ tvs tys}
      → All (IsCand (Al-Diffable doP) xs ys) 
            (Al-mapM (uncurry (cands doP)) k)
      → All (IsCand (Al-Diffable doP) {a = tv ∷ tvs} {ty ∷ tys} (x , xs) (y , ys)) 
            (Al-mapM (uncurry (cands doP)) (AX (x , y) k))
    lemma-cands-AX {ty} {tv} x xs y ys {k} hip 
      with okP {ty} {tv} x y
    ...| csOk
      with cands doP {ty} {tv} x y
    ...| cs = All-bind-commute {x = cs} 
                (λ x' → AX x' <$> Al-mapM (uncurry (cands doP)) k) 
                (mapᵢ (λ {j} h → All-<$>-commute 
                                   {x = Al-mapM (uncurry (cands doP)) k} 
                                   (AX j) 
                                   (mapᵢ (λ {l} → AX-correct x xs y ys {j} {l} h) 
                                         hip )) 
                      csOk)


    mutual
      lemma-cands-Ains-helper
        : {ty : Atom}{tys tvs : Π}(y : ⟦ ty ⟧ₐ)(xs : ⟦ tvs ⟧ₚ)(ys : ⟦ tys ⟧ₚ)
        → All (IsCand (Al-Diffable doP) {tvs} {ty ∷ tys} xs (y , ys))
              ((Ains y <$> align* xs ys) >>= Al-mapM (uncurry (cands doP)))
      lemma-cands-Ains-helper y xs ys
        = All-<$>->>=-commute {x = align* xs ys} 
              (Ains y) 
              (Al-mapM (uncurry (cands doP))) 
              (mapᵢ (λ {k} → lemma-cands-ins y xs ys {k}) 
                (All-bind-uncommute (Al-mapM (uncurry (cands doP))) 
                                    (lemma-cands-ok xs ys)))

      lemma-cands-Adel-helper
        : {tv : Atom}{tys tvs : Π}(x : ⟦ tv ⟧ₐ)(xs : ⟦ tvs ⟧ₚ)(ys : ⟦ tys ⟧ₚ)
        → All (IsCand (Al-Diffable doP) {tv ∷ tvs} {tys} (x , xs) ys)
              ((Adel x <$> align* xs ys) >>= Al-mapM (uncurry (cands doP)))
      lemma-cands-Adel-helper x xs ys
        = All-<$>->>=-commute {x = align* xs ys} 
            (Adel x) 
            (Al-mapM (uncurry (cands doP))) 
            (mapᵢ (λ {k} → lemma-cands-del x xs ys {k}) 
              (All-bind-uncommute (Al-mapM (uncurry (cands doP))) 
                                  (lemma-cands-ok xs ys)))

      lemma-cands-AX-helper
        : {tv ty : Atom}{tys tvs : Π}(x : ⟦ tv ⟧ₐ)(xs : ⟦ tvs ⟧ₚ)(y : ⟦ ty ⟧ₐ)(ys : ⟦ tys ⟧ₚ)
        → All (IsCand (Al-Diffable doP) {tv ∷ tvs} {ty ∷ tys} (x , xs) (y , ys))
              ((AX (x , y) <$> align* xs ys) >>= Al-mapM (uncurry (cands doP)))
      lemma-cands-AX-helper x xs y ys 
        = All-<$>->>=-commute {x = align* xs ys} 
            (AX (x , y)) 
            (Al-mapM (uncurry (cands doP))) 
            (mapᵢ (λ {k} →  lemma-cands-AX x xs y ys {k}) 
                  (All-bind-uncommute (Al-mapM (uncurry (cands doP))) 
                                      (lemma-cands-ok xs ys)))

      lemma-cands-ok 
        : {ty tv : Π}(x : ⟦ ty ⟧ₚ)(y : ⟦ tv ⟧ₚ)
        → All (IsCand (Al-Diffable doP) x y) (cands (Al-Diffable doP) x y)
      lemma-cands-ok {[]} {[]} unit unit 
        = refl ∷ []
      lemma-cands-ok {[]} {tv ∷ tvs} unit (y , ys) 
        = lemma-cands-Ains-helper y unit ys
      lemma-cands-ok {ty ∷ tys} {[]} (x , xs) unit
        = lemma-cands-Adel-helper x xs unit
      lemma-cands-ok {ty ∷ tys} {tv ∷ tvs} (x , xs) (y , ys) 
        rewrite ++->>=-commute 
                   (AX {a = ty} {tv} (x , y) <$> align* xs ys)
                   {(Adel x <$> align* xs (y , ys)) 
                      ++ (Ains y <$> align* (x , xs) ys)}
                   (Al-mapM (λ {k} {v} → uncurry (cands doP {k} {v})))
              | ++->>=-commute 
                   (Adel {a = ty} x <$> align* xs (y , ys))
                   {Ains {a = tv} y <$> align* (x , xs) ys}
                   (Al-mapM (λ {k} {v} → uncurry (cands doP {k} {v})))
              =    lemma-cands-AX-helper x xs y ys 
              ++ₐ (lemma-cands-Adel-helper x xs (y , ys)
              ++ₐ  lemma-cands-Ains-helper y (x , xs) ys)


private 
  module CandsNonNil 
           (doP : Diffable ⟦_⟧ₐ)
           (okP : CandsNonNil ⟦_⟧ₐ doP)
      where

    -- Al-mapM cands is, by (module) hypothesis, always non-nil.
    lemma-Al-mapM-nonnil
      : {ty tv : Π}(x : Al Trivialₐ ty tv)
      → 1 ≤ length (Al-mapM (λ {k} {v} → uncurry (cands doP {k} {v})) x)
    lemma-Al-mapM-nonnil A0 = s≤s z≤n
    lemma-Al-mapM-nonnil {tv = tv ∷ tvs} (Ains x d) 
      = ≤-trans (lemma-Al-mapM-nonnil d) 
                (length-<$>-≤ {f = Ains {a = tv} x} 
                  (Al-mapM (λ {k} {v} → uncurry (cands doP {k} {v})) d))
    lemma-Al-mapM-nonnil {ty ∷ tys} (Adel x d)
      = ≤-trans (lemma-Al-mapM-nonnil d) 
                (length-<$>-≤ {f = Adel {a = ty} x} 
                  (Al-mapM (λ {k} {v} → uncurry (cands doP {k} {v})) d))
    lemma-Al-mapM-nonnil {tv ∷ tvs} {ty ∷ tys} (AX (x , y) d)
      rewrite length-concat (map (λ x' → AX x' <$> Al-mapM (λ {k} {v} 
                                 → uncurry (cands doP {k} {v})) d) 
                            (cands doP {tv} {ty} x y)) 
         with okP {tv} {ty} x y
    ...| prf with cands doP {tv} {ty} x y
    ...| [] = prf
    ...| c ∷ cs with 1≤length-witness 
                       {l = Al-mapM (λ {k} {v} → uncurry (cands doP {k} {v})) d} 
                       (lemma-Al-mapM-nonnil d)
    ...| (k , ks) , kprf rewrite kprf = s≤s z≤n 

    -- Therefore, Al-mapM (uncurry cands) will only increase the length!
    lemma-cands-length-incr
      : {ty tv : Π}(l : List (Al Trivialₐ ty tv))
      → length l ≤ length (l >>= Al-mapM (λ {k} {v} → uncurry (cands doP {k} {v})))
    lemma-cands-length-incr [] = z≤n
    lemma-cands-length-incr (x ∷ l) 
      rewrite length-concat (map (Al-mapM (λ {k} {v} → uncurry (cands doP {k} {v}))) 
                                 (x ∷ l)) 
         with 1≤-witness (lemma-Al-mapM-nonnil x)
    ...| n , prf rewrite prf 
       = s≤s (≤-steps n 
                (subst (λ p → length l ≤ p) 
                       (length-concat 
                               (map (Al-mapM (λ {k} {v} 
                                           → uncurry (cands doP {k} {v}))) 
                                l))
                       (lemma-cands-length-incr l)))


    -- Now, align* is always nonnil!
    lemma-align*
      : {ty tv : Π}(x : ⟦ ty ⟧ₚ)(y : ⟦ tv ⟧ₚ)
      → 1 ≤ length (align* x y)
    lemma-align* {[]} {[]} unit unit
      = s≤s z≤n
    lemma-align* {[]} {tv ∷ tvs} unit (y , ys)
      = ≤-trans (lemma-align* unit ys) (length-<$>-≤ (align* unit ys))
    lemma-align* {ty ∷ tys} {[]} (x , xs) unit
      = ≤-trans (lemma-align* xs unit) (length-<$>-≤ (align* xs unit))
    lemma-align* {ty ∷ tys} {tv ∷ tvs} (x , xs) (y , ys)
      = ≤-trans (≤-trans (lemma-align* xs ys) (length-<$>-≤ (align* xs ys))) 
                (length-++-≤ (AX (x , y) <$> align* xs ys))

    -- This lets us prove that the candidates for Al-diffable
    -- are non-nil in a somewhat painless way.
    lemma-cands-length 
      : {ty tv : Π}(x : ⟦ ty ⟧ₚ)(y : ⟦ tv ⟧ₚ)
      → 1 ≤ length (cands (Al-Diffable doP) x y)
    lemma-cands-length {[]} {[]} unit unit 
      = s≤s z≤n
    lemma-cands-length {[]} {tv ∷ tvs} unit (y , ys) 
      = ≤-trans (≤-trans (lemma-align* unit ys) (length-<$>-≤ (align* unit ys))) 
                (lemma-cands-length-incr (Ains y <$> align* unit ys))
    lemma-cands-length {ty ∷ tys} {[]} (x , xs) unit 
      = ≤-trans (≤-trans (lemma-align* xs unit) (length-<$>-≤ (align* xs unit)))  
                (lemma-cands-length-incr (Adel x <$> align* xs unit))
    lemma-cands-length {ty ∷ tys} {tv ∷ tvs} (x , xs) (y , ys) 
      rewrite ++->>=-commute 
                   (AX {a = ty} {tv} (x , y) <$> align* xs ys)
                   {(Adel x <$> align* xs (y , ys)) 
                      ++ (Ains y <$> align* (x , xs) ys)}
                   (Al-mapM (λ {k} {v} → uncurry (cands doP {k} {v})))
              | ++->>=-commute 
                   (Adel {a = ty} x <$> align* xs (y , ys))
                   {Ains {a = tv} y <$> align* (x , xs) ys}
                   (Al-mapM (λ {k} {v} → uncurry (cands doP {k} {v})))
              = ≤-trans (≤-trans (≤-trans (lemma-align* xs ys) (length-<$>-≤ (align* xs ys)))
                        (lemma-cands-length-incr (AX (x , y) <$> align* xs ys)))
                (length-++-≤ ((AX (x , y) <$> align* xs ys) 
                      >>= Al-mapM (λ {k} {v} → uncurry (cands doP {k} {v}))))



Al-Correct : (doP : Diffable ⟦_⟧ₐ)(okP : CandsCorrect ⟦_⟧ₐ doP)
           → CandsCorrect ⟦_⟧ₚ (Al-Diffable doP)
Al-Correct doP okP = lemma-cands-ok
  where
    open CandsCorrect doP okP
      
      
Al-Inhab : (doP : Diffable ⟦_⟧ₐ)(okP : CandsNonNil ⟦_⟧ₐ doP)
         → CandsNonNil ⟦_⟧ₚ (Al-Diffable doP)
Al-Inhab doP okP = lemma-cands-length
  where
    open CandsNonNil doP okP
