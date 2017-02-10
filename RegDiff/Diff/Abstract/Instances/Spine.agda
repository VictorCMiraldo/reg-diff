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

module RegDiff.Diff.Abstract.Instances.Spine
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

open import RegDiff.Diff.Universe ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Base.Spine ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Apply ks keqs A _≟-A_
open import RegDiff.Diff.Regular.Lemmas ks keqs A _≟-A_

open Monad {{...}}

-- Given a diff for Products, we can assemble
-- a diff for Sums using the spine construction
-- we have:
S-Diffable : Diffable ⟦_⟧ₚ → Diffable₀ ⟦_⟧
S-Diffable doP = record 
  { P₀     = S (P doP) 
  ; cands₀ = λ x y → S-mapM (uncurry (cands doP)) (spine x y)
  ; apply₀ = S-app (apply doP) 
  ; cost₀ = S-cost (cost doP) 
  }

-- Now, we prove that if the diff for Products
-- is a correct diff, then S-Diffable also is!
--
-- warning: not for the faint of heart!
--
-- We shall do this inside a parametrized module
-- to save some typing.
private 
  module CandsCorrect 
           (doP : Diffable ⟦_⟧ₚ)
           (okP : CandsCorrect ⟦_⟧ₚ doP)
      where

    -- Proving that our candidates function is correct is hard.
    -- specially in the Scns case.
    -- 
    -- A proof on paper should be fairly straight forward,
    -- as the only actual insight one need is:
    --   if (spine x y) = Scns i p, then x ≡ (inject i dx)
    --                               and y ≡ (inject i dy)
    --
    --   Hence, it is sufficient to prove that
    --     p♭ dx ≡ just dy
    --
    --   given that:
    --     p♭ dx ≡ just dy ⇒ (Scns i p)♭ (inject i dx) ≡ just (inject i dy)
    --
    -- This eliminates (Scns i) from the game and
    -- puts the focus on S-app-prod function.
    S-app-Scns-elim
      : {ty : U}{i : Constr ty}{dx dy : ⟦ typeOf ty i ⟧ₚ}
      → (p : All (contr (P doP) ∘ β) (typeOf ty i))
      → S-app-prod (apply doP) p dx ≡ just dy
      → S-app (apply doP) (Scns i p) (inject {ty = ty} i dx) 
      ≡ just (inject i dy)
    S-app-Scns-elim {ty} {i} {dx} {dy} p hip 
      rewrite fromInj-inject {ty = ty} i dx
            | hip
            = refl

    -- It is important to have the inductive step ready
    -- for the S-app-prod, as this will show up in quite
    -- a contrived context.
    S-app-prod-correct
      : {y : Atom}{ty : Π}(dx dy : ⟦ y ⟧ₐ)(dxs dys : ⟦ ty ⟧ₚ)
      → {k : P doP (β y) (β y)}{ks : All (contr (P doP) ∘ β) ty}
      → IsCand doP (dx , unit) (dy , unit) k
      → S-app-prod (apply doP) ks dxs ≡ just dys
      → S-app-prod (apply doP) (k ∷ ks) (dx , dxs) ≡ just (dy , dys)
    S-app-prod-correct dx dy dxs dys hip0 hip1
      rewrite hip0 | hip1 = refl

    -- Now, we have a bunch of higher-order monadic code to
    -- handle, as the S-mapM for the (Scns i) case is specially
    -- nasty.
    --
    -- Recall, S-mapM f (Scns i p) = mapMᵢ f p >>= return ∘ (Scns i)
    -- But when we produce (Scns i p), p has the form (zipₚ dx dy). 
    --
    -- We define a few synonyms.
    eval-cands : {ty : Π}(dx dy : ⟦ ty ⟧ₚ)
               → List (All (contr (P doP) ∘ β) ty)
    eval-cands dx dy = mapMᵢ (uncurry (cands doP)) (zipₚ dx dy)

    -- A special synonym for when ty = x ∷ ty.
    eval-cands-cons : {x : Atom}{ty : Π}(dx dy : ⟦ ty ⟧ₚ)(xy : P doP (β x) (β x))
                    → List (All (contr (P doP) ∘ β) (x ∷ ty))
    eval-cands-cons dx dy p = eval-cands dx dy >>= return ∘ (_∷_ p)

    -- A simpler version of the above.
    eval-cands-cons' : {x : Atom}{ty : Π}(dx dy : ⟦ ty ⟧ₚ)(xy : P doP (β x) (β x))
                     → List (All (contr (P doP) ∘ β) (x ∷ ty))
    eval-cands-cons' dx dy p = map (_∷_ p) (eval-cands dx dy)

    -- A proof they are the same!
    eval-cands-simplify
      : {x : Atom}{ty : Π}(dx dy : ⟦ ty ⟧ₚ)(xy : P doP (β x) (β x))
      → eval-cands-cons dx dy xy ≡ eval-cands-cons' dx dy xy
    eval-cands-simplify dx dy xy 
      = MonadProperties.>>=-return-f (eval-cands dx dy) (_∷_ xy)

    -- Now, we can "finally" prove that our S-app-prod
    -- is correct with respect to the zipped candidates,
    --
    -- This part is specially nasty as we have A LOT of
    -- nested "All"s types that need to be shuffled around.
    mutual
      S-app-prod-hip
        : {ty : Π}(dx dy : ⟦ ty ⟧ₚ)
        → All (λ z → S-app-prod (apply doP) z dx ≡ just dy)
              (eval-cands dx dy)
      S-app-prod-hip {[]} unit unit = refl ∷ []
      S-app-prod-hip {x ∷ ty} (dx , dxs) (dy , dys)
        = All-concat-commute 
          (S-app-prod-hip-aux dx dy dxs dys) 

      S-app-prod-hip-aux
        : {y : Atom}{ty : Π}(dx dy : ⟦ y ⟧ₐ)(dxs dys : ⟦ ty ⟧ₚ)
        → All (All (λ z → S-app-prod (apply doP) z (dx , dxs) ≡ just (dy , dys)))
              (map (eval-cands-cons dxs dys)  
                (uncurry (cands doP {β y} {β y}) ((dx , unit) , dy , unit)))
      S-app-prod-hip-aux {y} dx dy dxs dys 
        rewrite fun-ext (eval-cands-simplify {y} dxs dys) 
              = All-map-commute 
                  (eval-cands-cons' dxs dys) 
                  (mapᵢ (λ {k} → All-map-commute (_∷_ k)) 
                  (mapᵢ (S-app-prod-core dx dy dxs dys) 
                        (okP {β y} {β y} 
                                              (dx , unit) (dy , unit))))

      S-app-prod-core
        : {y : Atom}{ty : Π}(dx dy : ⟦ y ⟧ₐ)(dxs dys : ⟦ ty ⟧ₚ)
        → {k : P doP (β y) (β y)}
        → IsCand doP (dx , unit) (dy , unit) k
        → All (λ z → S-app-prod (apply doP) (k ∷ z) (dx , dxs) ≡ just (dy , dys))
              (eval-cands dxs dys)
      S-app-prod-core dx dy dxs dys {k} hip
        = mapᵢ (S-app-prod-correct dx dy dxs dys hip) 
               (S-app-prod-hip dxs dys)


    -- The Schg case is pretty simple, as there is no shuffling around.
    S-app-chg-correct
      : {ty : U}(cx cy : Constr ty)(dx : ⟦ typeOf ty cx ⟧ₚ)(dy : ⟦ typeOf ty cy ⟧ₚ)
      → {k : P doP (typeOf ty cx) (typeOf ty cy)}
      → IsCand doP dx dy k
      → S-app (apply doP) (Schg cx cy k) (inject {ty = ty} cx dx) 
      ≡ just (inject cy dy)
    S-app-chg-correct {ty} cx cy dx dy hip 
      rewrite fromInj-inject {ty} cx dx
            | hip 
            = refl

    -- We are now ready to assemble the monster!
    lemma-cands-ok 
      : {ty : U}(x y : ⟦ ty ⟧)
      → All (IsCand₀ (S-Diffable doP) x y) (cands₀ (S-Diffable doP) x y)
    -- The proof follows the structure of the spine function.
    -- Using the spine-view makes like oh-so-much easier.
    lemma-cands-ok x y with spine x y | spine-view x y 
    lemma-cands-ok _ _ | _ | spineP-eq x 
      = cong just refl ∷ []
    lemma-cands-ok _ _ | _ | spineP-cns i dx dy 
      = All-<$>-commute 
            (Scns i) 
            (mapᵢ (λ {x} p → S-app-Scns-elim x p) 
                  (S-app-prod-hip dx dy))
    lemma-cands-ok _ _ | _ | spineP-chg i j dx dy i≢j 
      = All-<$>-commute 
            (Schg i j) 
            (mapᵢ (S-app-chg-correct i j dx dy)
                  (okP dx dy))

-- Now, we need to prove the candidates list
-- is never empty.
private 
  module CandsNonNil
           (doP : Diffable ⟦_⟧ₚ)
           (okP : CandsNonNil ⟦_⟧ₚ doP)
      where

    eval-cands : {ty : Π}(dx dy : ⟦ ty ⟧ₚ)
               → List (All (contr (P doP) ∘ β) ty)
    eval-cands dx dy = mapMᵢ (uncurry (cands doP)) (zipₚ dx dy)

    -- The Scns case is still the hardest one, but this
    -- time it goes much easier.
    lemma-eval-cands-length
      : {ty : Π}(dx dy : ⟦ ty ⟧ₚ)
      → 1 ≤ length (eval-cands dx dy)
    lemma-eval-cands-length {[]} unit unit 
      = s≤s z≤n
    lemma-eval-cands-length {x ∷ ty} (dx , dxs) (dy , dys)
      with okP {β x} {β x} (dx , unit) (dy , unit)
    ...| aux
      with cands doP {β x} {β x} (dx , unit) (dy , unit)
    ...| []     = aux
    ...| c ∷ cs 
      with lemma-eval-cands-length dxs dys
    ...| aux' 
      with eval-cands dxs dys
    ...| []      = ⊥-elim (1+n≰n aux')
    ...| r ∷ res = s≤s z≤n

    lemma-cands-length 
      : {ty : U}(x y : ⟦ ty ⟧)
      → 1 ≤ length (cands₀ (S-Diffable doP) x y)
    lemma-cands-length x y with spine x y | spine-view x y
    lemma-cands-length _ _ | _ | spineP-eq x 
      = s≤s z≤n
    lemma-cands-length _ _ | _ | spineP-cns i dx dy 
      = ≤-trans (lemma-eval-cands-length dx dy) 
                 (length-<$>-≤ (eval-cands dx dy))
    lemma-cands-length _ _ | _ | spineP-chg i j dx dy i≢j 
      = ≤-trans (okP dx dy)
                  (length-<$>-≤ (cands doP dx dy)) 


-- Finally, we export some concise definitions!
S-Correct : (doP : Diffable ⟦_⟧ₚ)(okP : CandsCorrect ⟦_⟧ₚ doP)
          → CandsCorrect₀ ⟦_⟧ (S-Diffable doP)
S-Correct doP okP = lemma-cands-ok
  where
    open CandsCorrect doP okP
      

S-Inhab : (doP : Diffable ⟦_⟧ₚ)(okP : CandsNonNil ⟦_⟧ₚ doP)
        → CandsNonNil₀ ⟦_⟧ (S-Diffable doP)
S-Inhab doP okP = lemma-cands-length
  where
    open CandsNonNil doP okP
