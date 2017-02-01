{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector using (Vec ; VecI)
open import Prelude.Monad
open import Prelude.List.All
open import Prelude.PartialFuncs.Base

open import RegDiff.Generic.Parms

open import RegDiff.Diff.Abstract.Base

module RegDiff.Diff.Abstract.Instances.Spine
       {ks#    : ℕ}(ks : Vec Set ks#)(keqs  : VecI Eq ks)
       {parms# : ℕ}(A : Parms parms#)(_≟-A_ : ParmEq A)
    where

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
  open import RegDiff.Diff.Regular.Base ks keqs A _≟-A_
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
  private 
    module Hypothesis (doP : Diffable ⟦_⟧ₚ)
                      (IsDiff-P : IsDiff ⟦_⟧ₚ doP)
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
        rewrite fromInj-inject {ty} i dx
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
               (map (eval-cands-cons dxs dys) 
                    (uncurry (cands doP) ((dx , unit) , dy , unit))) 
            (S-app-prod-hip-aux dx dy dxs dys) 

        S-app-prod-hip-aux
          : {y : Atom}{ty : Π}(dx dy : ⟦ y ⟧ₐ)(dxs dys : ⟦ ty ⟧ₚ)
          → All (All (λ z → S-app-prod (apply doP) z (dx , dxs) ≡ just (dy , dys)))
                (map (eval-cands-cons dxs dys)  
                  (uncurry (cands doP {β y} {β y}) ((dx , unit) , dy , unit)))
        S-app-prod-hip-aux {y} dx dy dxs dys 
          rewrite fun-ext (eval-cands-simplify {y} dxs dys) 
                = All-map-commute 
                    (cands doP {β y} {β y} (dx , unit) (dy , unit)) 
                    (eval-cands-cons' dxs dys) 
                    (mapᵢ (λ {k} → All-map-commute (eval-cands dxs dys) (_∷_ k)) 
                    (mapᵢ (S-app-prod-core dx dy dxs dys) 
                          (IsDiff.candidates-ok IsDiff-P {β y} {β y} 
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
      -- The proof follows the structure of the spine function,
      -- first we compare x and y for equality:
      lemma-cands-ok {ty} x y with dec-eq _≟-A_ ty x y
      -- If they are, this is trivial!
      ...| yes p = (cong just p) ∷ []

      -- If they are not equal, we check their constructor:
      ...| no  _ with sop x | sop y
      lemma-cands-ok _ _ | no _
         | strip cx dx | strip cy dy 
         with cx ≟-Fin cy

      -- If they have the same constructor, we are in the Scns case.
      lemma-cands-ok _ _ | no _ | strip cx dx | strip _ dy
         | yes refl 
         = All-bind-return-split 
              (mapMᵢ (uncurry (cands doP)) (zipₚ dx dy)) 
              (Scns cx) 
              (mapᵢ (λ {x} p → S-app-Scns-elim x p) 
                    (S-app-prod-hip dx dy))

      -- If not, we are in the Schg case.
      lemma-cands-ok _ _ | no _ | strip cx dx | strip cy dy
         | no _ 
         = All-bind-return-split 
              (cands doP dx dy) 
              (Schg cx cy) 
              (mapᵢ (S-app-chg-correct cx cy dx dy)
                    (IsDiff.candidates-ok IsDiff-P dx dy))



      -- Last but not least, we assemble all of them
      -- in a record that proves that our Spine
      -- construction is a diffing structure.
      IsDiff-S-priv : IsDiff₀ ⟦_⟧ (S-Diffable doP)
      IsDiff-S-priv = record
        { candidates-ok₀ = lemma-cands-ok
        ; candidates-nonnil₀ = {!!}
        ; cost-eq = {!!}
        ; cost-order₀ = {!!}
        }

  -- Finally, we export a concise definition!
  IsDiff-S : (doP : Diffable ⟦_⟧ₚ)(IsDiff-P : IsDiff ⟦_⟧ₚ doP)
           → IsDiff₀ ⟦_⟧ (S-Diffable doP)
  IsDiff-S doP okP = IsDiff-S-priv
    where
      open Hypothesis doP okP
      
