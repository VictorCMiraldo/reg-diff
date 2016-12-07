  Here we try to tie the know for a mutually recursive family
  of datatypes.

\begin{code}
open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.Monad
open import Prelude.ListI
open import RegDiff.Generic.Parms

module RegDiff.Diff.Multirec.Base
       {ks# : ℕ}(ks : Vec Set ks#)(keqs : VecI Eq ks)
    where

  open Monad {{...}}
  open Applicative {{...}}

  open import RegDiff.Generic.Multirec ks
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
  open import RegDiff.Generic.Eq ks keqs
\end{code}
%<*UUSet-coprod>
\begin{code}
  _+ᵤ_ : {n : ℕ} → (σπ n → σπ n → Set) → (σπ n → σπ n → Set) → (σπ n → σπ n → Set)
  (P +ᵤ Q) ty tv = (P ty tv) ⊎ (Q ty tv)
\end{code}
%</UUSet-coprod>
\begin{code}
  WB-FAM : {n : ℕ}{fam : Fam n} → WBParms (Fix fam)
  WB-FAM = wb-parms Fam-size _≟_
\end{code}

  The idea is almost the same as for fixpoints,
  but now, we parametrize over a family of datatypes.

\begin{code}
  module Internal {fam# : ℕ}(fam : Fam fam#) where
\end{code}

\begin{code}
    open import RegDiff.Diff.Regular.Base ks keqs (Fix fam) WB-FAM
      public
\end{code}

  And now, we just change the types slightly, but
  the rationale behind this is the same as normal fixpoints.

  But now, instead oh matching only I's, we match (I k)'s.

%<*Fami-def>
\begin{code}
    Famᵢ : Set
    Famᵢ = Fin fam#

    T : Famᵢ → σπ fam#
    T k = lookup k fam
\end{code}
%</Fami-def>
%<*Patchmu-skel-def>
\begin{code}
    data Patchμ : U → U → Set where
      skel  : {ty : U} → Patch (UU→AA Patchμ) ty 
            → Patchμ ty ty
\end{code}
%</Patchmu-skel-def>
%<*Patchmu-ins-del-def>
\begin{code}
      ins   : {ty : U}{k : Famᵢ}(i : Constr ty)
            → Al (UU→AA Patchμ) (I k ∷ []) (typeOf ty i) 
            → Patchμ (T k) ty
      del   : {ty : U}{k : Famᵢ}(i : Constr ty)
            → Al (UU→AA Patchμ) (typeOf ty i) (I k ∷ [])  
            → Patchμ ty (T k)
\end{code}
%</Patchmu-ins-del-def>
%<*Patchmu-fix-set-def>
\begin{code}
      fix   : {k k'   : Famᵢ}  
            → Patchμ (T k) (T k')      
            → Patchμ (α (I k)) (α (I k'))
      set   : {ty tv : U} 
            → Δₛ ty tv
            → Patchμ ty tv
\end{code}
%</Patchmu-fix-set-def>

%<*Patchmu-cost>
\begin{code}
    {-# TERMINATING #-}
    Patchμ-cost : {ty tv : U} → Patchμ ty tv → ℕ
    Patchμ-cost (skel x)  
      = Patch-cost Patchμ-cost x
    Patchμ-cost (ins i x) 
      = Al-cost Patchμ-cost x
    Patchμ-cost (del i x) 
      = Al-cost Patchμ-cost x
    Patchμ-cost (fix p)   
      = Patchμ-cost p
    Patchμ-cost (set x)
      = cost-Δₛ x
\end{code}
%</Patchmu-cost>

\begin{code}
    mutual
      diffμ*-atoms : {ty tv : Atom} → ⟦ ty ⟧ₐ → ⟦ tv ⟧ₐ → List (UU→AA Patchμ ty tv)
      diffμ*-atoms {I ty} {I tv} x y = fix <$> diffμ* x y
      diffμ*-atoms {K ty} {K tv} x y = return (set (→α {K ty} x , →α {K tv} y))
      diffμ*-atoms {K ty} {I tv} x y = []
      diffμ*-atoms {I ty} {K tv} x y = []

      alignμ : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ
             → List (Al (UU→AA Patchμ) ty tv)
      alignμ x y = align* x y >>= Al-mapM (uncurry diffμ*-atoms)
      
      alignμ' : {ty tv : Π} → ⟦ ty ⟧ₚ → ⟦ tv ⟧ₚ
              → List (Al (UU→AA Patchμ) ty tv)
      alignμ' {[]} {_} _ _  = []
      alignμ' {_}  {[]} _ _ = []
      alignμ' {_ ∷ _} {_ ∷ _} x y = alignμ x y

      diffμ*-mod : {ty tv : U} → ⟦ ty ⟧ → ⟦ tv ⟧ → List (Patchμ ty tv)
      diffμ*-mod {ty} {tv} x y with σπ-eq ty tv
      ...| no _ = []
      diffμ*-mod x y
         | yes refl = skel <$> (diff1* x y >>= Patch-mapM (uncurry diffμ*-atoms))

      diffμ*-ins : {ty : U}{k : Famᵢ} → Fix fam k → ⟦ ty ⟧ → List (Patchμ (T k) ty)
      diffμ*-ins x y with sop y
      diffμ*-ins x _ | strip cy dy 
        = ins cy <$> alignμ' (x , unit) dy

      diffμ*-del : {ty : U}{k : Famᵢ} → ⟦ ty ⟧ → Fix fam k → List (Patchμ ty (T k))
      diffμ*-del x y with sop x
      diffμ*-del _ y | strip cx dx
        = del cx <$> alignμ' dx (y , unit) 

      {-# TERMINATING #-}
      diffμ* : {k k' : Famᵢ} → Fix fam k → Fix fam k' → List (Patchμ (T k) (T k'))
      diffμ* {k} {k'} ⟨ x ⟩ ⟨ y ⟩ 
        =  diffμ*-mod {T k} {T k'} x y
        ++ diffμ*-ins {lookup k' fam} {k} ⟨ x ⟩   y
        ++ diffμ*-del {lookup k fam} {k'}   x   ⟨ y ⟩
\end{code}

\begin{code}
    _<μ>_ : {ty tv : U} → Patchμ ty tv → List (Patchμ ty tv) → Patchμ ty tv
    s <μ> []       = s
    s <μ> (o ∷ os) with Patchμ-cost s ≤?-ℕ Patchμ-cost o
    ...| yes _ = s <μ> os
    ...| no  _ = o <μ> os

    Patchμ* : U → U → Set
    Patchμ* ty tv = List (Patchμ ty tv)

    Patchμ& : U → U → Set
    Patchμ& ty tv = List (ℕ × Patchμ ty tv)

    addCostsμ : {ty tv : U} → Patchμ* ty tv → Patchμ& ty tv
    addCostsμ = map (λ x → Patchμ-cost x , x)
\end{code}
%<*diffmu-det>
\begin{code}
    diffμ : {k k' : Famᵢ} → Fix fam k → Fix fam k' → Patchμ (T k) (T k')
    diffμ {k} x y with diffμ* x y
    ...| s ∷ ss = s <μ> ss
    ...| []     = set (unmu x , unmu y)
\end{code}
%</diffmu-det>


%<*Patchmu-aux-def>
begin{code}
    data Cμ (P : AASet) : U → U → Set where
      Cins  : {ty : U}{k : Famᵢ}(i : Constr ty)
            → Al P (I k ∷ []) (typeOf ty i) → Cμ P (T k) ty

      Cdel  : {ty : U}{k : Famᵢ}(i : Constr ty)
            → Al P (typeOf ty i) (I k ∷ []) → Cμ P ty (T k)

      Cmod  : {ty tv : U}(i : Constr ty)(j : Constr tv)
            → Al P (typeOf ty i) (typeOf tv j) → Cμ P ty tv

      Ccpy  : {ty : U}(i : Constr ty)
            → ListI (λ k → P k k) (typeOf ty i) → Cμ P ty ty
\end{code}
%</Patchmu-aux-def>
%<*Patchmu-def>
begin{code}
    data Patchμ : U → U → Set where
      
      chng : {ty tv  : U}     → Cμ (UU→AA Patchμ) ty tv  → Patchμ ty tv
      fix  : {k k'   : Famᵢ}  → Patchμ (T k) (T k')      → Patchμ (α (I k)) (α (I k'))
      set  : {k  : Fin ks# }  → (x y : lookup k ks)      → Patchμ (α (K k)) (α (K k))
      cp   : {ty : U} → Patchμ ty ty
\end{code}
%</Patchmu-def>

  The rest of the code is exactly the same as for single fixpoints.

%<*diffmu-costs>
begin{code}
    mutual
      {-# TERMINATING #-}
      Patchμ-cost : {ty tv : U} → Patchμ ty tv → ℕ
      Patchμ-cost (chng x)  = Cμ-cost Patchμ-cost x
      Patchμ-cost (fix s)   = Patchμ-cost s
      Patchμ-cost cp        = 0
      Patchμ-cost (set {k = k} x y) 
        with Eq.cmp (lookupᵢ k keqs) x y 
      ...| yes _ = 0
      ...| no  _ = 2

      Cμ-cost : {ty tv : U}{P : AASet} 
              → (costP : ∀{k v} → P k v → ℕ)
              → Cμ P ty tv → ℕ
      Cμ-cost c (Cins i x)
        = Al-cost c x
      Cμ-cost c (Cdel i x)
        = Al-cost c x
      Cμ-cost c (Cmod i j y) 
        = Al-cost c y
      Cμ-cost c (Ccpy i xs)
        = foldrᵢ (λ h r → c h + r) 0 xs
\end{code}
%</diffmu-costs>

%<*diffmu-refinements>
begin{code}
    mutual
      refine-Al : {k v : Atom} → Δₐ k v → List (Patchμ (α k) (α v))
      refine-Al {I k} {I k'} (x , y) = fix <$> diffμ* x y
      refine-Al {K k} {K k'} (x , y) 
        with k ≟-Fin k' 
      ...| no  _ = []
      refine-Al {K k} {K _} (x , y) 
         | yes refl = return (set x y)
      refine-Al {_}   {_}    _       = []
\end{code}
%</diffmu-refinements>
%<*diffmu-non-det>
begin{code}
      alignμ : {ty tv : Π} → ⟦ ty ⟧ₚ (Fix fam) → ⟦ tv ⟧ₚ (Fix fam) 
             → List (Al (UU→AA Patchμ) ty tv)
      alignμ x y = align* x y >>= Al-mapM refine-Al
      
      alignμ' : {ty tv : Π} → ⟦ ty ⟧ₚ (Fix fam) → ⟦ tv ⟧ₚ (Fix fam) 
              → List (Al (UU→AA Patchμ) ty tv)
      alignμ' {[]} {_} _ _  = []
      alignμ' {_}  {[]} _ _ = []
      alignμ' {_ ∷ _} {_ ∷ _} x y = alignμ x y

      changeμ : {ty tv : U} 
              → ⟦ ty ⟧ (Fix fam) → ⟦ tv ⟧ (Fix fam) 
              → List (C (Al (UU→AA Patchμ)) ty tv)
      changeμ x y = C-mapM (uncurry alignμ) (change x y) 

      diffμ*-mod' : {ty tv : U} → ⟦ ty ⟧ (Fix fam) → ⟦ tv ⟧ (Fix fam) → List (Patchμ ty tv)
      diffμ*-mod' x y with sop x | sop y
      diffμ*-mod' _ _ | strip cx dx | strip cy dy 
        = (chng ∘ Cmod cx cy) <$> alignμ dx dy

      zipμ : {ty : Π}
       → ⟦ ty ⟧ₚ (Fix fam)  → ⟦ ty ⟧ₚ (Fix fam) → List (ListI (λ k → UU→AA Patchμ k k) ty)
      zipμ {[]} x y = return []
      zipμ {ty ∷ tys} (x , xs) (y , ys) 
        = diffμ*-aux x y >>= λ xy → zipμ xs ys >>= return ∘ (xy ∷_) 

      diffμ*-mod-cpy : {ty : U} → ⟦ ty ⟧ (Fix fam) → ⟦ ty ⟧ (Fix fam) → List (Patchμ ty ty)
      diffμ*-mod-cpy x y with sop x | sop y
      diffμ*-mod-cpy _ _ | strip cx dx | strip cy dy
        with cx ≟-Fin cy
      ...| no _ = (chng ∘ Cmod cx cy) <$> alignμ dx dy
      diffμ*-mod-cpy _ _ | strip _ dx | strip cy dy
         | yes refl = (chng ∘ Ccpy cy) <$>  zipμ dx dy
      

      diffμ*-mod : {ty tv : U} → ⟦ ty ⟧ (Fix fam) → ⟦ tv ⟧ (Fix fam) → List (Patchμ ty tv)
      diffμ*-mod {ty} {tv}  x y with U-eq ty tv 
      diffμ*-mod {ty} {tv}  x y | no  _    = diffμ*-mod' x y
      diffμ*-mod {ty} {.ty} x y | yes refl with dec-eq _≟-A_ ty x y
      ...| yes _ = return cp
      ...| no  _ = diffμ*-mod-cpy x y

      diffμ*-ins : {ty : U}{k : Famᵢ} → Fix fam k → ⟦ ty ⟧ (Fix fam) → List (Patchμ (T k) ty)
      diffμ*-ins x y with sop y
      diffμ*-ins x  _  | strip cy dy
        = (chng ∘ Cins cy) <$> alignμ' (x , unit) dy

      
      diffμ*-del : {ty : U}{k : Famᵢ} → ⟦ ty ⟧ (Fix fam) → Fix fam k → List (Patchμ ty (T k))
      diffμ*-del {k} {k'} x y with sop x
      diffμ*-del {k} {k'} _ y | strip cx dx
        = (chng ∘ Cdel cx) <$> alignμ' dx (y , unit)

      diffμ*-aux : {ty : Atom} → (x y : ⟦ ty ⟧ₐ (Fix fam)) → List (Patchμ (α ty) (α  ty))
      diffμ*-aux {I k} x y = fix <$> diffμ* x y
      diffμ*-aux {K k} x y = return (set x y)
        
  
      {-# TERMINATING #-}
      diffμ* : {k k' : Famᵢ} → Fix fam k → Fix fam k' → List (Patchμ (T k) (T k'))
      diffμ* {k} {k'} ⟨ x ⟩ ⟨ y ⟩ 
        =  diffμ*-mod {T k} {T k'} x y
        ++ diffμ*-ins {lookup k' fam} {k} ⟨ x ⟩   y
        ++ diffμ*-del {lookup k fam} {k'}   x   ⟨ y ⟩
{-
        ++ ((chng ∘ Cins {k = k} {k'}) <$> changeμ (i1 (⟨ x ⟩ , unit)) y)
        ++ ((chng ∘ Cdel {k = k} {k'}) <$> changeμ x (i1 (⟨ y ⟩ , unit)))
-}
\end{code}
%</diffmu-non-det>


begin{code}
    _<μ>_ : {ty tv : U} → Patchμ ty tv → List (Patchμ ty tv) → Patchμ ty tv
    s <μ> []       = s
    s <μ> (o ∷ os) with Patchμ-cost s ≤?-ℕ Patchμ-cost o
    ...| yes _ = s <μ> os
    ...| no  _ = o <μ> os

    Patchμ* : U → U → Set
    Patchμ* ty tv = List (Patchμ ty tv)

    Patchμ& : U → U → Set
    Patchμ& ty tv = List (ℕ × Patchμ ty tv)

    addCostsμ : {ty tv : U} → Patchμ* ty tv → Patchμ& ty tv
    addCostsμ = map (λ x → Patchμ-cost x , x)
\end{code}
%<*diffmu-det>
begin{code}
    diffμ : {k : Famᵢ} → Fix fam k → Fix fam k → Patchμ (T k) (T k)
    diffμ {k} x y with diffμ* x y
    ...| s ∷ ss = s <μ> ss
    ...| []     = impossible {k}
      where postulate impossible : {k : Famᵢ} → Patchμ (T k) (T k)
\end{code}
%</diffmu-det>
