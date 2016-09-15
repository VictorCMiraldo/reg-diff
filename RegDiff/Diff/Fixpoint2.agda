open import Prelude hiding (_⊔_)
open import Prelude.Vector

{-
  Here we try a different approach to diffing fixpoints.
  Linearizing and diffing the euler strings of our trees
  makes it very hard to reconstruct the inserted and
  deleted contexts. 

  Let f(x₀ , ⋯ , xₙ) denote a constructor f
  with children x₀ to xₙ.

  The usual edit distance function, that work on forests,
  is defined as:

  d(f(x₀ , ⋯ , xₙ) ∘ F , g(y₀ , ⋯ , yₖ) ∷ G)
    = min { del f   + d(x₀ ∷ ⋯ ∷ xₙ ∷ F , g(y̅) ∷ G)
          , ins g   + d(f(x̅) ∷ F , y₀ ∷ ⋯ ∷ yₖ ∷ G)
          , mod f g + d(x₀ ∷ ⋯ ∷ xₙ ∷ F , y₀ ∷ ⋯ ∷ yₖ ∷ G)
          }

  And the actual edit script (or patch) is obtained from
  the branches the min function chooses.

  This works just fine for untyped trees, or even for typed-trees
  by adding some indexes. 

  One could also say that if the transformation is correct,
  it is obvious that we can only diff two type-correct trees,
  hence the produced patches will also be type-safe.

  Nevertheless, a big problem arises when we want to look at patches
  as a list of locations and changes in those respective locations:

    How do we extract the one-hole contexts that were inserted
    and deleted from that untyped euler-string patch?

  This problem is harder than what meets the eye! Specially because
  on modifying a label f to g, we need to make sure they have the same
  arity. This arity information needs to be passed everywhere later on.

  Not to mention that the algorithm will choose to insert things in an
  arbitrary place, instead of grouping inserts together, for instance:

          Ta           Tb      

          a             a
         / \           / \
        .   .         b   .
                     / \
                    .   .
  
  Take the transformation of Ta into Tb, denoting del , ins and mod by + , - , %
  respectively, the following three patches have the very same cost (mod id will be 
  denoted =)

    =++== ; =+=+= ; =+==+

  This happens because since leaves (.) have no information, it is indifferent
  which ones we insert, which ones we copy. So, it is not always the case
  that looking into a (ins hdX d), we can extract other (ar hdX - 1) 
  to make a one-hole context with hdX directly from the first (ar hdX) elements
  produced by d.

  On this module we try a different approach. Let e(t₁ , t₂) be a distance function
  over trees (not forests!) (here, Σ denotes standard mathematical summation).

  e(f(x₀ , ⋯ , xₙ) , g(y₀ , ⋯ , yₖ))
    = min { del f   + π₁ (aₗ(x₀ ∷ ⋯ ∷ xₙ , g(y̅)))     , n > 0
          , ins g   + π₁ (aᵣ(f(x̅) , y₀ ∷ ⋯ ∷ yₖ))     , k > 0
          , mod f g + Σ e*(x₀ ∷ ⋯ ∷ xₙ , y₀ ∷ ⋯ ∷ yₖ) , n ≡ k
          }
   
  first we need to see that we will never be asking for the minimum of an empty set!
  if n ≡ k, the set is already not empty by the last clause.
  if n ≢ k, then they cannot be both 0, hence either the first or second
  clause will kick in. 

  aₗ and aᵣ are alignment functions, dual of each other.

  aₗ(x₀ ∷ ⋯ ∷ xₙ , t)
    = let xᵢ = max { x₀ ∷ ⋯ ∷ xₙ }
       in e(xᵢ , t) , (i , x̅ / { xᵢ })

  aᵣ(t , y₀ ∷ ⋯ ∷ yₖ)
    = let yᵢ = max { y₀ ∷ ⋯ ∷ yₖ }
       in e(t , yᵢ) , (i , y̅ / { yᵢ })

  and e* is just applying e pointwise to each element in both vectors.

    e*(x₀ ∷ ⋯ ∷ xₙ , y₀ ∷ ⋯ ∷ yₙ)
      = e(x₀ , y₀) ∷ ⋯ ∷ e(xₙ , yₙ)

  Note that the alignment functions produce a context where the insertion happens!
  For the time being, we always select the biggest subtree to keep diffing against,
  as we want to insert and delete as little as possible, and instead, try
  to modify as much as we can!

  This choice is based on the assumption that most of the times,
  information is inserted or delete in comparatively small parts of a file
  in a given time.

  TODO:
    (1)
      It could be interesting if, instead of simply choosing the biggest subtree
      in the aligment functions, choose the one that is closer to the tree we're
      aligning against. This will increase the complexity of the diff function
      exponentially, however.
-}

module RegDiff.Diff.Fixpoint2
       {n : ℕ}(v : Vec Set n)(eqs : VecI Eq v)
    where

  open import RegDiff.Diff.Regular v eqs

  Al : Set → ℕ → Set
  Al A zero = Unit
  Al A (suc n) = Vec A (suc n) × Fin (suc n)

  Al-size : {ty : U}{n : ℕ} → Al (μ ty) n → ℕ
  Al-size {n = zero}  al = 0
  Al-size {n = suc n} (al , f)
    = vsum (vmap μ-size (vdrop al f))

  mutual
    data Dμ (ty : U) : Set where
      ins : (x : ⟦ ty ⟧ Unit)
          → Al (μ ty) (ar ty x)
          → Dμ ty
          → Dμ ty
      del : (x : ⟦ ty ⟧ Unit)
          → Al (μ ty) (ar ty x)
          → Dμ ty
          → Dμ ty
      mod : (x y : ⟦ ty ⟧ Unit)
          → (hip : ar ty x ≡ ar ty y)
          → Vec (Dμ ty) (ar ty x)
          → Dμ ty


  {-# TERMINATING #-}
  costμ : {ty : U} → Dμ ty → ℕ
  costμ {ty} (ins x x₁ d) 
    = 1 + size ty x + Al-size x₁ + costμ d
  costμ {ty} (del x x₁ d) 
    = 1 + size ty x + Al-size x₁ + costμ d
  costμ {ty} (mod x y hip d) 
    = cost (diff ty x y) + size ty y + vsum (vmap costμ d)

  _⊔μ_ : {ty : U} → Dμ ty → Dμ ty → Dμ ty
  p ⊔μ q with costμ p ≤?-ℕ costμ q
  ...| yes _ = p
  ...| no  _ = q

  enum-fin : (k : ℕ) → Vec (Fin k) k
  enum-fin zero = []
  enum-fin (suc n) = fz ∷ (vmap fs (enum-fin n))

  biggest : {n : ℕ}{ty : U} → Vec (μ ty) (suc n) → Fin (suc n)
  biggest {n} {ty} (v ∷ vs)
    = max (μ-size v , fz) (vzip refl vs (vmap fs (enum-fin n)))
    where  
      max : {k : ℕ} → ℕ × Fin (suc n) 
          → Vec (μ ty × Fin (suc n)) k → Fin (suc n)
      max (_ , i) [] = i
      max curr ((x , i) ∷ xs)
        with μ-size x ≤?-ℕ (p1 curr)
      ...| no  _ = max (μ-size x , i) xs
      ...| yes _ = max curr xs

  ⊔μ* : {n : ℕ}{ty : U} → Vec (Dμ ty) (suc n) → Fin (suc n)
  ⊔μ* {n} {ty} (v ∷ vs) 
    = min (costμ v , fz) (vzip refl vs (vmap fs (enum-fin n)))
    where  
      min : {k : ℕ} → ℕ × Fin (suc n) 
          → Vec (Dμ ty × Fin (suc n)) k → Fin (suc n)
      min (_ , i) [] = i
      min curr ((x , i) ∷ xs)
        with costμ x ≤?-ℕ (p1 curr)
      ...| yes _ = min (costμ x , i) xs
      ...| no  _ = min curr xs

  ifd_then_else_ 
    : {A B : Set} → Dec A → (A → B) → (¬ A → B) → B
  ifd (yes p) then f else _ = f p
  ifd (no ¬p) then _ else g = g ¬p

  mutual
    {-# TERMINATING #-}
    diffμ : {ty : U} → μ ty → μ ty → Dμ ty
    diffμ {ty} x y
      with μ-chv x | μ-chv y
    ...| chX | chY
      with μ-hd x | μ-hd y
    ...| hdX | hdY
      = ifd (ar ty hdX ≟-ℕ ar ty hdY)
        then (λ p₁ → 
          ifd (ar ty hdX ≟-ℕ 0)
          then (λ p₂ → mod hdX hdY p₁ (diffμ* p₁ chX chY))
          else (λ q₂ → mod hdX hdY p₁ (diffμ* p₁ chX chY) 
                    ⊔μ let dal , dd = do-del chX q₂ y
                           ial , ii = do-ins x chY (q₂ ∘ trans p₁)
                        in ins hdY ial ii ⊔μ del hdX dal dd))
        else (λ q₁ → 
          ifd (ar ty hdX ≟-ℕ 0)
          then (λ p₁ → let ial , ii = do-ins x chY (q₁ ∘ trans p₁ ∘ sym)
                        in ins hdY ial ii)
          else (λ p₂ → let dal , dd = do-del chX p₂ y
                        in del hdX dal dd))
      where
        do-del : {k : ℕ} → Vec (μ ty) k → (¬ k ≡ 0) → μ ty
               → Al (μ ty) k × Dμ ty
        do-del [] hip y       = ⊥-elim (hip refl)
        do-del (v ∷ vs) hip y = alignl (v ∷ vs) y

        do-ins : {k : ℕ} → μ ty → Vec (μ ty) k → (¬ k ≡ 0)
               → Al (μ ty) k × Dμ ty
        do-ins y [] hip       = ⊥-elim (hip refl)
        do-ins y (v ∷ vs) hip = alignr y (v ∷ vs)

    diffμ* : {n k : ℕ}{ty : U}
           → (hip : n ≡ k)
           → Vec (μ ty) n
           → Vec (μ ty) k 
           → Vec (Dμ ty) n
    diffμ* refl []       []       = []
    diffμ* refl (x ∷ xs) (y ∷ ys) 
      = diffμ x y ∷ diffμ* refl xs ys

    alignl : {n : ℕ}{ty : U}
           → Vec (μ ty) (suc n) → μ ty → Al (μ ty) (suc n) × Dμ ty
    alignl v x 
      = let maxv = biggest v
         in (v , maxv) , diffμ (lookup maxv v) x

    alignr : {n : ℕ}{ty : U}
           → μ ty → Vec (μ ty) (suc n) →  Al (μ ty) (suc n) × Dμ ty
    alignr x v 
      = let maxv = biggest v
         in (v , maxv) , diffμ x (lookup maxv v)
