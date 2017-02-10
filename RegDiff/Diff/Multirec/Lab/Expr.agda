open import Prelude
open import Prelude.Eq
open import Prelude.Vector
open import Prelude.RelCalc.Base
open import Prelude.List.All
open import Data.String hiding (_≟_)

module RegDiff.Diff.Multirec.Lab.Expr where

  open import RegDiff.Generic.Konstants
  open import RegDiff.Generic.Multirec konstants 
    hiding (Atom; ⟦_⟧ₐ; ⟦_⟧ₚ; ⟦_⟧)
    public
  open import RegDiff.Generic.Eq konstants keqs public

  import RegDiff.Diff.Multirec.Base konstants keqs 
    as DIFF
  import RegDiff.Diff.Multirec.Apply konstants keqs
    as APPLY

  -- We start by defining and expression language
  -- We shall have:
  --
  -- <expression> ::= <term> | <expression> "+" <term>
  -- <term>       ::= <factor> | <term> "*" <factor>
  -- <factor>     ::= Int | Name | "(" <expression> ")"

  n : ℕ
  n = 3

  exprᵢ termᵢ factorᵢ : Fin n
  exprᵢ = fz
  termᵢ = fs fz
  factorᵢ = fs (fs fz)

  expr-type term-type factor-type : Sum n
  expr-type = (I termᵢ ⊗ u1) ⊕ (I exprᵢ ⊗ I termᵢ ⊗ u1) ⊕ [] 
  
  term-type = (I factorᵢ ⊗ u1) ⊕ (I termᵢ ⊗ I factorᵢ ⊗ u1) ⊕ []
  
  factor-type = (K kℕ ⊗ u1) ⊕ (K kString ⊗ u1) ⊕ (I exprᵢ ⊗ u1) ⊕ []

  EXPR : Fam n
  EXPR = expr-type ∷ term-type ∷ factor-type ∷ []

  Expr Term Factor : Set
  Expr   = Fix EXPR exprᵢ
  Term   = Fix EXPR termᵢ
  Factor = Fix EXPR factorᵢ

  infixl 20 _+!_
  infixl 15 _*!_

  _+!_ : Expr → Term → Expr
  e +! t = ⟨ i2 (i1 (e , t , unit)) ⟩

  term : Term → Expr
  term t = ⟨ i1 (t , unit) ⟩

  _*!_ : Term → Factor → Term
  t *! f = ⟨ i2 (i1 (t , f , unit)) ⟩

  factor : Factor → Term
  factor f = ⟨ i1 (f , unit) ⟩

  num : ℕ → Factor
  num n = ⟨ i1 (n , unit) ⟩

  var : String → Factor
  var v = ⟨ i2 (i1 (v , unit)) ⟩

  parens : Expr → Factor
  parens e = ⟨ i2 (i2 (i1 (e , unit))) ⟩

  tf : Factor → Expr
  tf = term ∘ factor

  e8 e8' e15 e15' e19 e21 e31 e29 e29' : Expr

  e8 = tf (var "g") +! factor (var "c")
  
  e8' = tf (var "g") +! factor (num 4)

  e19 = e8 +! factor (parens e8')

  e15 = tf (var "g") +! (factor (num 3) *! var "v") +! factor (var "v")

  e15' = tf (var "g") +! (factor (num 6) *! var "v") +! factor (var "v")

  e29' = e8 +! (factor (var "l") *! parens e15)

  e21 = tf (var "g") +! (factor (num 3) *! parens (term (factor (var "g") *! (var "v") ))) +! factor (var "v")

  e31 = term (factor (parens (tf (var "g") +! factor (num 5))) *! var "k") 
     +! (factor (num 3) *! parens (term (factor (var "g") *! (var "v") ))) 
     +! factor (var "v")

  e29 = term (factor (num 3) *! var "v") +! factor (parens e15')  +! factor (var "k")
  

  open DIFF.Internal EXPR public
  open APPLY.Internal EXPR public
  open import RegDiff.Diff.Universe konstants keqs (Fix EXPR) _≟_
    using (⟦_⟧)

  d12 : Patchμ (T exprᵢ) (T exprᵢ)
  d12 = {!diffμ e19 e29'!}
