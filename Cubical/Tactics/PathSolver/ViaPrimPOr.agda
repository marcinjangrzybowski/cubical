{-# OPTIONS --safe #-}
module Cubical.Tactics.PathSolver.ViaPrimPOr where

open import Cubical.Core.Primitives public
import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base renaming (v to 𝒗)
open import Cubical.Data.List

infixr 30 _∙_


private
  variable
    ℓ : Level
    A : Type ℓ
    
    x y z w : A

_∙∙_∙∙_ : x ≡ y → y ≡ z → z ≡ w → x ≡ w
(p ∙∙ q ∙∙ r) i =
  hcomp (λ k → primPOr (~ i) i (λ _ → p (~ k)) λ _ → r k) (q i)

doubleCompPath-filler : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
                      → PathP (λ j → p (~ j) ≡ r j) q (p ∙∙ q ∙∙ r)
doubleCompPath-filler p q r j i =
  hcomp (λ k → primPOr (~ j) (~ i ∨ i) (λ _ → q i) (primPOr (~ i) i
           (λ _ → p (~ k ∨ ~ j)) λ _ → r (k ∧ j)))
     (q i)


_∙_ : x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q = (λ _ → x) ∙∙ p ∙∙ q

compPath-filler : (p : x ≡ y) (q : y ≡ z) → PathP (λ j → x ≡ q j) p (p ∙ q)
compPath-filler {x = x} p q = doubleCompPath-filler (λ _ → x) p q


R∙ : R.Term → R.Term → R.Term
R∙ x y = R.def (quote _∙_) (x v∷ y v∷ [] )

-- R∙' : R.Term → R.Term → R.Term
-- R∙' x y = R.def (quote _∙'_) (x v∷ y v∷ [] )


-- R∙∙ : R.Term → R.Term → R.Term → R.Term
-- R∙∙ x y z = R.def (quote _∙∙_∙∙_) (x v∷ y v∷ z v∷ [] )

