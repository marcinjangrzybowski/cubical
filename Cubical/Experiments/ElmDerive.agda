{-# OPTIONS --safe #-}

module Cubical.Experiments.ElmDerive where

open import Cubical.Foundations.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Int renaming (ℤ to Int)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥ renaming (elim to ⊥-elim ; rec to ⊥-rec)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe
open import Cubical.Data.Maybe as ℙ renaming (Maybe to ℙ ; nothing to ₋₋ ; just to ⌞_) 
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Cubical.Relation.Nullary
import Cubical.Functions.Logic as L
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Agda.Builtin.String

open import Cubical.Algebra.Lattice
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.CommMonoid.CommMonoidProd
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring

open import Cubical.HITs.PropositionalTruncation as T₁

open import Cubical.Experiments.Elm
open import Cubical.Experiments.ElmMore
open import Cubical.Experiments.ElmMoreMore

open import Cubical.Functions.Embedding

import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base


module _ (Ty : ℕ → Type)  where 

 instance
  HasPatTy : ∀ {k} → HasPat (Ty k)
  HasPatTy = hasPatAtom _
  
 data AA : Type where
  aa1 : Ty 0 → AA
  aa2 : Ty 0 → Ty 1 → AA
  aa3 : Ty 0 → Ty 1 → Ty 2 → AA

 AA' = Ty 0 ⊎ ((Ty 0 × Ty 1) ⊎ (Ty 0 × (Ty 1 × Ty 2)))

 AA→AA' : AA → AA'
 AA→AA' (aa1 x) = inl x
 AA→AA' (aa2 x x₁) = inr (inl (x , x₁))
 AA→AA' (aa3 x x₁ x₂) = inr (inr (x , x₁ , x₂))

 pattern aa3' x x₁ x₂ = just (inr (just (inr (just ((x , just (x₁ , x₂)))))))

 pattern aa3c x x₁ x₂ = (x , x₁ , x₂)


 pattern aa3* x =
   just (inr (just (inr (just ((nothing , just (nothing , nothing))))))) ⊢>
   x

-- syntax ∃[∶]-syntax {A = A} (λ x → P) = ∃[ x ∶ A ] P
-- syntax ∃[]-syntax (λ x → P) = ∃[ x ] P


 

 -- syntax aa3* (λ x → b) = aa3p x nn b  

 -- HasPatAA' : AA → ℕ
 -- HasPatAA' = λ {
 --    (aa1 x ) → {!!}
 --  ; (aa3 x x' x'') → {!!}
 --  ; _ → {!!}
 --  }
