{-# OPTIONS --safe -v testMarkVert:3 -v tactic:3 #-} 
-- -v 3 
module Cubical.Tactics.PathSolver.PathTerm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ

open import Cubical.Data.Sigma.Base


open import Cubical.Reflection.Base renaming (v to 𝒗)
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)

import Agda.Builtin.Reflection as R

open import Cubical.Tactics.PathSolver.Reflection
-- open import Cubical.Tactics.Reflection 
open import Agda.Builtin.String
-- open import Agda.Builtin.Char
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.PathSolver.Error
open import Cubical.Tactics.PathSolver.Dimensions
open import Cubical.Tactics.PathSolver.QuoteCubical

import Cubical.Tactics.PathSolver.PathEval as PT


-- compPath'-filler, but composition is 'simplified' according to groupoid laws

-- p → q → Square q (p ∙ q) p refl


PathTerm = R.Term ⊎ R.Term

record SquareTerm : Type where
 constructor squareTerm
 field
  term : R.Term


pattern 𝒓efl x = inl x
pattern 𝒑λ x = inr x

asPathTerm : R.Term → PathTerm
asPathTerm tm = 
  if (hasVar zero tm) then (𝒑λ tm) else (𝒓efl tm)

-- compPath'-filler, but composition is 'simplified' according to groupoid laws

-- (p : x ≡ y) → (q : y ≡ z) → (Σ (p∙q ∈ x ≡ z) (Square q p∙q p refl))

-- assumes that terms are already pre rpocessed : addNDimsToCtx 1 ∘S R.normalise ∘S pathApp


bfs' : PT.CTerm → R.TC R.Term
bfs' xs =  do
    let q = (PT.foldPath' (tail (PT.fill-flatten' xs)))
    hd ← Mb.rec (R.typeError [ "imposible tfct≡" ]ₑ )
           pure (listToMaybe (PT.fill-flatten' xs))
    -- addNDimsToCtx 2 $  R.typeError [ hd ]ₑ
    PT.fillHeadTrm hd q


_↙_ : PathTerm → PathTerm → R.TC (PathTerm × SquareTerm)
𝒓efl x ↙ q = q ,_ <$>  (squareTerm <$> PT.bfs (⊎.rec (idfun _) (idfun _) q))
𝒑λ x ↙ 𝒓efl y = 
  (𝒑λ (PT.wrapPaths x) ,_) <$> (squareTerm <$> (PT.bfs (PT.wrapFills x)) ) 
𝒑λ p ↙ 𝒑λ q = do
  pq-sq ← (PT.absorb 0 (PT.wrapPaths p) q)
  
  pq ← (PT.cTermEnd pq-sq) >>= Mb.rec
     ( 𝒓efl <$> (addNDimsToCtx 1 $ R.normalise
          (replaceVarWithCon (λ { zero → just (quote i0) ; _ → nothing }) p))) (pure ∘S 𝒑λ)
  -- addNDimsToCtx 1 $ R.typeError [ pq-sq ]ₑ
  pq ,_ <$> (squareTerm <$> bfs' pq-sq)
   
-- _ ↙ _ = R.typeError [ "testes" ]ₑ

macro
 ↙-test : R.Term → R.Term → R.Term → R.TC Unit
 ↙-test p q h = do
   p' ← asPathTerm <$> (addNDimsToCtx 1 ∘S R.normalise ∘S pathApp) p
   q' ← asPathTerm ∘S PT.wrapPaths <$> (addNDimsToCtx 1 ∘S R.normalise ∘S pathApp) q
   pq ← (SquareTerm.term ∘S snd) <$> p' ↙ q'
   R.unify pq h




module ↙-tests {ℓ} (A : Type ℓ)
  (f₁ : A → A) (f₂ : A → A → A)
  (x y z w : A)
  (p : x ≡ y)
  (q : y ≡ z)
  (r : z ≡ w)
  (s : f₂ z y ≡ y) where

 t0 : Square (p ∙' q) q p refl
 t0 = ↙-test p q

 t1 : Square _ _ _ _
 t1 = ↙-test p (refl {x = y})

 t2 : Square _ _ _ _
 t2 = ↙-test (refl {x = x}) (p ∙ q)

 t3 : Square _ _ _ _
 t3 = ↙-test (refl {x = x}) (refl {x = x})

 t4 : Square _ _ _ _
 t4 = ↙-test p (sym p)

 t5 : Square _ _ _ _
 t5 = ↙-test (cong f₁ p) (cong f₁ q)

 t6 : Square _ _ _ _
 t6 = ↙-test (cong f₁ p) (cong f₁ (sym p))

 t7 : Square (cong₂ f₂ q p) (λ 𝒊 → f₂ (q 𝒊) y) (λ i → f₂ y (p i)) refl
 t7 = ↙-test (cong (f₂ y) p) (cong (flip f₂ y) q )
