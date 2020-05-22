{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.BaseVecCut where


open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.List

open import Cubical.HITs.Interval
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.IntervalPrim

open import Cubical.HITs.NCube.BaseVec



Nmax : ℕ 
Nmax = 5

C→-dim-subst : ∀ (n₁ n₂ : ℕ) → n₁ ≡ n₂ → C→I n₁ → C→I n₂ 
C→-dim-subst zero zero p x₁ = x₁
C→-dim-subst zero (suc n₂) p x₁ = ⊥-recω (znots p)
C→-dim-subst (suc n₁) zero p x₁ =  ⊥-recω (snotz p)
C→-dim-subst (suc n₁) (suc n₂) p x₁ i = C→-dim-subst n₁ n₂ (cong predℕ p) (x₁ i) 

eval-dim : List (Bool × Bool) → ℕ
eval-dim [] = 0
eval-dim ((false , false) ∷ x₁) =  eval-dim x₁ 
eval-dim ((false , true) ∷ x₁) = suc (eval-dim x₁)
eval-dim ((true , false) ∷ x₁) = suc (eval-dim x₁)
eval-dim ((true , true) ∷ x₁) = suc (eval-dim x₁)

faceControlExpr' : ∀ n → (l : List (Bool × Bool)) → C→I ((n * 3) + (eval-dim l))
faceControlExpr' zero [] = i0
faceControlExpr' (suc n) [] i i-0 i-1 =
    [ (i ∧ i-1) ∨ ((~ i) ∧ i-0) ]Iexpr ∨ⁿ (faceControlExpr' n [])
faceControlExpr' n ((false , false) ∷ l) = (faceControlExpr' n l)
    
faceControlExpr' n ((false , true) ∷ l) = 
    C→-dim-subst _ _ (sym (+-suc (n * 3) (eval-dim l)))
      (λ i → [ i ]Iexpr ∨ⁿ (faceControlExpr' n l))

    
faceControlExpr' n ((true , false) ∷ l) =
      C→-dim-subst _ _ (sym (+-suc (n * 3) (eval-dim l)))
      (λ i → [ ~ i ]Iexpr ∨ⁿ (faceControlExpr' n l))

faceControlExpr' n ((true , true) ∷ l) = 
      C→-dim-subst _ _ (sym (+-suc (n * 3) (eval-dim l)))
      (λ i → [ i ∨ ~ i ]Iexpr ∨ⁿ (faceControlExpr' n l))

faceControlExpr : ∀ n → _
faceControlExpr = λ n → faceControlExpr' n []
  
ctrl-ev-step : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n 
           → (i-0 : Bool) → (i-1 : Bool) → (l : List (Bool × Bool)) 
           → (Partialⁿ (A) _ (faceControlExpr' (suc n) l))
           → (Partialⁿ (A) _ (faceControlExpr' n ((i-0 , i-1) ∷ l))) 
ctrl-ev-step zero false false [] x ()
ctrl-ev-step zero false false (lh ∷ ls) x = {!x i0 i0 i0!}
ctrl-ev-step (suc n) false false l x = {!!}
ctrl-ev-step n false true l x = {!!}
ctrl-ev-step n true false l x = {!!}

ctrl-ev-step zero true true [] x i = x i i1 i1 
ctrl-ev-step zero true true (x₁ ∷ l) x i = {! x i i1 i1!}
ctrl-ev-step (suc n) true true l x = {!!}

-- ctrl-all : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n
--            → (Partialⁿ (A) (n * 3) (faceControlExpr' n []))
--            → (Partialⁿ (A) n (boundaryExpr n)) 
-- ctrl-all = {!!}

-- Partialⁿ-NBoundary-Max-ctrl : Partialⁿ (NBoundary Nmax) (Nmax * 3) (faceControlExpr Nmax)
-- Partialⁿ-NBoundary-Max-ctrl i₀ i₀0 i₀1 i₁ i₁0 i₁1 i₂ i₂0 i₂1 i₃ i₃0 i₃1 i₄ i₄0 i₄1 = 
--   let
--       cu = (nCubeω Nmax i₀ i₁ i₂ i₃ i₄ 1=1)
--       fc : (b : Bool) (k : ℕ) → (NBoundary Nmax)
--       fc = λ b k →  faceInj k b ( removeAt k cu )   

--       fc0 = fc false
--       fc1 = fc true
--   in

--   λ {
--       (i₀ = i0)(i₀0 = i1) →  fc0 0 ; (i₀ = i1)(i₀1 = i1) →  fc1 0
--     ; (i₁ = i0)(i₁0 = i1) →  fc0 1 ; (i₁ = i1)(i₁1 = i1) →  fc1 1
--     ; (i₂ = i0)(i₂0 = i1) →  fc0 2 ; (i₂ = i1)(i₂1 = i1) →  fc1 2
--     ; (i₃ = i0)(i₃0 = i1) →  fc0 3 ; (i₃ = i1)(i₃1 = i1) →  fc1 3
--     ; (i₄ = i0)(i₄0 = i1) →  fc0 4 ; (i₄ = i1)(i₄1 = i1) →  fc1 4
--    }


-- Partialⁿ-NBoundary-Max : Partialⁿ (NBoundary Nmax) Nmax (boundaryExpr Nmax)
-- Partialⁿ-NBoundary-Max = ctrl-all Nmax Partialⁿ-NBoundary-Max-ctrl 

-- -- Partialⁿ-NBoundary-Max : Partialⁿ (NBoundary Nmax) Nmax (boundaryExpr Nmax)
-- -- Partialⁿ-NBoundary-Max = {!!}





-- -- NBoundary→ω : (n : ℕ) → (NBoundary n) → I → NCubeBoundaryω (suc n)
-- -- NBoundary→ω = {!!}
 


-- -- Partialⁿ-NBoundary↓ : ∀ n → Partialⁿ (NBoundary (suc n)) (suc n) (boundaryExpr (suc n))
-- --                           → Partialⁿ (NBoundary n) n (boundaryExpr n)
-- -- Partialⁿ-NBoundary↓ zero x ()
-- -- Partialⁿ-NBoundary↓ (suc n) x i = {!x i1 i!}

-- -- Partialⁿ-NBoundary< : ∀ n → (Σ[ m ∈ ℕ ] n ≡ Nmax + m) →
-- --                        Partialⁿ (NBoundary n) n (boundaryExpr n)
-- -- Partialⁿ-NBoundary< n (zero , _) = {!!}
-- -- Partialⁿ-NBoundary< n (suc fst₁ , snd₁) = {!!}

-- -- Partialⁿ-NBoundary : ∀ n → Partialⁿ (NBoundary n) n (boundaryExpr n)
-- -- Partialⁿ-NBoundary n with dichotomy≤ Nmax n
-- -- ... | inl x = Partialⁿ-bd-const NBoundary n (λ n' → lid' {n = n'} false corner0)
-- -- ... | inr x = Partialⁿ-NBoundary< n x

-- -- Boundary→ω : ∀ {ℓ} → {A : Type ℓ} → (n : ℕ)
-- --         → (NBoundary n → A)
-- --         → Boundaryω A n
-- -- Boundary→ω n bd = Partialⁿ-map {n = n} bd (Partialⁿ-NBoundary n)




