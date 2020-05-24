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
open import Cubical.Data.Maybe

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

eval-dim : (n k n-k : ℕ) → k + n-k ≡ n → ℕ → ℕ
eval-dim n k n-k p zero = n * 3
eval-dim n zero n-k p (suc m) = zero
eval-dim n (suc k) n-k p (suc m) = {!!}


-- dim-execExpr : ∀ n
--            → (e : C→I (3 + n))
--            → Maybe (Bool)
--            → C→I (suc n) 
-- dim-execExpr n e nothing i = e i i1 i1
-- dim-execExpr n e (just x) i = e i ((Bool→I (not x))) (Bool→I x)


-- faceControlExpr' : ∀ n → (l : List (Maybe (Maybe Bool))) → C→I (eval-dim n l)
-- faceControlExpr' zero [] = i0
-- faceControlExpr' zero (nothing ∷ l) = (faceControlExpr' zero l)
-- faceControlExpr' zero (just x ∷ l) i = [ mkDimE x i ]Iexpr ∨ⁿ (faceControlExpr' zero l)
-- faceControlExpr' (suc n) l i i-0 i-1 =
--     [ (i ∧ i-1) ∨ ((~ i) ∧ i-0) ]Iexpr ∨ⁿ (faceControlExpr' n l)

-- faceControlExpr : ∀ n → C→I (eval-dim n [])
-- faceControlExpr n = faceControlExpr' n []

-- -- -- dim-exec : ∀ {ℓ} → {A : Type ℓ} → ∀ n → ∀ l
-- -- --            → (y : Maybe Bool)
-- -- --            → Partialⁿ A {!!} (faceControlExpr' (suc n) l)
-- -- --            → {!!} --Partialⁿ A {!!} (dim-execExpr n {!!} y {!!} --{!!} y)
-- -- -- dim-exec = {!!}

-- -- -- hlp1 : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n
-- -- --         → Partialⁿ A (n * 3) (faceControlExpr' (suc n) [] i0 i0 i0)
-- -- --         → Partialⁿ A (n * 3) ([ i0 ]Iexpr ∨ⁿ faceControlExpr' n [])
-- -- -- hlp1 n x = {!n!}

-- -- -- ctrl-ev-stepH : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n 
-- -- --            → (y : _) 
-- -- --            → (Partialⁿ (A) _ (faceControlExpr' (suc n) []))
-- -- --            → (Partialⁿ (A) _ (faceControlExpr' n (y ∷ []))) 
-- -- -- ctrl-ev-stepH {ℓ} {A} n nothing x = {!  (x i0 i0 i0) !}
-- -- -- ctrl-ev-stepH {ℓ} {A} n (just nothing) x = {!!}
-- -- -- ctrl-ev-stepH {ℓ} {A} n (just (just x₁)) x = {!!}

-- -- hlp-nothing : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n → ∀ l
-- --                 → Partialⁿ A (eval-dim n l) (faceControlExpr' n (nothing ∷ l))
-- --                  → Partialⁿ A (eval-dim n l)
-- --                        (faceControlExpr' n (nothing ∷ nothing ∷ l))
-- -- hlp-nothing zero l x = x
-- -- hlp-nothing (suc n) l x = x

-- fromVec : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → Vec A n → List A
-- fromVec [] = []
-- fromVec (x ∷ x₁) = (x ∷ fromVec x₁)

-- -- hlp-1 : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n
-- --                 →  Partialⁿ A (eval-dim n [])
-- --                             (faceControlExpr' (suc n) [] i0 i0 i0)
-- --                  →  Partialⁿ A (eval-dim n []) (faceControlExpr' n [])
-- -- hlp-1 zero x = x
-- -- hlp-1 (suc n) x i i₁ i₂ = {! x i i₁ i₂ !}


-- ctrl-ev-All : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n 
--            → (l : Vec (Maybe (Maybe Bool)) n) 
--            → (Partialⁿ (A) _ (faceControlExpr' (n) []))
--            → (Partialⁿ (A) _ (faceControlExpr' 0 (fromVec l)))
-- ctrl-ev-All zero [] x ()
-- ctrl-ev-All (suc n) (nothing ∷ l) x =
--    ctrl-ev-All n l (⊂→⊂' _ _ (⊂-∨2 i0ⁿ (faceControlExpr' (n) [])) (x i0 i0 i0))
-- ctrl-ev-All (suc n) (just x₁ ∷ l) x i = {!x i ? ? !}
--   -- let z = ctrl-ev-All n l {!x i i1 i1!}
--   -- in {!x i i1 i1!}
-- -- ctrl-ev-All (suc n) (just (just x₁) ∷ l) x i = {!!}

-- -- ctrl-ev-step : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n 
-- --            → (y : _) → (l : List _) 
-- --            → (Partialⁿ (A) _ (faceControlExpr' (suc n) l))
-- --            → (Partialⁿ (A) _ (faceControlExpr' n (y ∷ l)))
-- -- ctrl-ev-step zero nothing l x = 
-- --   ⊂→⊂' _ _ (⊂-∨2 i0ⁿ (faceControlExpr' (zero) l))  (x i0 i0 i0)
-- -- ctrl-ev-step zero (just nothing) l x i = x i i1 i1
-- -- ctrl-ev-step zero (just (just false)) l x i = x i i1 i0
-- -- ctrl-ev-step zero (just (just true)) l x i = x i i0 i1

-- -- ctrl-ev-step {A = A} (suc n) y l x =
-- --   let x0 : (i i₁ i₂ i₃ i₄ i₅ : I) →
-- --             Partialⁿ A (eval-dim n l)
-- --             ([ (i ∧ i₂) ∨ ~ i ∧ i₁ ]Iexpr ∨ⁿ
-- --              ([ (i₃ ∧ i₅) ∨ ~ i₃ ∧ i₄ ]Iexpr ∨ⁿ faceControlExpr' n l))
-- --       x0 = {!x!}

-- --       x00 : (i i₁ i₂ i₃ i₄ i₅ : I) →
-- --             Partialⁿ A (eval-dim n l)
-- --             (([ (i₃ ∧ i₅) ∨ ~ i₃ ∧ i₄ ]Iexpr ∨ⁿ faceControlExpr' n l))
-- --       x00 = {!!}


-- --       z0 : Partialⁿ {!!} (suc (suc (suc (eval-dim n l))))
-- --              (faceControlExpr' (suc n) l)
-- --       z0 = λ i i₁ i₂ →
-- --             {!x i i₁ i₂!}
-- --            -- ⊂→⊂' {n = suc (suc (suc (eval-dim n l)))}
-- --            --   (λ z z₁ z₂ → faceControlExpr' (suc n) l z z₁ z₂)
-- --            --   (λ z z₁ z₂ → faceControlExpr' (suc (suc n)) l i i₁ i₂ z z₁ z₂)
-- --            --   (⊂-∨2 {!!} {!!}) (x i i₁ i₂) 
-- -- -- ctrl-ev-step n y l ?
-- --       z : (i i₁ i₂ : I) → Partialⁿ {!!} (eval-dim n (y ∷ l)) (faceControlExpr' n (y ∷ l))
-- --       z = λ i i₁ i₂ → ctrl-ev-step n y l {!!} 
      
-- --       -- w' : Partialⁿ _ (eval-dim (suc n) (y ∷ l))
-- --       --       (faceControlExpr' (suc n) (y ∷ l))
-- --       -- w' = λ i i₁ i₂
-- --       --     → ⊂→⊂'
-- --       --        ([ (i ∧ i₂) ∨ ~ i ∧ i₁ ]Iexpr ∨ⁿ faceControlExpr' n (y ∷ l))
-- --       --        (faceControlExpr' n (y ∷ l))
-- --       --        {!⊂-∨2 ? ?!}
-- --       --        {!!}
-- --       -- --⊂→⊂' _ _ {!!} {!!}
-- --       w : Partialⁿ A (eval-dim (suc n) (y ∷ l))
-- --             (faceControlExpr' (suc n) (y ∷ l))
-- --       w = {!z!}

--   -- in w 

-- -- ctrl-ev-step zero nothing [] x ()
-- -- ctrl-ev-step (suc n) nothing [] x i i₁ i₂ =
-- --    ⊂→⊂' _ _ (⊂-∨2 i0ⁿ (faceControlExpr' (suc n) []) i i₁ i₂)  (x i0 i0 i0 i i₁ i₂)

-- -- ctrl-ev-step zero (just nothing) [] x i x₁ = {!!}
-- -- ctrl-ev-step zero (just (just false)) [] x i x₁ = {!!}
-- -- ctrl-ev-step zero (just (just true)) [] x i x₁ = {!!}

-- -- ctrl-ev-step (suc n) (just nothing) [] x i' = x i' i1 i1
-- -- ctrl-ev-step (suc n) (just (just false)) [] x i' = x i' i1 i0
-- -- ctrl-ev-step (suc n) (just (just true)) [] x i' = x i' i0 i1

-- -- ctrl-ev-step n nothing (nothing ∷ l) x = hlp-nothing n l (ctrl-ev-step n nothing l x)  
-- -- ctrl-ev-step n (just y) (nothing ∷ l) x i = {!!}
-- -- ctrl-ev-step n nothing (just x₁ ∷ l) x = {!ctrl-ev-step n (just x₁) l x!}
-- -- ctrl-ev-step n (just y) (just x₁ ∷ l) x = {!!}

-- -- Partialⁿ-NBoundary-Max-ctrl : Partialⁿ (NBoundary Nmax) (Nmax * 3) (faceControlExpr Nmax)
-- -- Partialⁿ-NBoundary-Max-ctrl i₀ i₀0 i₀1 i₁ i₁0 i₁1 i₂ i₂0 i₂1 i₃ i₃0 i₃1 i₄ i₄0 i₄1 = 
-- --   let
-- --       cu = (nCubeω Nmax i₀ i₁ i₂ i₃ i₄ 1=1)
-- --       fc : (b : Bool) (k : ℕ) → (NBoundary Nmax)
-- --       fc = λ b k →  faceInj k b ( removeAt k cu )   

-- --       fc0 = fc false
-- --       fc1 = fc true
-- --   in

-- --   λ {
-- --       (i₀ = i0)(i₀0 = i1) →  fc0 0 ; (i₀ = i1)(i₀1 = i1) →  fc1 0
-- --     ; (i₁ = i0)(i₁0 = i1) →  fc0 1 ; (i₁ = i1)(i₁1 = i1) →  fc1 1
-- --     ; (i₂ = i0)(i₂0 = i1) →  fc0 2 ; (i₂ = i1)(i₂1 = i1) →  fc1 2
-- --     ; (i₃ = i0)(i₃0 = i1) →  fc0 3 ; (i₃ = i1)(i₃1 = i1) →  fc1 3
-- --     ; (i₄ = i0)(i₄0 = i1) →  fc0 4 ; (i₄ = i1)(i₄1 = i1) →  fc1 4
-- --    }


-- -- -- -- -- Partialⁿ-NBoundary-Max : Partialⁿ (NBoundary Nmax) Nmax (boundaryExpr Nmax)
-- -- -- -- -- Partialⁿ-NBoundary-Max = ctrl-all Nmax Partialⁿ-NBoundary-Max-ctrl 

-- -- -- -- -- -- Partialⁿ-NBoundary-Max : Partialⁿ (NBoundary Nmax) Nmax (boundaryExpr Nmax)
-- -- -- -- -- -- Partialⁿ-NBoundary-Max = {!!}





-- -- -- -- -- -- NBoundary→ω : (n : ℕ) → (NBoundary n) → I → NCubeBoundaryω (suc n)
-- -- -- -- -- -- NBoundary→ω = {!!}
 


-- -- -- -- -- -- Partialⁿ-NBoundary↓ : ∀ n → Partialⁿ (NBoundary (suc n)) (suc n) (boundaryExpr (suc n))
-- -- -- -- -- --                           → Partialⁿ (NBoundary n) n (boundaryExpr n)
-- -- -- -- -- -- Partialⁿ-NBoundary↓ zero x ()
-- -- -- -- -- -- Partialⁿ-NBoundary↓ (suc n) x i = {!x i1 i!}

-- -- -- -- -- -- Partialⁿ-NBoundary< : ∀ n → (Σ[ m ∈ ℕ ] n ≡ Nmax + m) →
-- -- -- -- -- --                        Partialⁿ (NBoundary n) n (boundaryExpr n)
-- -- -- -- -- -- Partialⁿ-NBoundary< n (zero , _) = {!!}
-- -- -- -- -- -- Partialⁿ-NBoundary< n (suc fst₁ , snd₁) = {!!}

-- -- -- -- -- -- Partialⁿ-NBoundary : ∀ n → Partialⁿ (NBoundary n) n (boundaryExpr n)
-- -- -- -- -- -- Partialⁿ-NBoundary n with dichotomy≤ Nmax n
-- -- -- -- -- -- ... | inl x = Partialⁿ-bd-const NBoundary n (λ n' → lid' {n = n'} false corner0)
-- -- -- -- -- -- ... | inr x = Partialⁿ-NBoundary< n x

-- -- -- -- -- -- Boundary→ω : ∀ {ℓ} → {A : Type ℓ} → (n : ℕ)
-- -- -- -- -- --         → (NBoundary n → A)
-- -- -- -- -- --         → Boundaryω A n
-- -- -- -- -- -- Boundary→ω n bd = Partialⁿ-map {n = n} bd (Partialⁿ-NBoundary n)



