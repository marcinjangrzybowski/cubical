{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.CubeIn2 where


open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Prod
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.NCube.Base

variable
  ℓ : Level

NCubeIn : ∀ {ℓ} → (A : Type ℓ) → ℕ → Type ℓ  
NCubeIn A n = NCube n → A

NBoundaryIn : ∀ {ℓ} → (A : Type ℓ) → ℕ → Type ℓ  
NBoundaryIn A n = NBoundary n → A 

variable
  A : Type ℓ


nCubeLid : ∀ {n} → Bool → NCubeIn A (suc n) → NCubeIn A n 
nCubeLid b = _∘ boundaryMap ∘ lid b

nCubeFace : ∀ {n} → ℕ → Bool → NCubeIn A (suc n) → NCubeIn A n 
nCubeFace k b = _∘ boundaryMap ∘ faceMap k b


_isBoundaryOf_ : ∀ {n} → NBoundaryIn A n → NCubeIn A n → Type _
_isBoundaryOf_ {n = n} bd nci = nci ∘ boundaryMap ≡ bd 

nBoundaryEnd : ∀ {n} → Bool → NBoundaryIn A (suc n) → NBoundaryIn A n
nBoundaryEnd b = _∘ lid b ∘ boundaryMap


nCubeFromPath : ∀ {n} → (I → NCubeIn A n) → NCubeIn A (suc n)  
nCubeFromPath x (end x₁ , x₂) = x (Bool→I x₁) x₂ 
nCubeFromPath x (inside i , x₂) = x i x₂

nBoundaryFaceBoundary : ∀ {n}
                     → ℕ → Bool
                     →  NBoundaryIn A (suc n)
                     →  NBoundaryIn A n
nBoundaryFaceBoundary k b = _∘ (faceMap k b) ∘ boundaryMap 


nBoundaryEndsPath :  ∀ {n}
                     → (bd : NBoundaryIn A (suc n)) 
                     → nBoundaryEnd false bd ≡ nBoundaryEnd true bd 
nBoundaryEndsPath bd i = bd ∘ cylEx i

isBoundaryOf-Pt : ∀ {bd : NBoundaryIn A 0} → {a : A} → bd isBoundaryOf (const a)
isBoundaryOf-Pt i ()


isBoundaryOfLid : ∀ {n}
                     → ∀ b → (bd : NBoundaryIn A (suc n)) → ∀ c
                     → bd isBoundaryOf c
                     → (nBoundaryEnd b bd) isBoundaryOf nCubeLid b c
isBoundaryOfLid {n = suc n} b bd c x i zz = x i (lid b (boundaryMap zz))

isBoundaryOfFace : ∀ {n}
                     → ∀ k → ∀ b → (bd : NBoundaryIn A (suc n)) → ∀ c
                     → bd isBoundaryOf c
                     → (nBoundaryFaceBoundary k b bd) isBoundaryOf nCubeFace k b c
isBoundaryOfFace {n = suc n} k b bd c x i zz = x i (faceMap k b (boundaryMap zz))



-- this cutoff is introduced becouse i was not able to convince agda to accept definition of
-- NCubeIn→insideOf for arbitrary n,
-- it can be easily lifted just by changing this number and
-- adding new lines to definition of NCubeIn→insideOf

cutoffVal = 7

✂ : ℕ → Type₀
✂ = ≥Ty cutoffVal

✂↓ = ≥Ty-weak {m = cutoffVal} 



-- InsideOf, NCubeIn→insideOf and insideOfBoundaryLid are mutually defined

InsideOf : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → {✂ : ✂ n} → NBoundaryIn A n → Type ℓ

NCubeIn→insideOf : ∀ {n} → ∀ {✂}
                    → (c : NCubeIn A n)
                    → InsideOf {✂ = ✂} (c ∘ boundaryMap)

insideOfBoundaryLid : ∀ {n} → {✂ : ✂ n}
                     → (s : Bool) → (bd : NBoundaryIn A (suc n))
                     → InsideOf {✂ = ✂} (nBoundaryEnd s bd)
insideOfBoundaryLid {n = n} {✂ = ✂} s bd = NCubeIn→insideOf (bd ∘ (lid s))



InsideOf {ℓ} {A = A} {n = zero} {✂ = ✂} _ = A
InsideOf {n = suc n} {✂ = ✂} bd =
             PathP
             (λ i → InsideOf {✂ = ✂↓ {n = n} ✂} (nBoundaryEndsPath bd i))
             (insideOfBoundaryLid {✂ = ✂↓ {n = n} ✂} false bd)
             (insideOfBoundaryLid {✂ = ✂↓ {n = n} ✂} true  bd)

NCubeIn→insideOf {n = zero} c = c _
NCubeIn→insideOf {n = suc n} c = {!!}


-- --- end of mutual definitions of InsideOf, NCubeIn→insideOf and insideOfBoundaryLid



-- insideOf→NCubeIn : ∀ {n} → ∀ {✂}
--                    → {bd : NBoundaryIn A n} → InsideOf {✂ = ✂} (bd)
--                    → NCubeIn A n
-- insideOf→NCubeIn {ℓ} {A} {zero} {✂₁} {bd} x x₁ = x
-- insideOf→NCubeIn {ℓ} {A} {suc n} {✂₁} {bd} x (end x₁ , x₂) =
--     insideOf→NCubeIn (x (Bool→I x₁)) x₂
-- insideOf→NCubeIn {ℓ} {A} {suc n} {✂₁} {bd} x (inside i , x₂) =
--     insideOf→NCubeIn (x i) x₂


-- -- this function allows one to assmble boundaries up to 5th dimension,
-- -- it can be easily expanded to higher dimensions, agda is unbale to fill values automatically
-- -- but for each expanded argument proper value can copied without any changes from constrains

-- asembleBoundary :  ∀ {n} → ∀ {✂} → {✂ab : ≥Ty 4 n}
--                   → {endBoundarys : Bool → NBoundaryIn A n}
--                   → (ends : ∀ b → InsideOf {✂ = ✂} (endBoundarys b))
--                   →  endBoundarys false ≡ endBoundarys true 
--                    → NBoundaryIn A (suc n)

-- asembleBoundary {n = suc n} ends x (cyl (lid b x₁) i) = x i (lid b x₁)
-- asembleBoundary {n = suc n} {endBoundarys = eb} ends _ (lid b (end bb , x₁)) =  eb b (lid bb x₁)

-- asembleBoundary {n = 0} ends _ (lid b _) = ends b
-- asembleBoundary {n = 1} ends _ (lid b (inside i , _)) =  ends b i
-- asembleBoundary {n = 2} ends _ (lid b (inside i , inside i₁ , _)) = ends b i i₁
-- asembleBoundary {n = 3} ends _ (lid b (inside i , inside i₁ , inside i₂ , _)) =
--   ends b i i₁ i₂
-- asembleBoundary {n = 4} ends _ (lid b (inside i , inside i₁ , inside i₂ , inside i₃ , _)) =
--   ends b i i₁ i₂ i₃ 

-- asembleBoundary {n = suc (suc n)} {endBoundarys = eb} _ _ (lid b (inside i , (end x₁ , x₂)))
--                                         = eb b (cyl (lid x₁ x₂) i )
-- asembleBoundary {n = 2} ends x (cyl (cyl (lid x₁ _) i₁) i) =
--                                         x i (cyl (lid x₁ _) i₁)
-- asembleBoundary {n = 3} {endBoundarys = eb} _ _ (lid b (inside i , (inside i₁ , (end x₂ , x₃))))
--                                         = eb b (cyl (cyl (lid x₂ x₃) i₁) i )

-- asembleBoundary {n = 3} _ x (cyl (cyl (lid x₁ x₂) i₁) i) =
--                                        x i (cyl (lid x₁ x₂) i₁)

-- asembleBoundary {n = 3} _ x (cyl (cyl (cyl (lid x₁ _) i₂) i₁) i) =
--                                        x i (cyl (cyl (lid x₁ _) i₂) i₁)


-- asembleBoundary {n = 4} {endBoundarys = eb} _ _ (lid x₁ (inside i , (inside i₁ , (end x , (end x₃ , _))))) =
--                                        eb x₁ (cyl (cyl (lid x (end x₃ , _)) i₁) i)
-- asembleBoundary {n = 4} {endBoundarys = eb} _ _ (lid x₁ (inside i , (inside i₁ , (inside i₂ , (end x₃ , x₄))))) =
--                                        eb x₁ (cyl (cyl (cyl (lid x₃ _) i₂) i₁) i)

-- asembleBoundary {n = 4} {endBoundarys = eb} _ _ (lid x₁ (inside i , (inside i₁ , (end x₂ , (inside i₂ , _))))) =
--                                        eb x₁ (cyl (cyl (lid x₂ (inside i₂ , _)) i₁) i)


-- asembleBoundary {n = 4} ends x (cyl (cyl (lid x₁ (end x₂ , (end x₃ , _))) i) i₁) =
--                                 x i₁ (cyl (lid x₁ (end x₂ , (end x₃ , _))) i)
-- asembleBoundary {n = 4} ends x (cyl (cyl (lid x₁ (end x₂ , (inside i₂ , x₄))) i) i₁) =
--                                 x i₁ (cyl (lid x₁ (end x₂ , (inside i₂ , x₄))) i)
-- asembleBoundary {n = 4} ends x (cyl (cyl (lid x₁ (inside i₂ , (end x₂ , x₃))) i) i₁) =
--                                 x i₁ (cyl (lid x₁ (inside i₂ , (end x₂ , x₃))) i)
-- asembleBoundary {n = 4} ends x (cyl (cyl (lid x₁ (inside i₂ , (inside i₃ , x₃))) i) i₁) =
--                                 x i₁ (cyl (lid x₁ (inside i₂ , (inside i₃ , x₃))) i)
-- asembleBoundary {n = 4} ends x (cyl (cyl (cyl (lid x₁ (end x₂ , x₃)) i) i₁) i₂) =
--                                 x i₂ ((cyl (cyl (lid x₁ (end x₂ , x₃)) i) i₁))
-- asembleBoundary {n = 4} ends x (cyl (cyl (cyl (lid x₁ (inside i₃ , x₃)) i) i₁) i₂) =
--                                 x i₂ (cyl (cyl (lid x₁ (inside i₃ , x₃)) i) i₁)
-- asembleBoundary {n = 4} ends x (cyl (cyl (cyl (cyl (lid x₁ x₂) i) i₁) i₂) i₃) =
--                                 x i₃ ((cyl (cyl (cyl (lid x₁ x₂) i) i₁) i₂))



-- mkBoundary :  ∀ {n} → ∀ {✂} → {✂ab : ≥Ty 4 n}
--                   → {eb0 eb1 : NBoundaryIn A n}
--                   → (end0 : InsideOf {✂ = ✂} eb0)
--                   → (end1 : InsideOf {✂ = ✂} eb1)
--                   →  eb0 ≡ eb1 
--                    → NBoundaryIn A (suc n)
-- mkBoundary {✂ = ✂} {✂ab = ✂ab} {eb0 = eb0} {eb1 = eb1} end0 end1 =
--     asembleBoundary {✂ = ✂} {✂ab = ✂ab}
--     {endBoundarys = caseBool eb1 eb0  }
--     h
--   where

--   h : (b : Bool) → InsideOf (caseBool eb1 eb0 b)
--   h false = end0
--   h true = end1

-- -- By infering all holes in Square and Cube
-- -- those tests shows that NBoundaryIn carries all the informations from hidden and
-- -- explicit arguments of Square and Cube from Prelude

-- makeSquareBoundary :
--    {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
--    {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
--    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
--     →  NBoundaryIn A 2
-- makeSquareBoundary a₀₋ a₁₋ a₋₀ a₋₁ =
--     mkBoundary a₀₋ a₁₋
--     λ i → mkBoundary {eb0 = λ ()} ( a₋₀ i) ( a₋₁ i) refl 

-- makeCubeBoundary :
--     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
--     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
--     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
--     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
--     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
--     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
--     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
--     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
--     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
--     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
--     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
--     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
--     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
--     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
--     →  NBoundaryIn A 3
-- makeCubeBoundary a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
--     mkBoundary a₀₋₋ a₁₋₋
--     λ i → makeSquareBoundary (a₋₀₋ i) (a₋₁₋ i) (a₋₋₀ i) (a₋₋₁ i) 



-- squareTest :
--     {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
--     {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
--     (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
--      → 
--        (Square a₀₋ a₁₋ a₋₀ a₋₁) ≡
--        (InsideOf (makeSquareBoundary  a₀₋ a₁₋ a₋₀ a₋₁))
-- squareTest a₀₋ a₁₋ a₋₀ a₋₁ = refl

-- squareTestHoles :
--           (bd : NBoundaryIn A 2) →   
--           (Square _ _ _ _) ≡
--           (InsideOf {A = A} {n = 2} bd)
-- squareTestHoles bd = refl


-- cubeTest :
--     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
--     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
--     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
--     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
--     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
--     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
--     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
--     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
--     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
--     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
--     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
--     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
--     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
--     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
--      → 
--        (Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) ≡
--        (InsideOf (makeCubeBoundary  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁))
-- cubeTest a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = refl

-- cubeTestHoles :
--           (bd : NBoundaryIn A 3) →   
--           (Cube _ _ _ _ _ _) ≡
--           (InsideOf {A = A} {n = 3} bd)
-- cubeTestHoles bd = refl
