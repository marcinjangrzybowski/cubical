{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.CubeIn where


open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Prod
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.NCube.Base




NCubeIn : ∀ {ℓ} → (A : Type ℓ) → ℕ → Type ℓ  
NCubeIn A n = NCube n → A

nCubeLid : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → Bool → NCubeIn A (suc n) → NCubeIn A n 
nCubeLid b = _∘ boundaryMap ∘ lid b

nCubeFace : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ℕ → Bool → NCubeIn A (suc n) → NCubeIn A n 
nCubeFace k b = _∘ boundaryMap ∘ faceMap k b

NBorderIn : ∀ {ℓ} → (A : Type ℓ) → ℕ → Type ℓ  
NBorderIn A n = NBorder n → A 

_isBorderOf_ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → NBorderIn A n → NCubeIn A n → Type ℓ
_isBorderOf_ {A = A} {n = n} bd nci = nci ∘ boundaryMap ≡ bd 

nBorderEnd : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → Bool → NBorderIn A (suc n) → NBorderIn A n
nBorderEnd b = _∘ lid b ∘ boundaryMap

nBorderFaceBorder : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → ℕ → Bool
                     →  NBorderIn A (suc n)
                     →  NBorderIn A n
nBorderFaceBorder k b = _∘ (faceMap k b) ∘ boundaryMap 


nBorderEndsPath :  ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → (bd : NBorderIn A (suc n)) 
                     → nBorderEnd false bd ≡ nBorderEnd true bd 
nBorderEndsPath bd i = bd ∘ cylEx i

isBorderOf-Pt : ∀ {ℓ} → {A : Type ℓ} → ∀ {bd : NBorderIn A 0} → {a : A} → bd isBorderOf (const a)
isBorderOf-Pt i ()


isBorderOfLid : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → ∀ b → (bd : NBorderIn A (suc n)) → ∀ c
                     → bd isBorderOf c
                     → (nBorderEnd b bd) isBorderOf nCubeLid b c
isBorderOfLid {n = suc n} b bd c x i zz = x i (lid b (boundaryMap zz))

isBorderOfFace : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → ∀ k → ∀ b → (bd : NBorderIn A (suc n)) → ∀ c
                     → bd isBorderOf c
                     → (nBorderFaceBorder k b bd) isBorderOf nCubeFace k b c
isBorderOfFace {n = suc n} k b bd c x i zz = x i (faceMap k b (boundaryMap zz))

cutoffVal = 7

✂ : ℕ → Type₀
✂ = ≥Ty cutoffVal

✂↓ = ≥Ty-weak {m = cutoffVal} 


InsideOf : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → {✂ : ✂ n} → NBorderIn A n → Type ℓ

insideOfBorderLid : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → {✂ : ✂ n}
                     → (s : Bool) → (bd : NBorderIn A (suc n))
                     → InsideOf {✂ = ✂} (nBorderEnd s bd)

InsideOf {A = A} {n = zero} {✂ = ✂} _ = A
InsideOf {A = A} {n = suc n} {✂ = ✂} bd =
             PathP
             (λ i → InsideOf {✂ = ✂↓ {n = n} ✂} (nBorderEndsPath bd i))
             (insideOfBorderLid {✂ = ✂↓ {n = n} ✂} false bd)
             (insideOfBorderLid {✂ = ✂↓ {n = n} ✂} true  bd)

insideOf→NCubeIn : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {✂}
                   → {bd : NBorderIn A n} → InsideOf {✂ = ✂} (bd)
                   → NCubeIn A n
insideOf→NCubeIn {ℓ} {A} {zero} {✂₁} {bd} x x₁ = x
insideOf→NCubeIn {ℓ} {A} {suc n} {✂₁} {bd} x (end x₁ , x₂) =
    insideOf→NCubeIn (x (Bool→I x₁)) x₂
insideOf→NCubeIn {ℓ} {A} {suc n} {✂₁} {bd} x (inside i , x₂) =
    insideOf→NCubeIn (x i) x₂

NCubeIn→insideOf : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {✂}
                    → (c : NCubeIn A n)
                    → InsideOf {✂ = ✂} (c ∘ boundaryMap)
NCubeIn→insideOf {n = 0} c =
  c _
NCubeIn→insideOf {n = 1} c i =
  c (inside i , _)
NCubeIn→insideOf {n = 2} c i i₁ =
  c (inside i , inside i₁ ,  _)
NCubeIn→insideOf {n = 3} c i i₁ i₂ =
  c (inside i , inside i₁ , inside i₂ , _)
NCubeIn→insideOf {n = 4} c i i₁ i₂ i₃ =
  c (inside i , inside i₁ , inside i₂ , inside i₃ , _)
NCubeIn→insideOf {n = 5} c i i₁ i₂ i₃ i₄ =
  c (inside i , inside i₁ , inside i₂ , inside i₃ , inside i₄ , _)
NCubeIn→insideOf {n = 6} c i i₁ i₂ i₃ i₄ i₅ =
  c (inside i , inside i₁ , inside i₂ ,
     inside i₃ , inside i₄  , inside i₅ , _)
NCubeIn→insideOf {n = 7} c i i₁ i₂ i₃ i₄ i₅ i₆ = 
  c (inside i ,  inside i₁ , inside i₂ ,
     inside i₃ , inside i₄ , inside i₅ , inside i₆ , _)



insideOfBorderLid {n = n} {✂ = ✂} s bd = NCubeIn→insideOf (bd ∘ (lid s))





-- InsideOf-Iso-ΣisInsideOf : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {✂}
--                           → (bd : NBorderIn A n) 
--                           → Iso (InsideOf {✂ = ✂} bd) (Σ _ (bd isBorderOf_) )
-- fst (Iso.fun (InsideOf-Iso-ΣisInsideOf {n = zero} bd) x) x₁ = x
-- snd (Iso.fun (InsideOf-Iso-ΣisInsideOf {n = zero} bd) x) i ()
-- Iso.inv (InsideOf-Iso-ΣisInsideOf {n = zero} bd) (fst₁ , snd₁) = fst₁ _
-- fst (Iso.rightInv (InsideOf-Iso-ΣisInsideOf {n = zero} bd) b i) = fst b
-- snd (Iso.rightInv (InsideOf-Iso-ΣisInsideOf {n = zero} bd) b i) i₁ ()
-- Iso.leftInv (InsideOf-Iso-ΣisInsideOf {n = zero} bd) a = refl
-- -- InsideOf-Iso-ΣisInsideOf {n = 1} bd = {!!}

-- InsideOf-Iso-ΣisInsideOf {A = A} {n = suc zero} {✂ = ✂} bd = {!!}
-- InsideOf-Iso-ΣisInsideOf {A = A} {n = suc (suc n)} {✂ = ✂} bd = {!!}



-- asembleBorder :  ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {✂}
--                   → {endBorders : Bool → NBorderIn A n}
--                   → (ends : ∀ b → InsideOf {✂ = ✂} (endBorders b))
--                   →  endBorders false ≡ endBorders true 
--                    → NBorderIn A (suc n)

-- asembleBorder {n = suc n} ends x (cyl (lid b x₁) i) = x i (lid b x₁)
-- asembleBorder {n = suc n} {endBorders = eb} ends _ (lid b (end bb , x₁)) =  eb b (lid bb x₁)

-- asembleBorder {n = 0} ends _ (lid b _) = ends b
-- asembleBorder {n = 1} ends _ (lid b (inside i , _)) =  ends b i
-- asembleBorder {n = 2} ends _ (lid b (inside i , inside i₁ , _)) = ends b i i₁
-- asembleBorder {n = 3} ends _ (lid b (inside i , inside i₁ , inside i₂ , _)) =
--   ends b i i₁ i₂
-- -- asembleBorder {n = 4} ends _ (lid b (inside i , inside i₁ , inside i₂ , inside i₃ , _)) =
-- --   ends b i i₁ i₂ i₃


-- asembleBorder {n = suc (suc n)} {endBorders = eb} _ _ (lid b (inside i , (end x₁ , x₂)))
--                                         = eb b (cyl (lid x₁ x₂) i )
-- asembleBorder {n = 2} ends x (cyl (cyl (lid x₁ _) i₁) i) =
--                                         x i (cyl (lid x₁ _) i₁)
-- asembleBorder {n = 3} {endBorders = eb} _ _ (lid b (inside i , (inside i₁ , (end x₂ , x₃))))
--                                         = eb b (cyl (cyl (lid x₂ x₃) i₁) i )

-- --***
-- asembleBorder {n = 3} _ x (cyl (cyl (lid x₁ x₂) i₁) i) =
--                                        x i (cyl (lid x₁ x₂) i₁)

-- asembleBorder {n = 3} _ x (cyl (cyl (cyl (lid x₁ _) i₂) i₁) i) =
--                                        x i (cyl (cyl (lid x₁ _) i₂) i₁)


-- -- asembleBorder {n = 4} {endBorders = eb} _ _ (lid x₁ (inside i , (inside i₁ , (end x , (end x₃ , _))))) =
-- --                                        eb x₁ (cyl (cyl (lid x (end x₃ , _)) i₁) i)
-- -- asembleBorder {n = 4} {endBorders = eb} _ _ (lid x₁ (inside i , (inside i₁ , (inside i₂ , (end x₃ , x₄))))) =
-- --                                        eb x₁ (cyl (cyl (cyl (lid x₃ _) i₂) i₁) i)

-- -- asembleBorder {n = 4} {endBorders = eb} _ _ (lid x₁ (inside i , (inside i₁ , (end x₂ , (inside i₂ , _))))) =
-- --                                         eb x₁ (cyl (cyl (lid x₂ (inside i₂ , _)) i₁) i)
                                        
-- -- asembleBorder {n = 4} ends x (cyl (cyl (lid x₁ (end x₂ , (end x₃ , x₄))) i) i₁) = {!!}
-- -- asembleBorder {n = 4} ends x (cyl (cyl (lid x₁ (end x₂ , (inside i₂ , x₄))) i) i₁) = {!!}
-- -- asembleBorder {n = 4} ends x (cyl (cyl (lid x₁ (inside i₂ , (end x₂ , x₃))) i) i₁) = {!!}
-- -- asembleBorder {n = 4} ends x (cyl (cyl (lid x₁ (inside i₂ , (inside i₃ , x₃))) i) i₁) = {!!}
-- -- asembleBorder {n = 4} ends x (cyl (cyl (cyl (lid x₁ (end x₂ , x₃)) i) i₁) i₂) =
-- --                                 x i₂ ((cyl (cyl (lid x₁ (end x₂ , x₃)) i) i₁))
-- -- asembleBorder {n = 4} ends x (cyl (cyl (cyl (lid x₁ (inside i₃ , x₃)) i) i₁) i₂) =
-- --                                 x i₂ (cyl (cyl (lid x₁ (inside i₃ , x₃)) i) i₁)
                                
-- -- asembleBorder {n = 4} ends x (cyl (cyl (cyl (cyl (lid x₁ x₂) i) i₁) i₂) i₃) =
-- --                                 x i₃ ((cyl (cyl (cyl (lid x₁ x₂) i) i₁) i₂))


-- makeSquareBorder :
--    ∀ {ℓ} → {A : Type ℓ} →
--    {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
--    {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
--    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
--     →  NBorderIn A 2
-- makeSquareBorder a₀₋ a₁₋ a₋₀ a₋₁ =
--   asembleBorder
--  {endBorders = eb}
--  (xx )
--   yy
--  where
--    eb : Bool → NBorderIn _ 1
--    eb false (lid false x₁) = a₀₋ i0
--    eb false (lid true x₁) = a₀₋ i1
--    eb true (lid false x₁) = a₁₋ i0
--    eb true (lid true x₁) = a₁₋ i1

--    xx : (b : Bool) → InsideOf (eb b)
--    xx false = a₀₋ 
--    xx true = a₁₋ 

--    yy : eb false ≡ eb true
--    yy i (lid false x₁) = a₋₀ i
--    yy i (lid true x₁) = a₋₁ i


-- square≡ :
--      ∀ {ℓ} → {A : Type ℓ} →
--     {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
--     {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
--     (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
--      → 
--        (Square a₀₋ a₁₋ a₋₀ a₋₁) ≡
--        (InsideOf (makeSquareBorder  a₀₋ a₁₋ a₋₀ a₋₁))
-- square≡ a₀₋ a₁₋ a₋₀ a₋₁ = refl

-- square≡' :
--      ∀ {ℓ} → {A : Type ℓ} →
--      ∀ bd
--      → 
--        (Square
--          (insideOfBorderLid false bd)
--          (insideOfBorderLid true bd)
--          (λ i → insideOfBorderLid false (nBorderEndsPath bd i))
--          λ i → insideOfBorderLid true (nBorderEndsPath bd i)
--          ) ≡
--        (InsideOf {A = A} bd)
-- square≡' bd = refl

squareTest : ∀ {ℓ} → {A : Type ℓ} →  ∀ (bd : NBorderIn A 2) →   
          (Square _ _ _ _) ≡
          (InsideOf {A = A} {n = 2} bd)
squareTest bd = refl


cubeTest : ∀ {ℓ} → {A : Type ℓ} →  ∀ (bd : NBorderIn A 3) →   
          (Cube _ _ _ _ _ _) ≡
          (InsideOf {A = A} {n = 3} bd)
cubeTest bd = refl
