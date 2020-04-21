{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.CubeEquational where


open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Prod
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.NCube.Base

open import Cubical.HITs.NCube.CubeIn


InsideOfEq : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → NBorderIn A n → Type ℓ
InsideOfEq bd = (Σ _ (bd isBorderOf_) )

-- insideOf→NCubeIn : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {✂}
--                    → {bd : NBorderIn A n} → 
--                    → InsideOf {✂ = ✂} (bd)
-- insideOf→NCubeIn = ?


InsideOf-Boundary-lem : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {✂}
                          → (bd : NBorderIn A n) 
                          → (ins : InsideOf {✂ = ✂} bd) → bd isBorderOf (insideOf→NCubeIn ins) 
InsideOf-Boundary-lem {A = A} {n = n'} {ctf'} bd' ins' = funExt (f n' {ctf'} bd' ins')


   where

     f : (n : ℕ) → ∀ {ctf} → (bd : NBorderIn A n)  → (ins : InsideOf {✂ = ctf} bd)
            → ∀ y → insideOf→NCubeIn ins (boundaryMap y) ≡ bd y
     f 1 bd ins (lid false x₁) = refl
     f 1 bd ins (lid true x₁) = refl
     
     f 2 bd ins (lid false (end false , x₁)) = refl 
     f 2 bd ins (lid false (end true , x₁)) = refl
     f 2 bd ins (lid false (inside i , x₁)) = refl
     f 2 bd ins (lid true (end false , _)) = refl
     f 2 bd ins (lid true (end true , _)) = refl
     f 2 bd ins (lid true (inside i , _)) = refl
     f 2 bd ins (cyl (lid false _) i) = refl
     f 2 bd ins (cyl (lid true _) i) = refl
     
     f 3 bd ins (lid false (end false , (end false , _))) = refl
     f 3 bd ins (lid false (end false , (end true , _))) = refl
     f 3 bd ins (lid false (end true , (end false , _))) = refl
     f 3 bd ins (lid false (end true , (end true , _))) = refl
     f 3 bd ins (lid false (end false , (inside i , _))) = refl
     f 3 bd ins (lid false (end true , (inside i , _))) = refl
     f 3 bd ins (lid false (inside i , (end false , _))) = refl
     f 3 bd ins (lid false (inside i , (end true , _))) = refl
     f 3 bd ins (lid false (inside i , (inside i₁ , _))) = refl
     f 3 bd ins (lid true (end false , (end false , _))) = refl
     f 3 bd ins (lid true (end false , (end true , _))) = refl
     f 3 bd ins (lid true (end false , (inside i , _))) = refl
     f 3 bd ins (lid true (end true , (end false , _))) = refl
     f 3 bd ins (lid true (end true , (end true , _))) = refl
     f 3 bd ins (lid true (end true , (inside i , _))) = refl
     f 3 bd ins (lid true (inside i , (end false , _))) = refl
     f 3 bd ins (lid true (inside i , (end true , _))) = refl
     f 3 bd ins (lid true (inside i , (inside i₁ , _))) = refl
     f 3 bd ins (cyl (lid false (end false , _)) i) = refl
     f 3 bd ins (cyl (lid false (end true , _)) i) = refl
     f 3 bd ins (cyl (lid false (inside i₁ , _)) i) = refl
     f 3 bd ins (cyl (lid true (end false , _)) i) = refl
     f 3 bd ins (cyl (lid true (end true , _)) i) = refl
     f 3 bd ins (cyl (lid true (inside i₁ , _)) i) = refl
     f 3 bd ins (cyl (cyl (lid false _) i₁) i) = refl
     f 3 bd ins (cyl (cyl (lid true _) i₁) i) = refl

     


     f (4) bd ins y = {!y!}
     f (5) bd ins y = {!y!}
     f (6) bd ins y = {!y!}
     f (7) bd ins y = {!y!}




InsideOf-Iso-InsideOfEq : ∀ {ℓ} → {A : Type ℓ}
                          → (bd : NBorderIn A 3) 
                          → Iso (InsideOf {n = 3} bd) (InsideOfEq bd )
Iso.fun (InsideOf-Iso-InsideOfEq bd) x = (insideOf→NCubeIn {bd = bd} x) , InsideOf-Boundary-lem _ x

Iso.inv (InsideOf-Iso-InsideOfEq bd) (cu , bd-fit) i i₁ i₂ =
         let q = (NCubeIn→insideOf {n = 3} cu)

             w : ℕ → Bool → I → I → I → _
             w k b z j₀ j₁ =  NCubeIn→insideOf ((bd-fit z) ∘ faceMap k b) j₀ j₁ 
         in
           hcomp
           (λ z → λ {
                (i = i0) → w 0 false z i₁ i₂ 
              ; (i = i1) → w 0 true z i₁ i₂
              ; (i₁ = i0) → w 1 false z i i₂
              ; (i₁ = i1) → w 1 true z i i₂
              ; (i₂ = i0) → w 2 false z i i₁
              ; (i₂ = i1) → w 2 true z i i₁
           })
           ( q i i₁ i₂)
           
fst (Iso.rightInv (InsideOf-Iso-InsideOfEq bd) (fst₁ , snd₁) i) = {!!}
snd (Iso.rightInv (InsideOf-Iso-InsideOfEq bd) (fst₁ , snd₁) i) = {!!}
Iso.leftInv (InsideOf-Iso-InsideOfEq bd) a i i₁ i₂ = {!!}


-- InsideOf-Boundary-lem : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {✂}
--                           → (bd : NBorderIn A n) 
--                           → (ins : InsideOf {✂ = ✂} bd) → bd isBorderOf (insideOf→NCubeIn ins) 
-- InsideOf-Boundary-lem {n = 0} bd ins _ ()
-- InsideOf-Boundary-lem {n = 1} bd ins _ (lid false _) = bd (lid false _)
-- InsideOf-Boundary-lem {n = 1} bd ins _ (lid true _) = bd (lid true _)
-- InsideOf-Boundary-lem {n = 2} bd ins _ (lid false (end false , _)) = bd (lid false (end false , _))
-- InsideOf-Boundary-lem {n = 2} bd ins _ (lid false (end true , _)) = bd (lid false (end true , _))
-- InsideOf-Boundary-lem {n = 2} bd ins _ (lid false (inside i₁ , _)) = bd (lid false (inside i₁ , _))
-- InsideOf-Boundary-lem {n = 2} bd ins _ (lid true (end false , _)) = bd (lid true (end false , _))
-- InsideOf-Boundary-lem {n = 2} bd ins _ (lid true (end true , _)) = bd (lid true (end true , _))
-- InsideOf-Boundary-lem {n = 2} bd ins _ (lid true (inside i₁ , _)) = bd (lid true (inside i₁ , _))
-- InsideOf-Boundary-lem {n = 2} bd ins _ (cyl (lid false _) i₁) = bd (cyl (lid false _) i₁)
-- InsideOf-Boundary-lem {n = 2} bd ins _ (cyl (lid true _) i₁) = bd (cyl (lid true _) i₁)
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid false (end false , (end false , _))) = ins i0 i0 i0
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid false (end false , (end true , _))) = ins i0 i0 i1
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid false (end true , (end false , _))) = ins i0 i1 i0
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid false (end true , (end true , _))) = ins i0 i1 i1
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid false (end false , (inside i₁ , _))) = ins i0 i0 i₁
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid false (end true , (inside i₁ , _))) = ins i0 i1 i₁
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid false (inside i₁ , (end false , _))) = ins i0 i₁ i0
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid false (inside i₁ , (end true , _))) = ins i0 i₁ i1
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid false (inside i₁ , (inside i₂ , _))) = ins i0 i₁ i₂
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid true (end false , (end false , _))) = ins i1 i0 i0
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid true (end false , (end true , _))) = ins i1 i0 i1
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid true (end true , (end false , _))) = ins i1 i1 i0
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid true (end true , (end true , _))) = ins i1 i1 i1
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid true (end false , (inside i₁ , _))) = {!!}
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid true (end true , (inside i₁ , _))) = {!!}
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid true (inside i₁ , (end false , _))) = {!!}
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid true (inside i₁ , (end true , _))) = {!!}
-- InsideOf-Boundary-lem {n = 3} bd ins _ (lid true (inside i₁ , (inside i₂ , _))) = {!!}
-- InsideOf-Boundary-lem {n = 3} bd ins _ (cyl (lid false (end false , x₂)) i₁) = {!!}
-- InsideOf-Boundary-lem {n = 3} bd ins _ (cyl (lid true (end false , x₂)) i₁) = {!!}
-- InsideOf-Boundary-lem {n = 3} bd ins _ (cyl (lid false (end true , x₂)) i₁) = {!!}
-- InsideOf-Boundary-lem {n = 3} bd ins _ (cyl (lid true (end true , x₂)) i₁) = {!!}
-- InsideOf-Boundary-lem {n = 3} bd ins _ (cyl (lid false (inside i₂ , x₂)) i₁) = {!!}
-- InsideOf-Boundary-lem {n = 3} bd ins _ (cyl (lid true (inside i₂ , x₂)) i₁) = {!!}
-- InsideOf-Boundary-lem {n = 3} bd ins _ (cyl (cyl (lid false x₁) i₂) i₁) =
--                   bd (cyl (cyl (lid false _) i₂) i₁)
-- InsideOf-Boundary-lem {n = 3} bd ins _ (cyl (cyl (lid true x₁) i₂) i₁) =
--                   bd (cyl (cyl (lid true _) i₂) i₁)
-- InsideOf-Boundary-lem {n = suc (suc (suc (suc n)))} bd ins = {!!}


-- -- InsideOf-Iso-InsideOfEq : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {✂}
-- --                           → (bd : NBorderIn A n) 
-- --                           → Iso (InsideOf {✂ = ✂} bd) (InsideOfEq bd )
-- -- fst (Iso.fun (InsideOf-Iso-InsideOfEq {n = zero} bd) x) x₁ = x
-- -- snd (Iso.fun (InsideOf-Iso-InsideOfEq {n = zero} bd) x) i ()
-- -- Iso.inv (InsideOf-Iso-InsideOfEq {n = zero} bd) (fst₁ , snd₁) = fst₁ _
-- -- fst (Iso.rightInv (InsideOf-Iso-InsideOfEq {n = zero} bd) b i) = fst b
-- -- snd (Iso.rightInv (InsideOf-Iso-InsideOfEq {n = zero} bd) b i) i₁ ()
-- -- Iso.leftInv (InsideOf-Iso-InsideOfEq {n = zero} bd) a = refl
-- -- -- InsideOf-Iso-InsideOfEq {n = 1} bd = {!!}

-- -- InsideOf-Iso-InsideOfEq {A = A} {n = 1} bd = {!!}

-- -- InsideOf-Iso-InsideOfEq {A = A} {n = 2} bd = {!!}

-- -- fst (Iso.fun (InsideOf-Iso-InsideOfEq {A = A} {n = 3} {✂ = ✂} bd) x) =
-- --      insideOf→NCubeIn {bd = bd} x
-- -- --insideOf→NCubeIn {bd = bd} x
-- -- snd (Iso.fun (InsideOf-Iso-InsideOfEq {A = A} {n = 3} {✂ = ✂} bd) x) = {!!}

-- -- Iso.inv (InsideOf-Iso-InsideOfEq {A = A} {n = 3} {✂ = ✂} bd) x = {!!}
-- -- Iso.rightInv (InsideOf-Iso-InsideOfEq {A = A} {n = 3} {✂ = ✂} bd) = {!!}
-- -- Iso.leftInv (InsideOf-Iso-InsideOfEq {A = A} {n = 3} {✂ = ✂} bd) = {!!}

-- -- InsideOf-Iso-InsideOfEq {A = A} {n = (suc (suc (suc (suc n))))} bd = {!!}


-- -- Σ-InsideOf-Iso-ΣInsideOfEq : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {✂}
-- --                              → Iso (Σ _ (InsideOf {A = A} {n = n} {✂ = ✂}))
-- --                                    (NCubeIn A n)
-- -- Σ-InsideOf-Iso-ΣInsideOfEq {n = zero} = {!!}
-- -- Σ-InsideOf-Iso-ΣInsideOfEq {n = suc zero} = {!!}
-- -- Σ-InsideOf-Iso-ΣInsideOfEq {n = suc (suc zero)} = {!!}

-- -- Iso.fun (Σ-InsideOf-Iso-ΣInsideOfEq {n = 3}) x = insideOf→NCubeIn {bd = fst x} (snd x)
-- -- Iso.inv (Σ-InsideOf-Iso-ΣInsideOfEq {n = 3}) x = {!!} , {!!}

-- -- Iso.rightInv (Σ-InsideOf-Iso-ΣInsideOfEq {n = 3}) = {!!}
-- -- Iso.leftInv (Σ-InsideOf-Iso-ΣInsideOfEq {n = 3}) = {!!}
-- -- Σ-InsideOf-Iso-ΣInsideOfEq {n = suc (suc (suc (suc n)))} = {!!}

-- -- -- -- asembleBorder :  ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {✂}
-- -- -- --                   → {endBorders : Bool → NBorderIn A n}
-- -- -- --                   → (ends : ∀ b → InsideOf {✂ = ✂} (endBorders b))
-- -- -- --                   →  endBorders false ≡ endBorders true 
-- -- -- --                    → NBorderIn A (suc n)

-- -- -- -- asembleBorder {n = suc n} ends x (cyl (lid b x₁) i) = x i (lid b x₁)
-- -- -- -- asembleBorder {n = suc n} {endBorders = eb} ends _ (lid b (end bb , x₁)) =  eb b (lid bb x₁)

-- -- -- -- asembleBorder {n = 0} ends _ (lid b _) = ends b
-- -- -- -- asembleBorder {n = 1} ends _ (lid b (inside i , _)) =  ends b i
-- -- -- -- asembleBorder {n = 2} ends _ (lid b (inside i , inside i₁ , _)) = ends b i i₁
-- -- -- -- asembleBorder {n = 3} ends _ (lid b (inside i , inside i₁ , inside i₂ , _)) =
-- -- -- --   ends b i i₁ i₂
-- -- -- -- -- asembleBorder {n = 4} ends _ (lid b (inside i , inside i₁ , inside i₂ , inside i₃ , _)) =
-- -- -- -- --   ends b i i₁ i₂ i₃


-- -- -- -- asembleBorder {n = suc (suc n)} {endBorders = eb} _ _ (lid b (inside i , (end x₁ , x₂)))
-- -- -- --                                         = eb b (cyl (lid x₁ x₂) i )
-- -- -- -- asembleBorder {n = 2} ends x (cyl (cyl (lid x₁ _) i₁) i) =
-- -- -- --                                         x i (cyl (lid x₁ _) i₁)
-- -- -- -- asembleBorder {n = 3} {endBorders = eb} _ _ (lid b (inside i , (inside i₁ , (end x₂ , x₃))))
-- -- -- --                                         = eb b (cyl (cyl (lid x₂ x₃) i₁) i )

-- -- -- -- --***
-- -- -- -- asembleBorder {n = 3} _ x (cyl (cyl (lid x₁ x₂) i₁) i) =
-- -- -- --                                        x i (cyl (lid x₁ x₂) i₁)

-- -- -- -- asembleBorder {n = 3} _ x (cyl (cyl (cyl (lid x₁ _) i₂) i₁) i) =
-- -- -- --                                        x i (cyl (cyl (lid x₁ _) i₂) i₁)


-- -- -- -- -- asembleBorder {n = 4} {endBorders = eb} _ _ (lid x₁ (inside i , (inside i₁ , (end x , (end x₃ , _))))) =
-- -- -- -- --                                        eb x₁ (cyl (cyl (lid x (end x₃ , _)) i₁) i)
-- -- -- -- -- asembleBorder {n = 4} {endBorders = eb} _ _ (lid x₁ (inside i , (inside i₁ , (inside i₂ , (end x₃ , x₄))))) =
-- -- -- -- --                                        eb x₁ (cyl (cyl (cyl (lid x₃ _) i₂) i₁) i)

-- -- -- -- -- asembleBorder {n = 4} {endBorders = eb} _ _ (lid x₁ (inside i , (inside i₁ , (end x₂ , (inside i₂ , _))))) =
-- -- -- -- --                                         eb x₁ (cyl (cyl (lid x₂ (inside i₂ , _)) i₁) i)
                                        
-- -- -- -- -- asembleBorder {n = 4} ends x (cyl (cyl (lid x₁ (end x₂ , (end x₃ , x₄))) i) i₁) = {!!}
-- -- -- -- -- asembleBorder {n = 4} ends x (cyl (cyl (lid x₁ (end x₂ , (inside i₂ , x₄))) i) i₁) = {!!}
-- -- -- -- -- asembleBorder {n = 4} ends x (cyl (cyl (lid x₁ (inside i₂ , (end x₂ , x₃))) i) i₁) = {!!}
-- -- -- -- -- asembleBorder {n = 4} ends x (cyl (cyl (lid x₁ (inside i₂ , (inside i₃ , x₃))) i) i₁) = {!!}
-- -- -- -- -- asembleBorder {n = 4} ends x (cyl (cyl (cyl (lid x₁ (end x₂ , x₃)) i) i₁) i₂) =
-- -- -- -- --                                 x i₂ ((cyl (cyl (lid x₁ (end x₂ , x₃)) i) i₁))
-- -- -- -- -- asembleBorder {n = 4} ends x (cyl (cyl (cyl (lid x₁ (inside i₃ , x₃)) i) i₁) i₂) =
-- -- -- -- --                                 x i₂ (cyl (cyl (lid x₁ (inside i₃ , x₃)) i) i₁)
                                
-- -- -- -- -- asembleBorder {n = 4} ends x (cyl (cyl (cyl (cyl (lid x₁ x₂) i) i₁) i₂) i₃) =
-- -- -- -- --                                 x i₃ ((cyl (cyl (cyl (lid x₁ x₂) i) i₁) i₂))


-- -- -- -- makeSquareBorder :
-- -- -- --    ∀ {ℓ} → {A : Type ℓ} →
-- -- -- --    {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
-- -- -- --    {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
-- -- -- --    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
-- -- -- --     →  NBorderIn A 2
-- -- -- -- makeSquareBorder a₀₋ a₁₋ a₋₀ a₋₁ =
-- -- -- --   asembleBorder
-- -- -- --  {endBorders = eb}
-- -- -- --  (xx )
-- -- -- --   yy
-- -- -- --  where
-- -- -- --    eb : Bool → NBorderIn _ 1
-- -- -- --    eb false (lid false x₁) = a₀₋ i0
-- -- -- --    eb false (lid true x₁) = a₀₋ i1
-- -- -- --    eb true (lid false x₁) = a₁₋ i0
-- -- -- --    eb true (lid true x₁) = a₁₋ i1

-- -- -- --    xx : (b : Bool) → InsideOf (eb b)
-- -- -- --    xx false = a₀₋ 
-- -- -- --    xx true = a₁₋ 

-- -- -- --    yy : eb false ≡ eb true
-- -- -- --    yy i (lid false x₁) = a₋₀ i
-- -- -- --    yy i (lid true x₁) = a₋₁ i


-- -- -- -- square≡ :
-- -- -- --      ∀ {ℓ} → {A : Type ℓ} →
-- -- -- --     {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
-- -- -- --     {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
-- -- -- --     (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
-- -- -- --      → 
-- -- -- --        (Square a₀₋ a₁₋ a₋₀ a₋₁) ≡
-- -- -- --        (InsideOf (makeSquareBorder  a₀₋ a₁₋ a₋₀ a₋₁))
-- -- -- -- square≡ a₀₋ a₁₋ a₋₀ a₋₁ = refl

-- -- -- -- square≡' :
-- -- -- --      ∀ {ℓ} → {A : Type ℓ} →
-- -- -- --      ∀ bd
-- -- -- --      → 
-- -- -- --        (Square
-- -- -- --          (insideOfBorderLid false bd)
-- -- -- --          (insideOfBorderLid true bd)
-- -- -- --          (λ i → insideOfBorderLid false (nBorderEndsPath bd i))
-- -- -- --          λ i → insideOfBorderLid true (nBorderEndsPath bd i)
-- -- -- --          ) ≡
-- -- -- --        (InsideOf {A = A} bd)
-- -- -- -- square≡' bd = refl

-- -- -- squareTest : ∀ {ℓ} → {A : Type ℓ} →  ∀ (bd : NBorderIn A 2) →   
-- -- --           (Square _ _ _ _) ≡
-- -- --           (InsideOf {A = A} {n = 2} bd)
-- -- -- squareTest bd = refl


-- -- -- cubeTest : ∀ {ℓ} → {A : Type ℓ} →  ∀ (bd : NBorderIn A 3) →   
-- -- --           (Cube _ _ _ _ _ _) ≡
-- -- --           (InsideOf {A = A} {n = 3} bd)
-- -- -- cubeTest bd = refl
