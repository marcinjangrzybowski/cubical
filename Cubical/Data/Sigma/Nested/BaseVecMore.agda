

{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Sigma.Nested.BaseVecMore where

open import Cubical.Data.Nat

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps


open import Cubical.HITs.NCube.IntervalPrim

open import Cubical.Data.Sigma.Nested.PathP

open import Cubical.HITs.NCube.BaseVec


NCubeP-Isomω : ∀ {ℓ} → ∀ n → (A : NCube n → (Type ℓ)) →
                                Isoω (∀ x → A x)
                                     (cu n (Ct[ n , A ]))
Isoω.to (NCubeP-Isomω zero A) x x₁ = x []
Isoω.toω (NCubeP-Isomω zero A) t₀ t₁ x x₁ i = x i []
Isoω.from (NCubeP-Isomω zero A) x [] = x 1=1
Isoω.sec (NCubeP-Isomω zero A) b i [] = b []
Isoω.ret (NCubeP-Isomω zero A) a x i = a 1=1

Isoω.to (NCubeP-Isomω (suc n) A) x i = Isoω.to (NCubeP-Isomω n _) (x i∷ i)
Isoω.toω (NCubeP-Isomω (suc n) A) t₀ t₁ x i =
  Isoω.toω (NCubeP-Isomω n _) _ _ (cong (_i∷ i) x)
Isoω.from (NCubeP-Isomω (suc n) A) x (end false ∷ x₂) =
    (Isoω.from (NCubeP-Isomω n _) (x i0)) x₂
Isoω.from (NCubeP-Isomω (suc n) A) x (end true ∷ x₂) =
   (Isoω.from (NCubeP-Isomω n _) (x i1)) x₂
Isoω.from (NCubeP-Isomω (suc n) A) x (inside i ∷ x₂) =
  (Isoω.from (NCubeP-Isomω n _) (x i)) x₂
Isoω.sec (NCubeP-Isomω (suc n) A) b i (end false ∷ x₁) =
  Isoω.sec (NCubeP-Isomω (n) _) (λ x → b (end false ∷ x)) i x₁
Isoω.sec (NCubeP-Isomω (suc n) A) b i (end true ∷ x₁) =
  Isoω.sec (NCubeP-Isomω (n) _) (λ x → b (end true ∷ x)) i x₁
Isoω.sec (NCubeP-Isomω (suc n) A) b i (inside i₁ ∷ x₁) =
  Isoω.sec (NCubeP-Isomω (n) _) (λ x → b (inside i₁ ∷ x)) i x₁
Isoω.ret (NCubeP-Isomω (suc n) A) a i = Isoω.ret (NCubeP-Isomω (n) _) (a i) 



NBoundary-Boundaryω-Isoω : ∀ {ℓ} → ∀ n → (A : NCube n → Type ℓ) →
                                Isoω (∀ x → A (boundaryInj x))
                                     (Boundaryω n (Ct[ n , A ]))









CylΣ-squashedTy : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) → 
                     Type ℓ
CylΣ-squashedTy n A c0 c1 = ∀ x → (PathCu A c0 c1) (boundaryInj x)

Cylω-squashedTy : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) →  
                     ωType
Cylω-squashedTy n A c0 c1 = Boundaryω n (Ct[ _ , (PathCu A c0 c1)])


CylΣ-squash : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) →
                     (PathP (λ i → ∀ x → (A i∷ i) (boundaryInj x))
                                    (c0 ∘ boundaryInj) 
                                    (c1 ∘ boundaryInj))
                     → CylΣ-squashedTy n A c0 c1
CylΣ-squash (suc n) A c0 c1 x z i = x i z


CylΣ-unsquash : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) 
                     → CylΣ-squashedTy n A c0 c1
                     → (PathP (λ i → ∀ x → (A i∷ i) (boundaryInj x))
                                    (c0 ∘ boundaryInj) 
                                    (c1 ∘ boundaryInj))
                     
CylΣ-unsquash n A c0 c1 x i z = x z i



mkCylEndsΣ : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) → 
                T[ Partialⁿ (suc n)
                     (↑Expr 1 (boundaryExpr n) ∧ⁿ (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr))
                       Ct[ _ , A ] ]
mkCylEndsΣ {ℓ} n A c0 c1 =
  mkCylEnds n
   (Isoω.to (NCubeP-Isomω _ _) c0)
   (Isoω.to (NCubeP-Isomω _ _) c1)

CylωΣ : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) → 
                     ωType 
CylωΣ n A c0 c1 = Partialⁿ-Sub (suc n) {A = Ct[ _ ,  A ]}
                        {i = ↑Expr 1 (boundaryExpr n)}
                        {j = (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)}
                        (mkCylEndsΣ n A c0 c1) 

Cylω-squash : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) →
                     T[ CylωΣ n A c0 c1 ]
                     → T[ Cylω-squashedTy n A c0 c1 ] 
Cylω-squash {ℓ} zero A c0 c1 x ()
-- Cylω-squash {ℓ} (suc zero) A c0 c1 x i = zz
--   where
--     zz : T[ Partialⁿ zero (boundaryExpr 1 i) (Ct[ 1 , PathCu A c0 c1 ] i) ]
--     zz (i = i0) = λ i₁ → outS (x i₁ i 1=1)
--     zz (i = i1) = λ i₁ → outS (x i₁ i 1=1)
    
Cylω-squash {ℓ} (suc n) A c0 c1 x i =
 {!deattachEndsFromCylω ? ?!}



Cylω-unsquash : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) →
                     T[ Cylω-squashedTy n A c0 c1 ]
                     → T[ CylωΣ n A c0 c1 ] 
Cylω-unsquash zero A c0 c1 x i ()
Cylω-unsquash (suc n) A c0 c1 x i i₁ = {!!}

fromωCyl : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) →
                     T[ CylωΣ n A c0 c1 ]
                     → T[ Boundaryω (suc n) Ct[ _ , A ] ]
fromωCyl {ℓ} n A c0 c1 x i = {!deattachEndsFromBrdω!}

toωCyl : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) →
                      T[ Boundaryω (suc n) Ct[ _ , A ] ]
                     → T[ CylωΣ n A c0 c1 ]

toωCyl zero A c0 c1 x i ()
toωCyl (suc n) A c0 c1 x = λ i i₁ → {!pp i₁ i!} 
   where
    pp : (j : I) → {!!}
    pp j = toωCyl n (λ x₁ → A (head x₁ ∷ inside j ∷ tail x₁))
                (c0 i∷ j) ((c1 i∷ j)) λ i → {!x i j!} 














Isoω.to (NBoundary-Boundaryω-Isoω zero A) x ()
Isoω.toω (NBoundary-Boundaryω-Isoω zero A) t₀ t₁ x () i
Isoω.from (NBoundary-Boundaryω-Isoω zero A) x ()
Isoω.sec (NBoundary-Boundaryω-Isoω zero A) b i ()
Isoω.ret (NBoundary-Boundaryω-Isoω zero A) a () i

NBoundary-Boundaryω-Isoω (suc n) A = h

  where

    module bIso = Iso (NBoundaryP-rec-Iso {A = A}) 

    h : Isoω ((x : NBoundary (suc n)) → A (boundaryInj x))
               (Boundaryω (suc n) Ct[ suc n , A ])
    Isoω.to h bd =
      let ((e0 , e1) , cy) = bIso.fun bd
          w = Isoω.to (NBoundary-Boundaryω-Isoω n _) (CylΣ-squash n A e0 e1 cy)

      in fromωCyl n A e0 e1 (Cylω-unsquash n A e0 e1 w)       

    
    Isoω.toω h bd = {!!}
      
    Isoω.from h bdω =
       let c0 = (Isoω.from (NCubeP-Isomω n (_))
                   (Boundaryω-getLid n false (Ct[ _ , A ]) bdω))
           c1 = (Isoω.from (NCubeP-Isomω n (_))
                    (Boundaryω-getLid n true (Ct[ _ , A ]) bdω))

           z = Cylω-squash n A
                    c0 c1
                  (toωCyl n A c0 c1 bdω)
           w = Isoω.from (NBoundary-Boundaryω-Isoω n _) z
       in bIso.inv ((c0 , c1) ,
                    CylΣ-unsquash n A
                    c0
                    c1
                    w)

    
    Isoω.sec h = {!!}
    Isoω.ret h = {!!}



-- Cylω→Path : ∀ {ℓ} → ∀ n → (A : T[ CType ℓ (suc n) ]) → (e : Ie n)
--                → (x₀ : T[ cu n (A i0) ]) → (x₁ : T[ cu n (A i1) ]) → T[ Cylω n A e x₀ x₁ ]
--                → {B : I → Type ℓ} → (f : (i : I) → T[ Partialⁿ (n) e (A i) ] → B i )
--                → PathP B (f i0 (paⁿ n x₀)) (f i1 (paⁿ n x₁)) 
-- Cylω→Path = {!!}


-- mkCylω2 : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
--             (c0 : (CubePⁿ' n (Cubeⁿ'-elim n A i0))) → 
--             (c1 : (CubePⁿ' n (Cubeⁿ'-elim n A i1))) → 
--             (PathP (λ i → BoundaryPⁿ' n (Cubeⁿ'-elim n A i))
--                (cubeBdP' n _ c0) 
--                (cubeBdP' n _ c1) ) →
--             T[ Cylω n (toCType (suc n) A)
--                (boundaryExpr n)
--                ((Isoω.to (CubePⁿ'-Isomω n (Cubeⁿ'-elim n A i0))) c0)
--                ((Isoω.to (CubePⁿ'-Isomω n (Cubeⁿ'-elim n A i1))) c1)  ]
           

-- mkCyl2 : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' (suc n) (Type ℓ)) →
--             (c0 : T[ cu n (toCType (suc n) A i0) ]) → 
--             (c1 : T[ cu n (toCType (suc n) A i1) ]) → 
--             T[ Cylω n (λ z → toCType (suc n) A z) (boundaryExpr n) c0 c1 ] →
--             PathP (λ i → BoundaryPⁿ' n (Cubeⁿ'-elim n A i))
--                 (cubeBdP' n (Cubeⁿ'-elim n A i0)
--                  (Isoω.from (CubePⁿ'-Isomω n (Cubeⁿ'-elim n A i0))
--                   c0))
--                 (cubeBdP' n (Cubeⁿ'-elim n A i1)
--                  (Isoω.from (CubePⁿ'-Isomω n (Cubeⁿ'-elim n A i1))
--                   c1))
                  



-- BoundaryPⁿ'-Boundaryω-Isoω : ∀ {ℓ} → ∀ n → (A : Cubeⁿ' n (Type ℓ)) →
--                                 Isoω (BoundaryPⁿ' n A) (Boundaryω n (toCType n A))





-- BoundaryPⁿ'-Boundaryω-Isoω zero A =
--   record { to = λ x ()
--          ; toω = λ t₀ t₁ x ()
--          ; from = λ x → _
--          ; sec = λ b → refl
--          ; ret = λ a () }


-- BoundaryPⁿ'-Boundaryω-Isoω (suc n) A = h

--   where


   
--     module bIso = Iso (BoundaryPⁿ'-elim-iso n A) 

--     h : Isoω (BoundaryPⁿ' (suc n) A)
--           (Boundaryω (suc n) (toCType (suc n) A))
--     Isoω.to h bd =
--       let ((e0 , e1) , cy) = bIso.fun bd

--       in attachEndsToBrdω n _ _ _ (mkCylω2 n A _ _ cy)      
    
--     Isoω.toω h bd = {!!}
      
--     Isoω.from h bdω =
--       let (pairω e0 e1 ,ω pω) = deattachEndsFromBrdω n _ bdω
--           e0' = (Isoω.from (CubePⁿ'-Isomω n (Cubeⁿ'-elim n A i0))) e0
--           e1' = (Isoω.from (CubePⁿ'-Isomω n (Cubeⁿ'-elim n A i1))) e1
          
--       in bIso.inv ((e0' , e1') , {!!})

    
--     Isoω.sec h = {!!}
--     Isoω.ret h = {!!}



-- mkCyl2 zero A c0 c1 x = refl
-- mkCyl2 (suc n) A c0 c1 x =
--   let zz : PathP (λ i → BoundaryPⁿ' (suc n) (Cubeⁿ'-elim (suc n) A i))
--                (Isoω.from
--                  (BoundaryPⁿ'-Boundaryω-Isoω (suc n) (Cubeⁿ'-elim (suc n) A i0))
--                  (paⁿ (suc n) c0))
--                (Isoω.from
--                  (BoundaryPⁿ'-Boundaryω-Isoω (suc n) (Cubeⁿ'-elim (suc n) A i1))
--                  (paⁿ (suc n) c1))
--       zz = Cylω→Path (suc n) (toCType (suc (suc n)) A) (boundaryExpr (suc n)) c0 c1 x
--               {λ i → BoundaryPⁿ' (suc n) (Cubeⁿ'-elim (suc n) A i)}
--               λ i → Isoω.from (BoundaryPⁿ'-Boundaryω-Isoω (suc n) (Cubeⁿ'-elim (suc n) A i))


--       qq : PathP (λ i → BoundaryPⁿ' (suc n) (Cubeⁿ'-elim (suc n) A i))
--              (cubeBdP' (suc n) (Cubeⁿ'-elim (suc n) A i0)
--               (Isoω.from (CubePⁿ'-Isomω (suc n) (Cubeⁿ'-elim (suc n) A i0)) c0))
--              (cubeBdP' (suc n) (Cubeⁿ'-elim (suc n) A i1)
--               (Isoω.from (CubePⁿ'-Isomω (suc n) (Cubeⁿ'-elim (suc n) A i1)) c1))
--       qq = {!zz!}

--   in qq

-- mkCylω2 zero A c0 c1 x i ()

-- mkCylω2 (suc n) A c0 c1 x = {!!}
