{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.CompN where


open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Nat.Order
open import Cubical.Data.Prod
open import Cubical.Data.Vec
open import Cubical.Data.Sum

open import Cubical.HITs.Interval
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.NCube.IntervalPrim
open import Cubical.HITs.NCube.BaseVec


compMaxN : ℕ
compMaxN = 10


dichotomy≤ : ∀ b n → (n < b) ⊎ (Σ[ m ∈ ℕ ] n ≡ b + m)
dichotomy≤ b n
  = case n Cubical.Data.Nat.Order.≟ b return (λ _ → (n < b) ⊎ (Σ[ m ∈ ℕ ] n ≡ b + m)) of λ
  { (lt o) → inl o
  ; (eq p) → inr (0 , p ∙ sym (+-zero b))
  ; (gt (m , p)) → inr (suc m , sym p ∙ +-suc m b ∙ +-comm (suc m) b)
  }


replaceAt : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → ℕ → A → Vec A n → Vec A n  
replaceAt {n = zero} _ _ _ = []
replaceAt {n = suc n} zero a v = a ∷ (tail v)
replaceAt {n = suc n} (suc k) a v = head v ∷ replaceAt k a (tail v)

removeAt : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → ℕ → Vec A (suc n) → Vec A n  
removeAt zero v = (tail v)
removeAt {n = zero} (suc k) v = []
removeAt {n = suc n} (suc k) v = head v ∷ removeAt k (tail v)

padWithFirst : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → ∀ k → Vec A (suc n) → Vec A (k + suc n)  
padWithFirst k x = repeat {n = k} (head x) ++ x

padWithFirst< : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n}
                → ∀ m → (suc n ≤ m)
                → Vec A (suc n) → Vec A (m)  
padWithFirst< m sn<m v = subst (Vec _) (snd sn<m) (padWithFirst (fst sn<m) v)

dropFirst : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → ∀ k →  Vec A (k + suc n) → Vec A (suc n)
dropFirst zero x = x
dropFirst (suc k) x = dropFirst k (tail x) 

trimFin : ∀ {n} → ℕ → Fin (suc n) 
trimFin {zero} _ = fzero
trimFin {suc n} zero = fzero
trimFin {suc n} (suc x) = fsuc (trimFin x)

FM : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n}
     → (I → (NBoundary (suc n) → A)) → NCube (suc n)
     →  I → Bool → ℕ →  A
FM sides cu j b k = (sides j ∘ (faceInj k b)) (removeAt k cu)


hfillCutΣ : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n}
              → (sides : I → (NBoundary n → A)) 
              → (center : InsideOf (sides i0))
              → Σ _ (PathP (λ i → InsideOf (sides i)) center)
hfillCutΣ {n = 0} sides center =
              _ , λ i →  hfill {φ = i0}
               (λ j → λ ())
              (inS (center)) i
hfillCutΣ {n = 1} sides center =
       _ , λ i i₀ →
       let z = FM sides (inside i₀ ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0
              })
              (inS (center i₀)) i
hfillCutΣ {n = 2} sides center =
              _ , λ i i₀ i₁ →
         let z = FM sides (inside i₀ ∷ inside i₁
                 ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1
              })
              (inS (center i₀ i₁)) i
hfillCutΣ {n = 3} sides center =
              _ , λ i i₀ i₁ i₂ →
         let z = FM sides (inside i₀ ∷ inside i₁ ∷ inside i₂
                 ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 
              })
              (inS (center i₀ i₁ i₂)) i
hfillCutΣ {n = 4} sides center =
              _ , λ i i₀ i₁ i₂ i₃ → 
         let z = FM sides (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                 ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3
              })
              (inS (center i₀ i₁ i₂ i₃)) i
hfillCutΣ {n = 5} sides center =
              _ , λ i i₀ i₁ i₂ i₃ i₄ → 
         let z = FM sides (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                 ∷ inside i₄ ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 
              })
              (inS (center i₀ i₁ i₂ i₃ i₄)) i
hfillCutΣ {n = 6} sides center =
              _ , λ i i₀ i₁ i₂ i₃ i₄ i₅ → 
         let z = FM sides (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                 ∷ inside i₄ ∷ inside i₅ ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 ;
                  (i₅ = i0) → z j false 5 ; (i₅ = i1) → z j true 5 
              })
              (inS (center i₀ i₁ i₂ i₃ i₄ i₅)) i
hfillCutΣ {n = 7} sides center =
              _ , λ i i₀ i₁ i₂ i₃ i₄ i₅ i₆ → 
         let z = FM sides (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                 ∷ inside i₄ ∷ inside i₅ ∷ inside i₆ ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 ;
                  (i₅ = i0) → z j false 5 ; (i₅ = i1) → z j true 5 ;
                  (i₆ = i0) → z j false 6 ; (i₆ = i1) → z j true 6  
              })
              (inS (center i₀ i₁ i₂ i₃ i₄ i₅ i₆)) i
hfillCutΣ {n = 8} sides center =
              _ , λ i i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ → 
         let z = FM sides (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                 ∷ inside i₄ ∷ inside i₅ ∷ inside i₆ ∷ inside i₇ ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 ;
                  (i₅ = i0) → z j false 5 ; (i₅ = i1) → z j true 5 ;
                  (i₆ = i0) → z j false 6 ; (i₆ = i1) → z j true 6 ;
                  (i₇ = i0) → z j false 7 ; (i₇ = i1) → z j true 7 
                  
              })
              (inS (center i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇)) i
hfillCutΣ {n = 9} sides center =
              _ , λ i i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ → 
         let z = FM sides (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                 ∷ inside i₄ ∷ inside i₅ ∷ inside i₆ ∷ inside i₇ ∷ inside i₈ ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 ;
                  (i₅ = i0) → z j false 5 ; (i₅ = i1) → z j true 5 ;
                  (i₆ = i0) → z j false 6 ; (i₆ = i1) → z j true 6 ;
                  (i₇ = i0) → z j false 7 ; (i₇ = i1) → z j true 7 ;
                  (i₈ = i0) → z j false 8 ; (i₈ = i1) → z j true 8 
                  
                  
              })
              (inS (center i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈)) i
hfillCutΣ {n = 10} sides center =
              _ , λ i i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ i₉ → 
         let z = FM sides (inside i₀ ∷ inside i₁ ∷ inside i₂ ∷ inside i₃
                 ∷ inside i₄ ∷ inside i₅ ∷ inside i₆ ∷ inside i₇ ∷ inside i₈ ∷ inside i₉ ∷ [])
       in 
               hfill
               (λ j → λ {
                  (i₀ = i0) → z j false 0 ; (i₀ = i1) → z j true 0 ;
                  (i₁ = i0) → z j false 1 ; (i₁ = i1) → z j true 1 ;
                  (i₂ = i0) → z j false 2 ; (i₂ = i1) → z j true 2 ;
                  (i₃ = i0) → z j false 3 ; (i₃ = i1) → z j true 3 ;
                  (i₄ = i0) → z j false 4 ; (i₄ = i1) → z j true 4 ;
                  (i₅ = i0) → z j false 5 ; (i₅ = i1) → z j true 5 ;
                  (i₆ = i0) → z j false 6 ; (i₆ = i1) → z j true 6 ;
                  (i₇ = i0) → z j false 7 ; (i₇ = i1) → z j true 7 ;
                  (i₈ = i0) → z j false 8 ; (i₈ = i1) → z j true 8 ;
                  (i₉ = i0) → z j false 9 ; (i₉ = i1) → z j true 9                   
              })
              (inS (center i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ i₉)) i
hfillCutΣ {n = (suc (suc (suc (suc (suc (suc (suc (suc n))))))))} sides center =
   _ , λ i → coe0→i (λ v → InsideOf (sides v)) i center

hcompCut : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n}
              → (sides : I → (NBoundary n → A)) 
              → (center : InsideOf (sides i0))
              → InsideOf (sides i1)
hcompCut sides center = fst (hfillCutΣ sides center)


hfillCut : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n}
              → (sides : I → (NBoundary n → A)) 
              → (center : InsideOf (sides i0))
              → PathP (λ z → InsideOf (sides z)) center (hcompCut sides center)
hfillCut sides center i = snd (hfillCutΣ sides center) i




-- -- elimNBoundary : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n}
-- --                  → (bd : I → NBoundary n → A)
-- --                  → (c : ∀ b → InsideOf (bd (Bool→I b)))
-- --                  → NBoundary (suc n) → A
-- -- elimNBoundary bd c (lid x x₁) = toCubical (c x) x₁

-- -- elimNBoundary {n = 1} bd c (cyl (lid false []) i) = bd i (lid false [])

-- -- elimNBoundary {n = 2} bd c (cyl (lid x x₁) i) = {!!}
-- -- elimNBoundary {n = 2} bd c (cyl (cyl x i₁) i) = {!!}

-- -- elimNBoundary {n = 3} bd c (cyl x i) = {!!}

-- -- elimNBoundary {n = 4} bd c (cyl x i) = {!!}

-- -- elimNBoundary {n = n} bd c (cyl x i) = {!!}


-- hcompCubCut : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n}
--               → (sides : Bool × Fin (suc n) → (NCube (suc n) → A)) 
--               → (center : NCube (suc n) → A)
--               → (centerMatch :
--                      ∀ b → ∀ k →
--                        center ∘ (faceMap k b) ≡ (sides (b , trimFin k)) ∘ faceMap 0 false )
--               → (sidesMatch :
--                        ∀ b₁ b₂ → ∀ k₁ k₂ → (¬ (k₁ ≡ k₂)) → 
--                        (sides (b₁ , trimFin k₁)) ∘ faceMap (k₂) b₂
--                      ≡ (sides (b₂ , trimFin k₂)) ∘ faceMap (k₁) b₁
--                   )         
--               → NCube (suc n) → A
-- hcompCubCut = {!!}




-- hcompCubCut : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n}
--               → (sides : Bool × Fin (suc n) → (NCube (suc n) → A)) 
--               → (center : NCube (suc n) → A)
--               → (centerMatch :
--                      ∀ b → ∀ k →
--                        center ∘ (faceMap k b) ≡ (sides (b , trimFin k)) ∘ faceMap 0 false )
--               → (sidesMatch :
--                        ∀ b₁ b₂ → ∀ k₁ k₂ → (¬ (k₁ ≡ k₂)) → 
--                        (sides (b₁ , trimFin k₁)) ∘ faceMap (k₂) b₂
--                      ≡ (sides (b₂ , trimFin k₂)) ∘ faceMap (k₁) b₁
--                   )         
--               → NCube (suc n) → A
-- hcompCubCut = {!!}


-- hcompFaceFront : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n}
--               → (cu : NCube (suc n) → A)
--               → (f : NCube (n) → A)
--               → (cu ∘ (end true ∷_)) ≡ f
--               → NCube (suc n) → A
-- hcompFaceFront {n = n} cu f x (end x₁ ∷ x₂) = {!!}
-- hcompFaceFront {n = n} cu f x (inside i ∷ x₂) =
--    ( refl ∙∙ (λ i₁ → cu (inside i₁ ∷ x₂)) ∙∙ (λ i₁ → x i₁ x₂) ) i


-- (λ i₁ → x i₁ x₂)
  -- hfill
  --  (λ k → λ {
  --   (i = i1) → {!!}
  -- ; (i = i0) → {!!}
  -- ; (φ = i1) → (cu (inside i ∷ x₃))
  -- })
  -- (inS (cu (inside i ∷ x₃)) ) i'

-- hcompFaceFront cu f x i (end true ∷ x₂) = toCubical (x i) x₂
-- hcompFaceFront cu f x i (end false ∷ x₂) = cu (end false ∷ x₂)
-- hcompFaceFront cu f x i (inside i₁ ∷ x₂) = {!cu (inside i₁ ∷ x₂)!}

-- hcompFaceBd : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n}
--               → ∀ k → ∀ b
--               → (bd : NBoundary (suc n) → A)
--               → (f : NCube n → A)
--               → bd ∘ faceInj k b ≡ f 
--               → I → (NBoundary (suc n) → A)
-- hcompFaceBd zero false bd f x i = {!!}
-- hcompFaceBd zero true bd f x i (lid false x₃) = {!!}
-- hcompFaceBd zero true bd f x i (lid true x₃) = {!!}
-- hcompFaceBd zero true bd f x i (cyl x₂ i') = {!!}
-- hcompFaceBd (suc k) b bd f x x₁ = {!!}
