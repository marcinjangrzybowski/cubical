{-# OPTIONS --safe #-}
module Cubical.HITs.S3.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism



open Iso

data S³ : Type₀ where
  base : S³
  surf : PathP (λ j → PathP (λ i → base ≡ base) refl refl) refl refl

flip₀₂S³ : S³ → S³
flip₀₂S³ base = base
flip₀₂S³ (surf j i i₁) = surf i₁ i j

flip₀₂S³Id : (x : S³) → flip₀₂S³ (flip₀₂S³ x) ≡ x
flip₀₂S³Id base = refl
flip₀₂S³Id (surf j i i₁) = refl

flip₀₂S³Iso : Iso S³ S³
fun flip₀₂S³Iso = flip₀₂S³
inv flip₀₂S³Iso = flip₀₂S³
rightInv flip₀₂S³Iso = flip₀₂S³Id
leftInv flip₀₂S³Iso = flip₀₂S³Id


-- hpf'S : ∀ i j k → I → Partial (~ i ∨ i ∨ ~ j ∨ j ∨ ~ k ∨ k) S²
-- hpf'S i j k l =
--   primPOr (k ∨ ~ k) _
--     (λ _ → surf i j)
--     (primPOr (j ∨ ~ j) _ (λ _ → surf (i ∧ l) k)
--       (primPOr i (~ i) (λ _ → surf l k) λ _ → base))
    
-- hpf' : Cube {A = S²}
--               (λ _ _ → base)
--               (λ _ _ → base)
--               surf
--               surf
--               surf
--               surf
-- hpf' i j k =
--   hcomp (hpf'S i j k)
--     (surf i j)

-- data S³' : Type₀ where
--   base : S³'
--   face : Path (base ≡ base) refl refl
--   surf : face ≡ face



-- cyl : ∀ i j k → I →
--    Partial (~ i ∨ i ∨ ~ j ∨ j ∨ ~ k ∨ k) S³'
-- cyl i j k l = λ
--        { (i = i0) → face (j ∨ l) k
--        ; (i = i1) → face (j ∨ l) k
--        ; (j = i0) → face l k
--        ; (j = i1) → base
--        ; (k = i0) → base
--        ; (k = i1) → base
--        }

-- S³→S³' : S³ → S³'
-- S³→S³' base = base
-- S³→S³' (surf i j k) =
--   hcomp (cyl i j k)

--     (surf i j k)

-- S³'→S³ : S³' → S³
-- S³'→S³ base = base
-- S³'→S³ (face i j) = surf (i ∧ j) i j 
-- S³'→S³ (surf i j k) = surf (j ∧ k) j k 

-- -- IsoS³'S³ : Iso S³' S³
-- -- fun IsoS³'S³ = S³'→S³
-- -- inv IsoS³'S³ = S³→S³'
-- -- rightInv IsoS³'S³ base i = base
-- -- rightInv IsoS³'S³ (surf i j k) l = {!!} 
  
-- -- -- leftInv IsoS³'S³ base = {!!} --refl ∙ refl 
-- -- leftInv IsoS³'S³ (face i j) =
-- --   (λ l → hfill (cyl (i ∧ j) i j) (inS (surf (i ∧ j) i j)) (~ l) ) ∙ {!!}
-- -- leftInv IsoS³'S³ (surf i₁ x i₂) i = {!!}

-- -- i = i0 ⊢ base
-- -- i = i1 ⊢ base
-- -- j = i0 ⊢ base
-- -- j = i1 ⊢ base
-- -- k = i0 ⊢ base
-- -- k = i1 ⊢ base
-- -- l = i0 ⊢ hcomp (λ i₁ .o → S³'→S³ (cyl i j k i₁ _))
-- --          (surf (j ∧ k) j k)
-- -- l = i1 ⊢ surf i j k
