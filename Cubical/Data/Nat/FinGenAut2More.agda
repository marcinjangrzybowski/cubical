{-# OPTIONS --safe #-}
module Cubical.Data.Nat.FinGenAut2More where

open import Cubical.Data.Nat.Base as ℕ hiding (_·_)
open import Cubical.Data.Nat.Properties


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution

open import Cubical.Foundations.Everything
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Nat as ℕ hiding (_·_)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as Mb
import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group

open import Cubical.Algebra.SymmetricGroup

import Cubical.Functions.Logic as L

open import Cubical.Functions.Embedding

open import Cubical.Data.List as Li

open import Cubical.HITs.SequentialColimit as SC

import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.HITs.GroupoidQuotients as GQ
  renaming ([_] to [_]// ; RelimProp to  RelimProp// ; Rrec to Rrec//)


-- open import Cubical.Algebra.Group.Morphisms

-- open import Cubical.Algebra.Group.Generators

open import Cubical.Data.Nat.FinGenAut2



private
  variable
    ℓ : Level

module List-perm {A : Type ℓ} where

--  lookA⊎ℕ : List A → ℕ → A ⊎ ℕ 
--  lookA⊎ℕ [] n = inr n
--  lookA⊎ℕ (a ∷ _) zero = inl a
--  lookA⊎ℕ (_ ∷ l) (suc n) = lookA⊎ℕ l n

--  lookA⊎ℕ>length : ∀ l k → length l ≤ k → lookA⊎ℕ l k ≡ inr (k ∸ length l)
--  lookA⊎ℕ>length [] k x = refl
--  lookA⊎ℕ>length (x₁ ∷ l) (suc k) x = lookA⊎ℕ>length l k x


--  ipb' : List A → List A → (Iso ℕ ℕ) → Type ℓ
--  ipb' l l' x = lookA⊎ℕ l ∘' Iso.fun x ≡ lookA⊎ℕ l'

--  ipbR : List A → List A → Type ℓ
--  ipbR l l' = Σ _ (ipb' l l')

--  ipbR-sym : (l l' : List A) → ipbR l l' → ipbR l' l
--  ipbR-sym l l' (e , p) = invIso e ,
--    cong′ (_∘' (Iso.inv e)) (sym p) ∙
--      cong′ (lookA⊎ℕ l ∘'_) (funExt (Iso.rightInv e))

--  ¬ipbR[]∷ : ∀ x xs → ¬ ipbR [] (x ∷ xs)
--  ¬ipbR[]∷ _ _ (_ , x) =
--    ⊥.rec (𝟚.false≢true
--      (cong (⊎.rec (λ _ → 𝟚.true) (λ _ → 𝟚.false))
--        (funExt⁻ x zero)))

--  ¬ipbR∷[] : ∀ x xs → ¬ ipbR (x ∷ xs) []
--  ¬ipbR∷[] x xs = ¬ipbR[]∷ x xs ∘ ipbR-sym (x ∷ xs) []  
 
--  ipbR→length≡ : (l l' : List A) → ipbR l l' → length l ≡ length l'
--  ipbR→length≡ [] [] x = refl
--  ipbR→length≡ [] (x ∷ xs) = ⊥.rec ∘ ¬ipbR[]∷ x xs
--  ipbR→length≡ (x ∷ xs) [] = ⊥.rec ∘ ¬ipbR∷[] x xs
--  ipbR→length≡ (x₁ ∷ l) (x₂ ∷ l') x = {!!}


--  ipb' l l' ∘' fst ∘' to≃'

--  isConstFromLength : ∀ l l' e → ipb' l l' e
--              → ⟨ isConstFrom (Iso.fun e) (length l') ⟩ 
--  isConstFromLength l l' e x k l<k =
--    let z = lookA⊎ℕ>length l' k l<k
--        z' = lookA⊎ℕ>length l (Iso.fun e k) {!!}
--    in {!!}
--  [] [] e x x₁ x₂ =
--    invEq (_ , (isEmbedding-inr _ _)) (funExt⁻ x x₁)  
--  isConstFromLength (x₃ ∷ l) [] e x _ _ = ⊥.rec (¬ipbR∷[] x₃ l (e , x))
--  isConstFromLength [] (x₃ ∷ l') e x x₁ x₂ = ⊥.rec (¬ipbR[]∷ x₃ l' (e , x))
--  isConstFromLength (x₄ ∷ l) (x₃ ∷ l') e x (suc x₁) x₂ =
--     {!(funExt⁻ x (suc x₁))  !}



-- FinGen≃'

 ipb' : List A → List A → FGℕ≃ℕ → Type ℓ
 ipb' l l' = {!!}

 ↔at : List A → List A → ℕ → Type ℓ
 ↔at (x ∷ l) (y ∷ l') (suc n) = (x ≡ y) × ↔at l l' n
 ↔at (x ∷ x' ∷ l) (y ∷ y' ∷ l') (zero) = (x ≡ y') × (x' ≡ y') × (l ≡ l')
 ↔at (_) (_) (zero) = ⊥*
 ↔at [] x (suc x₁) = ⊥*
 ↔at (x ∷ x₁) [] (suc x₂) = ⊥*


 ipb : (l l' : List A) → (e : FGℕ≃ℕ) →
          Σ (Type ℓ) λ T → T ≃ ipb' l l' e  
 ipb l l' = Relim.f (w l l')
  where
  open Relim

  -- wId : ∀ l l' → ListPath.Cover l l' ≃ (lookA⊎ℕ l ≡ lookA⊎ℕ l')
  -- wId = {!!}
  
  w : ∀ l l' → Relim (λ z → Σ (Type ℓ) (λ T → T ≃ ipb' l l' z))
  isSetA (w l l') = {!!}
  εA (w l l') = (l ≡ l') , {!!}
  ∷A (w l l') k (X , E) = {!(↔at l l' k) × ?  , ? !}
    
  invoA (w l l') = {!!}
  braidA (w l l') = {!!}
  commA (w l l') = {!!}

 -- ipb : FGℕ≃ℕ → List A → List A → Type ℓ 
 -- ipb = Rrec.f w
  -- where
  -- w : Rrec (List A → List A → Type ℓ)
  -- Rrec.isSetA w = {!!}
  -- Rrec.εA w = _≡_
  -- Rrec.∷A w (suc k) _ [] [] = ⊥*
  -- Rrec.∷A w (suc k) _ [] (x ∷ x₃) = ⊥*
  -- Rrec.∷A w (suc k) _ (x ∷ x₂) [] = ⊥*
  -- Rrec.∷A w (suc k) X (x ∷ x₂) (x₃ ∷ x₄) =
  --   (x ≡ x₃) × Rrec.∷A w (k) X x₂ x₄
  -- Rrec.∷A w zero x₁ x₂ x₃ = {!!}
  -- Rrec.invoA w = {!!}
  -- Rrec.braidA w = {!!}
  -- Rrec.commA w = {!!}



