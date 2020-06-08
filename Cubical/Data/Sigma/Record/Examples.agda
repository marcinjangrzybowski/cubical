{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Record.Examples where

open import Cubical.Core.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Fin

open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything

open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.Interval.Base renaming (elim to I-elim ; rec to I-rec)

open import Cubical.Data.Sigma.Record.Base



-- v-subst : ∀ {ℓ} → ∀ {n} →   Sig* ℓ n → Sig* ℓ n
-- v-subst = {!!}

-- ᵣtoₗ : ∀ {ℓ} → ∀ n → Sigᵣ ℓ n → Sigₗ ℓ n
-- ᵣtoₗ zero x = _
-- ᵣtoₗ (suc n) x = {!n!}


zzz : ∀ ℓ → ∀ n → Type (ℓ-suc ℓ)
zzz ℓ n = fromSigTypeₗ n corner0 (toₗ {n = n} corner1 (KindSig ℓ n)) (Type ℓ)


-- zzzTest : {!!} 
-- zzzTest = {! (zzz ℓ-zero 5)!}


someSig-2 : Sigₗ ℓ-zero 9
someSig-2 = ℕ , λ n₁
          → ℕ , λ n₂
          → ((Vec (Fin n₂) n₁) → ℕ) , λ P
          → Vec (Fin n₂) n₁ , λ x
          → Fin n₁ , λ k
          → (P x ≡ toℕ k) , λ eq1
          → ℕ , (λ n₃ → ℕ , (λ n₄ → n₁ + n₂ ≡ n₃ + n₄))

someSig-3 : Sigₗ ℓ-zero 9
someSig-3 = ℕ , λ n₁
          → ℕ , λ n₂
          → ℕ , λ n₃
          → ℕ , λ n₄
          → ℕ , λ n₅
          → Fin n₁ , λ _
          → Fin n₂ , (λ _ → Fin n₃ , (λ _ → Fin n₄))

-- zzz2 : ∀ ℓ → ∀ n → fromSigTypeₗ n corner0 (toₗ corner1 (KindSig ℓ n))
--                      (Recₗ (toₗ corner1 (KindSig ℓ n)))
-- zzz2 ℓ n = mkConstructor n corner0 (toₗ {n = n} corner1 (KindSig ℓ n))

someSigConstructor : constructorTypeₗ 9 corner0 someSig-2
someSigConstructor = mkConstructor 9 corner0 someSig-2


-- rec-from-constructor : Recₗ {n = 9} someSig-2
-- rec-from-constructor = someSigConstructor 1 2 (λ x → 0) (fzero ∷ []) fzero refl

l-test : Recₗ {n = 9} someSig-2
l-test = 1 , 2 , const 0 , fzero {1} ∷ []  , fzero {zero} , refl , 1 , 2 , refl

lr-test' : Recₗᵣ 9 someSig-2
lr-test' = (((((((1 , 2) , (const 0)) , fzero {1} ∷ []) , fzero {zero})
           , refl) , 1) , 2) , refl


lr-test : Recₗᵣ 9 someSig-3
lr-test = (((((((1 , 2) , 3) , 4) , 5) , (fzero {0})) , fzero {1}) , fzero {2}) , fzero {3}


someSig-4 : Sigₗ ℓ-zero 5
someSig-4 = ℕ , λ n₁
          → ℕ , λ n₂
          → ℕ , λ n₃
          → ℕ , λ n₄ → ℕ

qqq : Square {A = Type₀}
        {a₀₀ = ℕ × ℕ × ℕ × ℕ × ℕ}
        {a₀₁ = ℕ × (ℕ × ℕ × ℕ) ×  ℕ}        
        (λ i → Recc 2 ((seg i0 ∷ seg i ∷ [])) someSig-4)
        {a₁₀ = (ℕ × ℕ × ℕ × ℕ) × ℕ}
        {a₁₁ = (( ℕ × ℕ × ℕ) × ℕ) × ℕ}
        (λ i → Recc 2 ((seg i1 ∷ seg i ∷ [])) someSig-4)
        (λ i → Recc 2 ((seg i ∷ seg i0 ∷ [])) someSig-4)
        (λ i → Recc 2 ((seg i ∷ seg i1 ∷ [])) someSig-4)
        
qqq i i₁ = Recc 2 ((seg i ∷ seg i₁ ∷ [])) someSig-4

        -- 
        -- {a₁₀ = ?}
        -- {a₁₁ = ?}

-- ℕ , λ n₁
--           → ℕ , λ n₂
--           → ((Vec (Fin n₂) n₁) → ℕ) , λ P
--           → _ , λ x
--           → Fin n₁ , λ k
--           → (P x ≡ toℕ k) , λ eq1
--           → ℕ , (λ n₃ → ℕ , (λ n₄ → n₁ + n₂ ≡ n₃ + n₄))

-- someSig-2ᵣ : Sigᵣ ℓ-zero 9
-- someSig-2ᵣ = (((((((ℕ , λ _ → ℕ) , λ (n₁ , n₂) → ((Vec (Fin n₂) n₁) → ℕ))
--             , {!const x!}) , {!!}) , {!!}) , {!!}) , {!!}) , {!!}
          







-- someSigConstructor-implict : _
-- someSigConstructor-implict = {!toᵣ {n = 5} corner0 !}

