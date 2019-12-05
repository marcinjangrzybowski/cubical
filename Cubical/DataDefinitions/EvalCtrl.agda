{-# OPTIONS --cubical --safe #-}

module Cubical.DataDefinitions.EvalCtrl where

open import Cubical.Foundations.Everything
open import Cubical.Core.Everything
open import Cubical.Foundations.Logic

open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool

open import Cubical.Data.Prod

open import Cubical.Data.Universe

open import Cubical.Data.Nat

open import Cubical.HITs.SetQuotients


ℕ′ : Type₀
ℕ′ = (Bool × ℕ) / λ x x₁ → (proj₂ x) ≡ (proj₂ x₁)


toℕ : ℕ′ → ℕ
toℕ = elimSetQuotients (λ x → isSetℕ) proj₂ λ a b → idfun _




ℕ′-induction : ( A : ℕ → Type₀ ) → (isSetA : ∀ n → isSet (A n))
                       → A (zero)
                      → ((n : ℕ) → A n → A (suc n))
                        → (n : ℕ′) → A (toℕ n)
ℕ′-induction A isSetA x x₁ =
  elimSetQuotients (λ x₂ → isSetA _)
  (λ a → h1 a)
  λ a b r → h2 a b r

  where

  
    private

      postulate ℕ-induction-stop : {ℓ : Level} {A = A₁ : ℕ → Type ℓ} →
                           A₁ 0 → ((n : ℕ) → A₁ n → A₁ (suc n)) → (n : ℕ) → A₁ n
      -- ℕ-induction-stop = ℕ-induction

      postulate ℕ-induction-stop-eq : ∀ {ℓ} → ∀ {A} → (ℕ-induction {ℓ} {A}) ≡ (ℕ-induction-stop {ℓ})
      -- ℕ-induction-stop-eq = refl

    h1 : ∀ a → A (toℕ _/_.[ a ]) 
    h1 (false , n₁) = ℕ-induction-stop {_} {A} x x₁ n₁
    h1 (true , n₁) = ℕ-induction {_} {A} x x₁ n₁ 

    h2 : ∀ a → ∀ b → (r : proj₂ a ≡ proj₂ b) → PathP (λ i → A (toℕ (eq/ a b r i))) (h1 a) (h1 b)
    h2 (false , x₁) (false , x₃) r = cong (ℕ-induction-stop x _) r
    h2 (false , _) (true , _) r i = ((sym ℕ-induction-stop-eq) i) x x₁ (r i)
    h2 (true , n1) (false , n2) r i = (ℕ-induction-stop-eq i) x x₁ (r i)
    h2 (true , x₁) (true , x₃) r = cong (ℕ-induction x _) r



ℕ′-induction-test1 : ( A : ℕ → Type₀ ) → (isSetA : ∀ n → isSet (A n))
                       → (a0 : A (zero))
                      → (as : (n : ℕ) → A n → A (suc n))
                        → (n : ℕ′) →
                        ℕ′-induction A isSetA a0 as _/_.[ false , zero ] ≡ a0
ℕ′-induction-test1 A isSetA x x₁ n = {!!}

