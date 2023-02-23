{-# OPTIONS --safe --show-implicit #-}
module Cubical.Experiments.Viz where
 
open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat

-- open import Cubical.HITs.S2

-- private
--   variable
--     ℓ : Level
--     A : Type ℓ
--     x y z w v : A



-- zzz : surf ≡ surf
-- zzz i j k = hcomp
--   (λ l → primPOr (i ∨ ~ i) ((j ∨ ~ j) ∨ (k ∨ ~ k))
--     (λ _ → surf j k) λ _ → surf i l)
--    (surf j k)

-- zz : Square surf surf surf surf
-- zz i j k = hcomp
--   (λ l → primPOr
--      {!!}
--      {!!}
--      {!!}
--      {!!})
--   base



ℕsq : ∀ n → Square {A = ℕ} (λ _ → n) (λ _ → n) (λ _ → n) (λ _ → n)
ℕsq n i j =
  hcomp
   (λ l → λ {
       (i = i0) → zero + n
      ;(i = i1) → n
      ;(j = i0) → n
      ;(j = i1) → n
      })
   n


ℕsq' : ∀ n → Square {A = ℕ} (λ _ → n) (λ _ → n) (λ _ → n) (λ _ → n)
ℕsq' n i j = hcomp
  (λ l → primPOr (i ∨ ~ i) (j ∨ ~ j)
    (primPOr i (~ i) (λ _ → zero + n) (λ _ → n))
    (primPOr j (~ j) (λ _ → n) (λ _ → n)))
   n

aaa : Type
aaa = {!ℕsq!}




-- ℕsq' : ∀ n → Square {A = ℕ} (λ _ → zero) (λ _ → zero) (λ _ → zero) (λ _ → zero)
-- ℕsq' n = {!zero + n!}
