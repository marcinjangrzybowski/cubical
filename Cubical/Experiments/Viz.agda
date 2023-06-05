{-# OPTIONS --safe --show-implicit #-}
module Cubical.Experiments.Viz where
 
open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat





-- -- open import Cubical.HITs.S2

-- -- private
-- --   variable
-- --     ℓ : Level
-- --     A : Type ℓ
-- --     x y z w v : A



-- -- zzz : surf ≡ surf
-- -- zzz i j k = hcomp
-- --   (λ l → primPOr (i ∨ ~ i) ((j ∨ ~ j) ∨ (k ∨ ~ k))
-- --     (λ _ → surf j k) λ _ → surf i l)
-- --    (surf j k)

-- -- zz : Square surf surf surf surf
-- -- zz i j k = hcomp
-- --   (λ l → primPOr
-- --      {!!}
-- --      {!!}
-- --      {!!}
-- --      {!!})
-- --   base



-- ℕsq : ∀ n → Square {A = ℕ} (λ _ → n) (λ _ → n) (λ _ → n) (λ _ → n)
-- ℕsq n i j =
--   hcomp
--    (λ l → λ {
--        (i = i0) → zero + n
--       ;(i = i1) → n
--       ;(j = i0) → n
--       ;(j = i1) → n
--       })
--    n


-- ℕsq' : ∀ n → Square {A = ℕ} (λ _ → n) (λ _ → n) (λ _ → n) (λ _ → n)
-- ℕsq' n i j = hcomp
--   (λ l → primPOr (i ∨ ~ i) (j ∨ ~ j)
--     (primPOr i (~ i) (λ _ → zero + n) (λ _ → n))
--     (primPOr j (~ j) (λ _ → n) (λ _ → n)))
--    n

-- aaa : Type
-- aaa = {!ℕsq!}




-- -- ℕsq' : ∀ n → Square {A = ℕ} (λ _ → zero) (λ _ → zero) (λ _ → zero) (λ _ → zero)
-- -- ℕsq' n = {!zero + n!}

-- data A : Type where
--  a : A
--  p : ℕ → a ≡ a


-- aLoop : ℕ → Square (λ _ → a) (λ _ → a) (λ _ → a) (λ _ → a)
-- aLoop k i j =
--     hcomp
--    (λ l' → λ {
--        (i = i0) → p k l'
--       ;(i = i1) → p k l'
--       ;(j = i0) → p k l'
--       ;(j = i1) → p k l'
--       })
--    a

-- -- aTest : Square (λ _ → a) (λ _ → a) (λ _ → a) (λ _ → a)
-- -- aTest i j =
-- --       hcomp
-- --    (λ l → λ {
-- --        (i = i0) → hcomp {ℓ-zero} {A} {~ l ∨ l ∨ ~ j ∨ j}
-- --                     (λ { l' (l = i0) → p _ l'
-- --                        ; l' (l = i1) → p _ l'
-- --                        ; l' (j = i0) → p _ l'
-- --                        ; l' (j = i1) → p _ l'
-- --                        })
-- --                     a
-- --       ;(i = i1) → hcomp {ℓ-zero} {A} {~ l ∨ l ∨ ~ j ∨ j}
-- --                     (λ { l' (l = i0) → p _ l'
-- --                        ; l' (l = i1) → p _ l'
-- --                        ; l' (j = i0) → p _ l'
-- --                        ; l' (j = i1) → p _ l'
-- --                        })
-- --                     a
-- --       ;(j = i0) → hcomp {ℓ-zero} {A} {~ l ∨ l ∨ ~ i ∨ i}
-- --                     (λ { l' (l = i0) → p _ l'
-- --                        ; l' (l = i1) → p _ l'
-- --                        ; l' (i = i0) → p _ l'
-- --                        ; l' (i = i1) → p _ l'
-- --                        })
-- --                     a
-- --       ;(j = i1) → hcomp {ℓ-zero} {A} {~ l ∨ l ∨ ~ i ∨ i}
-- --                     (λ { l' (l = i0) → p _ l'
-- --                        ; l' (l = i1) → p _ l'
-- --                        ; l' (i = i0) → p _ l'
-- --                        ; l' (i = i1) → p _ l'
-- --                        })
-- --                     a
-- --       })
-- --    a


-- aTest : Square (λ _ → a) (λ _ → a) (λ _ → a) (λ _ → a)
-- aTest i j =
--       hcomp
--    (λ l → λ {
--        (i = i0) → hcomp {ℓ-zero} {A} {~ l ∨ l ∨ ~ j ∨ j}
--                     (λ { l' (l = i0) → p 2 l'
--                        ; l' (l = i1) → p 2 l'
--                        ; l' (j = i0) → p 2 l'
--                        ; l' (j = i1) → p 2 l'
--                        })
--                     a
--       ;(i = i1) → hcomp {ℓ-zero} {A} {~ l ∨ l ∨ ~ j ∨ j}
--                     (λ { l' (l = i0) → p 1 l'
--                        ; l' (l = i1) → p 1 l'
--                        ; l' (j = i0) → p 1 l'
--                        ; l' (j = i1) → p 1 l'
--                        })
--                     a
--       ;(j = i0) → hcomp {ℓ-zero} {A} {~ l ∨ l ∨ ~ i ∨ i}
--                     (λ { l' (l = i0) → p 3 l'
--                        ; l' (l = i1) → p 3 l'
--                        ; l' (i = i0) → p 3 l'
--                        ; l' (i = i1) → p 3 l'
--                        })
--                     a
--       ;(j = i1) → hcomp {ℓ-zero} {A} {~ l ∨ l ∨ ~ i ∨ i}
--                     (λ { l' (l = i0) → p {!!} l'
--                        ; l' (l = i1) → p {!!} l'
--                        ; l' (i = i0) → p {!!} l'
--                        ; l' (i = i1) → p {!!} l'
--                        })
--                     a
--       })
--    a
