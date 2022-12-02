{-

This file contains:

- An implementation of the free group of a type of generators as a HIT

-}
{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.FinData
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Empty



private
  variable
    ℓ : Level

-- data FreeGroup (A : Type ℓ) : Type ℓ where
--   η     : A → FreeGroup A
--   _·_   : FreeGroup A → FreeGroup A → FreeGroup A
--   ε     : FreeGroup A
--   inv   : FreeGroup A → FreeGroup A
--   assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
--   idr   : ∀ x → x ≡ x · ε
--   idl   : ∀ x → x ≡ ε · x
--   invr  : ∀ x → x · (inv x) ≡ ε
--   invl  : ∀ x → (inv x) · x ≡ ε
--   trunc : isSet (FreeGroup A)

sucF : ∀ n → Fin (predℕ (predℕ n)) → Fin (predℕ n)
sucF (suc (suc n)) = suc

weakF : ∀ n → Fin (predℕ (predℕ n)) → Fin (predℕ n)
weakF (suc (suc n)) = weakenFin

diff : ℕ → ℕ → ℕ
diff zero zero = zero
diff zero (suc m) = suc m
diff (suc n) zero = suc n
diff (suc n) (suc m) = diff n m

>1 : ℕ → Type
>1 zero = ⊥
>1 one = ⊥
>1 (suc (suc x)) = Unit

commJ : ∀ n → Fin (predℕ n) → Fin (predℕ n) → Type
commJ n k l = >1 (diff (toℕ k) (toℕ l))

commJsym : ∀ n → (k l : Fin (predℕ n)) → commJ n k l → commJ n l k
commJsym zero () l x
commJsym (suc .(suc (suc _))) zero (suc (suc l)) _ = _
commJsym (suc .(suc (suc _))) (suc (suc k)) zero _ = _
commJsym (suc .(suc (suc n))) (suc {suc n} k) (suc l) x = commJsym (suc (suc n)) k l x

data Perm (n : ℕ) : Type where
  η : Fin (predℕ n) → Perm n
  ε     : Perm n
  _·_ : Perm n → Perm n → Perm n
  assocP : ∀ x y z → x · (y · z) ≡ (x · y) · z

  invo : ∀ k → η k · η k ≡ ε  
  braid : (k : Fin (predℕ (predℕ n))) →
               η (weakF n k) · (η (sucF n k) · η (weakF n k))
             ≡ η (sucF n k) · (η (weakF n k) · η (sucF n k))
  comm : ∀ k l → commJ n k l →  η k · η l ≡ η l · η k
  
  trunc : isSet (Perm n)


invP : ∀ n → Perm n → Perm n
invP n (η x) = η x
invP n ε = ε
invP n (x · x₁) = invP n x₁ · invP n x
invP n (assocP x x₁ x₂ i) = assocP (invP n x₂) (invP n x₁) (invP n x) (~ i)
invP n (invo k i) = invo k i
invP n (braid k i) = (sym (assocP _ _ _) ∙∙ braid k ∙∙ assocP _ _ _) i
invP n (comm k l x i) = comm l k (commJsym n k l x) i
invP n (trunc x x₁ x₂ y i i₁) =
  trunc (invP n x) (invP n x₁) (cong (invP n) x₂) (cong (invP n) y) i i₁


--   -- inv   : FreeGroup A → FreeGroup A
--   -- assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
--   -- idr   : ∀ x → x ≡ x · ε
--   -- idl   : ∀ x → x ≡ ε · x
--   -- invr  : ∀ x → x · (inv x) ≡ ε
--   -- invl  : ∀ x → (inv x) · x ≡ ε
--   -- trunc : isSet (FreeGroup A)
