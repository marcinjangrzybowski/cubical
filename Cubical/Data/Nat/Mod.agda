{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Nat.Mod where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎

-- Defining x mod 0 to be 0. This way all the theorems below are true
-- for n : ℕ instead of n : ℕ₊₁.

------ Preliminary definitions ------
modInd : (n : ℕ) → ℕ → ℕ
modInd n = +induction n (λ _ → ℕ) (λ x _ → x) λ _ x → x

modIndBase : (n m : ℕ) → m < suc n → modInd n m ≡ m
modIndBase n = +inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x)

modIndStep : (n m : ℕ) → modInd n (suc n + m) ≡ modInd n m
modIndStep n = +inductionStep n (λ _ → ℕ) (λ x _ → x) (λ _ x → x)
-------------------------------------

_mod_ : (x n : ℕ) → ℕ
x mod zero = 0
x mod (suc n) = modInd n x

mod< : (n x : ℕ) → x mod (suc n) < (suc n)
mod< n =
  +induction n
    (λ x → x mod (suc n) < suc n)
    (λ x base → fst base
               , (cong (λ x → fst base + suc x)
                       (modIndBase n x base)
                ∙ snd base))
     λ x ind → fst ind
              , cong (λ x → fst ind + suc x)
                     (modIndStep n x) ∙ snd ind

<→mod : (n x : ℕ) → x < (suc n) → x mod (suc n) ≡ x 
<→mod = modIndBase

mod-rUnit : (n x : ℕ) → x mod n ≡ ((x + n) mod n)
mod-rUnit zero x = refl
mod-rUnit (suc n) x =
    sym (modIndStep n x)
  ∙ cong (modInd n) (+-comm (suc n) x)

mod-lUnit : (n x : ℕ) → x mod n ≡ ((n + x) mod n)
mod-lUnit zero _ = refl
mod-lUnit (suc n) x = sym (modIndStep n x)

mod+mod≡mod : (n x y : ℕ)
  → (x + y) mod n ≡ (((x mod n) + (y mod n)) mod n)
mod+mod≡mod zero _ _ = refl
mod+mod≡mod (suc n) =
  +induction n
    (λ z → (x : ℕ)
         → ((z + x) mod (suc n))
         ≡ (((z mod (suc n)) + (x mod (suc n))) mod (suc n)))
    (λ x p →
      +induction n _
        (λ y q → cong (modInd n)
                       (sym (cong₂  _+_ (modIndBase n x p)
                       (modIndBase n y q))))
        λ y ind → cong (modInd n)
                        (cong (x +_) (+-comm (suc n) y)
                                   ∙ (+-assoc x y (suc n)))
                     ∙∙ sym (mod-rUnit (suc n) (x + y))
                     ∙∙ ind
                      ∙ cong (λ z → modInd n
                                    ((modInd n x + z)))
                             (mod-rUnit (suc n) y
                             ∙ cong (modInd n) (+-comm y (suc n))))
    λ x p y →
      cong (modInd n) (cong suc (sym (+-assoc n x y)))
        ∙∙ sym (mod-lUnit (suc n) (x + y))
        ∙∙ p y
         ∙ sym (cong (modInd n)
                (cong (_+ modInd n y)
                 (cong (modInd n)
                  (+-comm (suc n) x) ∙ sym (mod-rUnit (suc n) x))))

mod-idempotent : {n : ℕ} (x : ℕ) → (x mod n) mod n ≡ x mod n
mod-idempotent {n = zero} _ = refl
mod-idempotent {n = suc n} =
  +induction n (λ x → (x mod suc n) mod (suc n) ≡ x mod (suc n))
             (λ x p → cong (_mod (suc n))
                            (modIndBase n x p))
              λ x p → cong (_mod (suc n))
                            (modIndStep n x)
                          ∙∙ p
                          ∙∙ mod-rUnit (suc n) x
                           ∙ (cong (_mod (suc n)) (+-comm x (suc n)))

zero-charac : (n : ℕ) → n mod n ≡ 0
zero-charac zero = refl
zero-charac (suc n) = cong (_mod suc n) (+-comm 0 (suc n))
                  ∙∙ modIndStep n 0
                  ∙∙ modIndBase n 0 (n , (+-comm n 1))

zero-charac-gen : (n x : ℕ) → ((x · n) mod n) ≡ 0
zero-charac-gen zero x = refl
zero-charac-gen (suc n) zero = refl
zero-charac-gen (suc n) (suc x) =
  modIndStep n (x · (suc n)) ∙ zero-charac-gen (suc n) x

mod·mod≡mod : (n x y : ℕ)
  → (x · y) mod n ≡ (((x mod n) · (y mod n)) mod n)
mod·mod≡mod zero _ _ = refl
mod·mod≡mod (suc n) =
  +induction n _
    (λ x p → +induction n _
      (λ y q
        → cong (modInd n)
            (cong₂ _·_ (sym (modIndBase n x p)) (sym (modIndBase n y q))))
      λ y p →
           cong (modInd n) (sym (·-distribˡ  x (suc n) y))
        ∙∙ mod+mod≡mod (suc n) (x · suc n) (x · y)
        ∙∙ cong (λ z → modInd n (z + modInd n (x · y)))
                (zero-charac-gen (suc n) x)
        ∙∙ mod-idempotent (x · y)
        ∙∙ p
         ∙ cong (_mod (suc n)) (cong (x mod (suc n) ·_)
                (sym (mod-idempotent y)
                ∙∙ (λ i → modInd n (mod-rUnit (suc n) 0 i + modInd n y))
                ∙∙ sym (mod+mod≡mod (suc n) (suc n) y))))
    λ x p y →
         (sym (cong (_mod (suc n)) (·-distribʳ (suc n) x y))
       ∙∙ mod+mod≡mod (suc n) (suc n · y) (x · y)
       ∙∙ (λ i → modInd n ((cong (_mod (suc n))
             (·-comm (suc n) y) ∙ zero-charac-gen (suc n) y) i
             + modInd n (x · y)))
        ∙ mod-idempotent (x · y))
      ∙∙ p y
      ∙∙ cong (_mod (suc n)) (cong (_· y mod (suc n))
              ((sym (mod-idempotent x)
              ∙ cong (λ z → (z + x mod (suc n)) mod (suc n))
                     (mod-rUnit (suc n) 0))
              ∙ sym (mod+mod≡mod (suc n) (suc n) x)))

mod-rCancel : (n x y : ℕ) → (x + y) mod n ≡ (x + y mod n) mod n
mod-rCancel zero x y = refl
mod-rCancel (suc n) x =
  +induction n _
    (λ y p → cong (λ z → (x + z) mod (suc n))
                   (sym (modIndBase n y p)))
     λ y p → cong (_mod suc n) (+-assoc x (suc n) y
                             ∙∙ (cong (_+ y) (+-comm x (suc n)))
                             ∙∙ sym (+-assoc (suc n) x y))
          ∙∙ sym (mod-lUnit (suc n) (x + y))
          ∙∙ (p ∙ cong (λ z → (x + z) mod suc n) (mod-lUnit (suc n) y))

mod-lCancel : (n x y : ℕ) → (x + y) mod n ≡ (x mod n + y) mod n
mod-lCancel n x y =
     cong (_mod n) (+-comm x y)
  ∙∙ mod-rCancel n y x
  ∙∙ cong (_mod n) (+-comm y (x mod n))


-- remainder and quotient after division by n
-- Again, allowing for 0-division to get nicer syntax
remainder_/_ : (x n : ℕ) → ℕ
remainder x / zero = x
remainder x / suc n = x mod (suc n)

quotient_/_ : (x n : ℕ) → ℕ
quotient x / zero = 0
quotient x / suc n =
  +induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x

≡remainder+quotient : (n x : ℕ)
  → (remainder x / n) + n · (quotient x / n) ≡ x
≡remainder+quotient zero x = +-comm x 0
≡remainder+quotient (suc n) =
  +induction n
    (λ x → (remainder x / (suc n)) + (suc n)
          · (quotient x / (suc n)) ≡ x)
    (λ x base → cong₂ _+_ (modIndBase n x base)
                           (cong ((suc n) ·_)
                           (+inductionBase n _ _ _ x base))
              ∙∙ cong (x +_) (·-comm n 0)
              ∙∙ +-comm x 0)
     λ x ind → cong₂ _+_ (modIndStep n x)
                        (cong ((suc n) ·_) (+inductionStep n _ _ _ x))
          ∙∙ cong (modInd n x +_)
                  (·-suc (suc n) (+induction n _ _ _ x))
          ∙∙ cong (modInd n x +_)
                  (+-comm (suc n) ((suc n) · (+induction n _ _ _ x)))
          ∙∙ +-assoc (modInd n x) ((suc n) · +induction n _ _ _ x) (suc n)
          ∙∙ cong (_+ suc n) ind
           ∙ +-comm x (suc n)

private
  test₀ : 100 mod 81 ≡ 19
  test₀ = refl

  test₁ : ((11 + (10 mod 3)) mod 3) ≡ 0
  test₁ = refl



·mod : ∀ k n m → (k · n) mod (k · m)
             ≡ k · (n mod m)
·mod zero n m = refl
·mod (suc k) n zero = cong ((n + k · n) mod_) (sym (0≡m·0 (suc k)))
                  ∙ 0≡m·0 (suc k)
·mod (suc k) n (suc m) = ·mod' n n ≤-refl (splitℕ-≤ (suc m) n)

 where
 ·mod' : ∀ N n → n ≤ N → ((suc m) ≤ n) ⊎ (n < suc m) → 
    ((suc k · n) mod (suc k · suc m)) ≡ suc k · (n mod suc m)
 ·mod' _ zero x _ = cong (modInd (m + k · suc m)) (sym (0≡m·0 (suc k)))
                  ∙ 0≡m·0 (suc k)
 ·mod' zero (suc n) x _ = ⊥.rec (¬-<-zero x)
 ·mod' (suc N) n@(suc n') x (inl (m' , p)) =
  let z = ·mod' N m' (≤-trans (m
               , +-comm m m' ∙ injSuc (sym (+-suc m' m) ∙ p))
              (pred-≤-pred x)) (splitℕ-≤ _ _) ∙ cong ((suc k) ·_)
            (sym (modIndStep m m') ∙
             cong (_mod (suc m)) (+-comm (suc m) m' ∙ p))
  in (cong (λ y → ((suc k · y) mod (suc k · suc m))) (sym p)
       ∙ cong {x = (m' + suc m + k · (m' + suc m))}
               {suc (m + k · suc m + (m' + k · m'))}
            (modInd (m + k · suc m))
              (cong (_+ k · (m' + suc m)) (+-suc m' m ∙ cong suc (+-comm m' m))
                 ∙ cong suc
                  (sym (+-assoc m m' _)
                    ∙∙ cong (m +_)
                       (((cong (m' +_) (sym (·-distribˡ k _ _)
                         ∙ +-comm (k · m') _) ∙ +-assoc m' (k · suc m) (k · m'))
                        ∙ cong (_+ k · m') (+-comm m' _))
                        ∙ sym (+-assoc (k · suc m) m' (k · m')) )
                    ∙∙ +-assoc m _ _))
         ∙ modIndStep (m + k · suc m) (m' + k · m')) ∙ z
 ·mod' (suc N) n x (inr x₁) =
   modIndBase _ _ (
     subst2 _<_ (·-comm n (suc k)) (·-comm _ (suc k))
      (<-·sk {n} {suc m} {k = k} x₁) ) 
    ∙ cong ((suc k) ·_) (sym (modIndBase _ _ x₁))

-- ·quotient : ∀ k n m → quotient ((suc k) · n) / ((suc k) · (suc m))
--                        ≡ quotient n / (suc m)
-- ·quotient k zero m = {!!}
-- ·quotient k (suc n) m = zz

--   where


--     z : 
--           suc (remainder n / (suc m)) +
--            (suc m · (quotient ((suc k) · n) / ((suc k) · (suc m))))
--           ≡
--           (remainder suc n / (suc m)) +
--           suc m · (quotient suc n / (suc m))
--     z = cong suc (
--          cong (λ x →  (remainder n / (suc m)) +
--            suc m · x) (·quotient k n m)
--             ∙ ≡remainder+quotient ((suc m)) n)
--           ∙
--            (sym (≡remainder+quotient ((suc m)) (suc n)))

--     zz : (quotient suc k · suc n / (suc k · suc m)) ≡
--            (quotient suc n / suc m)
--     zz = {!!}

--   -- z : (suc k) · (remainder n / (suc m) +
--   --           (suc m) · (quotient n / (suc m)))
--   --        ≡ (remainder suc k · n / (suc k · suc m)) +
--   --            (suc k) · (suc m) · (quotient (suc k · n) / (suc k · suc m))
--   -- z = cong ((suc k) ·_) (≡remainder+quotient (suc m) n)
--   --    ∙ sym (≡remainder+quotient ((suc k) · (suc m)) ((suc k) · n))
--   --     -- ∙ {!!}
