{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Record.Alt where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything

open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.Interval.Base renaming (elim to I-elim ; rec to I-rec)


Tree : ?
Tree = ?


-- Sigₗ : ∀ ℓ → ℕ → Type (ℓ-suc ℓ)




-- Sigₗ : ∀ ℓ → ℕ → Type (ℓ-suc ℓ)
-- Sigₗ ℓ 0 = Lift Unit
-- Sigₗ ℓ 1 = Type ℓ
-- Sigₗ ℓ (suc (suc n)) = Σ[ Ty ∈ Type ℓ ]  (Ty → Sigₗ ℓ (suc n))

-- Recₗ : ∀ {ℓ} → ∀ {n} → Sigₗ ℓ n → Type ℓ
-- Recₗ {n = 0} _ = Lift Unit
-- Recₗ {n = 1} x = x
-- Recₗ {n = suc (suc n)} x = Σ (fst x) (Recₗ ∘ snd x)


-- Sigᵣ : ∀ ℓ → ℕ → Type (ℓ-suc ℓ)

-- Recᵣ : ∀ {ℓ} → ∀ {n} → Sigᵣ ℓ n → Type ℓ


-- Sigᵣ ℓ 0 = Lift Unit
-- Sigᵣ ℓ 1 = Type ℓ
-- Sigᵣ ℓ (suc (suc n)) = Σ (Sigᵣ ℓ (suc n)) (λ x → Recᵣ x → Type ℓ)

-- Recᵣ {ℓ} {0} x = Lift Unit
-- Recᵣ {ℓ} {1} x = x
-- Recᵣ {ℓ} {suc (suc n)} x = Σ (Recᵣ (fst x)) (snd x)



-- trim-sig :  ∀ {ℓ} → ∀ {n} → (s : Sigₗ ℓ n) → Sigₗ ℓ (predℕ n)
-- trim-sig {n = 0} s = _
-- trim-sig {n = 1} s = _
-- trim-sig {n = 2} s = fst s
-- trim-sig {n = suc (suc (suc n))} s = fst s , λ x → trim-sig (snd s x)


-- push-Type :  ∀ {ℓ} → ∀ {n} → (s : Sigₗ ℓ n)
--               → (Recₗ s → Type ℓ)
--               → Sigₗ ℓ (suc n)
-- push-Type {n = zero} s x = x _
-- push-Type {n = suc zero} s x = s , x
-- push-Type {n = suc (suc n)} s x = (fst s) , (λ a → push-Type (snd s a) (x ∘ (a ,_) ))

-- trim-rec :  ∀ {ℓ} → ∀ {n} → (s : Sigₗ ℓ n) → Recₗ s → Recₗ (trim-sig s)
-- trim-rec {n = zero} x = _
-- trim-rec {n = suc zero} s x = _
-- trim-rec {n = suc (suc zero)} s x = fst x
-- trim-rec {n = suc (suc (suc n))} s x = fst x , trim-rec (snd s (fst x)) (snd x)


-- -- This functions describes Type of maixmally curried type of last field in record in given signature
-- -- the purpose of Boolean and (List ℕ) arguments, is to controll
-- -- explicity of arguments in generated type:
-- --  * Bool controls the "default" mode (true → implicit , false  → explicit)
-- --  * List ℕ controls "exceptions", it stores the list of spaces
-- --    betwen arguments which are treated in oposite way
-- --    (if this list is to long, the remaing elements are ignored)

-- Type-in-sig : ∀ {ℓ} → Bool → List ℕ → ∀ {n} → Sigₗ ℓ n → Type (ℓ-suc ℓ)
-- Type-in-sig _ _ {zero} _ = Type _
-- Type-in-sig false [] {suc zero} x = x → Type _
-- Type-in-sig {ℓ} true [] {suc zero} x = {_ : x} → Type ℓ

-- Type-in-sig {ℓ} false (zero ∷ _) {suc zero} x = {_ : x} → Type ℓ
-- Type-in-sig true (zero ∷ _) {suc zero} x = x → Type _

-- Type-in-sig false (suc x₁ ∷ xs) {suc zero} x = x → Type _
-- Type-in-sig {ℓ} true (suc x₁ ∷ xs) {suc zero} x = {_ : x} → Type ℓ

-- Type-in-sig false [] {suc (suc n)} x = (a : fst x) → Type-in-sig false [] (snd x a) 
-- Type-in-sig true [] {suc (suc n)} x = {a : fst x} → Type-in-sig true [] (snd x a)
-- Type-in-sig false (zero ∷ xs) {suc (suc n)} x = {a : fst x} → Type-in-sig false (xs) (snd x a)
-- Type-in-sig false (suc k ∷ xs) {suc (suc n)} x = (a : fst x) → Type-in-sig false (k ∷ xs) (snd x a)
-- Type-in-sig true (zero ∷ xs) {suc (suc n)} x = (a : fst x) → Type-in-sig true (xs) (snd x a)
-- Type-in-sig true (suc k ∷ xs) {suc (suc n)} x = {a : fst x} → Type-in-sig true (k ∷ xs) (snd x a)

-- -- maixmally curried Type of last field for given signature
-- pop-Type : ∀ {ℓ} → ∀ {n}
--            → (b : Bool) → (l : List ℕ) → (A : Sigₗ ℓ n)
--            → Type-in-sig b l (trim-sig A)
-- pop-Type {n = zero} _ _ _ = Lift Unit
-- pop-Type {n = suc zero} _ _ A = A
-- pop-Type {n = suc (suc zero)} false [] A = snd A
-- pop-Type {n = suc (suc zero)} true [] A {a} = snd A a
-- pop-Type {n = suc (suc zero)} false (zero ∷ l) A {a} = snd A a
-- pop-Type {n = suc (suc zero)} false (suc k ∷ l) A = snd A
-- pop-Type {n = suc (suc zero)} true (zero ∷ l) A = snd A
-- pop-Type {n = suc (suc zero)} true (suc k ∷ l) A {a} = snd A a
-- pop-Type {n = suc (suc (suc n))} false [] A a = pop-Type false [] (snd A a)
-- pop-Type {n = suc (suc (suc n))} true [] A {a} = pop-Type true [] (snd A a)
-- pop-Type {n = suc (suc (suc n))} false (zero ∷ l) A {a} = pop-Type false l (snd A a)
-- pop-Type {n = suc (suc (suc n))} false (suc k ∷ l) A a = pop-Type false (k ∷ l) (snd A a)
-- pop-Type {n = suc (suc (suc n))} true (zero ∷ l) A a = pop-Type true l (snd A a)
-- pop-Type {n = suc (suc (suc n))} true (suc k ∷ l) A {a} = pop-Type true (k ∷ l) (snd A a)

-- -- maximally uncuried  Type of last field for given signature
-- pop-Type-overRecₗ : ∀ {ℓ} → ∀ {n}
--                      → (s : Sigₗ ℓ n)
--                      →  Recₗ (trim-sig s) → Type ℓ
-- pop-Type-overRecₗ {n = zero} _ _ = Lift Unit
-- pop-Type-overRecₗ {n = suc zero} A _ = A
-- pop-Type-overRecₗ {n = suc (suc zero)} x a = snd x a
-- pop-Type-overRecₗ {n = suc (suc (suc n))} x a = pop-Type-overRecₗ (snd x (fst a)) (snd a)


-- pushVal : ∀ {ℓ} → ∀ {n} → (A : Sigₗ ℓ n)
--         → (x : Recₗ (trim-sig A))
--         → (pop-Type-overRecₗ A x) → Recₗ A 
-- pushVal {n = zero} _ _ _ = _
-- pushVal {n = suc zero} _ _ a = a
-- pushVal {n = suc (suc zero)} _ x x₁ = x , x₁
-- pushVal {n = suc (suc (suc n))} A x x₁ = fst x , (pushVal (snd A (fst x)) (snd x) x₁)

-- popVal : ∀ {ℓ} → ∀ {n} → (A : Sigₗ ℓ n)
--         → (x : Recₗ A) → pop-Type-overRecₗ A (trim-rec A x) 
-- popVal {n = zero} _ _ = _
-- popVal {n = suc zero} _ x = x
-- popVal {n = suc (suc zero)} _ x = snd x
-- popVal {n = suc (suc (suc n))} A x = popVal (snd A (fst x)) (snd x)

-- push-trim : ∀ {ℓ} → ∀ {n} → {s : Sigₗ ℓ n}
--              → ∀ x → trim-sig (push-Type s x) ≡ s
-- push-trim {n = zero} x = refl
-- push-trim {n = suc zero} x = refl
-- push-trim {n = suc (suc n)} {s} x i = fst s , λ a → push-trim ( x ∘ (a ,_)) i

-- concatSigₗ : ∀ {ℓ} → ∀ {n m} → Sigₗ ℓ n → Sigₗ ℓ m → Sigₗ ℓ (n + m)
-- concatSigₗ {n = zero} {zero} x x₁ = _
-- concatSigₗ {n = zero} {suc m} x x₁ = x₁
-- concatSigₗ {n = suc n} {zero} x x₁ = subst (Sigₗ _) (sym (+-zero (suc n))) x 
-- concatSigₗ {n = suc zero} {suc m} x x₁ = x , (λ _ → x₁)
-- concatSigₗ {n = suc (suc n)} {suc m} x x₁ = (fst x) , λ a → concatSigₗ (snd x a) x₁

-- concatSigₗ-dep : ∀ {ℓ} → ∀ {n m}
--                  → (s : Sigₗ ℓ n)
--                  → (Recₗ s → Sigₗ ℓ m)
--                  → Sigₗ ℓ (n + m)
-- concatSigₗ-dep {n = zero} {m = m} s x = x _
-- concatSigₗ-dep {n = suc n} {m = zero} s x = subst (Sigₗ _) (sym (+-zero (suc n))) s 
-- concatSigₗ-dep {n = suc zero} {m = suc m} s x = s , x
-- concatSigₗ-dep {n = suc (suc n)} {m = suc m} s x =
--   (fst s) , (λ a → concatSigₗ-dep (snd s a) (x ∘ (a ,_ )))

-- splitSigₗ :  ∀ {ℓ} → ∀ {n m}
--                  → Sigₗ ℓ (n + m)
--                   → Σ[ sₙ ∈ Sigₗ ℓ n ] ((Recₗ sₙ → Sigₗ ℓ m))                  
-- splitSigₗ {n = zero} x = _ , const x
-- splitSigₗ {n = suc n} {zero} x = subst (Sigₗ _) (+-zero (suc n)) x , const _
-- splitSigₗ {n = suc zero} {suc m} x = x
-- splitSigₗ {ℓ} {n = suc (suc n)} {suc m} x =
--   let z : (a : fst x) → Σ (Sigₗ ℓ (suc n)) (λ sₙ → Recₗ sₙ → Sigₗ ℓ (suc m))
--       z a =  splitSigₗ ((snd x) a)

--   in (fst x , fst ∘ z) , λ x₁ →  snd (z (fst x₁)) (snd x₁)


-- fromVecOfTypes : ∀ {ℓ} → ∀ {n} → Vec (Type ℓ) n → Sigₗ ℓ n
-- fromVecOfTypes {n = 0} _ = _
-- fromVecOfTypes {n = 1} (x) = head x
-- fromVecOfTypes {n = (suc (suc n))} x = head x , const (fromVecOfTypes (tail x) )




-- -- This functions describes Type of maixmally curried type of last field in record in given signature
-- -- the purpose of Boolean and (List ℕ) arguments, is to controll
-- -- explicity of arguments in generated type:
-- --  * Bool controls the "default" mode (true → implicit , false  → explicit)
-- --  * List ℕ controls "exceptions", it stores the list of spaces
-- --    betwen arguments which are treated in oposite way
-- --    (if this list is to long, the remaing elements are ignored)

-- -- Type-in-sigᵣ : ∀ {ℓ} → ∀ {n} → Sigₗ ℓ n → Type (ℓ-suc ℓ)
-- -- Type-in-sigᵣ {n = zero} x = Lift Unit
-- -- Type-in-sigᵣ {n = suc zero} x = x → Type _
-- -- Type-in-sigᵣ {n = suc (suc n)} x = {!x!}
