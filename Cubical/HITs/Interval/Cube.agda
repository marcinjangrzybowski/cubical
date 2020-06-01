{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Interval.Cube where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Data.Vec
open import Cubical.Data.List
open import Cubical.Data.Bool

open import Cubical.Foundations.Everything

open import Cubical.HITs.Interval.Base renaming (elim to I-elim ; rec to I-rec)



Typeⁿ' : ℕ → Level → Typeω
Typeⁿ' zero ℓ = I → Type ℓ
Typeⁿ' (suc n) ℓ = I → Typeⁿ' n ℓ

NCube : ℕ → Type₀
NCube = Vec Interval

Typeⁿ : ℕ → ∀ ℓ → Type (ℓ-suc ℓ)
Typeⁿ n ℓ = NCube n → Type ℓ

Π : ∀ {ℓ ℓ'} → {A : Type ℓ} → (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Π B = ∀ x → B x


_∘∷_ : ∀ {ℓ ℓ'} → {A : Type ℓ} → {B : Type ℓ'}
       → ∀ {n}
       → (Vec A (suc n) → B) → A → (Vec A n → B)
A ∘∷ a = A ∘ (a ∷_ )

_∷ₗ_ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → Vec A n → A → Vec A (suc n)
_∷ₗ_ {n = zero} x x₁ = x₁ ∷ []
_∷ₗ_ {n = suc n} x x₁ = head x ∷ ((tail x) ∷ₗ x₁)

_∘∷ₗ_ : ∀ {ℓ ℓ'} → {A : Type ℓ} → {B : Type ℓ'}
       → ∀ {n}
       → (Vec A (suc n) → B) → A → (Vec A n → B)
A ∘∷ₗ a = A ∘ (_∷ₗ a )

Typeⁿ'→Typeⁿ : ∀ {ℓ} → ∀ n →  Typeⁿ' n ℓ → Typeⁿ (suc n) ℓ
Typeⁿ'→Typeⁿ zero x x₁ = I-rec (λ i → x i) (head x₁)
Typeⁿ'→Typeⁿ (suc n) x x₁ = I-rec (λ i →  Typeⁿ'→Typeⁿ n (x i) (tail x₁)) (head x₁)

Typeⁿ→Typeⁿ' : ∀ {ℓ} → ∀ n → Typeⁿ (suc n) ℓ → Typeⁿ' n ℓ
Typeⁿ→Typeⁿ' zero x i = x (seg i ∷ [])
Typeⁿ→Typeⁿ' (suc n) x i = Typeⁿ→Typeⁿ' n (x ∘∷ (seg i))



Sig : ∀ ℓ → ℕ → Type (ℓ-suc ℓ)
Sig ℓ 0 = Lift Unit
Sig ℓ 1 = Type ℓ
Sig ℓ (suc (suc n)) = Σ[ Ty ∈ Type ℓ ]  (Ty → Sig ℓ (suc n))

trim-sig :  ∀ {ℓ} → ∀ {n} → (s : Sig ℓ n) → Sig ℓ (predℕ n)
trim-sig {n = 0} s = lift _
trim-sig {n = 1} s = lift _
trim-sig {n = 2} s = fst s
trim-sig {n = suc (suc (suc n))} s = fst s , λ x → trim-sig (snd s x)

-- Π-sig : ∀ {ℓ} → ∀ {n} → (s : Sig ℓ n) → Type ℓ
-- Π-sig {n = 0} s = Lift Unit
-- Π-sig {n = 1} s = s
-- Π-sig {n = suc (suc n)} s = (a : fst s) → Π-sig (snd s a)

-- Π-sig-pick : ∀ {ℓ} → List ℕ → ∀ {n} → (s : Sig ℓ n) → Type ℓ
-- Π-sig-pick xs {0} s = Lift Unit
-- Π-sig-pick xs {1} s = s
-- Π-sig-pick [] {suc (suc n)} s = {a : fst s} → Π-sig-pick [] (snd s a)
-- Π-sig-pick (zero ∷ xs) {suc (suc n)} s = (a : fst s) → Π-sig-pick xs (snd s a)
-- Π-sig-pick (suc x ∷ xs) {suc (suc n)} s = {a : fst s} → Π-sig-pick (x ∷ xs) (snd s a)


Σ-sig : ∀ {ℓ} → ∀ {n} → Sig ℓ n → Type ℓ
Σ-sig {n = 0} x = Lift Unit
Σ-sig {n = 1} x = x
Σ-sig {n = suc (suc n)} x = Σ (fst x) (Σ-sig ∘ snd x) 

Type-in-sig : ∀ {ℓ} → Bool → List ℕ → ∀ {n} → Sig ℓ n → Type (ℓ-suc ℓ)
Type-in-sig _ _ {zero} _ = Type _
Type-in-sig false [] {suc zero} x = x → Type _
Type-in-sig {ℓ} true [] {suc zero} x = {_ : x} → Type ℓ

Type-in-sig {ℓ} false (zero ∷ _) {suc zero} x = {_ : x} → Type ℓ
Type-in-sig true (zero ∷ _) {suc zero} x = x → Type _

Type-in-sig false (suc x₁ ∷ xs) {suc zero} x = x → Type _
Type-in-sig {ℓ} true (suc x₁ ∷ xs) {suc zero} x = {_ : x} → Type ℓ

Type-in-sig false [] {suc (suc n)} x = (a : fst x) → Type-in-sig false [] (snd x a) 
Type-in-sig true [] {suc (suc n)} x = {a : fst x} → Type-in-sig true [] (snd x a)
Type-in-sig false (zero ∷ xs) {suc (suc n)} x = {a : fst x} → Type-in-sig false (xs) (snd x a)
Type-in-sig false (suc k ∷ xs) {suc (suc n)} x = (a : fst x) → Type-in-sig false (k ∷ xs) (snd x a)
Type-in-sig true (zero ∷ xs) {suc (suc n)} x = (a : fst x) → Type-in-sig true (xs) (snd x a)
Type-in-sig true (suc k ∷ xs) {suc (suc n)} x = {a : fst x} → Type-in-sig true (k ∷ xs) (snd x a)

-- Type-in-sig-impl : ∀ {ℓ} → ∀ {n} → Sig ℓ n → Type (ℓ-suc ℓ)
-- Type-in-sig-impl {n = zero} x = Type _
-- Type-in-sig-impl {ℓ} {n = suc zero} x = ∀ {a : x} → Type ℓ
-- Type-in-sig-impl {n = suc (suc n)} x = {a : fst x} → Type-in-sig-impl ((snd x) a)

pop-Type : ∀ {ℓ} → ∀ {n}
           → (b : Bool) → (l : List ℕ) → (A : Sig ℓ n)
           → Type-in-sig b l (trim-sig A)
pop-Type {n = zero} _ _ _ = Lift Unit
pop-Type {n = suc zero} _ _ A = A
pop-Type {n = suc (suc zero)} false [] A = snd A
pop-Type {n = suc (suc zero)} true [] A {a} = snd A a
pop-Type {n = suc (suc zero)} false (zero ∷ l) A {a} = snd A a
pop-Type {n = suc (suc zero)} false (suc k ∷ l) A = snd A
pop-Type {n = suc (suc zero)} true (zero ∷ l) A = snd A
pop-Type {n = suc (suc zero)} true (suc k ∷ l) A {a} = snd A a
pop-Type {n = suc (suc (suc n))} false [] A a = pop-Type false [] (snd A a)
pop-Type {n = suc (suc (suc n))} true [] A {a} = pop-Type true [] (snd A a)
pop-Type {n = suc (suc (suc n))} false (zero ∷ l) A {a} = pop-Type false l (snd A a)
pop-Type {n = suc (suc (suc n))} false (suc k ∷ l) A a = pop-Type false (k ∷ l) (snd A a)
pop-Type {n = suc (suc (suc n))} true (zero ∷ l) A a = pop-Type true l (snd A a)
pop-Type {n = suc (suc (suc n))} true (suc k ∷ l) A {a} = pop-Type true (k ∷ l) (snd A a)

pop-Type-overΣ : ∀ {ℓ} → ∀ {n}
                     → (A : Sig ℓ n)
                     →  Σ-sig (trim-sig A) → Type ℓ
pop-Type-overΣ {n = zero} _ _ = Lift Unit
pop-Type-overΣ {n = suc zero} A _ = A
pop-Type-overΣ {n = suc (suc zero)} x a = snd x a
pop-Type-overΣ {n = suc (suc (suc n))} x a = pop-Type-overΣ (snd x (fst a)) (snd a)


combineSig : ∀ {ℓ} → ∀ {n} → (I → Sig ℓ n) → Sig ℓ (n * 3)
combineSig {n = 0} x = lift _
combineSig {n = 1} x = (x i0) , (λ x0 → (x i1) , λ x1 → PathP x x0 x1)
combineSig {n = suc (suc n)} x =
             (fst (x i0)) ,
     (λ x0 → (fst (x i1)) ,
     (λ x1 → (PathP (λ i → fst (x i)) x0 x1) ,
      λ p → combineSig λ i → snd (x i) (p i) ))

3^ : ℕ → ℕ
3^ zero = suc zero
3^ (suc x) = (3^ x) * 3


CubeIn-Sig : ∀ {ℓ} → ∀ {n} → Typeⁿ n ℓ → Sig ℓ (3^ n)
CubeIn-Sig {n = zero} x = x []
CubeIn-Sig {n = suc n} x = combineSig (λ i → CubeIn-Sig (x ∘∷ (seg i)))


PathPⁿ-explicit : ∀ {ℓ} → ∀ {n}
                 → (A : Typeⁿ n ℓ)
                  → Type-in-sig false [] (trim-sig (CubeIn-Sig A) )
PathPⁿ-explicit x = pop-Type _ _ (CubeIn-Sig x)

argsToPick : ℕ → List ℕ
argsToPick zero = []
argsToPick (suc x) = predℕ (3^ x) ∷ predℕ (3^ x) ∷ argsToPick x 

PathPⁿ : ∀ {ℓ} → ∀ {n}
                 → (A : Typeⁿ n ℓ)
                  → Type-in-sig true (argsToPick n) (trim-sig (CubeIn-Sig A) )
PathPⁿ x = pop-Type _ _ (CubeIn-Sig x)

Pathⁿ : ∀ {ℓ} → ∀ n
                 → {A : Type ℓ}
                  → Type-in-sig true (argsToPick n) (trim-sig (CubeIn-Sig {n = n} (const A)) )
Pathⁿ n {x} = PathPⁿ (const x)

BoundaryPⁿ : ∀ {ℓ} → ∀ {n}
                 → (A : Typeⁿ n ℓ)
                 → Type ℓ
BoundaryPⁿ A = Σ-sig (trim-sig (CubeIn-Sig A) )

Boundaryⁿ : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Type ℓ
Boundaryⁿ n A = BoundaryPⁿ {n = n} (const A)

InsideOfP :  ∀ {ℓ} → ∀ {n}
                 → (A : Typeⁿ n ℓ)
                 → BoundaryPⁿ A → Type ℓ
InsideOfP A = pop-Type-overΣ (CubeIn-Sig A)


Σ-Bd-Ins : ∀ {ℓ} → ∀ {n} → (A : Typeⁿ n ℓ) → Type ℓ
Σ-Bd-Ins A = Σ (BoundaryPⁿ A) (InsideOfP A)


Boundaryⁿ-ends : ∀ {ℓ} → ∀ {n}
                 → (A : Typeⁿ (suc n) ℓ)
                 → BoundaryPⁿ A
                 → (b : Bool) → Σ-Bd-Ins (A ∘∷ (end b) ) 
Boundaryⁿ-ends {n = zero} A x false = _ , fst x
Boundaryⁿ-ends {n = zero} A x true = _ , snd x
Boundaryⁿ-ends {n = suc zero} A x false = (fst x , fst (snd (snd (snd x)))) ,
                                          {!fst (snd (snd x))!}
Boundaryⁿ-ends {n = suc zero} A x true = {!!}
Boundaryⁿ-ends {n = suc (suc n)} = {!!}


from-ends-Path :  ∀ {ℓ} → ∀ {n} → (A : Typeⁿ (suc n) ℓ)
                  → Iso ((i' : Interval) → Σ-Bd-Ins (A ∘∷ i'))
                        (Σ-Bd-Ins A)

IsoCub : ∀ {ℓ} → ∀ n → (A : Typeⁿ n ℓ)
           → Iso (Π A) (Σ (BoundaryPⁿ A) (InsideOfP A))

Iso.fun (IsoCub 0 A) x = lift _ , x []
Iso.inv (IsoCub 0 A) x [] = snd x 
Iso.rightInv (IsoCub 0 A) b = refl
Iso.leftInv (IsoCub 0 A) a i [] = a []

-- Iso.fun (IsoCub 1 A) x = (x _ , x _) , λ i →  x (seg i ∷ [])  
-- Iso.inv (IsoCub 1 A) x (x₁ ∷ []) = I-elim (λ v → (A ∘∷ v) []) (snd x) x₁
-- Iso.rightInv (IsoCub 1 A) _ = refl
-- Iso.leftInv (IsoCub 1 A) a i (x ∷ []) = intervalEta {A = (λ v → (A ∘∷ v) []) } (λ _ → a _) i x 

-- IsoCub 2 A = {!!}

IsoCub (suc n) A = iso funS invS secS retS

   where
     prev : (i' : Interval) → Iso (Π (λ x → A (i' ∷ x)))
                        (Σ (BoundaryPⁿ (λ x → A (i' ∷ x)))
                         (InsideOfP (λ x → A (i' ∷ x))))
     prev i' = IsoCub n (A ∘∷ i' )

     sec : ∀ i → _
     sec i = Iso.rightInv (prev i)

     ret : ∀ i → _
     ret i = Iso.leftInv (prev i)
     

     funS : Π A → Σ (BoundaryPⁿ A) (InsideOfP A)
     funS x = Iso.fun (from-ends-Path A) (λ i' → (Iso.fun (prev i')) (x ∘ (i' ∷_))) 

     invS : Σ (BoundaryPⁿ A) (InsideOfP A) → Π A
     invS x (i' ∷ c) = (Iso.inv (prev i')) (Iso.inv (from-ends-Path A) x i') c

     secS : section funS invS
     secS = {!!}

     retS : retract funS invS
     retS = {!!}


Iso.fun (from-ends-Path {n = zero} A) x = snd (x (seg i0) , snd (x (seg i0))
                                         , snd (x (seg i1))) , λ i → snd (x (seg i))
Iso.inv (from-ends-Path {n = zero} A) x i' = (lift _) , I-elim (λ v → A (v ∷ []) ) (snd x) i'
Iso.rightInv (from-ends-Path {n = zero} A) b = refl
Iso.leftInv (from-ends-Path {n = zero} A) a i i' =
   (lift _) , (intervalEta {A = λ x → A (x ∷ [])} (snd ∘ a) i i')

from-ends-Path {n = 1} A = {!!}

fst (Iso.fun (from-ends-Path {n = suc (suc n)} A) x) = {!!}
snd (Iso.fun (from-ends-Path {n = suc (suc n)} A) x) = {!!}
Iso.inv (from-ends-Path {n = suc (suc n)} A) = {!!}
Iso.rightInv (from-ends-Path {n = suc (suc n)} A) = {!!}
Iso.leftInv (from-ends-Path {n = suc (suc n)} A) = {!!}

  -- let
  --     w11 : ((i' : Interval) → Σ-Bd-Ins (λ x → A (i' ∷ x))) ≡
  --            ((i' : Interval) → Π λ z → A (i' ∷ z))
  --     w11 i = (i' : Interval) → isoToPath (IsoCub (suc n) (λ x → A (i' ∷ x))) (~ i)

  --     w1 : Iso ((i' : Interval) → Σ-Bd-Ins (A ∘∷ i')) ((i' : Interval) → Π (λ z → A (i' ∷ z)))
  --     w1 = pathToIso w11

  --     w22 : {!!}
  --     w22 = {!!}

  --     w2 = Iso {!!} (Σ-Bd-Ins A)
  --     w2 = {!!}
  -- in  compIso w1 (compIso w22 w2)  

-- generated cube is definationaly equall to one from Prelude
Cube-test : ∀ {ℓ} → ∀ (A : Type ℓ) → 
  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
  (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
  (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
  → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
    ≡
    Pathⁿ 3 _ _ _ _ _ _
Cube-test _ _ _ _ _ _ _ = refl



test-3 : ∀ {ℓ} → ∀ (A : Type ℓ)
             → (PathPⁿ {n = 2} (const A)) ≡ {!Pathⁿ 3!}
test-3 = {!!}

-- PathPⁿ-Ty : ∀ {ℓ} → ∀ {n} → Typeⁿ n ℓ → Type ℓ
-- PathPⁿ-Ty {n = n} x = Π-sig-pick (argsToPick n) (CubeIn-Sig x) 
--   where
--     argsToPick : ℕ → List ℕ
--     argsToPick zero = []
--     argsToPick (suc x) = predℕ (3^ x) ∷ predℕ (3^ x) ∷ argsToPick x 


-- PathPⁿ-test : ∀ {ℓ} → ∀ (A : Typeⁿ' 3 ℓ) → PathPⁿ-Ty {n = 4} (Typeⁿ'→Typeⁿ {ℓ} 3 A)
-- PathPⁿ-test A a a₁ a₂ a₃ a₄ a₅ a₆ a₇ = {!!}

-- PathPⁿ-test-3' : ∀ {ℓ} → ∀ (A : Type ℓ) → {!!}
              
-- PathPⁿ-test-3'  A = {! !}


-- PathPⁿ-test-3 : ∀ {ℓ} → ∀ (A : Type ℓ) →
--                     PathPⁿ-Ty {n = 2} (const A)   
              
-- PathPⁿ-test-3  A = {!Square {A = A}!}

-- -- PathPⁿ-test : ∀ {ℓ} → ∀ (A : Typeⁿ' 3 ℓ) → PathPⁿ {n = 4} (Typeⁿ'→Typeⁿ {ℓ} 3 A)
-- -- PathPⁿ-test A a a₁ a₂ a₃ a₄ a₅ a₆ a₇ = {!!}

-- -- 1 - 0,0
-- -- 2 - 2,2,0,0
-- -- 3 - 8,8,2,2,0,0
-- -- 4 - 26,26,8,8,2,2,0,0
