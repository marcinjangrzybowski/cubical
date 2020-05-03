{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.Globe where


open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat
-- open import Cubical.Data.Prod
open import Cubical.Data.List
open import Cubical.Data.Sigma

open import Cubical.HITs.Interval
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.Base

Globeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n} → (S (-1+ n) → A) → Type ℓ

northGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
                 → ∀ (bd : (S (-1+ (suc n)) → A))
                 → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → north))

southGlobeⁿ : ∀ {ℓ} → {A : Type ℓ} →  ∀ {n}
                 → ∀ (bd : (S (-1+ (suc n)) → A))
                 → Globeⁿ {A = A} {n = n} (bd ∘ (λ _ → south))
                 
Globeⁿ {A = A} {n = zero} bd = A 
Globeⁿ {A = A} {n = suc n} bd =
             PathP
             (λ i → Globeⁿ {n = n} ( bd ∘ (λ x → merid x i)))
             (northGlobeⁿ {A = A} {n = n} bd)
             (southGlobeⁿ {A = A} {n = n} bd)


north-south-const : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ {n} → (a : A)
                     →  (northGlobeⁿ {n = n} (λ _ → a))
                        ≡ 
                        (southGlobeⁿ {n = n} (λ _ → a))

northGlobeⁿ {n = zero} bd = bd north
northGlobeⁿ {ℓ} {A} {suc zero} bd _ = bd north
northGlobeⁿ {ℓ} {A} {suc (suc n)} bd = north-south-const (bd north)

southGlobeⁿ {n = zero} bd = bd south
southGlobeⁿ {n = suc zero} bd _ = bd south
southGlobeⁿ {n = suc (suc n)} bd = north-south-const (bd south)

north-south-const {n = zero} a = refl
north-south-const {n = suc zero} a = refl
north-south-const {n = suc (suc n)} a = refl


-- globTo : ∀ {ℓ} → (A : Type ℓ) → ∀ n → A → Σ _ (Globeⁿ {A = A} {n})
-- fst (globTo A n x) = const x
-- snd (globTo A zero x) = x
-- snd (globTo A (suc n) x) = north-south-const x

-- globFrom : ∀ {ℓ} → (A : Type ℓ) → ∀ n → Σ _ (Globeⁿ {A = A} {n}) → A
-- globFrom {ℓ} A zero (bd , x) = x
-- globFrom {ℓ} A (suc n) (bd , x) = bd north

-- globRet : ∀ {ℓ} → (A : Type ℓ) → ∀ n → ∀ a → globFrom A n (globTo A n a) ≡ a
-- globRet {ℓ} A zero a = refl
-- globRet {ℓ} A (suc n) a = refl

-- globSec : ∀ {ℓ} → (A : Type ℓ) → ∀ n → ∀ b → globTo A n (globFrom A n b) ≡ b
-- fst (globSec {ℓ} A zero (_ , _) i) ()
-- snd (globSec {ℓ} A zero (_ , x) i) = x

-- fst (globSec {ℓ} A (suc zero) (_ , p) i) north = p i0
-- fst (globSec {ℓ} A (suc zero) (_ , p) i) south = p i
-- snd (globSec {ℓ} A (suc zero) (_ , p) i) i₁ = p (i ∧ i₁)

-- fst (globSec {ℓ} A (suc (suc zero)) (bd , p) i) north = bd north
-- fst (globSec {ℓ} A (suc (suc zero)) (bd , p) i) south = bd (merid north i)
-- fst (globSec {ℓ} A (suc (suc zero)) (bd , p) i) (merid north i₁) = bd (merid north (i ∧ i₁)) 
-- fst (globSec {ℓ} A (suc (suc zero)) (bd , p) i) (merid south i₁) =
--        hcomp
--        (λ k → λ {
--            (i = i0) → bd (merid north (i₁ ∧ (~ k)))
--         ;  (i = i1) → bd (merid south i₁)
--         ;  (i₁ = i0) → bd north
--         ;  (i₁ = i1) → bd (merid north (i ∨ (~ k)))
--           })
--        (p i₁ i)
       
-- snd (globSec {ℓ} A (suc (suc zero)) (bd , p) i) i₁ j = {!c!}

-- globSec {ℓ} A (suc (suc (suc n))) b i = {!!}

-- glob= : ∀ {ℓ} → (A : Type ℓ) → ∀ n
--         → Iso (A) (Σ (_) (Globeⁿ {A = A} {n = n} ))
-- glob= A n = iso (globTo A n) (globFrom A n) (globSec A n) (globRet A n)


globTo : ∀ {ℓ} → (A : Type ℓ) → ∀ n → (NCube n → A) → Σ _ (Globeⁿ {A = A} {n})
fst (globTo A zero x) ()
snd (globTo A zero x) = x _
fst (globTo A (suc n) x) north = x corner0
fst (globTo A (suc n) x) south = x corner1
fst (globTo A (suc n) x) (merid a i) = x (corner0-≡-corner1 i)
snd (globTo A (suc zero) x) i = x (inside i , tt)
snd (globTo A (suc (suc n)) x) i  = ?

globFrom : ∀ {ℓ} → (A : Type ℓ) → ∀ n → Σ _ (Globeⁿ {A = A} {n}) → (NCube n → A)
globFrom {ℓ} A zero x x₁ = snd x
globFrom {ℓ} A (suc zero) x (end false , _) = snd x i0 
globFrom {ℓ} A (suc zero) x (end true , _) = snd x i1
globFrom {ℓ} A (suc zero) x (inside i , _) = snd x i
globFrom {ℓ} A (suc (suc n)) x (end false , snd₁) =
  globFrom A (suc n) ((λ x₁ → fst x (merid x₁ i0)) , (snd x i0)) snd₁ 
globFrom {ℓ} A (suc (suc n)) x (end true , snd₁) =
  globFrom A (suc n) ((λ x₁ → fst x (merid x₁ i1)) , (snd x i1)) snd₁
globFrom {ℓ} A (suc (suc n)) x (inside i , snd₁) =
  globFrom A (suc n) ((λ x₁ → fst x (merid x₁ i)) , (snd x i)) snd₁

globRet : ∀ {ℓ} → (A : Type ℓ) → ∀ n → ∀ a → globFrom A n (globTo A n a) ≡ a
globRet {ℓ} A = {!!}

globSec : ∀ {ℓ} → (A : Type ℓ) → ∀ n → ∀ b → globTo A n (globFrom A n b) ≡ b
globSec = {!!}

glob= : ∀ {ℓ} → (A : Type ℓ) → ∀ n
        → Iso (NCube n → A) (Σ (_) (Globeⁿ {A = A} {n = n} ))
glob= A n = iso (globTo A n) (globFrom A n) (globSec A n) (globRet A n)
