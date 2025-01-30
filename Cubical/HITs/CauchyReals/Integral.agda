module Cubical.HITs.CauchyReals.Integral where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Fin

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative

  -- foldl : ∀ {ℓ'} {B : Type ℓ'} → (B → A → B) → B → List A → B

private
  variable
    ℓ : Level
    A B : Type ℓ


foldlFin : ∀ {n} → (B → A → B) → B → (Fin n → A) → B
foldlFin {n = zero} f b v = b
foldlFin {n = suc n} f b v = foldlFin {n = n} f (f b (v fzero)) (v ∘ fsuc)

record Partition[_,_] (a b : ℝ) : Type₀ where 
 field
  len : ℕ
  pts : Fin (1 ℕ.+ len) → ℝ
  a≤pts : ∀ k → a ≤ᵣ pts k 
  pts≤b : ∀ k → pts k ≤ᵣ b
  pts≤pts : (k : Fin len) → pts (finj k) ≤ᵣ pts (fsuc k)

 diffs : Fin len → Σ ℝ (0 ≤ᵣ_) 
 diffs k = _ , x≤y→0≤y-x (pts (finj k)) _ (pts≤pts k)
 
 mesh : ℝ
 mesh = foldlFin maxᵣ 0 (fst ∘ diffs)

 record Sample : Type₀ where
  field
   samples : Fin len → ℝ
   ≤samples : (k : Fin len) → pts (finj k) ≤ᵣ samples k
   samples≤ : (k : Fin len) → samples k ≤ᵣ pts (fsuc k)
   
  samplesΣ : Fin len → Σ[ t ∈ ℝ ] (a ≤ᵣ t ) × (t ≤ᵣ b)
  samplesΣ = {!!}
  
  riemannSum : (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ
  riemannSum f = foldlFin
    (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t a≤t t≤b) ) 0
     (λ k →  samplesΣ k , pts (fsuc k) -ᵣ pts (finj k))

 open Sample public
open Partition[_,_] 

TaggedPartition[_,_] : ℝ → ℝ → Type
TaggedPartition[ a , b ] = Σ (Partition[ a , b ]) Sample


on[_,_]IntegralOf_is_ : ∀ a b → (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ → Type
on[ a , b ]IntegralOf f is s =
  ∀ ((p , t) : TaggedPartition[ a , b ]) →
   ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
     (mesh p <ᵣ rat (fst δ) →
       absᵣ (riemannSum t f -ᵣ s) <ᵣ rat (fst ε))


FTOC : ∀ a b (f F : ∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ)
                 → (∀ x → (≤x : a ≤ᵣ x) → (x≤ : x ≤ᵣ b)
                     → on[ a , x ]IntegralOf
                         (λ r ≤r r≤ → f r ≤r (isTrans≤ᵣ r _ _ r≤ x≤))
                           is F x ≤x x≤)
                 → ∀ x → (≤x : a ≤ᵣ x) → (x≤ : x ≤ᵣ b) →
                     {!derivativeOf F at_is_!}
FTOC = {!!}

-- derivativeOf_at_is_
