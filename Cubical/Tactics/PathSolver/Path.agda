{-# OPTIONS --safe -v testMarkVert:3 -v tactic:3 #-} 
-- -v 3 
module Cubical.Tactics.PathSolver.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Interpolate

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Empty
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order.Recursive

open import Cubical.Data.Sigma.Base


open import Cubical.Reflection.Base renaming (v to 𝒗)
open import Cubical.Reflection.Sugar
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)

import Agda.Builtin.Reflection as R

open import Cubical.Tactics.PathSolver.Reflection
-- open import Cubical.Tactics.Reflection 
open import Agda.Builtin.String
-- open import Agda.Builtin.Char
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.QuoteCubical



_∙f0_ : ∀ {ℓ} {A : Type ℓ} →
         ∀ {x₀ y₀ y₁ z : A}
         → {p₀ : x₀ ≡ y₀} {q₀ : y₀ ≡ z} {q₁ : y₁ ≡ z}
         → {r : x₀ ≡ y₁} {y≡ : y₀ ≡ y₁}
         → Square p₀ (λ _ → y₁)  r y≡
         → Square q₀ q₁ y≡ (λ _ → z)

         → Square (p₀ ∙' q₀) q₁ r λ _ → z
(u ∙f0 v) j i =
  hcomp (λ k → primPOr (~ i) (i ∨ j) (λ _ → u j (~ k)) λ _ → v j i)
        (v j i)

_∙f1_ : ∀ {ℓ} {A : Type ℓ} →
         ∀ {x₁ y₀ y₁ z : A}
         → {p₁ : x₁ ≡ y₁} {q₀ : y₀ ≡ z} {q₁ : y₁ ≡ z}
         → {r : y₀ ≡ x₁} {y≡ : y₀ ≡ y₁}
         → Square (λ _ → y₀) p₁ r y≡
         → Square q₀ q₁ y≡ (λ _ → z)

         → Square q₀ (p₁ ∙' q₁) r λ _ → z
(u ∙f1 v) j i =
    hcomp (λ k → primPOr (~ i) (i ∨ (~ j)) (λ _ → u j (~ k)) λ _ → v j i)
        (v j i)


_∙∙■_∙∙■_ : ∀ {ℓ} {A : Type ℓ} →
         ∀ {x x₀ x₁ x₂ x₃ : A}
         → {p₀ : x₀ ≡ x₁} {p₁ : x₁ ≡ x₂} {p₂ : x₂ ≡ x₃}
           {q₀ : x₀ ≡ x} {q₁ : x₁ ≡ x} {q₂ : x₂ ≡ x} {q₃ : x₃ ≡ x}
         → Square q₀ q₁ p₀ refl  
         → Square q₁ q₂ p₁ refl
         → Square q₂ q₃ p₂ refl
         → Square q₀ q₃ (p₀ ∙∙ p₁ ∙∙ p₂) refl 
_∙∙■_∙∙■_ {x = x} s₀ s₁ s₂ j i = 
  hcomp (λ k → λ where
     (j = i0) → s₀ (~ k) i 
     (j = i1) → s₂ k i 
     (i = i1) → x 
             ) (s₁ j i)

◪→≡ : ∀ {ℓ} {A : Type ℓ} {x y : A} {p p' : x ≡ y} →
           Square p' refl p refl → p ≡ p' 
◪→≡ s i j = 
   hcomp (λ k → λ where
     (j = i0) → s i0 (i ∧ ~ k)
     (i = i1) → s i0 (j ∨ ~ k)
     (i = i0) → s j i ; (j = i1) → s j i) (s j i)

◪→◪→≡ : ∀ {ℓ} {A : Type ℓ} {x y : A} {p₀ p₁ p : x ≡ y}
         → Square p refl p₀ refl
         → Square p refl p₁ refl
         → p₀ ≡ p₁ 
◪→◪→≡ {y = y} {p = p} s₀ s₁ i j =
   hcomp
    (λ k → primPOr (~ i ∨ ~ j ∨ j) i (λ _ →  s₀ j (~ k))
         λ _ → s₁ j (~ k)) y

comp₋₀ : ∀ {ℓ} {A : Type ℓ} →
    {a a₀₀ : A} {a₀₋ : a₀₀ ≡ a}
  {a₁₀ : A} {a₁₋ : a₁₀ ≡ a} 
  {a₋₀ a₋₀' : a₀₀ ≡ a₁₀} 
  → Square a₀₋ a₁₋ a₋₀ refl
  → a₋₀' ≡ a₋₀
  → Square a₀₋ a₁₋ a₋₀' refl
comp₋₀ s p i j =
  hcomp (λ k → primPOr (~ j) (j ∨ i ∨ ~ i) (λ _ → p (~ k) i) λ _ → s i j)  (s i j)

◪mkSq : ∀ {ℓ} {A : Type ℓ} →
    {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ p₁₀ : a₁₀ ≡ a₁₁} 
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ p₀₁ : a₀₁ ≡ a₁₁}
  → {p : a₀₀ ≡ a₁₁}
  → Square p p₀₁ a₀₋ refl
  → Square p₁₀ refl a₁₋ refl
  → Square p p₁₀ a₋₀ refl
  → Square  p₀₁ refl a₋₁ refl
  → Square a₀₋ a₁₋ a₋₀ a₋₁  
◪mkSq {a₁₁ = a₁₁} s₀₋ s₁₋ s₋₀ s₋₁ i j =
  hcomp (λ k → λ where
     (i = i0) → s₀₋ j (~ k)
     (i = i1) → s₁₋ j (~ k)
     (j = i0) → s₋₀ i (~ k)
     (j = i1) → s₋₁ i (~ k))
    a₁₁


data Sequence (n : ℕ) : Type where
 𝓿 : ∀ k → {k ≤ n} → Sequence n
 𝓹 : ∀ k → ∀ {k≤n sk≤n} → 𝓿 k {k≤n} ≡ 𝓿 (suc k) {sk≤n} 


record NPath {ℓ} n (A : Type ℓ) : Type ℓ where
 field
  𝑣 : ∀ k → {k ≤ n} → A
  𝑝 : ∀ k → ∀ {k≤n sk≤n} → 𝑣 k {k≤n} ≡ 𝑣 (suc k) {sk≤n}

 𝑣₀ : A
 𝑣₀ = 𝑣 0
 
 𝑣₁ : {1 ≤ n} → A
 𝑣₁ {k≤} = 𝑣 1 {k≤}

 𝑣₂ : {2 ≤ n} → A
 𝑣₂ {k≤} = 𝑣 2 {k≤}

 𝑣₃ : {3 ≤ n} → A
 𝑣₃ {k≤} = 𝑣 3 {k≤}

 𝑣₄ : {4 ≤ n} → A
 𝑣₄ {k≤} = 𝑣 4 {k≤}

 𝑣₅ : {5 ≤ n} → A
 𝑣₅ {k≤} = 𝑣 5 {k≤}


 𝑣₆ : {6 ≤ n} → A
 𝑣₆ {k≤} = 𝑣 6 {k≤}


 𝑝₀ : ∀ {k≤n sk≤n} → 𝑣 0 {k≤n} ≡ 𝑣 1 {sk≤n} 
 𝑝₀ {k≤n} {sk≤n} = 𝑝 zero {k≤n} {sk≤n}

 𝑝₁ : ∀ {k≤n sk≤n} → 𝑣 1 {k≤n} ≡ 𝑣 2 {sk≤n} 
 𝑝₁ {k≤n} {sk≤n} = 𝑝 (suc zero) {k≤n} {sk≤n}

 𝑝₂ : ∀ {k≤n sk≤n} → 𝑣 2 {k≤n} ≡ 𝑣 3 {sk≤n} 
 𝑝₂ {k≤n} {sk≤n} = 𝑝 (suc (suc zero)) {k≤n} {sk≤n}

 𝑝₃ : ∀ {k≤n sk≤n} → 𝑣 3 {k≤n} ≡ 𝑣 4 {sk≤n} 
 𝑝₃ {k≤n} {sk≤n} = 𝑝 (suc (suc (suc zero))) {k≤n} {sk≤n}

 𝑝₄ : ∀ {k≤n sk≤n} → 𝑣 4 {k≤n} ≡ 𝑣 5 {sk≤n} 
 𝑝₄ {k≤n} {sk≤n} = 𝑝 (suc (suc (suc (suc zero)))) {k≤n} {sk≤n}

 𝑝₅ : ∀ {k≤n sk≤n} → 𝑣 5 {k≤n} ≡ 𝑣 6 {sk≤n} 
 𝑝₅ {k≤n} {sk≤n} = 𝑝 (suc (suc (suc (suc (suc zero))))) {k≤n} {sk≤n}


module _ {ℓ} n (A : Type ℓ) where

 fromNPath : (Sequence n → A) → NPath n A
 fromNPath x .NPath.𝑣 k {k≤n} = x (𝓿 k {k≤n})
 fromNPath x .NPath.𝑝 k {k≤n} {k≤n'} i = x (𝓹 k {k≤n} {k≤n'} i)

 toNPath : NPath n A → (Sequence n → A) 
 toNPath x (𝓿 k {k≤n}) = x .NPath.𝑣 k {k≤n}
 toNPath x (𝓹 k {k≤n} {k≤n'} i) = x .NPath.𝑝 k {k≤n} {k≤n'} i

 IsoFunSequenceNPath : Iso (NPath n A) (Sequence n → A)
 IsoFunSequenceNPath .Iso.fun = toNPath
 IsoFunSequenceNPath .Iso.inv = fromNPath
 IsoFunSequenceNPath .Iso.rightInv b i a@(𝓿 k) = b a
 IsoFunSequenceNPath .Iso.rightInv b i a@(𝓹 k i₁) = b a
 IsoFunSequenceNPath .Iso.leftInv a i .NPath.𝑣 = a .NPath.𝑣
 IsoFunSequenceNPath .Iso.leftInv a i .NPath.𝑝 = a .NPath.𝑝



coh₃helper : ∀ {ℓ} {A : Type ℓ} →
               {x₀ x₁ : A} → {p p₀₀ p₀₁ p₁₀ p₁₁ : x₀ ≡ x₁} → 
               {s₀₀ : Square refl p₀₀ refl p}
               {s₀₁ : Square refl p₀₁ refl p}
               {s₁₀ : Square refl p₁₀ refl p}
               {s₁₁ : Square refl p₁₁ refl p}
               →
               Cube _ _ _ _ (λ _ _ → x₀) (λ _ _ → x₁)
coh₃helper {x₀ = x₀} {p = p} {s₀₀ = s₀₀} {s₀₁} {s₁₀} {s₁₁} i j k =
   hcomp
      (λ z → λ {
        (k = i0) → x₀
       ;(k = i1) → p z
       ;(i = i0)(j = i0) → s₀₀ z k
       ;(i = i1)(j = i0) → s₁₀ z k
       ;(i = i0)(j = i1) → s₀₁ z k
       ;(i = i1)(j = i1) → s₁₁ z k
      }) x₀


comp-coh-helper : ∀ {ℓ} {A : Type ℓ} →
               {x₀ x₁ : A} → {p p₀ p₁ p₂ : x₀ ≡ x₁} → 
               {s₀ : Square refl p₀ refl p}
               {s₁ : Square refl p₁ refl p}
               {s₂ : Square refl p₂ refl p}
               
               →
               Cube ((cong sym (◪→◪→≡ (λ i i₁ → s₀ (~ i₁) (~ i)) (λ i i₁ → s₁ (~ i₁) (~ i))))
                    ∙ (cong sym (◪→◪→≡ (λ i i₁ → s₁ (~ i₁) (~ i)) (λ i i₁ → s₂ (~ i₁) (~ i))))) 
                   (cong sym (◪→◪→≡ (λ i i₁ → s₀ (~ i₁) (~ i)) (λ i i₁ → s₂ (~ i₁) (~ i))))
                  (refl {x = p₀}) (refl {x = p₂}) (λ _ _ → x₀) (λ _ _ → x₁)
comp-coh-helper {x₀ = x₀} {x₁} {p = p} {p₀} {p₁} {p₂} {s₀ = s₀} {s₁} {s₂} =
  λ k i j  → 
   hcomp
     (λ z → λ {
        (j = i0) → x₀
      ;(j = i1) → p (~ k ∨ z ∨ ~ i)
      ;(i = i0) → p₀ j
      ;(i = i1) → hcomp (λ k' → λ {(z = i0) → s₁ (k' ∧ ~ k)  j
                         ;(z = i1) → s₂ k' j
                         ;(j = i0) → x₀
                         ;(j = i1) → p (k' ∧ (~ k ∨ z))
                         }) x₀
      ;(k = i1) → hcomp
           (λ k → λ {(i = i0) → s₀ k j
                    ;(i = i1)(z = i0) → x₀
                    ;(i = i1)(z = i1) → s₂ k j 
                    ;(j = i0) → x₀
                    ;(j = i1) → p (k ∧ (z ∨ (~ i)))
                    }) x₀

       }) (hcomp (λ k' → λ {(i = i0) → s₀ k' j
                      ;(i = i1) → s₁ (k' ∧ ~ k) j
                      ;(j = i0) → x₀
                      ;(j = i1) → p (k' ∧ (~ k ∨ ~ i))
                       }) x₀)
