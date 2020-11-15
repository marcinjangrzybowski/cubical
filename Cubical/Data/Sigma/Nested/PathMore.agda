

{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Sigma.Nested.PathMore where

open import Cubical.Data.Nat

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying

open import Cubical.Data.Sigma.Nested.Path

open import Cubical.HITs.NCube.IntervalPrim

open import Cubical.HITs.NCube.BaseVec



Iso-hlp : ∀ {ℓ} {A B : Type ℓ} → Iso A B → Iso (Σ[ (x₀ , x₁) ∈ A × A ] x₀ ≡ x₁ ) (Σ[ (x₀ , x₁) ∈ B × B ] x₀ ≡ x₁)
Iso-hlp {ℓ} isom = iso (fun' fun) (fun' inv) (sec' fun inv rightInv) (sec' inv fun leftInv)
  where

    open Iso isom

    fun' : {A B : Type ℓ} → (A → B) → (Σ[ (x₀ , x₁) ∈ A × A ] x₀ ≡ x₁ ) → (Σ[ (x₀ , x₁) ∈ B × B ] x₀ ≡ x₁)
    fun' f ((x0 , x1) , p) = ((f x0 , f x1) , cong f p)

    sec' : {A B : Type ℓ} → (f : A → B) → (g : B → A) → (section f g) → section (fun' f) (fun' g)  
    sec' f g x b i = ((x _ i) , (x _ i)) , (λ i₁ → x (snd b i₁) i)

IsoCub' : ∀ {ℓ} {A : Type ℓ} → ∀ n → Iso (NCube n → A ) (Cubeⁿ' n A)


Iso.fun (IsoCub' 0) x = x []
Iso.inv (IsoCub' 0) x _ = x
Iso.rightInv (IsoCub' 0) b = refl
Iso.leftInv (IsoCub' 0) a i [] = a []

IsoCub' {A = A} (suc n) = 
      _ Iso⟨ iso-NCube  ⟩
      _ Iso⟨ Iso-hlp (IsoCub' {A = A} n)  ⟩
      _ Iso⟨ invIso (Cubeⁿ'-elim-iso n) ⟩ _ ∎Iso




toCType : ∀ {ℓ} → ∀ n → (Cubeⁿ' n (Type ℓ)) → T[ CType ℓ n ]
toCType zero A _ = A
toCType (suc n) A i = toCType n (Cubeⁿ'-elim n A i)

fromCType : ∀ {ℓ} → ∀ n → T[ CType ℓ n ] → (Cubeⁿ' n (Type ℓ)) 
fromCType zero x = x 1=1
fromCType (suc n) x = Iso.inv (Cubeⁿ'-elim-iso n) (_ , (λ i → fromCType n (x i))) 

Isoω-CubeΣ-Cubeω : ∀ {ℓ} → {A : Type ℓ}
                      → ∀ n → Isoω (Cubeⁿ' n A) (Cu A n)

Isoω.to (Isoω-CubeΣ-Cubeω zero) x _ = x
Isoω.toω (Isoω-CubeΣ-Cubeω zero) t₀ t₁ x _ i = lowerω (λ _ → x i) 
Isoω.from (Isoω-CubeΣ-Cubeω zero) x = x 1=1
-- Isoω.fromω (Isoω-CubeΣ-Cubeω zero) t₀ t₁ p = p 1=1
Isoω.sec (Isoω-CubeΣ-Cubeω zero) b = refl
Isoω.ret (Isoω-CubeΣ-Cubeω zero) a _ = refl

Isoω-CubeΣ-Cubeω {A = A} (suc n) = Isoω.precomp ww (Cubeⁿ'-elim-iso n)

   where

     module prev = Isoω (Isoω-CubeΣ-Cubeω {A = A} n)

     ww : Isoω (Σ (Cubeⁿ' n _ × Cubeⁿ' n _) (λ a → fst a ≡ snd a))
               (Cu _ (suc n))

     Isoω.to ww x i = prev.to (snd x i) 
     Isoω.toω ww t₀ t₁ x i = prev.toω (snd t₀ i) (snd t₁ i) λ j → snd (x j) i 
     Isoω.from ww x = _ , (λ i → prev.from (x i))
     Isoω.sec ww ((e0 , e1) , p) i = ((prev.sec e0 i) , prev.sec e1 i) , λ j → prev.sec (p j) i
     Isoω.ret ww a i = prev.ret (a i)


Cubeⁿ'-map : ∀ {ℓ ℓb} → {A : Type ℓ} → {B : Type ℓb} → ∀ n → (A → B) → Cubeⁿ' n A → Cubeⁿ' n B
Cubeⁿ'-map n f = Iso.fun (IsoCub' n) ∘ (f ∘_) ∘ Iso.inv (IsoCub' n)

Cubeⁿ'-zip : ∀ {ℓ ℓb} → {A : Type ℓ} → {B : Type ℓb} → ∀ n → Cubeⁿ' n A → Cubeⁿ' n B → Cubeⁿ' n (A × B)
Cubeⁿ'-zip n a b = Iso.fun (IsoCub' n) λ x → (Iso.inv (IsoCub' n) a x) , (Iso.inv (IsoCub' n) b x)

Cubeⁿ'-map2 : ∀ {ℓ ℓb} → {A A' : Type ℓ} → {B : Type ℓb} → ∀ n → (A → A' → B) → Cubeⁿ' n A → Cubeⁿ' n A' → Cubeⁿ' n B
Cubeⁿ'-map2 n f A B = Cubeⁿ'-map n (uncurry f) (Cubeⁿ'-zip n A B)
