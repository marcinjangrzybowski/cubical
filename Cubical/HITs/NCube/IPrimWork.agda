{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.IPrimWork where


import Agda.Primitive.Cubical

open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat renaming (elim to ℕ-elim)
open import Cubical.Data.Nat.Order

open import Cubical.Data.Vec
open import Cubical.Data.Fin renaming (elim to Fin-elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum 

open import Cubical.HITs.Interval hiding (end)
open import Cubical.HITs.PropositionalTruncation renaming (map to mapₚ)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1 hiding (_*_)
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
import Cubical.Foundations.Logic as Lo

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.IntervalPrim



mkPartialEnds : ∀ {ℓ} → ∀ n → {A : T[ CType ℓ (suc n) ]} → {e : Ie n}
               → (x₀ : T[ cu n (A i0) ]) → (x₁ : T[ cu n (A i1) ])
               → T[ Partialⁿ (suc n) (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) A ]
mkPartialEnds zero {A} x₀ x₁ i = zz
  where
    zz : _
    zz (i = i0) = x₀ 1=1
    zz (i = i1) = x₁ 1=1
    
mkPartialEnds (suc n) {A} {e} x₀ x₁ i j = mkPartialEnds n {λ l → A l j} {e = e j} (x₀ j) (x₁ j) i 


mkCylEnds : ∀ {ℓ} → ∀ n → {A : T[ CType ℓ (suc n) ]} → {e : Ie n}
               → (x₀ : T[ cu n (A i0) ]) → (x₁ : T[ cu n (A i1) ])
               → T[ Partialⁿ (suc n) (↑Expr 1 e ∧ⁿ (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) A ]
mkCylEnds n {A} {e = e} x₀ x₁ = ⊆'2-∧ (↑Expr 1 e) (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) (mkPartialEnds n {A} {e = e} x₀ x₁)

Cylω : ∀ {ℓ} → ∀ n → (A : T[ CType ℓ (suc n) ]) → (e : Ie n)
               → (x₀ : T[ cu n (A i0) ]) → (x₁ : T[ cu n (A i1) ])
               → ωType 
Cylω n A e x₀ x₁ = Partialⁿ-Sub (suc n) {A = A}
                        {i = ↑Expr 1 e}
                        {j = (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)}
                        (mkCylEnds n x₀ x₁) 

attachEndsToCylω : ∀ {ℓ} → ∀ n → (A : T[ CType ℓ (suc n) ]) → (e : Ie n)
               → (x₀ : T[ cu n (A i0) ]) → (x₁ : T[ cu n (A i1) ]) → T[ Cylω n A e x₀ x₁ ]
                → T[ Partialⁿ (suc n) ((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ (↑Expr 1 e)  ) A ]
attachEndsToCylω zero _ e x₀ x₁ x i = zz 
  where
    zz : _
    zz (i = i0) = x₀ 1=1
    zz (i = i1) = x₁ 1=1
    zz (e = i1) = outS (x i 1=1)
attachEndsToCylω (suc n) A e x₀ x₁ x i j =
  attachEndsToCylω n (λ l → A l j) (e j) (x₀ j) (x₁ j) (λ l → x l j) i

attachEndsToBrdω : ∀ {ℓ} → ∀ n → (A : T[ CType ℓ (suc n) ]) 
                    → (x₀ : T[ cu n (A i0) ]) → (x₁ : T[ cu n (A i1) ])
                    → T[ Cylω n A (boundaryExpr n) x₀ x₁ ]
                    → T[ Boundaryω (suc n) A ]
attachEndsToBrdω zero A = attachEndsToCylω zero A (boundaryExpr zero)
attachEndsToBrdω (suc n) A = attachEndsToCylω (suc n) A (boundaryExpr (suc n))


deattachEndsFromCylω : ∀ {ℓ} → ∀ n → (A : T[ CType ℓ (suc n) ]) → (e : Ie n)               
                → T[ Partialⁿ (suc n) ((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ (↑Expr 1 e)  ) A ]
                → Σω (T[ cu n (A i0) ] ×ω  T[ cu n (A i1) ] ) λ a → T[ Cylω n A e (proj₁ω a) (proj₂ω a)  ] 
deattachEndsFromCylω zero A e x = (pairω (x i0) (x i1)) ,ω ww

  where
    ww : T[ Cylω zero A e (x i0) (x i1) ]
    ww i i=1 = inS ((⊆I→⊆'I 1 (⊆I-∨2 {1} ((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) (↑Expr 1 e) ) x) i i=1)

deattachEndsFromCylω (suc n) A e x =
    (pairω (λ i → proj₁ω (fstω (pp i))) (λ i → proj₂ω (fstω (pp i)))) ,ω
      λ i j → sndω (pp j) i
  where
    pp : (j : I) → _
    pp j = deattachEndsFromCylω n (λ l → A l j) (e j) (λ l → x l j) 

