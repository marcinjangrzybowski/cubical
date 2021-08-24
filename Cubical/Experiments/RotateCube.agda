{-# OPTIONS --safe #-}
module Cubical.Experiments.RotateCube where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.GroupoidLaws


open import Cubical.Foundations.Univalence

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Foundations.CartesianKanOps

private
  variable
    ℓ : Level
    A : Type ℓ


module SquareRotation
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} where

  ◰ = Square a₀₋ a₁₋ a₋₀ a₋₁
  ◳ = Square (sym a₋₀) (sym a₋₁) a₁₋ a₀₋
  
  
  ≡rotateSquare : ◰ ≡ ◳
  ≡rotateSquare i =
    Square (invSides-filler a₀₋ a₋₀ i)
           (invSides-filler (sym a₋₁) (sym a₁₋) (~ i))
           (invSides-filler a₁₋ (sym a₋₀) (~ i))
           (invSides-filler a₋₁ (sym a₀₋) i)

  rotateSquare : ◰ → ◳
  rotateSquare x i j = x (~ j) i

  rotateSquare⁻ : ◳ → ◰ 
  rotateSquare⁻ x i j = x j (~ i)


  rotateSquareIso : Iso ◰ ◳
  Iso.fun rotateSquareIso = rotateSquare
  Iso.inv rotateSquareIso = rotateSquare⁻
  Iso.rightInv rotateSquareIso _ = refl
  Iso.leftInv rotateSquareIso _ = refl

 
  rotateSquare≃ : ◰ ≃ ◳
  rotateSquare≃ = isoToEquiv rotateSquareIso  


  squareTwisting : (x : ◰) → PathP (λ i → ≡rotateSquare i) x (rotateSquare x)
  squareTwisting  x k i j =
         hcomp
            (λ l → λ {
                    (k = i0) → x (i ∧ l) (j ∧ l)
                  ; (k = i1) → x (~ j ∧ l) (i ∧ l)
                  ; (i = i0) → hcomp
                                (λ w →
                                  λ { (l = i0) → x i0 i0
                                    ; (k = i0) → x i0 (w ∧ j ∧ l)
                                    ; (k = i1) → x (w ∧ ~ j ∧ l) i0                                    
                                    ; (j = i0) → x (w ∧ l ∧ k) i0                                    
                                    ; (j = i1) → x i0 (w ∧ l ∧ (~ k))
                                    })
                                (x i0 i0)
                  ; (i = i1) → hcomp
                                (λ w →
                                  λ { (l = i0) → x i0 i0
                                    ; (k = i0) → x l (l ∧ (j ∨ ~ w))
                                    ; (k = i1) → x ((~ w ∨ ~ j) ∧ l) l                                    
                                    ; (j = i0) → x l ( (k ∨ ~ w) ∧ l)                                   
                                    ; (j = i1) → x ((~ k ∨ ~ w) ∧ l) l
                                    })
                                (x l l)
                  ; (j = i0) → hcomp
                                (λ w →
                                  λ { (l = i0) → x (~ w) i0
                                    ; (k = i0) → x ((i ∧ l) ∨ ~ w) i0
                                    ; (k = i1) → x (~ w ∨ l) (i ∧ l ∧ w)                                    
                                    ; (i = i0) → x ((~ w) ∨ (l ∧ k)) i0                                    
                                    ; (i = i1) → x (l ∨ ~ w) (k ∧ w ∧ l)
                                    })
                                (x i1 i0)
                  ; (j = i1) → hcomp
                                (λ w →
                                  λ { (l = i0) → x i0 (~ w)
                                    ; (k = i0) → x ( i ∧ l ∧ w) (l ∨ ~ w)
                                    ; (k = i1) → x i0 ((i ∧ l) ∨ ~ w)                                     
                                    ; (i = i0) → x i0 ((l ∧ ~ k) ∨ ~ w)                                    
                                    ; (i = i1) → x ((~ k) ∧ l ∧ w) (l ∨ ~ w)
                                    })
                                (x i0 i1)
                   })
            (x i0 i0)



  rotateSquare≃-≡rotateSquare-lemma :
        rotateSquare≃
          ≡
        pathToEquiv ≡rotateSquare
  rotateSquare≃-≡rotateSquare-lemma = equivEq (funExt p)
    where

      p : (x : Square _ _ _ _) → rotateSquare x ≡ pathToEquiv ≡rotateSquare .fst x
      p x k i j =
         hcomp
           (λ l →
             primPOr k (~ k ∨ i ∨ ~ i ∨ j ∨ ~ j)
              (λ _ → coe0→i (λ i' → ≡rotateSquare i') l x i j)
               λ _ → squareTwisting x l i j
               )
           (x i j)


open SquareRotation

rotateSquare≃⁴-≡-idEquiv :
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  → idEquiv (Square a₀₋ a₁₋ a₋₀ a₋₁) ≡ (
      _ ≃⟨ rotateSquare≃ ⟩
      _ ≃⟨ rotateSquare≃ ⟩
      _ ≃⟨ rotateSquare≃ ⟩
      _ ≃⟨ rotateSquare≃ ⟩ idEquiv _)

rotateSquare≃⁴-≡-idEquiv = equivEq refl

