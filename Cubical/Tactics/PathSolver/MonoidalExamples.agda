{-# OPTIONS --safe #-} 

module Cubical.Tactics.PathSolver.MonoidalExamples where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary

-- open import Cubical.Algebra.Group.Free

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ

open import Cubical.Data.Sigma

open import Cubical.Reflection.Base renaming (v to 𝒗)
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection 
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Cubical.Tactics.Reflection.Utilities


open import Cubical.Tactics.PathSolver.CongComp
open import Cubical.Tactics.PathSolver.CuTerm

open import Cubical.Tactics.PathSolver.QuoteCubical
open import Cubical.Tactics.PathSolver.Dimensions
open import Cubical.Tactics.PathSolver.MonoidalSolver


private
  variable
    ℓ : Level
    A B : Type ℓ


module E0 {x y z w : A}
  (p : x ≡ y)
  (q : y ≡ z)
  (r : z ≡ w) (f : A → A) (f₂ : A → A → A) (f₄ : A → {A} → A → A → A) where




 e-refl : refl ≡ refl
 e-refl = simplifyFill (refl {x = x})

 e-refl≡refl : e-refl ≡ refl
 e-refl≡refl = refl
 
 e0 : (((p ∙∙ q ∙∙ sym q ) ∙∙ q  ∙∙ r)) ≡ (p ∙' (q ∙' r))
 e0 = simplifyPath ((p ∙∙ q ∙∙ sym q ) ∙∙ q  ∙∙ r)


 e1 : (p ∙∙ q ∙∙ r ) ≡ p ∙' (q ∙' r)
 e1 = simplifyPath (p ∙∙ q ∙∙ r )

 e1' : (refl ∙∙ q ∙∙ r ) ≡ q ∙' r
 e1' = simplifyPath (refl ∙∙ q ∙∙ r )


 e2 : (p ∙∙ refl ∙∙ refl ) ≡ p
 e2 = simplifyPath (p ∙∙ refl ∙∙ refl )



 e3 : _ ≡ _
 e3 = simplifyPath (cong f p ∙ cong f q ∙ (refl ∙ cong f r))

 e4 : _ ≡ cong₂ f₂ q p
 e4 = simplifyPath (cong (f₂ y) p ∙ cong (flip f₂ y) q )



 e5 : _ ≡ λ 𝓲 → f₄ (p 𝓲) {q 𝓲} (r 𝓲) (q 𝓲)
 e5 = simplifyPath
       ((λ i → f₄ (p i) {y} z (p (~ i)))
     ∙∙ (λ i → f₄ y {q i} z ((p ∙ q) i)) ∙∙
        (λ i → f₄ ((refl {x = y} ∙' refl {x = y}) i) {z} (r i) z) )



module E2 {x y z w : A}
  (p : x ≡ y)
  (q : y ≡ z)
  (r : z ≡ w) (f : A → A) (f₂ : A → A → A) (f₄ : A → A → A → A → A) where

 e0 : (cong f (cong (f₂ y) p ∙ cong (flip f₂ y) q )) ≡
         (cong (f ∘S flip f₂ x) q ∙ cong (f ∘S f₂ z) p)
 e0 = solvePaths


 e1 : Square
        (cong f p) 
        (cong f q)
        (cong f p) 
        (cong f q)
 e1 = solvePaths


 e2 : Square
        (cong f p) 
        (cong f (sym r))
        (cong f (p ∙ q ∙ r))
        (cong f ((λ i → p (i ∨ ~ i)) ∙ q))
 e2 = solvePaths


module E3 {ℓ} where

 data D : Type ℓ where
  x y z w : D
  p : x ≡ y
  q : y ≡ z
  r : z ≡ w
  f : D → D
  f₂ : D → D → D
  f₄ : D → D → D → D → D

 e-refl : refl ≡ refl
 e-refl = simplifyFill (refl {x = x})

 e-refl≡refl : e-refl ≡ refl
 e-refl≡refl = refl
 
 e0 : (((p ∙∙ q ∙∙ sym q ) ∙∙ q  ∙∙ r)) ≡ (p ∙' (q ∙' r))
 e0 = simplifyPath ((p ∙∙ q ∙∙ sym q ) ∙∙ q  ∙∙ r)


 e1 : (p ∙∙ q ∙∙ r ) ≡ p ∙' (q ∙' r)
 e1 = simplifyPath (p ∙∙ q ∙∙ r )

 e1' : (refl ∙∙ q ∙∙ r ) ≡ q ∙' r
 e1' = simplifyPath (refl ∙∙ q ∙∙ r )


 e2 : (p ∙∙ refl ∙∙ refl ) ≡ p
 e2 = simplifyPath (p ∙∙ refl ∙∙ refl )



 e3 : _ ≡ _
 e3 = simplifyPath (cong f p ∙ cong f q ∙ (refl ∙ cong f r))

 e4 : _ ≡ cong₂ f₂ q p
 e4 = simplifyPath (cong (f₂ y) p ∙ cong (flip f₂ y) q )

module E4 {x : A}
  (f g h : A → A)
  (p : f ≡ g)
  (q : g ≡ h)
  
   where
 
 e0 : funExt⁻ (p ∙ q ∙ sym q) x ≡ (λ i → p (i ∧ ~ i) x) ∙ funExt⁻ p x
 e0 = solvePaths

 e1 : p ∙ q ∙ sym q ≡ (λ i → p (i ∧ ~ i)) ∙ p
 e1 = solvePaths


module E5 (A B C D : Type ℓ)
  (e₀ : A ≃ B) (e₁ : B ≃ C) (e₂ : C ≃ D) where

 e0 : ua e₀ ∙ ua e₁ ∙ ua e₂ ≡ ua e₀ ∙∙ ua e₁ ∙∙ ua e₂
 e0 = solvePaths


 e0L : Square (cong List (ua e₀) ∙ cong List (ua e₁))
              (cong List (ua e₀ ∙∙ ua e₁ ∙∙ ua e₂))
              refl (cong List (ua e₂))
 e0L = solvePaths


module E6 {ℓ ℓ' ℓ''} {A : Type ℓ } {B : Type ℓ'} {C : Type ℓ''}
  {x y z w : A}
  {x' y' z' w' : B}
  (f : A → B → C)
  (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) 
  (p' : x' ≡ y') (q' : y' ≡ z') (r' : z' ≡ w') 
  
   where
 
 e0 : Square
        (cong₂ f p q')
        (cong₂ f (sym r) (p' ∙ q' ∙ r'))
        (cong₂ f p (sym p') ∙ cong₂ f q p' ∙ cong₂ f r (sym p'))
        (cong₂ f q r')
 e0 = solvePaths

