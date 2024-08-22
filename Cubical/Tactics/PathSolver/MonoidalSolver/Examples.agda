{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.MonoidalSolver.Examples where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence


open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sum

open import Cubical.Data.Sigma

open import Agda.Builtin.String



open import Cubical.Tactics.PathSolver.MonoidalSolver.MonoidalSolver
open import Cubical.Tactics.PathSolver.Path



private
  variable
    ℓ ℓ' : Level
    A B C D E : Type ℓ


module E0' (SA : NPath 3 A)
           (SB : NPath 3 B)
           (SC : NPath 3 C)
           (SD : NPath 3 D)  where

 module A = NPath SA
 module B = NPath SB
 module C = NPath SC
 module D = NPath SD

 module _ (f₄ : A → {B} → C → D → E) where
   cong₄Funct∙₃ :
                  ([ f₄ ]$≡ A.𝑝₀ ≡$'≡ B.𝑝₀ ≡$≡ C.𝑝₀ ≡$≡ D.𝑝₀)
                ∙ ([ f₄ ]$≡ A.𝑝₁ ≡$'≡ B.𝑝₁ ≡$≡ C.𝑝₁ ≡$≡ D.𝑝₁)
                ∙ ([ f₄ ]$≡ A.𝑝₂ ≡$'≡ B.𝑝₂ ≡$≡ C.𝑝₂ ≡$≡ D.𝑝₂)
                ≡
                  ([ f₄ ]$≡  (A.𝑝₀ ∙ A.𝑝₁ ∙ A.𝑝₂)
                        ≡$'≡ (B.𝑝₀ ∙ B.𝑝₁ ∙ B.𝑝₂)
                        ≡$≡  (C.𝑝₀ ∙ C.𝑝₁ ∙ C.𝑝₂)
                        ≡$≡  (D.𝑝₀ ∙ D.𝑝₁ ∙ D.𝑝₂))
   cong₄Funct∙₃ = solvePaths

   cong-comm₄ :
           (λ i → f₄ (A.𝑝₀ i) {B.𝑣₀} (C.𝑣₀) (D.𝑣₀))
         ∙ (λ i → f₄ (A.𝑣₁) {B.𝑝₀ i} (C.𝑣₀) (D.𝑣₀))
         ∙ (λ i → f₄ (A.𝑣₁) {B.𝑣₁} (C.𝑝₀ i) (D.𝑣₀))
         ∙ (λ i → f₄ (A.𝑣₁) {B.𝑣₁} (C.𝑣₁) (D.𝑝₀ i))
                      ≡
           (λ i → f₄ (A.𝑣₀) {B.𝑣₀} (C.𝑣₀) (D.𝑝₀ i))
         ∙ (λ i → f₄ (A.𝑣₀) {B.𝑣₀} (C.𝑝₀ i) (D.𝑣₁))
         ∙ (λ i → f₄ (A.𝑣₀) {B.𝑝₀ i} (C.𝑣₁) (D.𝑣₁))
         ∙ (λ i → f₄ (A.𝑝₀ i) {B.𝑣₁} (C.𝑣₁) (D.𝑣₁))
   cong-comm₄ = solvePaths



 _ : (f : A → B → C) → Square
        (cong₂ f A.𝑝₀ B.𝑝₁)
        (cong₂ f (sym A.𝑝₂) (B.𝑝₀ ∙ B.𝑝₁ ∙ B.𝑝₂))
        (cong₂ f A.𝑝₀ (sym B.𝑝₀) ∙ cong₂ f A.𝑝₁ B.𝑝₀ ∙ cong₂ f A.𝑝₂ (sym B.𝑝₀))
        (cong₂ f A.𝑝₁ B.𝑝₂)
 _ = λ f → solvePaths



module simplify-examples {x y z w : A} {x' y' z' w' : B}
  (p : x ≡ y)
  (q : y ≡ z)
  (r : z ≡ w)
  (p' : x' ≡ y')
  (q' : y' ≡ z')
  (r' : z' ≡ w')
  (f : A → A) (f₂ : A → A → A) (f₄ : A → {A} → A → A → A) where


 e0 : _ ≡ (p ∙' (q ∙' r))
 e0 = simplifyPath ((p ∙∙ q ∙∙ sym q ) ∙∙ q  ∙∙ r)


 e1 : _ ≡ p ∙' (q ∙' r)
 e1 = simplifyPath (p ∙∙ q ∙∙ r )

 e1' : _ ≡ q ∙' r
 e1' = simplifyPath (refl ∙∙ q ∙∙ r )


 e2 : _ ≡ p
 e2 = simplifyPath (p ∙∙ refl ∙∙ refl )



 e3 : _ ≡ ((λ 𝓲 → f (p 𝓲)) ∙' ((λ 𝓲 → f (q 𝓲)) ∙' (λ 𝓲 → f (r 𝓲))))
 e3 = simplifyPath (cong f p ∙ cong f q ∙ (refl ∙ cong f r))

 e4 : _ ≡ cong₂ f₂ q p
 e4 = simplifyPath (cong (f₂ y) p ∙ cong (flip f₂ y) q )



 e5 : _ ≡ λ 𝓲 → f₄ (p 𝓲) {q 𝓲} (r 𝓲) (q 𝓲)
 e5 = simplifyPath
       ((λ i → f₄ (p i) {y} z (p (~ i)))
     ∙∙ (λ i → f₄ y {q i} z ((p ∙ q) i)) ∙∙
        (λ i → f₄ ((refl {x = y} ∙' refl {x = y}) i) {z} (r i) z) )




module _ (A B C D : Type ℓ)
         (A≃B : A ≃ B) (B≃C : B ≃ C) (C≃D : C ≃ D)
          where

 _ : Square (cong List (cong₂ _⊎_ (ua A≃B) (sym (ua B≃C))) ∙ cong List (cong (_⊎ B) (ua B≃C)))
              (cong List (cong₂ _⊎_ (ua A≃B ∙∙ ua B≃C ∙∙ ua C≃D) (sym (ua B≃C))))
              refl (cong List (cong (_⊎ B) (ua C≃D)))
 _ = solvePaths

