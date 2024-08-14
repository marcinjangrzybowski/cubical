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
open import Cubical.Tactics.Reflection.CuTerm

open import Cubical.Tactics.Reflection.QuoteCubical
open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.PathSolver.MonoidalSolver
open import Cubical.Tactics.PathSolver.Path

private
  variable
    ℓ ℓ' : Level
    A B C D E : Type ℓ

module E0 (SA : NPath 5 A)  where
 open NPath SA

 symDist₄ : sym (𝑝₀ ∙ 𝑝₁ ∙ 𝑝₂ ∙ 𝑝₃ ∙ 𝑝₄)
          ≡ sym 𝑝₄ ∙ sym 𝑝₃ ∙ sym 𝑝₂ ∙ sym 𝑝₁ ∙ sym 𝑝₀ 
 symDist₄ = solvePaths

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





-- -- module E0 {x y z w : A} {x' y' z' w' : B}
-- --   (p : x ≡ y)
-- --   (q : y ≡ z)
-- --   (r : z ≡ w)
-- --   (p' : x' ≡ y')
-- --   (q' : y' ≡ z')
-- --   (r' : z' ≡ w')
-- --   (f : A → A) (f₂ : A → A → A) (f₄ : A → {A} → A → A → A) where

-- -- --  -- generalisation of cong₂Funct

-- -- --  congₙFunct : {!!}
-- -- --  congₙFunct = {!!}



-- -- -- --  e-refl : refl ≡ refl
-- -- -- --  e-refl = simplifyFill (refl {x = x})

-- -- -- --  e-refl≡refl : e-refl ≡ refl
-- -- -- --  e-refl≡refl = refl
 
-- -- -- --  e0 : (((p ∙∙ q ∙∙ sym q ) ∙∙ q  ∙∙ r)) ≡ (p ∙' (q ∙' r))
-- -- -- --  e0 = simplifyPath ((p ∙∙ q ∙∙ sym q ) ∙∙ q  ∙∙ r)


-- -- -- --  e1 : (p ∙∙ q ∙∙ r ) ≡ p ∙' (q ∙' r)
-- -- -- --  e1 = simplifyPath (p ∙∙ q ∙∙ r )

-- -- -- --  e1' : (refl ∙∙ q ∙∙ r ) ≡ q ∙' r
-- -- -- --  e1' = simplifyPath (refl ∙∙ q ∙∙ r )


-- -- -- --  e2 : (p ∙∙ refl ∙∙ refl ) ≡ p
-- -- -- --  e2 = simplifyPath (p ∙∙ refl ∙∙ refl )



-- -- -- --  e3 : _ ≡ _
-- -- -- --  e3 = simplifyPath (cong f p ∙ cong f q ∙ (refl ∙ cong f r))

-- -- -- --  e4 : _ ≡ cong₂ f₂ q p
-- -- -- --  e4 = simplifyPath (cong (f₂ y) p ∙ cong (flip f₂ y) q )



-- -- -- --  e5 : _ ≡ λ 𝓲 → f₄ (p 𝓲) {q 𝓲} (r 𝓲) (q 𝓲)
-- -- -- --  e5 = simplifyPath
-- -- -- --        ((λ i → f₄ (p i) {y} z (p (~ i)))
-- -- -- --      ∙∙ (λ i → f₄ y {q i} z ((p ∙ q) i)) ∙∙
-- -- -- --         (λ i → f₄ ((refl {x = y} ∙' refl {x = y}) i) {z} (r i) z) )



-- -- -- -- module E2 {x y z w : A}
-- -- -- --   (p : x ≡ y)
-- -- -- --   (q : y ≡ z)
-- -- -- --   (r : z ≡ w) (f : A → A) (f₂ : A → A → A) (f₄ : A → A → A → A → A) where

-- -- -- --  e0 : (cong f (cong (f₂ y) p ∙ cong (flip f₂ y) q )) ≡
-- -- -- --          (cong (f ∘S flip f₂ x) q ∙ cong (f ∘S f₂ z) p)
-- -- -- --  e0 = solvePaths


-- -- -- --  e1 : Square
-- -- -- --         (cong f p) 
-- -- -- --         (cong f q)
-- -- -- --         (cong f p) 
-- -- -- --         (cong f q)
-- -- -- --  e1 = solvePaths


-- -- -- --  e2 : Square
-- -- -- --         (cong f p) 
-- -- -- --         (cong f (sym r))
-- -- -- --         (cong f (p ∙ q ∙ r))
-- -- -- --         (cong f ((λ i → p (i ∨ ~ i)) ∙ q))
-- -- -- --  e2 = solvePaths


-- -- -- -- module E3 {ℓ} where

-- -- -- --  data D : Type ℓ where
-- -- -- --   x y z w : D
-- -- -- --   p : x ≡ y
-- -- -- --   q : y ≡ z
-- -- -- --   r : z ≡ w
-- -- -- --   f : D → D
-- -- -- --   f₂ : D → D → D
-- -- -- --   f₄ : D → D → D → D → D

-- -- -- --  e-refl : refl ≡ refl
-- -- -- --  e-refl = simplifyFill (refl {x = x})

-- -- -- --  e-refl≡refl : e-refl ≡ refl
-- -- -- --  e-refl≡refl = refl
 
-- -- -- --  e0 : (((p ∙∙ q ∙∙ sym q ) ∙∙ q  ∙∙ r)) ≡ (p ∙' (q ∙' r))
-- -- -- --  e0 = simplifyPath ((p ∙∙ q ∙∙ sym q ) ∙∙ q  ∙∙ r)


-- -- -- --  e1 : (p ∙∙ q ∙∙ r ) ≡ p ∙' (q ∙' r)
-- -- -- --  e1 = simplifyPath (p ∙∙ q ∙∙ r )

-- -- -- --  e1' : (refl ∙∙ q ∙∙ r ) ≡ q ∙' r
-- -- -- --  e1' = simplifyPath (refl ∙∙ q ∙∙ r )


-- -- -- --  e2 : (p ∙∙ refl ∙∙ refl ) ≡ p
-- -- -- --  e2 = simplifyPath (p ∙∙ refl ∙∙ refl )



-- -- -- --  e3 : _ ≡ _
-- -- -- --  e3 = simplifyPath (cong f p ∙ cong f q ∙ (refl ∙ cong f r))

-- -- -- --  e4 : _ ≡ cong₂ f₂ q p
-- -- -- --  e4 = simplifyPath (cong (f₂ y) p ∙ cong (flip f₂ y) q )

-- -- -- -- module E4 {x : A}
-- -- -- --   (f g h : A → A)
-- -- -- --   (p : f ≡ g)
-- -- -- --   (q : g ≡ h)
  
-- -- -- --    where
 
-- -- -- --  e0 : funExt⁻ (p ∙ q ∙ sym q) x ≡ (λ i → p (i ∧ ~ i) x) ∙ funExt⁻ p x
-- -- -- --  e0 = solvePaths

-- -- -- --  e1 : p ∙ q ∙ sym q ≡ (λ i → p (i ∧ ~ i)) ∙ p
-- -- -- --  e1 = solvePaths


-- -- -- -- module E5 (A B C D : Type ℓ)
-- -- -- --   (e₀ : A ≃ B) (e₁ : B ≃ C) (e₂ : C ≃ D) where

-- -- -- --  e0 : ua e₀ ∙ ua e₁ ∙ ua e₂ ≡ ua e₀ ∙∙ ua e₁ ∙∙ ua e₂
-- -- -- --  e0 = solvePaths


-- -- -- --  e0L : Square (cong List (ua e₀) ∙ cong List (ua e₁))
-- -- -- --               (cong List (ua e₀ ∙∙ ua e₁ ∙∙ ua e₂))
-- -- -- --               refl (cong List (ua e₂))
-- -- -- --  e0L = solvePaths


-- -- -- -- module E6 {ℓ ℓ' ℓ''} {A : Type ℓ } {B : Type ℓ'} {C : Type ℓ''}
-- -- -- --   {x y z w : A}
-- -- -- --   {x' y' z' w' : B}
-- -- -- --   (f : A → B → C)
-- -- -- --   (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) 
-- -- -- --   (p' : x' ≡ y') (q' : y' ≡ z') (r' : z' ≡ w') 
  
-- -- -- --    where
 
-- -- -- --  e0 : Square
-- -- -- --         (cong₂ f p q')
-- -- -- --         (cong₂ f (sym r) (p' ∙ q' ∙ r'))
-- -- -- --         (cong₂ f p (sym p') ∙ cong₂ f q p' ∙ cong₂ f r (sym p'))
-- -- -- --         (cong₂ f q r')
-- -- -- --  e0 = solvePaths

