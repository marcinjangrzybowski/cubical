{-# OPTIONS --safe -v 0 #-} 

module Cubical.Tactics.PathSolver.NSolver.Tests where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Relation.Nullary

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
open import Cubical.Tactics.Reflection.Error

open import Cubical.Tactics.Reflection.QuoteCubical
open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.PathSolver.NSolver.NSolver
open import Cubical.Tactics.PathSolver.Path




-- --  aspects :
-- --  * dimension of goal 
-- --  * is equation? (goal can be written as path between some n-cubes)
-- --  * are path terms:
--     ** variables
--     ** definitions (abstract)
--     ** higher construstors
--     ** edges of some n-cubes
--     ** diagonals of some n-cubes
--     * are there 'degenerated' paths? i.e. `λ i → p (i ∨ ~ i)`
--     * is path is over funcion type?
--     * is solving requires using functoriality of `cong` ? (generalised `cong-∙`)





private
 variable
  ℓ ℓ' : Level

module ReflTests where

 module Var {A : Type ℓ} (a : A) where

  _ : refl {x = a} ∙ refl ≡ refl
  _ = solvePaths

  _ : refl ∙ (refl {x = a} ∙ refl) ∙ refl ∙ (refl ∙ refl) ∙ refl ≡ refl
  _ = solvePaths

  _ : Square
        (((((refl {x = a} ∙ refl) ∙ refl) ∙ refl) ∙ refl) ∙ refl)
        refl
        (refl ∙ refl ∙ refl ∙ refl ∙ refl ∙ refl)
        ((refl ∙ refl) ∙∙ (refl ∙ refl) ∙∙  (refl ∙ refl ))
  _ = solvePaths


  _ : Cube
         refl (assoc (refl {x = a}) refl refl)
         (cong (refl ∙_) (lUnit refl)) (cong (_∙ refl) (rUnit refl))
         refl refl
  _ = solvePaths

  module Def where
   abstract
    a' : A
    a' = a
   
   _ : refl {x = a'} ∙ refl ≡ refl
   _ = solvePaths

   _ : refl ∙ (refl {x = a'} ∙ refl) ∙ refl ∙ (refl ∙ refl) ∙ refl ≡ refl
   _ = solvePaths

   _ : Square
         (((((refl {x = a'} ∙ refl) ∙ refl) ∙ refl) ∙ refl) ∙ refl)
         refl
         (refl ∙ refl ∙ refl ∙ refl ∙ refl ∙ refl)
         ((refl ∙ refl) ∙∙ (refl ∙ refl) ∙∙  (refl ∙ refl ))
   _ = solvePaths


   _ : Cube
          refl (assoc (refl {x = a'}) refl refl)
          (cong (refl ∙_) (lUnit refl)) (cong (_∙ refl) (rUnit refl))
          refl refl
   _ = solvePaths

   

 module DataType {ℓ} where

  data A : Type ℓ where
   a : A 

  _ : refl {x = a} ∙ refl ≡ refl
  _ = solvePaths

  _ : refl ∙ (refl {x = a} ∙ refl) ∙ refl ∙ (refl ∙ refl) ∙ refl ≡ refl
  _ = solvePaths

  _ : Square
        (((((refl {x = a} ∙ refl) ∙ refl) ∙ refl) ∙ refl) ∙ refl)
        refl
        (refl ∙ refl ∙ refl ∙ refl ∙ refl ∙ refl)
        ((refl ∙ refl) ∙∙ (refl ∙ refl) ∙∙  (refl ∙ refl ))
  _ = solvePaths


  _ : Cube
         refl (assoc (refl {x = a}) refl refl)
         (cong (refl ∙_) (lUnit refl)) (cong (_∙ refl) (rUnit refl))
         refl refl
  _ = solvePaths


module Ω-Tests where
 module Var (A : Type ℓ) (a : A) (p : a ≡ a) where
  _ : p ∙ p ∙ p ∙ p ∙ p ≡ ((((p ∙ p) ∙ p) ∙ p) ∙ p)
  _ = solvePaths

  _ : p ∙ refl ∙ p ∙ refl ∙ p ∙ refl ∙ refl ∙ p ∙ refl ∙ refl ∙ p ∙ refl
         ≡ p ∙ p ∙ p ∙ p ∙ p
  _ = solvePaths

  _ : p ∙ p ⁻¹ ∙ p ∙' p ∙ p ⁻¹ ∙ p ∙ p ∙ p ⁻¹ ∙ p ⁻¹ ∙ p ⁻¹  ≡ refl
  _ = solvePaths


  _ : Cube
         refl (assoc p refl p)
         (cong (p ∙_) (lUnit p)) (cong (_∙ p) (rUnit p))
         refl refl
  _ = solvePaths


  _ : Cube
         (λ i j → p (i ∨ ~ i ∨ j ∨ ~ j)) (λ _ _ → a)
         (λ _ _ → a) (λ _ _ → a)
         (λ _ _ → a) (λ _ _ → a)
  _ = solvePaths
      

 module HIT where
  open import Cubical.HITs.S1.Base

  _ : loop ∙ loop ∙ loop ∙ loop ∙ loop ≡ ((((loop ∙ loop) ∙ loop) ∙ loop) ∙ loop)
  _ = solvePaths

  _ : loop ∙ refl ∙ loop ∙ refl ∙ loop ∙ refl ∙ refl ∙ loop ∙ refl ∙ refl ∙ loop ∙ refl
         ≡ loop ∙ loop ∙ loop ∙ loop ∙ loop
  _ = solvePaths

  _ : loop ∙ loop ⁻¹ ∙ loop ∙' loop ∙ loop ⁻¹ ∙ loop ∙ loop ∙ loop ⁻¹ ∙ loop ⁻¹ ∙ loop ⁻¹  ≡ refl
  _ = solvePaths

  _ : Cube
         refl (assoc loop refl loop)
         (cong (loop ∙_) (lUnit loop)) (cong (_∙ loop) (rUnit loop))
         refl refl
  _ = solvePaths



module NoCong where
 module Var (A : Type ℓ) (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : A)
             (𝑝₀ : a₀ ≡ a₁)
             (𝑝₁ : a₁ ≡ a₂)
             (𝑝₂ : a₂ ≡ a₃)
             (𝑝₃ : a₃ ≡ a₄)
             (𝑝₄ : a₄ ≡ a₅)
             (𝑝₅ : a₅ ≡ a₆)
             (𝑝₆ : a₆ ≡ a₇) where

  a₀₋₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) 𝑝₀ (𝑝₂ ∙ 𝑝₃)
  a₀₋₋ = solvePaths
  
  a₁₋₋ : Square (𝑝₃ ∙ sym 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) (sym 𝑝₂)
           (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆)
  a₁₋₋ = solvePaths

  a₋₀₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₃ ∙ sym 𝑝₃) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₂
  a₋₀₋ = solvePaths

  a₋₁₋ : Square (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) 𝑝₁
      (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₁₋ = solvePaths

  a₋₋₀ : Square 𝑝₀ (sym 𝑝₂) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₁
  a₋₋₀ = solvePaths

  a₋₋₁ : Square (𝑝₂ ∙ 𝑝₃) (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆) 𝑝₂ (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₋₁ = solvePaths
  
  coh : Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
  coh =  solvePaths

 module HIT {ℓ} where


  data A : Type ℓ where
    a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : A
    𝑝₀ : a₀ ≡ a₁
    𝑝₁ : a₁ ≡ a₂
    𝑝₂ : a₂ ≡ a₃
    𝑝₃ : a₃ ≡ a₄
    𝑝₄ : a₄ ≡ a₅
    𝑝₅ : a₅ ≡ a₆
    𝑝₆ : a₆ ≡ a₇

  a₀₋₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) 𝑝₀ (𝑝₂ ∙ 𝑝₃)
  a₀₋₋ = solvePaths
  
  a₁₋₋ : Square (𝑝₃ ∙ sym 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) (sym 𝑝₂)
           (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆)
  a₁₋₋ = solvePaths

  a₋₀₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₃ ∙ sym 𝑝₃) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₂
  a₋₀₋ = solvePaths

  a₋₁₋ : Square (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) 𝑝₁
      (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₁₋ = solvePaths

  a₋₋₀ : Square 𝑝₀ (sym 𝑝₂) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₁
  a₋₋₀ = solvePaths

  a₋₋₁ : Square (𝑝₂ ∙ 𝑝₃) (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆) 𝑝₂ (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₋₁ = solvePaths

  coh : Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
  coh =  solvePaths


 module Edges&Diags {ℓ} (A : Type ℓ)
         (a⁵ : I → I → I → I → I → A)  where

  𝑝₀ : _  ≡ _
  𝑝₀ i = a⁵ i0 i i0 i (~ i)
  
  𝑝₁ : _ ≡ _
  𝑝₁ i = a⁵ i i1 i i1 i0
  
  𝑝₂ : _ ≡ _
  𝑝₂ i = a⁵ i1 (~ i) i1 i1 i0
  
  𝑝₃ : _ ≡ _
  𝑝₃ i =  a⁵ (~ i) i (~ i) (~ i) i
  
  𝑝₄ : _ ≡ _
  𝑝₄ _ = a⁵ i0 i1 i0 i0 i1
  
  𝑝₅ : _ ≡ _
  𝑝₅ i = a⁵ (i ∧ ~ i) i1 i0 i0 (i ∨  ~ i)
  
  𝑝₆ : _ ≡ _
  𝑝₆ i = a⁵ i0 i1 i0 i0 (~ i)

  a₀₋₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) 𝑝₀ (𝑝₂ ∙ 𝑝₃)
  a₀₋₋ = solvePaths
  
  a₁₋₋ : Square (𝑝₃ ∙ sym 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) (sym 𝑝₂)
           (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆)
  a₁₋₋ = solvePaths

  a₋₀₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₃ ∙ sym 𝑝₃) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₂
  a₋₀₋ = solvePaths

  a₋₁₋ : Square (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) 𝑝₁
      (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₁₋ = solvePaths

  a₋₋₀ : Square 𝑝₀ (sym 𝑝₂) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₁
  a₋₋₀ = solvePaths
  
  a₋₋₁ : Square (𝑝₂ ∙ 𝑝₃) (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆) 𝑝₂ (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₋₁ = solvePaths


  _ : Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
  _ =  solvePaths


 module InSubTerms {ℓ} (A : Type ℓ)
         (a₀ a₁ a₂ a₃ : A)
         (p₀₁ : a₀ ≡ a₁)
         (p₁₂ : a₁ ≡ a₂)
         
         (f : A → I → A)
         (g : A → A → A → A)
         (h : g a₀ a₁ ≡ g (f a₂ i0) a₃)
         (l : g (f a₂ i1) a₃ (f a₀ i1) ≡ a₀) where


  𝑝₀ : _  ≡ _
  𝑝₀ i = g (p₀₁ i) a₀ (f a₁ i)
  
  𝑝₁ : _ ≡ _
  𝑝₁ i = g (p₀₁ (~ i)) (p₀₁ i) (f (p₀₁ (~ i)) i1)
  
  𝑝₂ : _ ≡ _
  𝑝₂ i = h i (f a₀ i1)
  
  𝑝₃ : _ ≡ _
  𝑝₃ i = g (f a₂ i) a₃ (f a₀ i1)
  
  𝑝₄ : _ ≡ _
  𝑝₄ = l
  
  𝑝₅ : _ ≡ _
  𝑝₅ = p₀₁
  
  𝑝₆ : _ ≡ _
  𝑝₆ = p₁₂


  a₀₋₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) 𝑝₀ (𝑝₂ ∙ 𝑝₃)
  a₀₋₋ = solvePaths
  
  a₁₋₋ : Square (𝑝₃ ∙ sym 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) (sym 𝑝₂)
           (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆)
  a₁₋₋ = solvePaths

  a₋₀₋ : Square (𝑝₀ ∙ 𝑝₁) (𝑝₃ ∙ sym 𝑝₃) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₂
  a₋₀₋ = solvePaths

  a₋₁₋ : Square (𝑝₁ ∙∙ 𝑝₂ ∙∙ 𝑝₃) (𝑝₂ ∙ 𝑝₃ ∙ (𝑝₄ ∙∙ 𝑝₅ ∙∙ 𝑝₆)) 𝑝₁
      (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₁₋ = solvePaths

  a₋₋₀ : Square 𝑝₀ (sym 𝑝₂) (𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) 𝑝₁
  a₋₋₀ = solvePaths

  a₋₋₁ : Square (𝑝₂ ∙ 𝑝₃) (((𝑝₃ ∙' 𝑝₄) ∙' 𝑝₅) ∙' 𝑝₆) 𝑝₂ (𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆)
  a₋₋₁ = solvePaths


  _ : Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
  _ =  solvePaths

module WithCong where


 module Refl {A : Type ℓ} {B : Type ℓ'} (f : A → B) (a : A) where

  _ : cong f (refl {x = a} ∙ refl) ≡ refl
  _ = solvePaths

  _ : cong f (refl ∙ (refl {x = a} ∙ refl) ∙ refl) ∙ cong f ((refl ∙ refl) ∙ refl) ≡ refl
  _ = solvePaths

  _ : Square
        ((cong f (((refl {x = a} ∙ refl) ∙ refl) ∙ refl) ∙ refl) ∙ refl)
        refl
        (refl ∙ cong f (refl ∙ refl ∙ refl) ∙ cong f (refl ∙ refl))
        (cong f ((refl ∙ refl) ∙∙ (refl ∙ refl) ∙∙  (refl ∙ refl )))
  _ = solvePaths


  _ : Cube
         refl (congP (λ _ → cong f) (assoc (refl {x = a}) refl refl))
         (cong (refl ∙_) (lUnit refl) ∙ solvePaths)
         (cong (_∙ refl) (rUnit refl) ∙ solvePaths)
         refl refl
  _ = solvePaths

 module CongCoherent {A : Type ℓ} {B : Type ℓ'} (f : A → B) (SA : NPath 4 A) where
  open NPath SA

  LHS RHS : 𝑣₀ ≡ 𝑣₄
  LHS = (𝑝₀ ∙ refl ∙ 𝑝₁) ∙ (𝑝₂ ∙ refl ∙ 𝑝₃)
  RHS = 𝑝₀ ∙∙ (𝑝₁ ∙∙ refl ∙∙ 𝑝₂) ∙∙ 𝑝₃

  solve[cong] cong[solve] : cong f LHS ≡ cong f RHS
  
  solve[cong] = solvePaths
  
  cong[solve] = cong (cong f) solvePaths

  _ : cong[solve] ≡ solve[cong]
  _ = solvePaths


  
module CompCoherence {A : Type ℓ} (SA : NPath 7 A) where
  open NPath SA 

  module Basic where
   LHS₀ RHS₀ : 𝑣₀ ≡ 𝑣₂
   LHS₀ = 𝑝₀ ∙∙ 𝑝₁ ∙∙ refl
   RHS₀ = 𝑝₀ ∙∙ refl ∙∙ 𝑝₁ 

   LHS₁ RHS₁ : 𝑣₂ ≡ 𝑣₃
   LHS₁ = 𝑝₂
   RHS₁ = 𝑝₂

   LHS₀≡RHS₀ : LHS₀ ≡ RHS₀
   LHS₀≡RHS₀ = solvePaths

   LHS₁≡RHS₁ : LHS₁ ≡ RHS₁
   LHS₁≡RHS₁ = solvePaths

   LHS₀∙LHS₁≡RHS₀∙RHS₁ : LHS₀ ∙ LHS₁ ≡ RHS₀ ∙ RHS₁
   LHS₀∙LHS₁≡RHS₀∙RHS₁ = solvePaths


   _ : cong₂ _∙_ LHS₀≡RHS₀ LHS₁≡RHS₁ ≡ LHS₀∙LHS₁≡RHS₀∙RHS₁
   _ = solvePaths

   LHS₀⁻¹≡RHS₀⁻¹ : LHS₀ ⁻¹ ≡ RHS₀ ⁻¹
   LHS₀⁻¹≡RHS₀⁻¹ = solvePaths

   _ :  cong (_⁻¹) LHS₀≡RHS₀ ≡ LHS₀⁻¹≡RHS₀⁻¹
   _ = solvePaths

  module WithDegens where
   LHS₀ RHS₀ : 𝑣₀ ≡ 𝑣₄
   LHS₀ = 𝑝₀ ∙∙ 𝑝₁ ∙ (𝑝₂ ∙ (𝑝₁ ∙ 𝑝₂) ⁻¹) ∙ 𝑝₁ ∙∙ 𝑝₂ ∙ 𝑝₃
   RHS₀ = 𝑝₀ ∙ (λ i → 𝑝₁ (i ∧ ~ i)) ∙ 𝑝₁ ∙ 𝑝₂ ∙ (λ i → 𝑝₂ (i ∨ ~ i)) ∙  𝑝₃

   LHS₁ RHS₁ : 𝑣₄ ≡ 𝑣₇
   LHS₁ = 𝑝₄ ∙ 𝑝₅ ∙ 𝑝₆
   RHS₁ = 𝑝₄ ∙ refl ∙ 𝑝₅ ∙ refl ∙ refl ∙ 𝑝₆

   LHS₀≡RHS₀ : LHS₀ ≡ RHS₀
   LHS₀≡RHS₀ = solvePaths

   LHS₁≡RHS₁ : LHS₁ ≡ RHS₁
   LHS₁≡RHS₁ = solvePaths

   LHS₀∙LHS₁≡RHS₀∙RHS₁ : LHS₀ ∙ LHS₁ ≡ RHS₀ ∙ RHS₁
   LHS₀∙LHS₁≡RHS₀∙RHS₁ = solvePaths

   _ : cong₂ _∙_ LHS₀≡RHS₀ LHS₁≡RHS₁ ≡ LHS₀∙LHS₁≡RHS₀∙RHS₁
   _ = solvePaths

   LHS₀⁻¹≡RHS₀⁻¹ : LHS₀ ⁻¹ ≡ RHS₀ ⁻¹
   LHS₀⁻¹≡RHS₀⁻¹ = solvePaths

   _ :  cong (_⁻¹) LHS₀≡RHS₀ ≡ LHS₀⁻¹≡RHS₀⁻¹
   _ = solvePaths
