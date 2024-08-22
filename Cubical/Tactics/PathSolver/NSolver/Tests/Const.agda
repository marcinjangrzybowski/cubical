{-# OPTIONS --safe -v 0 #-} 

module Cubical.Tactics.PathSolver.NSolver.Tests.Const where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Tactics.PathSolver.NSolver.NSolver

private
 variable
  ℓ ℓ' : Level

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

