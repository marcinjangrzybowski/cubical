{-# OPTIONS --safe #-} 
module Cubical.Tactics.PathSolver.Tests.CongComp where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Agda.Builtin.Reflection as R

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.List


open import Cubical.Reflection.Base  renaming (v to 𝒗)
open import Cubical.Tactics.PathSolver.Error
open import Cubical.Tactics.PathSolver.CongComp

open import Cubical.Tactics.PathSolver.QuoteCubical
open import Cubical.Tactics.PathSolver.CuTerm
open import Cubical.Tactics.PathSolver.CongComp





module _ (dim : ℕ) (b : Bool) where

  macro
   testAppCong : R.Term → R.Term → R.TC Unit
   testAppCong t hole = do
    cu ← (extractCuTerm dim t)
    let cu' = appCongs dim cu 

    te ← ppCT dim 100 cu
    te' ← ppCT dim 100 cu'
    if b then (R.unify (toTerm dim cu') hole) else (R.typeError $
        te ++ₑ [ "\n \n" ]ₑ ++ₑ [ toTerm dim cu ]ₑ ++ [ "\n\n" ]ₑ
         ++ te'
         ++ₑ [ "\n \n" ]ₑ ++ₑ [ toTerm dim cu' ]ₑ)

   testAppFill : R.Term → R.Term → R.TC Unit
   testAppFill t hole = do
    cu ← (extractCuTerm dim t)
    let cu' = fillCongs 15 dim cu 

    te ← ppCT dim 100 cu
    te' ← ppCTn false (suc dim) 100 cu'
    if b then (R.unify (toTerm (suc dim) cu') hole) else (R.typeError $
        te ++ₑ [ "\n \n" ]ₑ ++ₑ [ toTerm dim cu ]ₑ ++ [ "\n\n" ]ₑ
         ++ te'
         ++ₑ [ "\n \n" ]ₑ ++ₑ [ toTerm (suc dim) cu' ]ₑ
         )


 


   


private
  variable
    ℓ : Level
    A : Type ℓ
    x y z w v : A


 
module cong-test {x : A}
            {B C : Type ℓ}
            (f f' : A → B)
          (g : B → B → C)
          (p p' : Path A x y) (q q' : y ≡ z)   (r : z ≡ w) where

-- --   cong1 : I → I → B
-- --   cong1 i j = cong-∙ f p q i j

-- --   -- cong1-test : Unit
-- --   -- cong1-test = {!testAppCong (suc (suc zero))
-- --   --        (λ (i j : I) → cong-∙ f p q i j) !}

-- --   -- cong2-test : Unit
-- --   -- cong2-test = {!extractCuTermTest (suc zero)
-- --   --        (λ (i : I) → cong₂ g (cong f (p ∙' q)) (cong f' (p' ∙ q')) i) !}


-- -- --    cong1-test' : cong-∙ f p q ≡
-- -- --                      getCuTerm (suc (suc zero))
-- -- --                        (λ (i j : I) → cong-∙ f p q i j)
-- -- --    cong1-test' = refl

  zzz = congP (λ _ → cong f) (doubleCompPath-filler p q r)

  zzz' = cong₂ g (cong f (p ∙' q)) (cong f' (p' ∙ q'))

-- --   -- cong2-test' : Unit
-- --   -- cong2-test' = {! testAppCong (suc zero) false
-- --   --                    (λ (i : I) → zzz' i)!}


  _ : Cube
                   zzz (testAppCong (suc (suc zero)) true
                     (λ (i j : I) → zzz i j))
                   refl (testAppFill (suc zero) true
                     (λ (j : I) → zzz i1 j))
                   refl refl
  _ =  testAppFill (suc (suc zero)) true
                     (λ (i j : I) → zzz i j)

  zzz'-test : (cong₂ g (cong f p) (cong f' refl)
                 ∙∙ cong₂ g (cong f q) (cong f' p')
                 ∙∙ cong₂ g (cong f refl) (cong f' q')) ≡ (testAppCong (suc zero) true
                     (λ (i : I) → zzz' i))

  zzz'-test  = refl

-- --   zzz'-fillTest : --I → I → C
-- --     zzz' ≡ (testAppCong (suc zero) true
-- --                      (λ (i : I) → zzz' i))
                         
-- --   zzz'-fillTest = testAppFill (suc zero) true
-- --                      (λ (i : I) → zzz' i)

-- --   zzz2 = cong f (p ∙ (q ∙ r))

-- --   zzz2-fillTest : zzz2 ≡ (testAppCong (suc zero) true
-- --                      (λ (i : I) → zzz2 i))
-- --   zzz2-fillTest = 
-- --        testAppFill (suc zero) true
-- --                      (λ (i : I) → zzz2 i)

module dcpf-test {B : Type ℓ} {x : A} (q : y ≡ z) (p : Path A x y)  (r : z ≡ w) (f : A → A → B) where

  codim1 : I → I → B 
  codim1 i j = f (hcomp
        h
       (q (i ∧ j)))
       (hcomp
        h
       (q (i ∧ j)))
    where
    h : _
    h = (λ k → λ { (i = i0) → p (~ k)
                ; (j = i0) → p (~ k)
                ; (i = i1)(j = i1) → r k
          })

  codim1-test' : Unit
  codim1-test' = testAppCong (suc (suc zero)) false
                     (λ (i j : I) → codim1 i j)
