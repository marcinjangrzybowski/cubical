{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.MacroExamples where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Tactics.PathSolver.Path

open import Cubical.Tactics.PathSolver.Macro
open import Cubical.Tactics.Reflection.QuoteCubical


private
  variable
    ℓ : Level
    A B : Type ℓ



module _ (SA : NPath 3 A) (f : A → B) where
  open NPath SA

  f[assoc] : cong f 𝑝₀ ∙ cong f 𝑝₁ ∙ cong f 𝑝₂
              ≡ (cong f 𝑝₀ ∙ cong f 𝑝₁) ∙ cong f 𝑝₂
  f[assoc] i j = cong$ (f (assoc 𝑝₀ 𝑝₁ 𝑝₂ i j))


module _ (SA : NPath 6 A) (f : A → {A} → A → A) (g : A → A) (𝑝ₓ : g (NPath.𝑣₀ SA) ≡ g (NPath.𝑣₀ SA)) where
  open NPath SA

  p : f 𝑣₀ 𝑣₁ ≡ f 𝑣₃ 𝑣₆
  p i =  (f ((𝑝₀ ∙∙ 𝑝₁ ∙∙ 𝑝₂) i) {g ((𝑝₁ ∙' 𝑝₂) i)} ((𝑝₁ ∙∙ 𝑝₂ ∙∙ (𝑝₃ ∙∙ 𝑝₄ ∙∙ 𝑝₅)) i))


  _ :  (λ i → cong$ (p i))
        ≡
          (λ i → f (𝑝₀ i) {g (𝑝₁ i)} (𝑝₁ i))
      ∙∙  (λ i → f (𝑝₁ i) {g (𝑝₂ i)} (𝑝₂ i))
      ∙∙ ((λ i → f  𝑣₂    {g 𝑣₃}     (𝑝₃ i))
      ∙∙  (λ i → f (𝑝₂ i) {g 𝑣₃}     (𝑝₄ i))
      ∙∙   λ i → f  𝑣₃    {g 𝑣₃}     (𝑝₅ i))
  _ = refl

  cg² : ∀ {x y : A} → (x ≡ y) → g (g x) ≡ g (g y)
  cg² = congS (g ∘S g)

  cpf : Square (cong g 𝑝₀) (cong g (𝑝₀ ∙ 𝑝₁))
                refl          (cong g 𝑝₁)
  cpf i j = g (compPath-filler 𝑝₀ 𝑝₁ i j)

  cpf' : Square (cong g 𝑝₀) (cong g 𝑝₀ ∙ cong g 𝑝₁)
                 refl        (cong g 𝑝₁)
  cpf' i j = cong$ (cpf i j)


  cpf≡cpf' : Cube
              cpf cpf'
              _ _
              _ _
  cpf≡cpf' _ i j = cong! (cpf i j)



  cpf2 : Square (cong g (𝑝ₓ ∙ cong g (𝑝₀ ∙ 𝑝₁)))
               (cong g ((𝑝ₓ ∙ cong g (𝑝₀ ∙ 𝑝₁)) ∙ cong g (𝑝₂ ∙ 𝑝₃)))
               refl (cg² (𝑝₂ ∙ 𝑝₃))
  cpf2 i j = g (compPath-filler (𝑝ₓ ∙ cong g (𝑝₀ ∙ 𝑝₁)) (cong g (𝑝₂ ∙ 𝑝₃)) i j)

  cpf2' : Square
              (cong g 𝑝ₓ ∙ cg² 𝑝₀ ∙ cg² 𝑝₁)
               ((cong g 𝑝ₓ ∙ cg² 𝑝₀ ∙ cg² 𝑝₁) ∙ cg² 𝑝₂ ∙ cg² 𝑝₃)
                refl
               (cg² 𝑝₂ ∙ cg² 𝑝₃)
  cpf2' i j = cong$ (cpf2 i j)


  cpf2≡cpf2' : Cube
              cpf2 cpf2'
              _ _
              _ _
  cpf2≡cpf2' _ i j = cong! (cpf2 i j)


module _ (A : Type) (x y z w v : A)
         (p : x ≡ y)(q : y ≡ z)(r : z ≡ w)(s : w ≡ v)
           where

 -- _ : p ∙ q ∙ r ∙ s ≡ (p ∙ q) ∙ r ∙ s
 -- _ = {!showCuCode (assoc p q (r ∙ s))!}


-- module _ (A : Type) (a : A) (p : a ≡ a)
--          (s : Square p p p p)  where

-- ```agda
-- λ 𝓲₀ 𝓲₁ →
--        hcomp (λ 𝒛₀ → λ {
--           (𝓲₁ = i0) → x
--           ;(𝓲₁ = i1) →
--              hcomp (λ 𝒛₁ → λ {
--                 (𝓲₀ = i1) →
--                    hcomp (λ 𝒛₂ → λ {
--                       (𝒛₁ = i0)          → z
--                       ;(𝒛₀ = i0)          → z
--                       ;(𝒛₁ = i1)(𝒛₀ = i1) → s 𝒛₂
--                        })
--                    (  r (𝒛₀ ∧ 𝒛₁))

--                 ;(𝒛₀ = i1) →
--                    hcomp (λ 𝒛₂ → λ {
--                       (𝒛₁ = i0) → z
--                       ;(𝒛₁ = i1) → s 𝒛₂
--                        })
--                    (  r 𝒛₁)

--                 ;(𝒛₀ = i0) → q 𝓲₀
--                  })
--              (  q (𝒛₀ ∨ 𝓲₀))

--            })
--        (
--          hcomp (λ 𝒛₀ → λ {
--             (𝓲₀ = i0) → p 𝓲₁
--             ;(𝓲₁ = i0) → x
--             ;(𝓲₁ = i1) → q (𝓲₀ ∧ 𝒛₀)
--              })
--          (  p 𝓲₁)
--           )
-- ```
