{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.MacroExamples where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Tactics.PathSolver.Path

open import Cubical.Tactics.PathSolver.Macro


private
  variable
    ℓ : Level
    A B : Type ℓ



module _ (SA : NPath 3 A) (f : A → B) where
  open NPath SA

  f[assoc] : cong f 𝑝₀ ∙ cong f 𝑝₁ ∙ cong f 𝑝₂ ≡ (cong f 𝑝₀ ∙ cong f 𝑝₁) ∙ cong f 𝑝₂
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


  -- TODO : debug this
  cpf2≡cpf2' : Cube
              cpf2 cpf2'
              _ _
              _ _
  cpf2≡cpf2' _ i j = cong! (cpf2 i j)



module _ (A : Type) (a : A) (p : a ≡ a) (s : Square p p p p)  where


 zz : Cube {A = A}
        _ _
        _ _
        _ _
 zz i j k = hcomp
              (λ { 𝒛₀ (i = i0) (j = i1) (k = i0) → a
                 ; 𝒛₀ (i = i1) → a
                 ; 𝒛₀ (k = i1) → hcomp
                                   (λ { 𝒛₁ (i = i0) → a
                                      ; 𝒛₁ (i = i1) → a
                                      ; 𝒛₁ (j = i0) → hcomp
                                                        (λ { 𝒛₂ (i = i0) → a
                                                           ; 𝒛₂ (i = i1) → a
                                                           ; 𝒛₂ (𝒛₀ = i0) → a
                                                           ; 𝒛₂ (𝒛₀ = i1) → a
                                                           ; 𝒛₂ (𝒛₁ = i0) → a
                                                           ; 𝒛₂ (𝒛₁ = i1) → a
                                                           })
                                                        a
                                      ; 𝒛₁ (j = i1) → a
                                      ; 𝒛₁ (𝒛₀ = i0) → a
                                      ; 𝒛₁ (𝒛₀ = i1) → a
                                      })
                                   a

                 ; 𝒛₀ (j = i0) → a
                 })
              (a)
