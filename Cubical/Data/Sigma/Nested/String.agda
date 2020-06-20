{-

This file is included only temporarly to test some features of this module,

I plan to remove it before final pull request (or maybe move it to the experiments folder?)

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Sigma.Nested.String where

open import Cubical.Data.Nat

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Vec.NAry
open import Cubical.Data.List
open import Cubical.Data.Fin

open import Cubical.Foundations.Everything

open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying
open import Cubical.Data.Sigma.Nested.Path

open import Cubical.Relation.Binary.Base





module cu-test {ℓ} (A : Type ℓ) (a : Bool → Bool → Bool → A) where


  sqH1 : {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
            {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
            {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
             → Square a₀₋ a₁₋ a₋₀ a₋₁ 
             → Square a₋₁ a₁₋ (sym a₀₋ ∙∙ refl ∙∙ a₋₀) refl
  sqH1 x i₀ i₁ =
    hcomp (λ k → λ {
               (i₀ = i0) → x (i₁ ∧ k) i1
              ;(i₀ = i1) → x i1 i₁
              ;(i₁ = i0) → doubleCompPath-filler (sym (x i0)) refl (λ i → x i i0) i1 i₀
              ;(i₁ = i1) → x (i₀ ∨ k) i1
              })
      (hcomp (λ k → λ {
               (i₀ = i0) → x i0 (i₁ ∨ k)
              ;(i₀ = i1) → x i1 i₁
              ;(i₁ = i1) → x i₀ i1
              ;(i₁ = i0) → (hcomp (λ k₁ → λ {
                              (i₀ = i0) → x i0 (k₁ ∧ k)
                             ;(i₀ = i1) → x (k₁ ∨ ~ k) i0
                             ;(k = i0) → x i₀ i0
                             }) (x (i₀ ∧ ~ k) i0))
              }) (x i₀ i₁))

  -- rotSq : {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  --             {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  --             {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  --              → (x : Square a₀₋ a₁₋ a₋₀ a₋₁) 
  --              → Cube
  --                     (λ i₀ i₁ → x (~ i₁) i₀)
  --                      x
  --                      {!!} {!!} {!!} {!!}
  -- rotSq  x i i₀ i₁ =
  --    {!!}

  rotSq' : {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
            {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
            {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
             → (x : Square a₀₋ a₁₋ a₋₀ a₋₁) 
             → Cube
                    (λ i₀ i₁ → x i₁ (~ i₀))
                     x
                     (λ i i₁ → x (i₁ ∧ ~ i) (i₁ ∨ ~ i))
                     (λ i i₁ → x (i₁ ∨ i) (i₁ ∧ i))
                     (λ i i₁ → x (i₁ ∧ i) (~ i₁ ∧ ~ i))
                     λ i i₁ → x (i₁ ∨ ~ i) (~ i₁ ∨ i)
  rotSq'  x i i₀ i₁ =
     hcomp 
     (λ k → λ {
               (i = i1) → x (i₀ ∧ k) (i₁ ∧ k)
              ;(i = i0) → x (i₁ ∧ k) (~ i₀ ∧ k)
              ;(i₀ = i0) → x (i₁ ∧ k ∧ ~ i) ((i₁ ∨ ~ i) ∧ k)
              ;(i₀ = i1) → x ((i₁ ∨ i) ∧ k) (i₁ ∧ k ∧ i)
              ;(i₁ = i0) → x (i₀ ∧ k ∧ i) (~ i₀ ∧ k ∧ ~ i) 
              ;(i₁ = i1) → x ((i₀ ∨ ~ i) ∧ k) ((~ i₀ ∨ i ) ∧ k)
              })
     (x i0 i0)
     

  -- ◇- : {a b₀ b₁ e c₀ c₁ d : A}
  --          → {ab₀ : a ≡ b₀} → {b₀c₀ : b₀ ≡ c₀} → {c₀d : c₀ ≡ d}
  --          → {ab₁ : a ≡ b₁} → {b₁c₁ : b₁ ≡ c₁} → {c₁d : c₁ ≡ d}
  --          → {b₀e : b₀ ≡ e} → {b₁e : b₁ ≡ e} →  {ed : e ≡ d}
  --          → ab₀ ∙ b₀e ≡ ab₁ ∙ b₁e
  --          → b₀e ∙ ed ≡ b₀c₀ ∙ c₀d → b₁e ∙ ed ≡ b₁c₁ ∙ c₁d
  --          → (ab₀ ∙∙ b₀c₀ ∙∙ c₀d) ≡ (ab₁ ∙∙ b₁c₁ ∙∙ c₁d)
  -- ◇- x x₁ x₂ = {!!}

  -- -◇ : {a b₀ b₁ e c₀ c₁ d : A}
  --          → {ab₀ : a ≡ b₀} → {b₀c₀ : b₀ ≡ c₀} → {c₀d : c₀ ≡ d}
  --          → {ab₁ : a ≡ b₁} → {b₁c₁ : b₁ ≡ c₁} → {c₁d : c₁ ≡ d}
  --          → {ae : a ≡ e} → {ec₀ : e ≡ c₀} → {ec₁ : e ≡ c₁}
  --          → ab₀ ∙ b₀c₀ ≡ ae ∙ ec₀ → ab₁ ∙ b₁c₁ ≡ ae ∙ ec₁
  --          →  ec₀ ∙ c₀d ≡ ec₁ ∙ c₁d
  --          → (ab₀ ∙∙ b₀c₀ ∙∙ c₀d) ≡ (ab₁ ∙∙ b₁c₁ ∙∙ c₁d)
  -- -◇ {c₀d = c₀d} {c₁d = c₁d} {ae = ae} x x₁ x₂ =
  --                (doubleCompPath-elim _ _ _) ∙∙
  --              (((cong (_∙ c₀d) x) ∙ sym (assoc _ _ _))
  --               ∙∙ (cong (ae ∙_) x₂) ∙∙ (assoc _ _ _ ∙ cong (_∙ c₁d) (sym x₁))) 
  --               ∙∙  sym (doubleCompPath-elim _ _ _)



  -◇' : {a b₀ b₁ e c₀ c₁ d : A}
           → {ab₀ : a ≡ b₀} → {b₀c₀ : b₀ ≡ c₀} → {c₀d : c₀ ≡ d}
           → {ab₁ : a ≡ b₁} → {b₁c₁ : b₁ ≡ c₁} → {c₁d : c₁ ≡ d}
           → {ae : a ≡ e} → {ec₀ : e ≡ c₀} → {ec₁ : e ≡ c₁}
           → Square ab₀ ec₀ ae b₀c₀ → Square ab₁ ec₁ ae  b₁c₁
           → Square ec₀ c₁d ec₁ c₀d
           → (ab₀ ∙∙ b₀c₀ ∙∙ c₀d) ≡ (ab₁ ∙∙ b₁c₁ ∙∙ c₁d)
  -◇' {a} {ab₀ = ab₀} {c₀d = c₀d} {ab₁} {c₁d = c₁d} {ae = ae} sq₁ sq₂ sq i₁ i₂ =
     hcomp (λ k → λ {
           (i₂ = i0) → hcomp (λ k₁ → λ {
                                   (k = i1) → a
                                 ; (i₁ = i0) → ab₀ ((~ k) ∧ k₁)
                                 ; (i₁ = i1) → ab₁ ((~ k) ∧ k₁) }) a
          ;(i₂ = i1) → sqH1 sq i₁ k
        })
        (hcomp (λ k
          → λ {
                (i₁ = i0) → sq₁ i₂ k
              ; (i₁ = i1) → sq₂ i₂ k}
              ) (ae i₂))


  -◇'-fill :  {a b₀ b₁ e c₀ c₁ d : A}
           → {ab₀ : a ≡ b₀} → {b₀c₀ : b₀ ≡ c₀} → {c₀d : c₀ ≡ d}
           → {ab₁ : a ≡ b₁} → {b₁c₁ : b₁ ≡ c₁} → {c₁d : c₁ ≡ d}
           → {ae : a ≡ e} → {ec₀ : e ≡ c₀} → {ec₁ : e ≡ c₁}
           → (sq₁ : Square ab₀ ec₀ ae b₀c₀) → (sq₂ : Square ab₁ ec₁ ae  b₁c₁)
           → (sq : Square ec₀ c₁d ec₁ c₀d)
           → Cube (-◇' sq₁ sq₂ sq) sq
            (λ i₀ i₂ → hcomp
                       (λ k₁ →
                          λ { (i₀ = i1) → sq₁ i₂ i0
                            ; (i₂ = i1) → {!!}
                            ; (i₂ = i0) → {!!}
                            })
                       (sq₁ i₂ (~ i₀))
                       )
            (λ i₀ i₂ → hcomp
                       (λ k₁ →
                          λ { (i₀ = i1) → {!!}
                            ; (i₂ = i1) → {!!}
                            ; (i₂ = i0) → {!!}
                            })
                       (sq i₂ i0)
                       )
            (λ i₀ i₁ →
                hcomp
                (λ k₁ →
                   λ { (i₁ = i0) → sq₂ i₀ i0
                     ; (i₀ = i1) → sq₂ i1 i₁
                     ; (i₀ = i0) → sq₂ i0 (i₁ ∧ ~ k₁)
                     })
                (sq₂ i₀ i₁))
            λ i i₁ → sq ( i₁ ∨ ~ i) i1  
  -◇'-fill {ae = ae} sq₁ sq₂ sq i₀ i₁ i₂ =
     hcomp
      (λ k → λ {
           (i₂ = i1) →
                 hcomp
                  (λ k₁ →
                    λ {
                       (i₀ = i1) → {!!} --sq i₁ k
                     ; (k = i1) → {!!}
                     ; (i₁ = i0) → {!!}
                     ; (i₁ = i1) → {!!}
                     ; (k = i0) → {!!}
                     })
                  {!!}
         ; (i₂ = i0) → {!!}
         ; (i₀ = i1) → hcomp (λ k₁ →
                        λ {
                            (k = i0) → ({!!})
                          ; (k = i1) → {!!} --sq i₁ (i₂ ∧ k₁)
                          ; (i₁ = i0) → {!!}
                          ; (i₁ = i1) → {!!}
                          ; (i₂ = i0) → {!!}
                          ; (i₂ = i1) → {!sq₂ k i0!} --sq i₁ (k₁ ∧ k )
                          })

                    (sq (i₁ ∧ (k ∨ i₂)) i0)
        })
              (hcomp (λ k
                  → λ {
                         (i₁ = i0) → sq₁ i₂ (k ∧ ~ i₀)
                       ; (i₁ = i1) → sq₂ (i₂ ∨ i₀) (k ∧ (~ i₂ ∨ ~ i₀ ))
                       ; (i₀ = i1) → sq₂ (i₂ ∨ i₁) (~ i₂ ∧ k ∧ i₁) 
              
              }
              )
                (ae (i₂ ∨ i₀ ∧ i₁))
              )


--   ◇-' : {a b₀ b₁ e c₀ c₁ d : A}
--            → {ab₀ : a ≡ b₀} → {b₀c₀ : b₀ ≡ c₀} → {c₀d : c₀ ≡ d}
--            → {ab₁ : a ≡ b₁} → {b₁c₁ : b₁ ≡ c₁} → {c₁d : c₁ ≡ d}
--            → {b₀e : b₀ ≡ e} → {b₁e : b₁ ≡ e} →  {ed : e ≡ d}
--            → Square ab₀ b₁e ab₁ b₀e
--            → Square b₀e c₀d b₀c₀ ed → Square b₁e c₁d b₁c₁ ed
--            → (ab₀ ∙∙ b₀c₀ ∙∙ c₀d) ≡ (ab₁ ∙∙ b₁c₁ ∙∙ c₁d)
--   ◇-' x x₁ x₂ i i₁ = -◇'  (λ i₂ i₃ → x₂ (~ i₂) (~ i₃)) (λ i₂ i₃ → x₁ (~ i₂) (~ i₃))
--                           (λ i₂ i₃ → x (~ i₂) (~ i₃)) (~ i) (~ i₁)


--   Square≡ : {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
--             {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
--             (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
--             → Type ℓ
--   Square≡ a₀₋ a₁₋ a₋₀ a₋₁ = (a₀₋ ∙ a₋₁ ≡ a₋₀ ∙ a₁₋)

--   sq2-Iso : {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
--             {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
--             {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
--          → Iso (a₀₋ ∙ a₋₁ ≡ a₋₀ ∙ a₁₋) (Square a₀₋ a₁₋ a₋₀ a₋₁)
--   sq2-Iso  {a₀₋ = a₀₋} {a₁₋ = a₁₋} {a₋₀ = a₋₀} {a₋₁ = a₋₁} =
--     let z : (i i₁ k : I) →  Partial (i ∨ ~ i ∨ i₁ ∨ ~ i₁) A
--         z i i₁ k = λ {
--                     (i = i0) → compPath-filler  a₀₋ a₋₁ (~ k) i₁
--                    ;(i = i1) → compPath-filler' a₋₀ a₁₋ (~ k) i₁
--                    ;(i₁ = i0) → a₋₀ (i ∧ k)
--                    ;(i₁ = i1) → a₋₁ (i ∨ ~ k)
--                   }
--         z' : (i i₁ : I) → I → _
--         z' = λ i i₁ k → z i i₁ (~ k)
--         f = (λ x i i₁ → hcomp (z i i₁) (x i i₁))
--         f' = (λ x i i₁ → hcomp (z' i i₁) (x i i₁))
        
--     in iso f f'           
--            (λ x j i i₁ → hcomp (λ l → primPOr j _ (λ _ → hfill (z' i i₁) (inS (x i i₁)) (~ l))
--                             (z i i₁ l)) (f' x i i₁))
--            (λ x j i i₁ → hcomp (λ l → primPOr j _ (λ _ → hfill (z i i₁) (inS (x i i₁)) (~ l))
--                             (z' i i₁ l)) (f x i i₁))

--   -- Cube≡ :
--   --   {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
--   --   {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
--   --   {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
--   --   (a₀₋₋ : Square≡ a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
--   --   {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
--   --   {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
--   --   {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
--   --   (a₁₋₋ : Square≡ a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
--   --   {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
--   --   (a₋₀₋ : Square≡ a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
--   --   {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
--   --   (a₋₁₋ : Square≡ a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
--   --   (a₋₋₀ : Square≡ a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
--   --   (a₋₋₁ : Square≡ a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
--   --   → Type ℓ 
--   -- Cube≡ a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = ◇- a₀₋₋ a₋₋₁ a₋₁₋ ≡ -◇ a₋₀₋ a₋₋₀ a₁₋₋


--   Cube-Iso1 :
--     {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
--     {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
--     {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
--     (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
--     {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
--     {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
--     {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
--     (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
--     {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
--     (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
--     {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
--     (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
--     (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
--     (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
--     → Σ _ (Iso
--           (Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁)) 
--   Cube-Iso1 a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
--     (◇-' a₀₋₋ a₋₋₁ a₋₁₋ ≡ -◇' a₋₀₋ a₋₋₀ a₁₋₋ ) ,
--     iso f' f {!!} {!!} --p' p


--     where

--       z0 :
--             Cube (◇-' a₀₋₋ a₋₋₁ a₋₁₋) a₀₋₋
--              {!!}
--              {!!}
--              {!!}
--              {!!}
--       z0 = {!!}




--       z1 : Cube (-◇' a₋₀₋ a₋₋₀ a₁₋₋) a₁₋₋
--             (λ i₁ i₂ → hcomp
--                        (λ k₁ →
--                           λ { (i₁ = i1) → a₋₀₋ i₂ i0
--                             ; (i₂ = i1) → {!!}
--                             ; (i₂ = i0) → {!!}
--                             })
--                        (a₋₀₋ i₂ (~ i₁))
--                        )
--             (λ i₁ i₂ → hcomp
--                        (λ k₁ →
--                           λ { (i₁ = i1) → a₋₁₋ (i₂ ∨ k₁) (i₂ ∧ k₁)
--                             ; (i₂ = i1) → {!!}
--                             ; (i₂ = i0) → {!!}
--                             })
--                        (a₋₁₋ i₂ i0)
--                        )
--             (λ i i₁ →
--                 hcomp
--                 (λ k₁ →
--                    λ { (i₁ = i0) → a₋₋₀ i i0
--                      ; (i = i1) → a₋₋₀ i1 i₁
--                      ; (i = i0) → a₋₋₀ i0 (i₁ ∧ ~ k₁)
--                      })
--                 (a₋₋₀ (i1 ∧ i) i₁))
--             λ i i₁ → a₁₋₋ ( i₁ ∨ ~ i) i1  
--       z1 = {!-◇-fill a₋₀₋ a₋₋₀ a₁₋₋!}

-- -- ?24 (i = i1) = a₋₀₀ i₁ : A
-- -- ?24 (i = i0) = a₀₀₋ (~ i₁) : A
-- -- ?24 (i₁ = i1) = a₋₀₀ i : A
-- -- ?24 (i₁ = i0) = a₀₀₋ (~ i) : A

--       zzz : Cube
--                 {!!}
--                 {!!}
--                 (λ i i₁ → a₋₀₋ i0 (~ i₁))
--                 (λ i i₁ → a₋₀₋ ((i ∨ i₁) ∧ i ∧ i₁) ((~ i ∨ ~ i₁) ∧ ~ i ∧ ~ i₁))
--                 (λ i i₁ → a₋₀₋ i0 (~ i ∨ ~ i₁))
--                 λ i i₁ → a₋₀₋ (i ∧ i₁) i0
--       zzz = {!!}


--       z : (i₀ i₁ i₂ : I) → I →  Partial (i₀ ∨ ~ i₀ ∨ i₁ ∨ ~ i₁ ∨ i₂ ∨ ~ i₂) A
--       z i₀ i₁ i₂ k =
--          λ {
--             (i₀ = i0) → z0 k i₁ i₂
--            ;(i₀ = i1) → z1 k i₁ i₂
--            ;(i₁ = i0) → hcomp (λ k₁ → λ {
--                                  -- (i₀ = i0) → {!a₋₀₋ i0 (i₂ ∧ (~ k₁))!}
--                                  (i₂ = i0) → zzz i₀ k k₁
--                                 ;(i₂ = i1) → {!!}
--                                 ;(k = i1) → rotSq' a₋₀₋ k₁ i₀ i₂
--                                 -- ;(k = i0) → doubleCompPath-filler
--                                 --               (λ i → a₋₀₋ i0 i)
--                                 --               (λ i → a₋₀₋ i i1)
--                                 --               (λ i → a₁₋₋ i i1) k₁ i₂
--                               })
--                         (a₋₀₋ i₂ ((~ i₀) ∨ (~ k)))
--            ;(i₁ = i1) → hcomp (λ k₁ → λ {
--                                  -- (i₀ = i0) → {!a₋₀₋ i0 (i₂ ∧ (~ k₁))!}
--                                  (i₂ = i0) → {!!}
--                                 ;(i₂ = i1) → {!!}
--                                 ;(k = i1) → rotSq' a₋₁₋ k₁ i₀ i₂ 
--                                 -- ;(k = i0) →  doubleCompPath-filler
--                                 --               (λ i → a₀₋₋ i i0)
--                                 --               (λ i → a₋₁₋ i i0)
--                                 --               (λ i → a₋₁₋ i1 i) (k₁) i₂
--                               })
--                         (a₋₁₋ (i₂) ((~ i₀) ∧ k))
--            ;(i₂ = i0)(i₁ = i0) → a₋₋₀ (i₀ ∧ k) i0
           
--            ;(i₂ = i0) → hcomp (λ k₁ → λ {
--                                  (i₀ = i0) → (a₋₋₀ i0 (i₁ ∧ (~ k₁ ∨ k)))
--                                 ;(i₁ = i0) → a₋₋₀ (i₀ ∧ k) i0
--                                 ;(k = i1) → a₋₋₀ i₀ i₁
--                                 ;(k = i0) → a₋₋₀ i0 (i₁ ∧ (~ k₁)) 
--                               }) (a₋₋₀ (i₀ ∧ k) (i₁))
--            ;(i₂ = i1) → hcomp (λ k₁ → λ {
--                                  (i₀ = i1) → (a₋₋₁ i1 (i₁ ∨ ( k₁ ∧ (~ k))))
--                                 ;(i₁ = i1) → a₋₋₁ (i₀ ∨ (~ k)) i1
--                                 ;(k = i1) → a₋₋₁ i₀ i₁
--                                 ;(k = i0) → a₋₋₁ i1 (i₁ ∨ (k₁)) 
--                               }) (a₋₋₁ (i₀ ∨ (~ k)) (i₁))
--            ;(i₂ = i1)(i₁ = i1) → a₋₋₁ (i₀ ∨ (~ k)) i1
           
--           }


--       z' : (i₀ i₁ i₂  : I) → I → _
--       z' = λ i₀ i₁ i₂  k → z i₀ i₁ i₂  (~ k)

--       f = (λ x i₀ i₁ i₂ → hcomp (z i₀ i₁ i₂) (x i₀ i₁ i₂))
--       f' = (λ x i₀ i₁ i₂ → hcomp (z' i₀ i₁ i₂) (x i₀ i₁ i₂))

--       -- p = (λ x i i₀ i₁ i₂ → hcomp
--       --                          (λ l → primPOr i _
--       --                            (λ _ → hfill (z' i₀ i₁ i₂) (inS (x i₀ i₁ i₂)) (~ l))
--       --                       (z i₀ i₁ i₂ l)) (f' x i₀ i₁ i₂)) 

--       -- p' = (λ x i i₀ i₁ i₂ → hcomp
--       --                          (λ l → primPOr i _
--       --                            (λ _ → hfill (z i₀ i₁ i₂) (inS (x i₀ i₁ i₂)) (~ l))
--       --                       (z' i₀ i₁ i₂ l)) (f x i₀ i₁ i₂)) 

-- --      -- sq₀ : Square (a₋₀₋ i1) ((λ i → a₋₋₀  (~ i) i1) ∙' a₀₋₋ i1)
-- --      --              (a₋₋₀ i1) ((λ i → a₋₀₋  (~ i) i1) ∙' λ i → a₀₋₋ i i1)
-- --      -- sq₀ i i₁ =
-- --      --   hcomp
-- --      --    (λ k → λ {
-- --      --                (i = i0) → a₋₀₋ k i₁ 
-- --      --               ;(i = i1)(i₁ = i1) → a₀₋₋ i1 i1
-- --      --               ;(i₁ = i0) → a₋₋₀ k i
-- --      --              })
-- --      --    (a₀₋₋ i i₁ )

-- --      -- sq₁ : Square (a₁₋₋ i0 ∙ λ i → a₋₋₁ (~ i) i0) (a₋₁₋ i0)
-- --      --              ((λ i → a₁₋₋ i i0) ∙ λ i → (a₋₁₋ (~ i) i0)) (a₋₋₁ i0)
-- --      -- sq₁ i i₁ =
-- --      --   hcomp
-- --      --    (λ k → λ {
-- --      --                (i = i1) → a₋₁₋ (~ k) i₁ 
-- --      --               ;(i = i0)(i₁ = i0) → a₁₋₋ i0 i0
-- --      --               ;(i₁ = i1) → a₋₋₁ (~ k) i
-- --      --              })
-- --      --    (a₁₋₋ i i₁ )


-- --      -- Ty : {!!} ≡ {!!}
-- --      -- Ty = {!!}
 



-- --     -- where
-- --     --   zz : (x :  a₀₋ ∙ a₋₁ ≡ a₋₀ ∙ a₁₋) →
-- --     --          Cube (λ i i₁ → hcomp (λ k → (sq2-Pa a₀₋ a₁₋ a₋₀ a₋₁ i i₁) (~ k))
-- --     --                           (hcomp (sq2-Pa a₀₋ a₁₋ a₋₀ a₋₁ i i₁ ) (x i i₁))) x
-- --     --            (λ i i₁ →
-- --     --                hfill (λ k → sq2-Pa a₀₋ a₁₋ a₋₀ a₋₁ i0 i₁ (~ k ∧ ~ i))
-- --     --                (inS (hfill (sq2-Pa a₀₋ a₁₋ a₋₀ a₋₁ i0 i₁) (inS (x i0 i₁)) (~ i)))
-- --     --                (~ i))
-- --     --            (λ i i₁ →
-- --     --                hfill (λ k → sq2-Pa a₀₋ a₁₋ a₋₀ a₋₁ i1 i₁ (~ k ∧ ~ i))
-- --     --                (inS (hfill (sq2-Pa a₀₋ a₁₋ a₋₀ a₋₁ i1 i₁) (inS (x i1 i₁)) (~ i)))
-- --     --                (~ i))
-- --     --            {!!}
-- --     --            {!!} 
-- --     --   zz = (λ x j i i₁ → hfill {φ = i ∨ ~ i ∨ i₁ ∨ ~ i₁} (λ k → (sq2-Pa a₀₋ a₁₋ a₋₀ a₋₁ i i₁)
-- --     --                                          (~ k ∧ ~ j ))
-- --     --                (inS (hfill {φ = i ∨ ~ i ∨ i₁ ∨ ~ i₁}
-- --     --                   ((sq2-Pa a₀₋ a₁₋ a₋₀ a₋₁ i i₁ )) (inS (x i i₁)) (~ j))) (~ j))


-- --   -- hfill
-- --   --                        (λ k → (sq2-Pa a₀₋ a₁₋ a₋₀ a₋₁ i i₁) (~ k))
-- --   --                        (inS (hfill (sq2-Pa a₀₋ a₁₋ a₋₀ a₋₁ i i₁ ) (inS (x i i₁)) (~ j))) (~ j)

-- -- --   Pa : ℕ → Bool → Bool → Type ℓ
-- -- --   Pa zero x₁ x₂ = a false x₁ x₂ ≡ a true x₁ x₂
-- -- --   Pa (suc zero) x₁ x₂ = a x₁ false x₂ ≡ a x₁ true x₂
-- -- --   Pa (suc (suc _)) x₁ x₂ = a x₁ x₂ false ≡ a x₁ x₂ true

  

-- -- --   Pa∙ : (pa : ∀ n → ∀ b1 b2 → Pa n b1 b2) → ℕ → a false false false ≡ a true true true
-- -- --   Pa∙ pa 0 = pa 0 false false ∙ pa 1 true false ∙ pa 2 true true  -- R
-- -- --   Pa∙ pa 1 = pa 0 false false ∙ pa 2 true false ∙ pa 1 true true 
-- -- --   Pa∙ pa 2 = pa 1 false false ∙ pa 0 true false ∙ pa 2 true true -- L
-- -- --   Pa∙ pa 3 = pa 1 false false ∙ pa 2 false true ∙ pa 0 true true -- 
-- -- --   Pa∙ pa 4 = pa 2 false false ∙ pa 0 false true ∙ pa 1 true true 
-- -- --   Pa∙ pa _ = pa 2 false false ∙ pa 1 false true ∙ pa 0 true true 

-- -- --   compInjᵣ : ∀ {x y z : A} → {p₁ p₂ : x ≡ y} → {q : y ≡ z}
-- -- --                  →  p₁ ∙ q ≡ p₂ ∙ q → p₁ ≡ p₂
-- -- --   compInjᵣ {p₁ = p₁} {p₂} {q} x i i₁ =
-- -- --       hcomp
-- -- --       (λ k → λ {
-- -- --         (i = i0) → compPath-filler p₁ q (~ k) i₁
-- -- --        ;(i = i1) → compPath-filler p₂ q (~ k) i₁
-- -- --        ;(i₁ = i0) → p₁ i0
-- -- --        ;(i₁ = i1) → q (~ k)
-- -- --       })
-- -- --        (x i i₁)

-- -- --   compInjₗ : ∀ {x y z : A} → {p : x ≡ y} → {q₁ q₂ : y ≡ z}
-- -- --                  →  p ∙ q₁ ≡ p ∙ q₂ → q₁ ≡ q₂
-- -- --   compInjₗ {p = p} {q₁} {q₂} x i i₁ =
-- -- --       hcomp
-- -- --       (λ k → λ {
-- -- --         (i = i0) → compPath-filler' p q₁ (~ k) i₁
-- -- --        ;(i = i1) → compPath-filler' p q₂ (~ k) i₁
-- -- --        ;(i₁ = i1) → q₁ i1
-- -- --        ;(i₁ = i0) → p k
-- -- --       })
-- -- --        (x i i₁)

-- -- --   cuu : (pa : ∀ n → ∀ b1 b2 → Pa n b1 b2) → (pa∙ : ∀ n₁ n₂ → Pa∙ pa n₁ ≡ Pa∙ pa n₂) →  
-- -- --          Cube {a₀₀₀ = a false false false} {a₀₀₁ = a false false true} {pa 2 false false}
-- -- --                {a₀₁₀ = a false true false} {a₀₁₁ = a false true true} {pa 2 false true}
-- -- --                 {pa 1 false false} {pa 1 false true}
-- -- --                ((sq2 (compInjᵣ {q = pa 0 true true} (sym (assoc _ _ _) ∙∙ (pa∙ 5 3) ∙∙ (assoc _ _ _)) )))
-- -- --                {a₁₀₀ = a true false false} {a₁₀₁ = a true false true} {pa 2 true false}
-- -- --                {a₁₁₀ = a true true false} {a₁₁₁ = a true true true} {pa 2 true true}
-- -- --                { pa 1 true false } {pa 1 true true }
-- -- --                (sq2 (compInjₗ (pa∙ 1 0))) 
-- -- --                 { pa 0 false false } {pa 0 false true }
-- -- --                (sq2 (compInjᵣ {q = pa 1 true true} (sym (assoc _ _ _) ∙∙ pa∙ 4 1 ∙∙ assoc _ _ _)))
-- -- --                { pa 0 true false } { pa 0 true true}
-- -- --                (sq2 (compInjₗ (pa∙ 3 2)))
-- -- --                (sq2 (compInjᵣ {q = pa 2 true true} (sym (assoc _ _ _) ∙∙ pa∙ 2 0 ∙∙ (assoc _ _ _))))
-- -- --                (sq2 (compInjₗ (pa∙ 5 4)))
-- -- --   cuu = {!!}
 
  

-- -- -- module string-of {ℓ} (A : Type ℓ) (R : A → A → Type ℓ) (trans : BinaryRelation.isTrans R) where

  


-- -- --   String : ∀ n → A → Vec A n → A → Type ℓ
-- -- --   String zero x _ y = R x y
-- -- --   String (suc n) x v y = (R x (head v)) × String _ (head v) (tail v) y 

-- -- --   Perm : ∀ n → Type₀
-- -- --   Perm n = Iso (Fin n) (Fin n)
  
-- -- --   Corners : ∀ n → Type ℓ
-- -- --   Corners n = Vec Bool n → A

-- -- --   string→R : ∀ n → ∀ x → ∀ v → ∀ y → String n x v y → R x y
-- -- --   string→R = {!!}

-- -- --   trav : ∀ n → Corners n → Perm n → Vec A n
-- -- --   trav = {!!}

-- -- --   Edges : ∀ n → Corners n → Type ℓ
-- -- --   Edges n co = {!!} 

-- -- --   -- Trav : ∀ n → Perm n → (co : Corners n) → Edges n co
-- -- --   --          → Σ _ (String n)
-- -- --   -- Trav n x co x₁ .fst = {!!}
-- -- --   -- Trav n x co x₁ .snd = {!!}
