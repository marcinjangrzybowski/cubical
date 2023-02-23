{-# OPTIONS --allow-unsolved-metas #-}

module Cubical.Experiments.Tmp2 where

open import Cubical.Foundations.Everything
open import Cubical.Core.Glue
open import Cubical.Homotopy.Loopspace hiding ( Ω )
-- open import Cubical.HITs.S2
-- open import Cubical.HITs.S3

Ω Ω² Ω³ Ω⁴ : ∀ {ℓ} (A : Type ℓ) (a : A) → Type ℓ
Ω A a = a ≡ a
Ω² A a = Ω (Ω A a) refl
Ω³ A a = Ω (Ω² A a) refl
Ω⁴ A a = Ω (Ω³ A a) refl

-- "constant" squares (need a better name...)
Csq : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → Type ℓ
Csq p q = PathP (λ i → p i ≡ q i) p q

csq : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → Ω² A y → Csq p q
csq p q r i j = hcomp (λ k → λ { (i = i0) → p (~ k ∨ j)
                               ; (i = i1) → q (k ∧ j)
                               ; (j = i0) → p (~ k ∨ i)
                               ; (j = i1) → q (k ∧ i)
                               })
                      (r i j)

csq⁻¹ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → Csq p q → Ω² A y
csq⁻¹ p q r i j = hcomp (λ k → λ { (i = i0) → p (k ∨ j)
                                 ; (i = i1) → q (~ k ∧ j)
                                 ; (j = i0) → p (k ∨ i)
                                 ; (j = i1) → q (~ k ∧ i)
                                 })
                        (r i j)




transpose : ∀ {ℓ} {A : Type ℓ} {x y z : A} {p : x ≡ y} {q : y ≡ z} → Csq p q → Csq p q
transpose r i j = r j i


transposeInv' : ∀ {ℓ} {A : Type ℓ} {x : A} (p : Path (Path A x x) refl refl) →
   transpose p ≡ sym p
transposeInv' p = {!!}
  

transposeInv : ∀ {ℓ} {A : Type ℓ} {x : A} (p : Path (Path A x x) refl refl) →
  transpose p ≡ sym p
transposeInv p i j k =
  hcomp
      (λ l →
        primPOr (i ∨ ~ i) _
            (primPOr i (~ i)
               (λ _ → p (~ j) k) (λ _ → p k j))
          (primPOr (j ∨ ~ j) _
             (primPOr j (~ j)
                (λ _ → p (~ i ∧ k ∧ ~ l) (~ i ∨ k))
                (λ _ → p (i ∨ k ∨ l) (i ∧ k)))
             (primPOr (k) (~ k)
               (λ _ → p (~ i ∨ ~ j ∨ l) (i ∨ j))
               λ _ → p (i ∧ ~ j ∧ ~ l) (~ i ∧ j))))
        (p ((~ j ∧ k) ∨ (i ∧ ~ j) ∨ (~ i ∧ k)) ((j ∧ k) ∨ (~ i ∧ j) ∨ (i ∧ k)))

-- -- "homogeneous" squares (again need a better name...)
-- hsq : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → Ω² A x → p ≡ p
-- hsq {x = x} p s i j = hcomp (λ k → λ { (i = i0) → p (j ∧ k)
--                                      ; (i = i1) → p (j ∧ k)
--                                      ; (j = i0) → x
--                                      ; (j = i1) → p k
--                                      })
--                             (s i j)

-- hsq⁻¹ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ p → Ω² A x
-- hsq⁻¹ {x = x} p s i j = hcomp (λ k → λ { (i = i0) → p (j ∧ ~ k)
--                                        ; (i = i1) → p (j ∧ ~ k)
--                                        ; (j = i0) → x
--                                        ; (j = i1) → p (~ k)
--                                        })
--                               (s i j)

-- 𝟙' -𝟙' : ∀ {ℓ} {A : Type ℓ} {x : A} (s : Ω² A x) → Csq s s
-- 𝟙' {x = x} s i j k =
--   hcomp (λ f → λ { (i = i0) → s j (k ∧ f)
--                  ; (i = i1) → s j (k ∧ f)
--                  ; (j = i0) → s i k
--                  ; (j = i1) → s i k
--                  ; (k = i0) → x
--                  ; (k = i1) → s j f
--                  })
--         (s i k)
-- -𝟙' {x = x} s i j k =
--   hcomp (λ f → λ { (i = i0) → s j k
--                  ; (i = i1) → s j k
--                  ; (j = i0) → s i (k ∧ f)
--                  ; (j = i1) → s i (k ∧ f)
--                  ; (k = i0) → x
--                  ; (k = i1) → s i f
--                  })
--         (s j k)

-- 𝟙 -𝟙 : ∀ {ℓ} {A : Type ℓ} {x : A} → Ω² A x → Ω³ A x
-- 𝟙 s = csq⁻¹ s s (𝟙' s)
-- -𝟙 s = csq⁻¹ s s (-𝟙' s)

-- 𝟚' : ∀ {ℓ} {A : Type ℓ} {x : A} (s : Ω² A x) → Path (Ω² A x) s s
-- 𝟚' s j a b =
--   hcomp (λ i → λ { (j = i0) → s a b
--                  ; (j = i1) → s a b
--                  ; (a = i0) → s i j
--                  ; (a = i1) → s i j
--                  ; (b = i0) → s i j
--                  ; (b = i1) → s i j
--                  })
--         (s a b)

-- 𝟚 : ∀ {ℓ} {A : Type ℓ} {x : A} → Ω² A x → Ω³ A x
-- 𝟚 s = hsq⁻¹ s (𝟚' s)


-- -- S² examples
-- module _ ℓ
--   (A : Type ℓ)
--   (x : A)
--   (s : PathP (λ i → PathP (λ j → A) x x) refl refl)
--   where
--   ex₁ : Csq {A = Ω A x} s s
--   ex₁ = 𝟙' s

--   ex₂ : Ω³ A x
--   ex₂ = 𝟙 s

--   ex₃ : Path (Ω² A x) s s
--   ex₃ = 𝟚' s

--   ex₄ : Ω³ A x
--   ex₄ = 𝟚 s

--   -- proving this would be nice. maybe it is better to start with some
--   -- alternative definition of "1 + 1"? _∙_ is kind of weird...
--   ex₅ : Path (Ω³ A x) (𝟙 s ∙ 𝟙 s) (𝟚 s)
--   ex₅ = {!!}

-- -- This type models ΩS³ (accurate up to π₄J₂S² ≃ π₅S³)

-- data J₂S² : Type where
--   base : J₂S²
--   surf : PathP (λ i → PathP (λ j → J₂S²) base base) refl refl
--   surf₂ : PathP (λ i → PathP (λ j → PathP (λ a → PathP (λ b → J₂S²) (surf i j) (surf i j)) refl refl) (λ a b → surf a b) (λ a b → surf a b)) refl refl

-- -- surf₂ gives us a path from 𝟙 to -𝟙
-- module _ ℓ
--   (J₂S² : Type ℓ)
--   (base : J₂S²)
--   (surf : PathP (λ i → PathP (λ j → J₂S²) base base) refl refl)
--   (surf₂ : PathP (λ i → PathP (λ j → PathP (λ a → PathP (λ b → J₂S²) (surf i j) (surf i j)) refl refl) (λ a b → surf a b) (λ a b → surf a b)) refl refl)
--   where
--   ex₆ : Path (Csq {A = Ω J₂S² base} surf surf) (𝟙' surf) (-𝟙' surf)
--   ex₆ f i j k =
--     hcomp (λ l → λ { (i = i0) → surf j (k ∧ (l ∨ f))
--                    ; (i = i1) → surf j (k ∧ (l ∨ f))
--                    ; (j = i0) → surf i (k ∧ (l ∨ ~ f))
--                    ; (j = i1) → surf i (k ∧ (l ∨ ~ f))
--                    ; (k = i0) → base
--                    ; (k = i1) → surf₂ i (l ∨ ~ f) j (l ∨ f)
--                    })
--           (surf₂ i (k ∧ ~ f) j (k ∧ f))

--   ex₇ : Path (Ω³ J₂S² base) (𝟙 surf) (sym (𝟙 surf))
--   ex₇ = cong (csq⁻¹ surf surf) ex₆ ∙ transposeInv (𝟙 surf)

-- -- S³ examples
-- module _ ℓ
--   (S³ : Type ℓ)
--   (base : S³)
--   (surf : PathP (λ i → PathP (λ j → PathP (λ k → S³) base base) refl refl) refl refl)
--   where
--   -- computations in cubicaltt seem to confirm that this should also be
--   -- "1" in Ω⁴S³.
--   ex₈ : Ω⁴ S³ base
--   ex₈ = 𝟙 surf

--   -- so we should have an analogous proof of 𝟙 = -𝟙... but how?
--   ex₉ : Path (Ω⁴ S³ base) (𝟙 surf) (sym (𝟙 surf))
--   ex₉ = {!!}

--   -- similarly, we should have this:
--   ex₁₀ : Path (Ω⁴ S³ base) (𝟚 surf) refl
--   ex₁₀ = {!!}

-- -- more S² examples
-- module _ ℓ
--   (S² : Type ℓ)
--   (base : S²)
--   (surf : Ω² S² base)
--   where
--   -- I expect this 4-cell to exist but I don't know how  
--   ex₁₁ : PathP (λ i → PathP (λ j → PathP (λ k → Ω S² base) (𝟙' surf i j) (𝟙' surf i j)) (λ k → 𝟙' surf i k) (λ k → 𝟙' surf i k)) (λ j k → 𝟙' surf j k) (λ j k → 𝟙' surf j k)
--   ex₁₁ = {!!}

--   -- this is one version of the "Eckmann-Hilton" generator of π₃S² as
--   -- defined using the Cubical library... :(
--   ex₁₂ : Ω³ S² base
--   ex₁₂ = sym (rCancel surf) ∙∙ EH 0 surf (sym surf) ∙∙ lCancel surf

-- Z : ∀ {ℓ} (A : Type ℓ) → Type ℓ
-- Z A = Path (A → A) (λ x → x) (λ x → x)

-- module _ {ℓ} {A : Type ℓ} (h : Z A) (i j : I) where
--   globalSys : Partial (~ i ∨ i ∨ ~ j ∨ j) (Σ[ T ∈ Type ℓ ] T ≃ A)
--   globalSys (i = i0) = A , idEquiv A
--   globalSys (i = i1) = A , idEquiv A
--   globalSys (j = i0) = A , equivEq {e = idEquiv A} {f = idEquiv A} (λ k x → h k x) i
--   globalSys (j = i1) = A , idEquiv A

-- global : ∀ {ℓ} {A : Type ℓ} → Z A → Ω² (Type ℓ) A
-- global {A = A} h i j = Glue A (globalSys h i j)

-- local :  ∀ {ℓ} {A : Type ℓ} → Ω² (Type ℓ) A → Z A
-- local h i = transp (λ j → h i j) (i ∨ ~ i)
