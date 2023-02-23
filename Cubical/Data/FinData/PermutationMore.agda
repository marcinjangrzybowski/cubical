{-# OPTIONS --safe #-}
module Cubical.Data.FinData.PermutationMore where

open import Cubical.Foundations.Everything
open import Cubical.Data.FinData
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.FinData.Properties

open import Cubical.Algebra.Group

open import Cubical.Algebra.Group.Morphisms

open import Cubical.Algebra.Group.Generators

open import Cubical.Data.FinData.Permutation

open import Cubical.HITs.ListedFiniteSet.Base2 as FM2

open import Cubical.Relation.Binary

open import Cubical.HITs.GroupoidQuotients as GQ renaming ([_] to [_]//)


infixr 9 _∘'_

_∘'_ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
        → (g : B → C) → (f : A → B) → A → C 
g ∘' f = λ x → g (f x)
{-# INLINE _∘'_ #-}


module FC2M {ℓ} {A : Type ℓ} where

 
  record _↔ₙ_  {n} (x y : Fin n → A) : Type ℓ where
    constructor prm
    field
      F≃ : Perm n
      l≡ : x ∘ (fst (to≃ n F≃)) ≡ y 
       



  open _↔ₙ_

  open import Cubical.HITs.FreeGroup.IPresentation3

  open Presentation

  isTrans↔ₙ : ∀ n → BinaryRelation.isTrans (_↔ₙ_ {n = n}) 
  isTrans↔ₙ n a b c (prm e p) (prm f q) =
    prm (f · e) (cong (_∘' fst (to≃ n f)) p ∙ q)

  Fin→//↔ : ℕ → Type ℓ
  Fin→//↔ n = (Fin n → A) // isTrans↔ₙ n

  tabulateFM2 : ∀ {n} → (Fin n → A) → FMSet2 A
  tabulateFM2 {zero} _ = []
  tabulateFM2 {suc n} f = (f zero) ∷2 tabulateFM2 (f ∘ suc)


  record Elim≡ (B : Type ℓ) : Type ℓ where
    field
      grpB : isGroupoid B
      b : ∀ n → (Fin n → A) → B
      b= : ∀ n k → (x y : (Fin (suc n) → A))
        → x ∘ fst (adjTransposition k) ≡ y → b (suc n) x ≡ b (suc n) y
      -- invoB= : ∀ n → (x y : (Fin (suc n) → A)) → ∀ k
      --    → PathP (λ i → (p : x ∘ (fst (adjTransposition²=idEquiv k i)) ≡ y)
      --                  → b (suc n) x ≡ b (suc n) y)
      --       (λ p → b= n k x _ refl
      --            ∙ b= n k _ y p)
      --       (cong (b (suc n)))
      -- braidB= : ∀ n k → (x y : (Fin (suc (k + suc (suc n))) → A)) 
      --    → PathP (λ i → (p : x ∘ (fst (adjTranspositionBraid  i)) ≡ y)
      --                  → b _ x ≡ b _ y)
      --       (λ p → ((((b= _ (+k one) x _ refl
      --               ∙ b= _ (+k zero) _ _ refl)
      --               ∙ b= _ (+k one) _ _ refl)
      --               ∙ b= _ (+k zero) _ _ refl)
      --               ∙ b= _ (+k one) _ _ refl)
      --               ∙ b= _ (+k zero) _ y p)
      --       (cong (b _))
      -- commB= : ∀ k n → ∀ k' → (x y : (Fin (suc k + (suc (suc n))) → A)) 
      --    → PathP (λ i → (p : x ∘ (fst (commTranspositions' k'  i)) ≡ y)
      --                  → b _ x ≡ b _ y)
      --       (λ p →  ((b= _ (+k (suc (suc k'))) x _ refl
      --               ∙ b= _ (+k zero) _ _ refl)
      --               ∙ b= _ (+k (suc (suc k'))) _ _ refl)
      --               ∙ b= _ (+k zero) _ y p)
      --       (cong (b _))


    fR= : ∀ n → (e : Perm n) → (x y : Fin n → A)
            → (p : x ∘ fst (to≃ n e) ≡ y) → b n x ≡ b n y
    fR= = {!!}

    fR : ∀ n → GQ.Rrec {Rt = isTrans↔ₙ n} B
    Rrec.Bgpd (fR n) = grpB
    Rrec.fb (fR n) = b n
    Rrec.feq (fR n) (prm e p) =
      fR= n e _ _ p
    -- Rrec.fsq (fR zero) (prm e p) (prm f q) =
    --   congP (λ _ → cong (b zero)) {!!}
    Rrec.fsq (fR n) (prm e p) (prm f q) =
      -- {!!}
      compPath-filler _ _ ▷ {!!}
           --   (λ i → fR= n e _ (p (~ i)) (λ j → p (~ i ∧ j))
           -- ∙ fR= n f (p (~ i)) _
           --   (compPath-filler' (cong ((_∘' fst (to≃ n f))) p) q i))

    -- Rrec.Bgpd (toFM2r n) = trunc
    -- Rrec.fb (toFM2r n) = tabulateFM2 {n}
    -- Rrec.feq (toFM2r n) (prm e p) =
    --   toFM2≡UC n e _ _ p


    f : ∀ n → Fin→//↔ n → B
    f n = GQ.Rrec.f (fR n)




    -- -- fR= : ∀ n → (e : fst (Perm n)) → (x y : Fin n → A)
    --         → (p : x ∘ fst (to≃' n e) ≡ y) → b n x ≡ b n y
    -- fR= zero e x y p = cong (b zero) =■
    -- fR= (suc n) (η k) x y p = b= n k x y p
    -- fR= (suc n) (e · e₁) x y p =
    --     fR= (suc n) e₁ x _ refl
    --   ∙ fR= (suc n) e _ y p
    -- fR= (suc n) ε x y = cong (b (suc n))
    -- fR= (suc n) (inv e) x y p =
    --   sym (fR= (suc n) e y x
    --     (cong (_∘' fst (to≃' (suc n) e)) (sym p)
    --       ∙ cong (x ∘'_ ) (funExt (retEq (to≃' (suc n) e)))))
    -- fR= (suc n) (PresentedGroup.assoc e e₁ e₂ i) x y p =
    --    GL.assoc
    --   (fR= (suc n) e₂ x _ refl)
    --   (fR= (suc n) e₁ _ _  refl)
    --   (fR= (suc n) e _ y p) (~ i)
    -- fR= (suc n) (idr e i) x y p = lUnit (fR= (suc n) e x y p) i
    -- fR= (suc n) (idl e i) x y p =
    --    (rUnit (fR= (suc n) e x y p) ∙
    --      λ i → fR= (suc n) e x (p (~ i)) (λ j → p (~ i ∧ j))
    --        ∙ cong (b (suc n)) λ j → p (~ i ∨ j)) i
    -- fR= (suc n) (invr e i) x y p = {!!}
    -- fR= (suc n) (invl e i) x y p = {!!}
    -- fR= (suc .(k + suc n)) (rel (zero {k = k} (invo {n})) i) x y p j =  
    --   invoB= (k + suc n) x y (+k zero) i p j
    -- fR= (suc .(k + suc (suc n))) (rel (zero {k = k} (braid {n})) i) x y p =
    --   braidB= n k x y i p
    -- fR= (suc .(k + suc (suc n))) (rel (zero {k = k} (comm {n} x₁)) i) x y p =
    --   commB= k n x₁ x y i p
    -- fR= (suc n) (trunc e e₁ x₁ y₁ i i₁) x y p j =
    --   {!!}
