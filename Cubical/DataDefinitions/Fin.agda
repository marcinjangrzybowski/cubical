{-# OPTIONS --cubical --no-exact-split --safe #-}

module Cubical.DataDefinitions.Fin where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Logic

open import Cubical.Data.Sum

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Data.Universe

import Cubical.Data.Nat as orgℕ
import Cubical.Data.Nat.Order as orgℕOrder
import Cubical.Data.Fin as orgFin

import Cubical.Data.Empty as Empty

open import Cubical.DataDefinitions.Definition
open import Cubical.DataDefinitions.Nat




record IsFin {ℕ : Set₀} (isNat-ℕ : isNat ℕ) (Fin : ℕ → Type₀) : Type (ℓ-suc ℓ-zero) where
  constructor isFin

  open isNat isNat-ℕ

  field
    fzero : {n : ℕ} →  Fin (suc n)
    fsuc : {n : ℕ} → (i : Fin n) → Fin (suc n)
    ¬Fin0 : Fin zero → (fst ⊥)
    finduction : ∀(P : ∀{k} → Fin k → Type₀)
                     → (∀{k} → P {suc k} fzero)
                     → (∀{k} {fn : Fin k} → P fn → P (fsuc fn))
                     → {k : ℕ} → (fn : Fin k) → P fn
    finduction-zero : ∀ (P : ∀{k} → Fin k → Type₀)
                        → (fz : ∀{k} → P {suc k} fzero)
                        → (fs : (∀{k} {fn : Fin k} → P fn → P (fsuc fn)))
                        → ∀ k
                         → finduction P fz fs {suc k} fzero ≡ fz
    finduction-suc : ∀ (P : ∀{k} → Fin k → Type₀)
                        → (fz : ∀{k} → P {suc k} fzero)
                        → (fs : (∀{k} {fn : Fin k} → P fn → P (fsuc fn)))
                        → ∀ k → ∀ fi
                         → finduction P fz fs {suc k} (fsuc fi) ≡  fs (finduction P fz fs {k} (fi))



IsFin-Fin : IsFin IsNat-ℕ orgFin.Fin
IsFin-Fin = isFin
  fzero
  fsuc
  ¬Fin0
  finduction
  finduction-org-zero
  finduction-org-suc

  where
    open orgFin


    finduction-org-zero : (P : {k : orgℕ.ℕ} → Fin k → Type₀) (fz : {k : orgℕ.ℕ} → P fzero)
                            (fs : {k : orgℕ.ℕ} {fn : Fin k} → P fn → P (fsuc fn))
                            (k : orgℕ.ℕ) →
                            finduction P fz fs fzero ≡ fz
    finduction-org-zero P fz fs k = isSet-subst {B = P} (isSetFin) (toℕ-injective (λ _ → toℕ (fzero {k}))) fz

    subst-help : ∀ {ℓ ℓ′} → ∀ {A : Set ℓ} → (B : A → Set ℓ′)
                 → ∀ {a b} → (p : a ≡ b) → (f : ∀ a → B a)
                 → subst B p (f a) ≡ f b 
    subst-help B {a} {b} p f = J (λ y x → subst B x (f a) ≡ f y) (substRefl {x = b} (f a)) p

    finduction-help : (P : {k : orgℕ.ℕ} → Fin k → Type₀) (fz : {k : orgℕ.ℕ} → P {orgℕ.suc k} fzero)
                           (fs : {k : orgℕ.ℕ} {fn : Fin k} → P fn → P (fsuc fn)) (k : orgℕ.ℕ)
                           (fi fi′ : Fin k) → ∀ p₁ → ∀ p₂ → ∀ e 
                           → subst {x = fi} {y = fi′} (P {k}) e p₁ ≡ p₂
                           → subst {x = fsuc fi} {y = fsuc fi′} (P {orgℕ.suc k}) (cong fsuc e) (fs p₁) ≡ (fs p₂)
    finduction-help P fz fs k fi fi′ p₁ p₂ e x =  
      (( J (λ y x₁ → ∀ qq →  subst P qq (fs p₁) ≡ fs (subst P x₁ p₁))
      (λ qq → (isSet-subst {B = λ x₁ → P x₁} isSetFin qq (fs p₁)
      ∙  (cong fs (sym (substRefl {B = P} p₁))))) e (cong fsuc e)))
      ∙ cong fs x 
    
    finduction-org-suc : (P : {k : orgℕ.ℕ} → Fin k → Type₀) (fz : {k : orgℕ.ℕ} → P fzero)
                           (fs : {k : orgℕ.ℕ} {fn : Fin k} → P fn → P (fsuc fn)) (k : orgℕ.ℕ)
                           (fi : Fin k) →
                           finduction P fz fs (fsuc fi) ≡ fs (finduction P fz fs fi)
    finduction-org-suc P fz fs k fi =
      let w =  λ (qq : ((fst fi , orgℕOrder.pred-≤-pred (snd (fsuc fi)))) ≡ fi) → subst-help (P) qq (λ x → (finduction P (λ {k = k₁} → fz) fs x)) in
      let wq =  (fs
                  (finduction P (λ {k = k₁} → fz) fs
                    (fst fi , orgℕOrder.pred-≤-pred (snd (fsuc fi)))))
      in (cong (λ q → subst P q wq) (isSetFin _ _ _ _))
        ∙ (finduction-help P fz fs k _ _ ((finduction P (λ {k = k₁} → fz) fs
        (fst fi , orgℕOrder.pred-≤-pred (snd (fsuc fi))))) _ _ (w (toℕ-injective refl))) 




IsFamilyDefinition-IsFin : IsFamilyDefinition {isNat} {isDefinition-isNat} IsFin
IsFamilyDefinition-IsFin =
  isFamilyDefinition
    wf1 
    wf-law
    wf2
    
  where

    wf1 : ∀ {ℕ} → ∀ {isnat : isNat ℕ} → ∀ A₁ A₂
            → (isfin₁ : IsFin isnat A₁) → (isfin₂ : IsFin isnat A₂) → ∀ a₀ → A₁ a₀ → A₂ a₀
    wf1 {ℕ} {isnat} A₁ A₂ isfin₁ isfin₂ = isNat.ℕ-induction isnat (λ z → A₁ z → A₂ z)
      (Empty.⊥-elim ∘(IsFin.¬Fin0 isfin₁))
      λ n x → IsFin.finduction isfin₁ (λ {v} v₁ → A₂ v) (IsFin.fzero isfin₂ ) (IsFin.fsuc isfin₂) {isNat.suc isnat n}


    
    

    wf-law : ∀ {ℕ} → ∀ {isnat : isNat ℕ} → ∀ A → ∀ isfin → (n : ℕ) → (x : A n) → wf1 {isnat = isnat} A A isfin isfin n x ≡ x
    wf-law {ℕ} {isnat} A isfin = isNat.ℕ-induction isnat
           (λ z → (x : A z) → wf1 A A isfin isfin z x ≡ x)
           ((Empty.⊥-elim ∘(IsFin.¬Fin0 isfin)))
           λ n x fi → cong (λ q → q fi) (isNat.ℕ-induction-suc isnat (λ z → A z → A z) _ _ n)
           ∙  (IsFin.finduction isfin
               (λ {v} v₁ → IsFin.finduction isfin (λ {v} v₁ → A v) (IsFin.fzero isfin) (λ {k} {fn} → IsFin.fsuc isfin) v₁ ≡ v₁)
               ( λ {k} → IsFin.finduction-zero isfin (λ {v} v₁ → A v) (λ {k = k₁} → IsFin.fzero isfin) (λ {k = k₁} {fn} → IsFin.fsuc isfin) k)
               (λ {k} {fj} =fsuc →
                 (IsFin.finduction-suc isfin (λ {v} v₁ → A v) (λ {k = k₁} → IsFin.fzero isfin) (λ {k = k₁} {fn} → IsFin.fsuc isfin) k fj)
                 ∙ cong (IsFin.fsuc isfin) =fsuc
                 )
               fi)

    wf2 : ∀ {ℕ} → ∀ {isnat : isNat ℕ} → ∀ A₁ A₂
            → (isfin₁ : IsFin isnat A₁) → (isfin₂ : IsFin isnat A₂) → ∀ n
            → section (wf1 {isnat = isnat} A₂ A₁ isfin₂ isfin₁ n) (wf1 {isnat = isnat} A₁ A₂ isfin₁ isfin₂ n)            
    wf2 {ℕ} {isnat} A₁ A₂ isfin₁ isfin₂ =
     ℕ-induction _
      (((Empty.⊥-elim ∘(IsFin.¬Fin0 isfin₁))))
      λ n x → 
       IsFin.finduction isfin₁
        (λ {v} fv → (wf1 A₂ A₁ isfin₂ isfin₁ (v)) ((wf1 A₁ A₂ isfin₁ isfin₂ (v)) fv) ≡ fv)
        (λ {k} →  (cong (λ f → f ((ℕ-induction (λ z → A₁ z → A₂ z)
       (λ x₁ → Empty.⊥-elim (IsFin.¬Fin0 isfin₁ x₁))
       (λ n₁ x₁ →
          IsFin.finduction isfin₁ (λ {v} v₁ → A₂ v) (IsFin.fzero isfin₂)
          (λ {k = k₁} {fn} → IsFin.fsuc isfin₂))
       (suc k) (IsFin.fzero isfin₁))))  (h1 _ _ k _ _))
       ∙ cong (IsFin.finduction isfin₂ (λ {v} v₁ → A₁ v)
      (IsFin.fzero isfin₁) (λ {k = k₁} {fn} → IsFin.fsuc isfin₁)) (cong (λ f → f (IsFin.fzero isfin₁)) (h1 A₂ A₁ k _ _))
        ∙ cong (IsFin.finduction isfin₂ (λ {v} v₁ → A₁ v)
      (λ {k = k₁} → IsFin.fzero isfin₁)
      (λ {k = k₁} {fn} → IsFin.fsuc isfin₁)) (IsFin.finduction-zero isfin₁ (λ {v} v₁ → A₂ v) (λ {k = k₁} → IsFin.fzero isfin₂) (λ {k = k₁} {fn} → IsFin.fsuc isfin₂) k) 
        ∙ (IsFin.finduction-zero isfin₂ (λ {v} v₁ → A₁ v) (λ {k = k₁} → IsFin.fzero isfin₁) (λ {k = k₁} {fn} → IsFin.fsuc isfin₁) k)
         )
        {!
        !}

      where

      open isNat isnat

      h1 : ∀ (A₁ A₂ : ℕ → Type₀) → ∀ k → ∀ ze → ∀ s →  ℕ-induction (λ z → A₂ z → A₁ z) ze s (suc k) ≡
                                s k (ℕ-induction (λ z → A₂ z → A₁ z) ze s k)
      h1  A₁ A₂ k ze s = ℕ-induction-suc (λ z → A₂ z → A₁ z) ze s k




Fin⊎ : orgℕ.ℕ → Set
Fin⊎ orgℕ.zero = fst ⊥
Fin⊎ ((orgℕ.suc x)) = (Fin⊎ (x)) ⊎ Unit

IsFin-Fin⊎ : IsFin IsNat-ℕ Fin⊎
IsFin-Fin⊎ = isFin
  (_⊎_.inr _)
  _⊎_.inl
  (idfun _)
  finduction⊎
  (λ P fz fs k → refl)
  λ P fz fs k fi → refl

  where

   

    finduction⊎ : (P : {k : orgℕ.ℕ} → Fin⊎ k → Type₀) →
                    ({k : orgℕ.ℕ} → P (_⊎_.inr tt)) →
                    ({k : orgℕ.ℕ} {fn : Fin⊎ k} → P fn → P _) →
                    {k : orgℕ.ℕ} (fn : Fin⊎ k) → P fn
    finduction⊎ P x x₁ {orgℕ.suc k} (_⊎_.inl x₂) = x₁ (finduction⊎ P x x₁ {k} x₂)
    finduction⊎ P x x₁ {orgℕ.suc k} (_⊎_.inr x₂) = x

