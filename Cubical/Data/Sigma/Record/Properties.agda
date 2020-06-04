{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Record.Properties where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ⊥-rec )

open import Cubical.Foundations.Everything

open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Sigma.Record.Base


push-popVal-Iso : ∀ {ℓ} → ∀ {n}
                     → (A : Sigₗ ℓ n)
                     → Iso (Σ (Recₗ (trim-sig A)) (pop-Type-overRecₗ A))
                           (Recₗ A)
Iso.fun (push-popVal-Iso A) x = pushVal A (fst x) (snd x)
Iso.inv (push-popVal-Iso A) x = trim-rec A x , popVal A x 
Iso.rightInv (push-popVal-Iso {n = zero} A) b = refl
Iso.rightInv (push-popVal-Iso {n = suc zero} A) b = refl
Iso.rightInv (push-popVal-Iso {n = suc (suc zero)} A) b = refl
Iso.rightInv (push-popVal-Iso {n = suc (suc (suc n))} A) b i =
  (fst b) , Iso.rightInv (push-popVal-Iso (snd A (fst b))) (snd b) i
Iso.leftInv (push-popVal-Iso {n = zero} A) a = refl
Iso.leftInv (push-popVal-Iso {n = suc zero} A) a = refl
Iso.leftInv (push-popVal-Iso {n = suc (suc zero)} A) a = refl
Iso.leftInv (push-popVal-Iso {n = suc (suc (suc n))} A) a i =
  let prev = Iso.leftInv (push-popVal-Iso (snd A (fst (fst a))))
            (snd (fst a) , (snd a)) i

  in  (fst (fst a) , (fst prev)) , snd prev


push-trim : ∀ {ℓ} → ∀ {n} → {s : Sigₗ ℓ n}
             → ∀ x → trim-sig (push-Type s x) ≡ s
push-trim {n = zero} x = refl
push-trim {n = suc zero} x = refl
push-trim {n = suc (suc n)} {s} x i = fst s , λ a → push-trim ( x ∘ (a ,_)) i

push-trim-Recₗ : ∀ {ℓ} → ∀ {n} → {s : Sigₗ ℓ n} → ∀ x →
                   Σ (Recₗ (trim-sig (push-Type s x)))
                      (pop-Type-overRecₗ (push-Type s x))
                   ≡ Σ (Recₗ s) x
push-trim-Recₗ {ℓ} {0} {s = s} x = refl
push-trim-Recₗ {ℓ} {1} {s = s} x = refl
push-trim-Recₗ {ℓ} {suc (suc n)} {s = s} x
  = 
 isoToPath (push-popVal-Iso (push-Type s x))
   ∙∙ cong (Σ (fst s))
        ((funExt (λ x₁ →
          sym (isoToPath (push-popVal-Iso  (snd (push-Type s x) x₁)))
          ∙ push-trim-Recₗ {s = (snd s x₁)}  (λ b → x (x₁ , b)))))
   ∙∙ sym (ua  assocΣ)


concatSigₗ : ∀ {ℓ} → ∀ {n m} → Sigₗ ℓ n → Sigₗ ℓ m → Sigₗ ℓ (n + m)
concatSigₗ {n = zero} {zero} x x₁ = _
concatSigₗ {n = zero} {suc m} x x₁ = x₁
concatSigₗ {n = suc n} {zero} x x₁ = subst (Sigₗ _) (sym (+-zero (suc n))) x 
concatSigₗ {n = suc zero} {suc m} x x₁ = x , (λ _ → x₁)
concatSigₗ {n = suc (suc n)} {suc m} x x₁ = (fst x) , λ a → concatSigₗ (snd x a) x₁

concatSigₗ-rec-Iso : ∀ {ℓ} → ∀ {n m} → (sₙ : Sigₗ ℓ n) → (sₘ : Sigₗ ℓ m) →
                      Iso (Recₗ sₙ × Recₗ sₘ) (Recₗ (concatSigₗ sₙ sₘ)) 
concatSigₗ-rec-Iso {n = zero} {zero} sₙ sₘ =
  iso (λ x → lift tt) (λ _ → lift tt , lift tt) (λ _ → refl) λ _ → refl
concatSigₗ-rec-Iso {n = zero} {suc m} sₙ sₘ =
  iso snd (_ ,_) (λ b → refl) λ a → refl

concatSigₗ-rec-Iso {ℓ} {n = suc n} {zero} sₙ _ = 
  compIso (iso fst (_, _) (λ _ → refl) (λ _ → refl))
   (pathToIso λ i → Recₗ (transp (λ i₁ → Sigₗ ℓ (suc (+-zero n (~ i₁ ∨ (~ i))))) (~ i) sₙ))
  
concatSigₗ-rec-Iso {n = suc zero} {suc m} sₙ sₘ =
  iso (λ x → x) (λ x → x) (λ b → refl) (λ b → refl)

concatSigₗ-rec-Iso {n = suc (suc n)} {suc m} sₙ sₘ =
  let prev : (x : fst sₙ) → Iso (Recₗ (snd sₙ x) × Recₗ sₘ) (Recₗ (concatSigₗ (snd sₙ x) sₘ))
      prev x = concatSigₗ-rec-Iso {n = suc n} {suc m} ((snd sₙ) x) sₘ
  in
   iso
    (λ x → fst (fst x) , Iso.fun (prev (fst (fst x))) (snd (fst x) , snd x))
    (λ x → let y = Iso.inv (prev (fst x)) (snd x)
           in (fst x ,  fst y) , snd y)
    (λ b i → fst b , Iso.rightInv (prev (fst b)) (snd b) i )
    λ a i → let y = Iso.leftInv (prev (fst (fst a))) ( snd (fst a) , snd a) i
             in ((fst (fst a)) , fst y) , snd y 


concatSigₗ-dep : ∀ {ℓ} → ∀ {n m}
                 → (s : Sigₗ ℓ n)
                 → (Recₗ s → Sigₗ ℓ m)
                 → Sigₗ ℓ (n + m)
concatSigₗ-dep {n = zero} {m = m} s x = x _
concatSigₗ-dep {n = suc n} {m = zero} s x = subst (Sigₗ _) (sym (+-zero (suc n))) s 
concatSigₗ-dep {n = suc zero} {m = suc m} s x = s , x
concatSigₗ-dep {n = suc (suc n)} {m = suc m} s x =
  (fst s) , (λ a → concatSigₗ-dep (snd s a) (x ∘ (a ,_ )))



---------- LR - ISO Start


zzzz  : ∀ {ℓ} → ∀ n → (A : Type ℓ)
           → ((A → Sigₗ ℓ (suc (suc n))) ,
                (λ x x₁ → Σ (fst (x x₁)) (λ x₂ → Recₗ (snd (x x₁) x₂))))
               ≡
               (Σ (A → Sigₗ ℓ (suc n)) (λ x → Recₗ (A , x) → Type ℓ) ,
                (λ z z₁ → Σ (Recₗ (fst z z₁)) (λ x₂ → snd z (z₁ , x₂))))
zzzz n A = pathΣ-pairPath 
             (λ x x₁ → Σ (fst (x x₁)) (λ x₂ → Recₗ (snd (x x₁) x₂)))
             (lem n A) (lem2 n A)

  where
     lem : ∀ {ℓ} → ∀ n → (A : Type ℓ)
             →  Iso (A → Sigₗ ℓ (suc (suc n)))
                (Σ (A → Sigₗ ℓ (suc n)) λ x → Recₗ {n = suc (suc n)} (A , x) → Type ℓ)  
     Iso.fun (lem n A) x = (trim-sig ∘ x) , pop-Type-overRecₗ (A , x)
     Iso.inv (lem n A) x a = push-Type (fst x a) ((snd x) ∘ ( a ,_ ))
     fst (Iso.rightInv (lem zero A) b i) x = push-trim (snd b ∘ (x ,_)) i
     snd (Iso.rightInv (lem zero A) b i) x = snd b x
     Iso.rightInv (lem (suc n) A) b i =
       let z = Iso.rightInv (lem n (Σ A (fst ∘ (fst b)))) ((λ x₁ → snd (fst b (fst x₁)) (snd x₁))
                , λ x → snd b (fst (fst x) , snd (fst x) , snd x)) i
       in (λ x → (fst (fst b x)) , (λ x₁ → fst z (x , x₁))) ,
           λ x → snd z ((fst x , fst (snd x)) , snd (snd x)) 
     Iso.leftInv (lem zero A) a i x = a x
     Iso.leftInv (lem (suc n) A) y i a = (fst (y a)) , Iso.leftInv (lem n (fst (y a)) ) (snd (y a)) i

     lem2 : ∀ {ℓ} n (A : Type ℓ) 
              (a₁ : Σ (A → Sigₗ ℓ (suc n)) (λ b → Recₗ (A , b) → Type ℓ))
              (a : A) →

                     (Σ (fst (Iso.inv (lem n A) a₁ a))
                      (λ x₂ → Recₗ (snd (Iso.inv (lem n A) a₁ a) x₂)))
                      ≡
                     (Σ (Recₗ (fst a₁ a)) (λ x₂ → snd a₁ (a , x₂)))
     lem2 zero A a₁ a = refl
     lem2 (suc n) A a₁ a =
        cong (Σ _) (funExt (λ x → lem2 n
            (fst (fst a₁ a))
            ((snd (fst a₁ a) ) , λ x₁ → snd a₁ (a , x₁))
            x)) ∙ sym (ua assocΣ)


     pathΣ-pairPath : ∀ {ℓ ℓ'} → {A : Type ℓ'}
                         → {A₀ A₁ : Type ℓ}
                         → (B₀ : A₀ → A → Type ℓ') → {B₁ : A₁ → A → Type ℓ'}
                         → (p : Iso A₀ A₁)
                         → (∀ (a₁ : A₁) → ∀ (a : A) → (B₀ (Iso.inv p a₁) a) ≡ (B₁ a₁ a))
                         → Path (Σ (Type ℓ) (λ x → x → A → Type ℓ'))
                            (A₀ , B₀) (A₁ , B₁)
     pathΣ-pairPath B₀ {B₁} p p2 =
         sigmaPath→pathSigma (_ , B₀) (_ , B₁) ((isoToPath p)
            , funExt λ x → funExt
                λ a → (λ i → B₀ (Iso.inv p (transportRefl x i)) (transportRefl a i))
                  ∙ (p2 x a))


LR-Iso' : ∀ {ℓ} → ∀ n → Path (Σ (Type (ℓ-suc ℓ)) (λ x → x → Type ℓ))
                           ((Sigₗ ℓ n) , Recₗ) ((Sigᵣ ℓ n) , Recᵣ)
LR-Iso' zero = refl
LR-Iso' (suc zero) = refl
LR-Iso' (suc (suc zero)) = refl
LR-Iso' {ℓ} (suc (suc (suc n))) =
     (λ i → (Σ (Type ℓ) (λ x → fst (lft x i))) , λ x → Σ (fst x) (snd (lft (fst x) i) (snd x)))
  ∙∙ mid=
  ∙∙ λ i → (Σ (fst (LR-Iso' {ℓ} (suc (suc n)) i)) λ x → (snd (LR-Iso' (suc (suc n)) i)) x → Type ℓ)
      , (λ x → Σ (snd (LR-Iso' (suc (suc n)) i) (fst x)) (snd x))
  where





    lft : (A : Type ℓ) → _

    lft A =
          ll
        ∙ λ i → (Σ (A → Sigₗ ℓ (suc n)) (λ b → Recₗ (A , b) → Type ℓ)) ,
            rr i

       where

         ll : _
         ll = zzzz n A

         rr : (λ z z₁ → Σ (Recₗ (fst z z₁)) λ x₂ → snd z ((z₁ , x₂)))
                  ≡
              λ z z₁ →
               Σ (Recₗ (transp (λ i → Sigₗ ℓ (suc n)) i0 (fst z (transp (λ j → A) i0 z₁))))
                 (λ x₂ → snd z (transp (
                    λ j → Σ A (λ x₃ → Recₗ (transp (λ i → Sigₗ ℓ (suc n)) j
                                        (fst z (transp (λ j₁ → A) j x₃))))) i0 (z₁ , x₂)))
         rr i x x₁ = Σ fst-p snd-p

           where
             
             fst-p = (Recₗ
                          (transportRefl
                           (fst x (transportRefl x₁ (~ i))) (~ i)))

             snd-p : fst-p → Set ℓ
             snd-p x₂ = snd x
                        (transp
                         (λ j →
                            Σ A
                            (λ x₃ →
                               Recₗ
                               (transp (λ i₁ → Sigₗ ℓ (suc n)) ((~ i) ∨ j)
                                (fst x (transp (λ j₁ → A) ((~ i) ∨  j) x₃)))))
                         (~ i) (x₁ , x₂))


    mid= : _
    mid= i = ((sym (ua (assocΣ {A = Type ℓ} {B = λ Ty → Ty → Sigₗ ℓ (suc n)}
            {C = λ a b → Recₗ (a , b) → Type ℓ} )) i)
        , λ x → (let z = coei→1 (λ x₁ → (sym (ua (assocΣ {A = Type ℓ} {B = λ Ty → Ty → Sigₗ ℓ (suc n)}
                                {C = λ a b → Recₗ (a , b) → Type ℓ} )) x₁)) i x 

                 in sym (ua (assocΣ {A = fst (fst z)} {B = λ a → Recₗ (snd (fst z) a)}
                               {C = λ a b → snd z (a , b)}) ) i))



