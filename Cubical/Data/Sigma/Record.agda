{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Record where

open import Cubical.Core.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import Cubical.Data.Vec
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥-elim ; rec to ⊥-rec )

open import Cubical.Foundations.Everything

open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.Interval.Base renaming (elim to I-elim ; rec to I-rec)


Π : ∀ {ℓ ℓ'} → {A : Type ℓ} → (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Π B = ∀ x → B x


Sigₗ : ∀ ℓ → ℕ → Type (ℓ-suc ℓ)
Sigₗ ℓ 0 = Lift Unit
Sigₗ ℓ 1 = Type ℓ
Sigₗ ℓ (suc (suc n)) = Σ[ Ty ∈ Type ℓ ]  (Ty → Sigₗ ℓ (suc n))

Recₗ : ∀ {ℓ} → ∀ {n} → Sigₗ ℓ n → Type ℓ
Recₗ {n = 0} _ = Lift Unit
Recₗ {n = 1} x = x
Recₗ {n = suc (suc n)} x = Σ (fst x) (Recₗ ∘ snd x)


Sigᵣ : ∀ ℓ → ℕ → Type (ℓ-suc ℓ)

Recᵣ : ∀ {ℓ} → ∀ {n} → Sigᵣ ℓ n → Type ℓ


Sigᵣ ℓ 0 = Lift Unit
Sigᵣ ℓ 1 = Type ℓ
Sigᵣ ℓ (suc (suc n)) = Σ (Sigᵣ ℓ (suc n)) (λ x → Recᵣ x → Type ℓ)

Recᵣ {ℓ} {0} x = Lift Unit
Recᵣ {ℓ} {1} x = x
Recᵣ {ℓ} {suc (suc n)} x = Σ (Recᵣ (fst x)) (snd x)



trim-sig :  ∀ {ℓ} → ∀ {n} → (s : Sigₗ ℓ n) → Sigₗ ℓ (predℕ n)
trim-sig {n = 0} s = _
trim-sig {n = 1} s = _
trim-sig {n = 2} s = fst s
trim-sig {n = suc (suc (suc n))} s = fst s , λ x → trim-sig (snd s x)


-- Π-sig : ∀ {ℓ} → ∀ {n} → (s : Sigₗ ℓ n) → Type ℓ
-- Π-sig {n = 0} s = Lift Unit
-- Π-sig {n = 1} s = s
-- Π-sig {n = suc (suc n)} s = (a : fst s) → Π-sig (snd s a)

-- Π-sig-pick : ∀ {ℓ} → List ℕ → ∀ {n} → (s : Sigₗ ℓ n) → Type ℓ
-- Π-sig-pick xs {0} s = Lift Unit
-- Π-sig-pick xs {1} s = s
-- Π-sig-pick [] {suc (suc n)} s = {a : fst s} → Π-sig-pick [] (snd s a)
-- Π-sig-pick (zero ∷ xs) {suc (suc n)} s = (a : fst s) → Π-sig-pick xs (snd s a)
-- Π-sig-pick (suc x ∷ xs) {suc (suc n)} s = {a : fst s} → Π-sig-pick (x ∷ xs) (snd s a)



-- Recₗ' : ∀ {ℓ} → ∀ {n} → Sigₗ ℓ n → Type ℓ
-- Recₗ' {n = zero} _ = Lift Unit
-- Recₗ' {n = suc zero} x = x
-- Recₗ' {n = suc (suc n)} x = Σ (Recₗ' (trim-sig x)) λ x₁ → {!!}


push-Type :  ∀ {ℓ} → ∀ {n} → (s : Sigₗ ℓ n)
              → (Recₗ s → Type ℓ)
              → Sigₗ ℓ (suc n)
push-Type {n = zero} s x = x _
push-Type {n = suc zero} s x = s , x
push-Type {n = suc (suc n)} s x = (fst s) , (λ a → push-Type (snd s a) (x ∘ (a ,_) ))

trim-rec :  ∀ {ℓ} → ∀ {n} → (s : Sigₗ ℓ n) → Recₗ s → Recₗ (trim-sig s)
trim-rec {n = zero} x = _
trim-rec {n = suc zero} s x = _
trim-rec {n = suc (suc zero)} s x = fst x
trim-rec {n = suc (suc (suc n))} s x = fst x , trim-rec (snd s (fst x)) (snd x)


-- This functions describes Type of maixmally curried families of types in given signature
-- the purpose of Boolean and (List ℕ) arguments, is to controll
-- explicity of arguments in generated type:
--  * Bool controls the "default" mode (true → implicit , false  → explicit)
--  * List ℕ controls "exceptions", it stores the list of spaces
--    betwen arguments which are treated in oposite way

Type-in-sig : ∀ {ℓ} → Bool → List ℕ → ∀ {n} → Sigₗ ℓ n → Type (ℓ-suc ℓ)
Type-in-sig _ _ {zero} _ = Type _
Type-in-sig false [] {suc zero} x = x → Type _
Type-in-sig {ℓ} true [] {suc zero} x = {_ : x} → Type ℓ

Type-in-sig {ℓ} false (zero ∷ _) {suc zero} x = {_ : x} → Type ℓ
Type-in-sig true (zero ∷ _) {suc zero} x = x → Type _

Type-in-sig false (suc x₁ ∷ xs) {suc zero} x = x → Type _
Type-in-sig {ℓ} true (suc x₁ ∷ xs) {suc zero} x = {_ : x} → Type ℓ

Type-in-sig false [] {suc (suc n)} x = (a : fst x) → Type-in-sig false [] (snd x a) 
Type-in-sig true [] {suc (suc n)} x = {a : fst x} → Type-in-sig true [] (snd x a)
Type-in-sig false (zero ∷ xs) {suc (suc n)} x = {a : fst x} → Type-in-sig false (xs) (snd x a)
Type-in-sig false (suc k ∷ xs) {suc (suc n)} x = (a : fst x) → Type-in-sig false (k ∷ xs) (snd x a)
Type-in-sig true (zero ∷ xs) {suc (suc n)} x = (a : fst x) → Type-in-sig true (xs) (snd x a)
Type-in-sig true (suc k ∷ xs) {suc (suc n)} x = {a : fst x} → Type-in-sig true (k ∷ xs) (snd x a)

-- maixmally curried Type families for given signature
pop-Type : ∀ {ℓ} → ∀ {n}
           → (b : Bool) → (l : List ℕ) → (A : Sigₗ ℓ n)
           → Type-in-sig b l (trim-sig A)
pop-Type {n = zero} _ _ _ = Lift Unit
pop-Type {n = suc zero} _ _ A = A
pop-Type {n = suc (suc zero)} false [] A = snd A
pop-Type {n = suc (suc zero)} true [] A {a} = snd A a
pop-Type {n = suc (suc zero)} false (zero ∷ l) A {a} = snd A a
pop-Type {n = suc (suc zero)} false (suc k ∷ l) A = snd A
pop-Type {n = suc (suc zero)} true (zero ∷ l) A = snd A
pop-Type {n = suc (suc zero)} true (suc k ∷ l) A {a} = snd A a
pop-Type {n = suc (suc (suc n))} false [] A a = pop-Type false [] (snd A a)
pop-Type {n = suc (suc (suc n))} true [] A {a} = pop-Type true [] (snd A a)
pop-Type {n = suc (suc (suc n))} false (zero ∷ l) A {a} = pop-Type false l (snd A a)
pop-Type {n = suc (suc (suc n))} false (suc k ∷ l) A a = pop-Type false (k ∷ l) (snd A a)
pop-Type {n = suc (suc (suc n))} true (zero ∷ l) A a = pop-Type true l (snd A a)
pop-Type {n = suc (suc (suc n))} true (suc k ∷ l) A {a} = pop-Type true (k ∷ l) (snd A a)

-- maximally uncuried functions for given signature
pop-Type-overRecₗ : ∀ {ℓ} → ∀ {n}
                     → (s : Sigₗ ℓ n)
                     →  Recₗ (trim-sig s) → Type ℓ
pop-Type-overRecₗ {n = zero} _ _ = Lift Unit
pop-Type-overRecₗ {n = suc zero} A _ = A
pop-Type-overRecₗ {n = suc (suc zero)} x a = snd x a
pop-Type-overRecₗ {n = suc (suc (suc n))} x a = pop-Type-overRecₗ (snd x (fst a)) (snd a)


pushVal : ∀ {ℓ} → ∀ {n} → (A : Sigₗ ℓ n)
        → (x : Recₗ (trim-sig A))
        → (pop-Type-overRecₗ A x) → Recₗ A 
pushVal {n = zero} _ _ _ = _
pushVal {n = suc zero} _ _ a = a
pushVal {n = suc (suc zero)} _ x x₁ = x , x₁
pushVal {n = suc (suc (suc n))} A x x₁ = fst x , (pushVal (snd A (fst x)) (snd x) x₁)

popVal : ∀ {ℓ} → ∀ {n} → (A : Sigₗ ℓ n)
        → (x : Recₗ A) → pop-Type-overRecₗ A (trim-rec A x) 
popVal {n = zero} _ _ = _
popVal {n = suc zero} _ x = x
popVal {n = suc (suc zero)} _ x = snd x
popVal {n = suc (suc (suc n))} A x = popVal (snd A (fst x)) (snd x)

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

concatSigₗ-rec-Iso {n = suc (suc n)} {suc m} sₙ sₘ = {!!}



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





lem : ∀ {ℓ} → ∀ n → (A : Type ℓ)
          →  Iso (A → Sigₗ ℓ (suc (suc n)))
             (Σ (A → Sigₗ ℓ (suc n)) λ x → Recₗ {n = suc (suc n)} (A , x) → Type ℓ)  
Iso.fun (lem n A) x = (trim-sig ∘ x) , pop-Type-overRecₗ (A , x)
Iso.inv (lem n A) x a = push-Type (fst x a) ((snd x) ∘ ( a ,_ ))
fst (Iso.rightInv (lem n A) b i) x = push-trim (snd b ∘ (x ,_)) i
snd (Iso.rightInv (lem n A) b i) x = {!!}
Iso.leftInv (lem n A) a i x = {!!}



lem2 : ∀ {ℓ} n (A : Type ℓ) 
         (a₁ : Σ (A → Sigₗ ℓ (suc n)) (λ b → Recₗ (A , b) → Type ℓ))
         (a : A) →
                Iso
                (Σ (fst (Iso.inv (lem n A) a₁ a))
                 (λ x₂ → Recₗ (snd (Iso.inv (lem n A) a₁ a) x₂)))
                (Σ (Recₗ (fst a₁ a)) (λ x₂ → snd a₁ (a , x₂)))
lem2 zero A a₁ a = pathToIso refl
Iso.fun (lem2 (suc n) A a₁ a) x = ((fst x) , {!!}) , {!!}
Iso.inv (lem2 (suc n) A a₁ a) = {!!}
Iso.rightInv (lem2 (suc n) A a₁ a) = {!!}
Iso.leftInv (lem2 (suc n) A a₁ a) = {!!}

pathΣ-pairPath : ∀ {ℓ ℓ'} → (A : Type ℓ')
                   → (A₀ A₁ : Type ℓ)
                   → (B₀ : A₀ → A → Type ℓ') → (B₁ : A₁ → A → Type ℓ')
                   → (p : Iso A₀ A₁)
                   → (∀ (a₁ : A₁) → ∀ (a : A) →  Iso (B₀ (Iso.inv p a₁) a) (B₁ a₁ a))
                   → Path (Σ (Type ℓ) (λ x → x → A → Type ℓ'))
                      (A₀ , B₀) (A₁ , B₁)
pathΣ-pairPath A A₀ A₁ B₀ B₁ p p2 =
   sigmaPath→pathSigma (A₀ , B₀) (A₁ , B₁) ((isoToPath p)
      , funExt λ x → funExt
          λ a → (λ i → B₀ (Iso.inv p (transportRefl x i)) (transportRefl a i))
            ∙ isoToPath (p2 x a))


LR-Iso' : ∀ {ℓ} → ∀ n → Path (Σ (Type (ℓ-suc ℓ)) (λ x → x → Type ℓ))
                           ((Sigₗ ℓ n) , Recₗ) ((Sigᵣ ℓ n) , Recᵣ)
LR-Iso' zero = refl
LR-Iso' (suc zero) = refl
LR-Iso' (suc (suc zero)) = refl
LR-Iso' {ℓ} (suc (suc (suc n))) =
     left
  ∙∙ mid=
  ∙∙ λ i → (Σ (fst (LR-Iso' {ℓ} (suc (suc n)) i)) λ x → (snd (LR-Iso' (suc (suc n)) i)) x → Type ℓ)
      , (λ x → Σ (snd (LR-Iso' (suc (suc n)) i) (fst x)) (snd x))
  where

    left=' : (A : Type ℓ)
                → Path (Σ (Type (ℓ-suc ℓ)) (λ x → x → A → Type ℓ))
                   ((A → Sigₗ ℓ (suc (suc n))) ,
                       λ x x₁ → Σ (fst (x x₁)) λ x₂ → Recₗ (snd (x x₁) x₂))
                       
                   ((Σ (A → Sigₗ ℓ (suc n)) (λ b → Recₗ (A , b) → Type ℓ)) ,
                       λ x x₁ → Σ
                                  (Recₗ
                                    (transp (λ i → Sigₗ ℓ (suc n)) i0
                                     (fst x (transp (λ j → A) i0 x₁))))
                                   (λ x₂ →
                                      snd x
                                      (transp
                                       (λ j →
                                          Σ A
                                          (λ x₃ →
                                             Recₗ
                                             (transp (λ i → Sigₗ ℓ (suc n)) j
                                              (fst x (transp (λ j₁ → A) j x₃)))))
                                       i0 (x₁ , x₂))))

    left=' A =
          ll
        ∙ λ i → (Σ (A → Sigₗ ℓ (suc n)) (λ b → Recₗ (A , b) → Type ℓ)) ,
            rr i

       where

         ll : ((A → Sigₗ ℓ (suc (suc n))) ,
                (λ x x₁ → Σ (fst (x x₁)) (λ x₂ → Recₗ (snd (x x₁) x₂))))
                 ≡
                 (Σ (A → Sigₗ ℓ (suc n)) (λ b → Recₗ (A , b) → Type ℓ) ,
                   (λ z z₁ → Σ (Recₗ (fst z z₁)) λ x₂ → snd z ((z₁ , x₂))))
         ll i = pathΣ-pairPath {(ℓ-suc ℓ)} {ℓ} A
                     (A → Sigₗ ℓ (suc (suc n)))
                     (Σ (A → Sigₗ ℓ (suc n)) (λ b → Recₗ (A , b) → Type ℓ))
                     ((λ x x₁ → Σ (fst (x x₁)) (λ x₂ → Recₗ (snd (x x₁) x₂))))
                      ((λ z z₁ → Σ (Recₗ (fst z z₁)) λ x₂ → snd z ((z₁ , x₂))))
                     (lem n A) (lem2 n A) i

         rr : (λ z z₁ → Σ (Recₗ (fst z z₁)) λ x₂ → snd z ((z₁ , x₂)))
                  ≡ λ z z₁ →
                         Σ
                         (Recₗ
                          (transp (λ i → Sigₗ ℓ (suc n)) i0
                           (fst z (transp (λ j → A) i0 z₁))))
                         (λ x₂ →
                            snd z
                            (transp
                             (λ j →
                                Σ A
                                (λ x₃ →
                                   Recₗ
                                   (transp (λ i → Sigₗ ℓ (suc n)) j
                                    (fst z (transp (λ j₁ → A) j x₃)))))
                             i0 (z₁ , x₂)))
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

    left :
           (Σ (Type ℓ) (λ x → x → Sigₗ ℓ (suc (suc n))) , λ x → Σ (fst x) λ x₁ → Recₗ (snd x x₁))
             ≡
            (Σ (Type ℓ)
                (λ x → Σ (x → Sigₗ ℓ (suc n)) (λ b → Recₗ (x , b) → Type ℓ))

             , λ x → Σ (fst x)
               λ x₁ →
                   Σ
                   (Recₗ
                    (transp (λ i → Sigₗ ℓ (suc n)) i0
                     (fst (snd x) (transp (λ j → fst x) i0 x₁))))
                   (λ x₂ →
                      snd (snd x)
                      (transp
                       (λ j →
                          Σ (fst x)
                          (λ x₃ →
                             Recₗ
                             (transp (λ i → Sigₗ ℓ (suc n)) j
                              (fst (snd x) (transp (λ j₁ → fst x) j x₃)))))
                       i0 (x₁ , x₂))))


    left i = (Σ (Type ℓ) (λ x → fst (left=' x i))) , λ x → Σ (fst x) (snd (left=' (fst x) i) (snd x))

      --((λ i → Σ (Type _) (λ x → {!!}) , λ x → Σ (fst x) {!!}))

    mid= : 
           Path ((Σ (Type (ℓ-suc ℓ)) (λ x → x → Type ℓ)))
              (Σ (Type ℓ) (λ x → Σ (x → Sigₗ ℓ (suc n)) λ b → Recₗ (x , b) → Type ℓ)
                 , λ x → 
                       Σ (fst x)
                         λ x₁ → Σ (Recₗ (transp (λ i → Sigₗ ℓ (suc n)) i0
                                    (fst (snd x) (transp (λ j → fst x) i0 x₁))))
                                 λ x₂ → snd (snd x)
                                          (transp
                                           (λ j →
                                              Σ (fst x)
                                              (λ x₃ →
                                                 Recₗ
                                                 (transp (λ i → Sigₗ ℓ (suc n)) j
                                                  (fst (snd x) (transp (λ j₁ → fst x) j x₃)))))
                                           i0 (x₁ , x₂))
                         )
                 
              (Σ (Σ (Type ℓ) λ Ty → Ty → Sigₗ ℓ (suc n)) (λ x → Recₗ (fst x , snd x) → Type ℓ)
                 , λ x →
                      Σ (Σ (fst (fst x)) λ x₁ → Recₗ (snd (fst x) x₁))
                        λ x₁ → snd x x₁
                        )
    mid= i = ((sym (ua (assocΣ {A = Type ℓ} {B = λ Ty → Ty → Sigₗ ℓ (suc n)}
            {C = λ a b → Recₗ (a , b) → Type ℓ} )) i)
        , λ x → (let z = coei→1 (λ x₁ → (sym (ua (assocΣ {A = Type ℓ} {B = λ Ty → Ty → Sigₗ ℓ (suc n)}
                                {C = λ a b → Recₗ (a , b) → Type ℓ} )) x₁)) i x 

                 in sym (ua (assocΣ {A = fst (fst z)} {B = λ a → Recₗ (snd (fst z) a)}
                               {C = λ a b → snd z (a , b)}) ) i))

  

 
  






------------- LR - ISO End


combineSigₗ : ∀ {ℓ} → ∀ {n} → (I → Sigₗ ℓ n) → Sigₗ ℓ (n * 3)
combineSigₗ {n = 0} x = lift _
combineSigₗ {n = 1} x = (x i0) , (λ x0 → (x i1) , λ x1 → PathP x x0 x1)
combineSigₗ {n = suc (suc n)} x =
              fst (x i0) ,
      λ x0 →  fst (x i1) ,
      λ x1 → PathP (λ i → fst (x i)) x0 x1 ,
      λ p → combineSigₗ λ i → snd (x i) (p i) 







combineSigₗ-Recₗ→ : ∀ {ℓ} → ∀ {n} → (p : I → Sigₗ ℓ n)
                 → Recₗ (combineSigₗ p)
                 → ∀ i → Recₗ (p i)
combineSigₗ-Recₗ→ {n = zero} p x i = _
combineSigₗ-Recₗ→ {n = suc zero} p x i = snd (snd x) i
combineSigₗ-Recₗ→ {n = suc (suc n)} p x i =
  (fst (snd (snd x)) i) ,
    (combineSigₗ-Recₗ→ ((λ i₁ → snd (p i₁) (fst (snd (snd x)) i₁)))
      (snd (snd (snd x)) ) i)

combineSigₗ-Recₗ← : ∀ {ℓ} → ∀ {n} → (p : I → Sigₗ ℓ n)
                 → (∀ i → Recₗ (p i))
                 → Recₗ (combineSigₗ p)
combineSigₗ-Recₗ← {ℓ} {zero} p x = _
combineSigₗ-Recₗ← {ℓ} {suc zero} p x = (x i0) , ((x i1) , λ i → x i)
combineSigₗ-Recₗ← {ℓ} {suc (suc n)} p x =
   fst (x i0) , fst (x i1) , (λ i → fst (x i))
   , combineSigₗ-Recₗ← (λ z → snd (p z) (fst (x z))) λ i → snd (x i)

combineSigₗ-Recₗ-Iso' : ∀ {ℓ} → ∀ {n} → (p : I → Sigₗ ℓ n)
                     → Iso
                       (Π (Recₗ ∘ I-rec λ i → p i ))
                       (Recₗ (combineSigₗ λ i → p i))
                       
Iso.fun (combineSigₗ-Recₗ-Iso' p) x = combineSigₗ-Recₗ← (λ i → p i) λ i → x (seg i)
Iso.inv (combineSigₗ-Recₗ-Iso' p) x = I-elim (Recₗ ∘ I-rec λ i → p i) (λ i → combineSigₗ-Recₗ→ (λ i → p i) x i)

Iso.rightInv (combineSigₗ-Recₗ-Iso' {n = 0} p) b = refl
Iso.rightInv (combineSigₗ-Recₗ-Iso' {n = 1} p) b = refl
Iso.rightInv (combineSigₗ-Recₗ-Iso' {n = suc (suc n)} p) b i =
  let w : _
      w = Iso.rightInv (combineSigₗ-Recₗ-Iso' {n = suc n} (λ z → snd (p z) (fst (snd (snd b)) z)))
           ((snd (snd (snd b))))
  in 
  (fst b) , (fst (snd b) , (fst (snd (snd b))) , w i)


Iso.leftInv (combineSigₗ-Recₗ-Iso' {n = 0} p) a = refl
Iso.leftInv (combineSigₗ-Recₗ-Iso' {n = 1} p) a = intervalEta a

Iso.leftInv (combineSigₗ-Recₗ-Iso' {n = suc (suc n)} p) a i zero =
  fst (a zero) ,
    Iso.leftInv (combineSigₗ-Recₗ-Iso' {n = suc n} (λ z → snd (p z) (fst (a (seg z)))))
     (I-elim (Recₗ ∘ I-rec (λ z → snd (p z) (fst (a (seg z))))) (λ i₁ → snd (a (seg i₁))))
     i zero
     
Iso.leftInv (combineSigₗ-Recₗ-Iso' {n = suc (suc n)} p) a i one =
    fst (a one) ,
    Iso.leftInv (combineSigₗ-Recₗ-Iso' {n = suc n} (λ z → snd (p z) (fst (a (seg z)))))
     (I-elim (Recₗ ∘ I-rec (λ z → snd (p z) (fst (a (seg z))))) (λ i₁ → snd (a (seg i₁))))
     i one

Iso.leftInv (combineSigₗ-Recₗ-Iso' {n = suc (suc n)} p) a i (seg i₁) =
   (fst (a (seg i₁))) ,
       Iso.leftInv (combineSigₗ-Recₗ-Iso' {n = suc n} (λ z → snd (p z) (fst (a (seg z)))))
     (I-elim (Recₗ ∘ I-rec (λ z → snd (p z) (fst (a (seg z))))) (λ i₁ → snd (a (seg i₁))))
     i (seg i₁)



combineSigₗ-Recₗ-Iso : ∀ {ℓ} → ∀ {n} → (p : Interval → Sigₗ ℓ n)
                     → Iso
                       (Π (Recₗ ∘ p ))
                       (Recₗ (combineSigₗ λ i → p (seg i)))
combineSigₗ-Recₗ-Iso p = 
  compIso (pathToIso ( λ i → Π (Recₗ ∘ (intervalEta-rec  p) (~ i))) )
             (combineSigₗ-Recₗ-Iso' λ i → p (seg i))



pathPSigma-≡-sigmaPathP : ∀ {ℓ ℓ'} → {A : I → Type ℓ} → {B : ∀ i → A i → Type ℓ' }
                      → {a : Σ (A i0) (B i0)} → {b : Σ (A i1) (B i1)}
                      → (PathP (λ i → Σ (A i) (B i)) a b)
                         ≡
                        (Σ[ p ∈ (PathP A (fst a) (fst b)) ]
                         (PathP (λ i → B i (p i)) (snd a) (snd b)))
pathPSigma-≡-sigmaPathP =
  isoToPath (iso
    (λ x → (λ i → fst (x i)) , (λ i → snd (x i)))
    (λ x i → (fst x i) , (snd x i)) (λ _ → refl) λ _ → refl)



zzz∀ :  ∀ {ℓ ℓ'} → {A : Type ℓ}
                  → {B : A → Type ℓ'}
                  → (∀ x → B x) ≡ Π (λ x → B x)
zzz∀ = refl





combineSigₗ'-hlp : ∀ {ℓ} → ∀ {n}
                 → (p : I → Sigₗ ℓ n)
                 → (x₀ : Recₗ (p i0)) → (x₁ : Recₗ (p i1))
                 → Σ[ sₚ ∈ Sigₗ ℓ n ]
                    (Recₗ sₚ) ≡ (PathP (λ i → Recₗ (p i)) x₀ x₁) 
fst (combineSigₗ'-hlp {ℓ} {zero} p x₀ x₁) = _
snd (combineSigₗ'-hlp {ℓ} {zero} p x₀ x₁) =
  isoToPath (iso (λ x i → _) (λ _ → _) (λ b i i₁ → _) (λ a i → _))
fst (combineSigₗ'-hlp {ℓ} {suc zero} p x₀ x₁) = PathP p x₀ x₁
snd (combineSigₗ'-hlp {ℓ} {suc zero} p x₀ x₁) = refl

combineSigₗ'-hlp {ℓ} {suc (suc n)} p x₀ x₁ =
  let                                              
       (sPrev , lawPrev) = (combineSigₗ'-hlp (λ i → trim-sig (p i))
                               (trim-rec (p i0) x₀) (trim-rec (p i1) x₁))   

       typeToPush : Recₗ sPrev → Type ℓ
       typeToPush x = PathP (λ i → pop-Type-overRecₗ (p i) (transport (lawPrev) x i))
                            (popVal (p i0) x₀)
                            (popVal (p i1) x₁)

       sNext : Sigₗ ℓ _
       sNext = push-Type sPrev typeToPush

       pu-po-sq : (i j : I) → Type ℓ 
       pu-po-sq i j = isoToPath (push-popVal-Iso (p i)) j


       -- this lemma is just removes transp in various places
       coe-fix : _
       coe-fix = (λ i → Σ ((PathP (λ i → Recₗ (trim-sig (p i)))
                    (trim-rec (p i0) x₀)
                    (trim-rec (p i1) x₁)))
                     (λ p₁ → PathP (λ j →
                                  pop-Type-overRecₗ (p j)
                                       (transportTransport⁻
                                        (snd
                                         (combineSigₗ'-hlp (λ i → trim-sig (p i))
                                          (trim-rec (p i0) x₀)
                                          (trim-rec (p i1) x₁))) p₁ i
                                        j)
                           )
                             (popVal (p i0) x₀)
                             (popVal (p i1) x₁)))
                ∙  λ i → Σ (PathP (λ i → Recₗ (trim-sig (p i)))
                                  (trim-rec (p i0) (transportRefl x₀ (~ i)))
                                  (trim-rec (p i1) (transportRefl x₁ (~ i))))
                           λ p₁ → PathP (λ j → pop-Type-overRecₗ (p j) (p₁ j))
                                      (popVal (p i0) (transportRefl x₀ (~ i)))
                                      (popVal (p i1) (transportRefl x₁ (~ i)))

       lawNext : Recₗ (push-Type sPrev typeToPush)
                          ≡
                 PathP (λ i → Recₗ (p i)) x₀ x₁
       lawNext =     sym (isoToPath (push-popVal-Iso sNext) )
                  ∙∙ (push-trim-Recₗ {s = sPrev} typeToPush
                     ∙ (λ i → Σ (lawPrev i) (coe0→i (λ i → lawPrev i → Type ℓ) i typeToPush))
                  ∙∙ coe-fix
                  ∙∙ sym (pathPSigma-≡-sigmaPathP))
                  ∙∙
                   λ j → PathP (λ i → pu-po-sq i j)
                          (coe1→i (pu-po-sq i0) j x₀)
                          (coe1→i (pu-po-sq i1) j x₁)

  in sNext , lawNext


combineSigₗ' : ∀ {ℓ} → ∀ {n} → (I → Sigₗ ℓ n) → Sigₗ ℓ ((n + n) + n)
combineSigₗ' x =
  concatSigₗ-dep (concatSigₗ (x i0) (x i1))
    λ x₀₁ →
      let (x₀ , x₁) = Iso.inv (concatSigₗ-rec-Iso (x i0) (x i1)) x₀₁
      in fst (combineSigₗ'-hlp x x₀ x₁)


