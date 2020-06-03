{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Interval.Cube where

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



Typeⁿ' : ℕ → Level → Typeω
Typeⁿ' zero ℓ = I → Type ℓ
Typeⁿ' (suc n) ℓ = I → Typeⁿ' n ℓ

NCube : ℕ → Type₀
NCube = Vec Interval

Typeⁿ : ℕ → ∀ ℓ → Type (ℓ-suc ℓ)
Typeⁿ n ℓ = NCube n → Type ℓ

Π : ∀ {ℓ ℓ'} → {A : Type ℓ} → (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Π B = ∀ x → B x


_∘∷_ : ∀ {ℓ ℓ'} → {A : Type ℓ} → {B : Type ℓ'}
       → ∀ {n}
       → (Vec A (suc n) → B) → A → (Vec A n → B)
A ∘∷ a = A ∘ (a ∷_ )

∷∘ : ∀ {ℓ ℓ'} → {A : Type ℓ} → {B : Type ℓ'}
       → ∀ {n}
       → (A → (Vec A n → B)) → (Vec A (suc n) → B) 
∷∘ x x₁ = x (head x₁) (tail x₁)

_∘∷-dep_ : ∀ {ℓ ℓ'} → {A : Type ℓ} → ∀ {n}
           → {B : Vec A (suc n) → Type ℓ'}
           → Π B → Π (Π ∘ (B ∘∷_))
A ∘∷-dep a = A ∘ (a ∷_ )

∷∘-dep : ∀ {ℓ ℓ'} → {A : Type ℓ} → ∀ {n}
           → {B : Vec A (suc n) → Type ℓ'}
           → Π (Π ∘ B ∘∷_) → Π B 
∷∘-dep x (h ∷ t) = x h t

∘∷-Iso :  ∀ {ℓ ℓ'} → {A : Type ℓ} → ∀ {n}
           → {B : Vec A (suc n) → Type ℓ'}
           → Iso (Π B) (Π (Π ∘ (B ∘∷_)))
Iso.fun ∘∷-Iso = _∘∷-dep_
Iso.inv ∘∷-Iso = ∷∘-dep
Iso.rightInv ∘∷-Iso b = refl
Iso.leftInv ∘∷-Iso a i (x ∷ x₁) = a (x ∷ x₁)


_∷ₗ_ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → Vec A n → A → Vec A (suc n)
_∷ₗ_ {n = zero} x x₁ = x₁ ∷ []
_∷ₗ_ {n = suc n} x x₁ = head x ∷ ((tail x) ∷ₗ x₁)

_∘∷ₗ_ : ∀ {ℓ ℓ'} → {A : Type ℓ} → {B : Type ℓ'}
       → ∀ {n}
       → (Vec A (suc n) → B) → A → (Vec A n → B)
A ∘∷ₗ a = A ∘ (_∷ₗ a )

Typeⁿ'→Typeⁿ : ∀ {ℓ} → ∀ n →  Typeⁿ' n ℓ → Typeⁿ (suc n) ℓ
Typeⁿ'→Typeⁿ zero x x₁ = I-rec (λ i → x i) (head x₁)
Typeⁿ'→Typeⁿ (suc n) x x₁ = I-rec (λ i →  Typeⁿ'→Typeⁿ n (x i) (tail x₁)) (head x₁)

Typeⁿ→Typeⁿ' : ∀ {ℓ} → ∀ n → Typeⁿ (suc n) ℓ → Typeⁿ' n ℓ
Typeⁿ→Typeⁿ' zero x i = x (seg i ∷ [])
Typeⁿ→Typeⁿ' (suc n) x i = Typeⁿ→Typeⁿ' n (x ∘∷ (seg i))



Sig : ∀ ℓ → ℕ → Type (ℓ-suc ℓ)
Sig ℓ 0 = Lift Unit
Sig ℓ 1 = Type ℓ
Sig ℓ (suc (suc n)) = Σ[ Ty ∈ Type ℓ ]  (Ty → Sig ℓ (suc n))

trim-sig :  ∀ {ℓ} → ∀ {n} → (s : Sig ℓ n) → Sig ℓ (predℕ n)
trim-sig {n = 0} s = _
trim-sig {n = 1} s = _
trim-sig {n = 2} s = fst s
trim-sig {n = suc (suc (suc n))} s = fst s , λ x → trim-sig (snd s x)


-- Π-sig : ∀ {ℓ} → ∀ {n} → (s : Sig ℓ n) → Type ℓ
-- Π-sig {n = 0} s = Lift Unit
-- Π-sig {n = 1} s = s
-- Π-sig {n = suc (suc n)} s = (a : fst s) → Π-sig (snd s a)

-- Π-sig-pick : ∀ {ℓ} → List ℕ → ∀ {n} → (s : Sig ℓ n) → Type ℓ
-- Π-sig-pick xs {0} s = Lift Unit
-- Π-sig-pick xs {1} s = s
-- Π-sig-pick [] {suc (suc n)} s = {a : fst s} → Π-sig-pick [] (snd s a)
-- Π-sig-pick (zero ∷ xs) {suc (suc n)} s = (a : fst s) → Π-sig-pick xs (snd s a)
-- Π-sig-pick (suc x ∷ xs) {suc (suc n)} s = {a : fst s} → Π-sig-pick (x ∷ xs) (snd s a)


Rec : ∀ {ℓ} → ∀ {n} → Sig ℓ n → Type ℓ
Rec {n = 0} x = Lift Unit
Rec {n = 1} x = x
Rec {n = suc (suc n)} x = Σ (fst x) (Rec ∘ snd x) 


push-Type :  ∀ {ℓ} → ∀ {n} → (s : Sig ℓ n)
              → (Rec s → Type ℓ)
              → Sig ℓ (suc n)
push-Type {n = zero} s x = x _
push-Type {n = suc zero} s x = s , x
push-Type {n = suc (suc n)} s x = (fst s) , (λ a → push-Type (snd s a) (x ∘ (a ,_) ))

trim-rec :  ∀ {ℓ} → ∀ {n} → (s : Sig ℓ n) → Rec s → Rec (trim-sig s)
trim-rec {n = zero} x = _
trim-rec {n = suc zero} s x = _
trim-rec {n = suc (suc zero)} s x = fst x
trim-rec {n = suc (suc (suc n))} s x = fst x , trim-rec (snd s (fst x)) (snd x)


-- the purpose of Boolean and (List ℕ) arguments, is to controll explicity of arguments in generated type
-- Bool controls the "default" mode (true → implicit , false  → explicit)
-- List ℕ controls "exceptions", the list of spaces betwen arguments wich are treated in oposite way

Type-in-sig : ∀ {ℓ} → Bool → List ℕ → ∀ {n} → Sig ℓ n → Type (ℓ-suc ℓ)
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

-- Type-in-sig-impl : ∀ {ℓ} → ∀ {n} → Sig ℓ n → Type (ℓ-suc ℓ)
-- Type-in-sig-impl {n = zero} x = Type _
-- Type-in-sig-impl {ℓ} {n = suc zero} x = ∀ {a : x} → Type ℓ
-- Type-in-sig-impl {n = suc (suc n)} x = {a : fst x} → Type-in-sig-impl ((snd x) a)

pop-Type : ∀ {ℓ} → ∀ {n}
           → (b : Bool) → (l : List ℕ) → (A : Sig ℓ n)
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

pop-Type-overRec : ∀ {ℓ} → ∀ {n}
                     → (A : Sig ℓ n)
                     →  Rec (trim-sig A) → Type ℓ
pop-Type-overRec {n = zero} _ _ = Lift Unit
pop-Type-overRec {n = suc zero} A _ = A
pop-Type-overRec {n = suc (suc zero)} x a = snd x a
pop-Type-overRec {n = suc (suc (suc n))} x a = pop-Type-overRec (snd x (fst a)) (snd a)


pushVal : ∀ {ℓ} → ∀ {n} → (A : Sig ℓ n)
        → (x : Rec (trim-sig A))
        → (pop-Type-overRec A x) → Rec A 
pushVal {n = zero} _ _ _ = _
pushVal {n = suc zero} _ _ a = a
pushVal {n = suc (suc zero)} _ x x₁ = x , x₁
pushVal {n = suc (suc (suc n))} A x x₁ = fst x , (pushVal (snd A (fst x)) (snd x) x₁)

popVal : ∀ {ℓ} → ∀ {n} → (A : Sig ℓ n)
        → (x : Rec A) → pop-Type-overRec A (trim-rec A x) 
popVal {n = zero} _ _ = _
popVal {n = suc zero} _ x = x
popVal {n = suc (suc zero)} _ x = snd x
popVal {n = suc (suc (suc n))} A x = popVal (snd A (fst x)) (snd x)

push-popVal-Iso : ∀ {ℓ} → ∀ {n}
                     → (A : Sig ℓ n)
                     → Iso (Σ (Rec (trim-sig A)) (pop-Type-overRec A))
                           (Rec A)
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

combineSig : ∀ {ℓ} → ∀ {n} → (I → Sig ℓ n) → Sig ℓ (n * 3)
combineSig {n = 0} x = lift _
combineSig {n = 1} x = (x i0) , (λ x0 → (x i1) , λ x1 → PathP x x0 x1)
combineSig {n = suc (suc n)} x =
              fst (x i0) ,
      λ x0 →  fst (x i1) ,
      λ x1 → PathP (λ i → fst (x i)) x0 x1 ,
      λ p → combineSig λ i → snd (x i) (p i) 







combineSig-Rec→ : ∀ {ℓ} → ∀ {n} → (p : I → Sig ℓ n)
                 → Rec (combineSig p)
                 → ∀ i → Rec (p i)
combineSig-Rec→ {n = zero} p x i = _
combineSig-Rec→ {n = suc zero} p x i = snd (snd x) i
combineSig-Rec→ {n = suc (suc n)} p x i =
  (fst (snd (snd x)) i) ,
    (combineSig-Rec→ ((λ i₁ → snd (p i₁) (fst (snd (snd x)) i₁)))
      (snd (snd (snd x)) ) i)

combineSig-Rec← : ∀ {ℓ} → ∀ {n} → (p : I → Sig ℓ n)
                 → (∀ i → Rec (p i))
                 → Rec (combineSig p)
combineSig-Rec← {ℓ} {zero} p x = _
combineSig-Rec← {ℓ} {suc zero} p x = (x i0) , ((x i1) , λ i → x i)
combineSig-Rec← {ℓ} {suc (suc n)} p x =
   fst (x i0) , fst (x i1) , (λ i → fst (x i))
   , combineSig-Rec← (λ z → snd (p z) (fst (x z))) λ i → snd (x i)

combineSig-Rec-Iso' : ∀ {ℓ} → ∀ {n} → (p : I → Sig ℓ n)
                     → Iso
                       (Π (Rec ∘ I-rec λ i → p i ))
                       (Rec (combineSig λ i → p i))
                       
Iso.fun (combineSig-Rec-Iso' p) x = combineSig-Rec← (λ i → p i) λ i → x (seg i)
Iso.inv (combineSig-Rec-Iso' p) x = I-elim (Rec ∘ I-rec λ i → p i) (λ i → combineSig-Rec→ (λ i → p i) x i)

Iso.rightInv (combineSig-Rec-Iso' {n = 0} p) b = refl
Iso.rightInv (combineSig-Rec-Iso' {n = 1} p) b = refl
Iso.rightInv (combineSig-Rec-Iso' {n = suc (suc n)} p) b i =
  let w : _
      w = Iso.rightInv (combineSig-Rec-Iso' {n = suc n} (λ z → snd (p z) (fst (snd (snd b)) z)))
           ((snd (snd (snd b))))
  in 
  (fst b) , (fst (snd b) , (fst (snd (snd b))) , w i)


Iso.leftInv (combineSig-Rec-Iso' {n = 0} p) a = refl
Iso.leftInv (combineSig-Rec-Iso' {n = 1} p) a = intervalEta a

Iso.leftInv (combineSig-Rec-Iso' {n = suc (suc n)} p) a i zero =
  fst (a zero) ,
    Iso.leftInv (combineSig-Rec-Iso' {n = suc n} (λ z → snd (p z) (fst (a (seg z)))))
     (I-elim (Rec ∘ I-rec (λ z → snd (p z) (fst (a (seg z))))) (λ i₁ → snd (a (seg i₁))))
     i zero
     
Iso.leftInv (combineSig-Rec-Iso' {n = suc (suc n)} p) a i one =
    fst (a one) ,
    Iso.leftInv (combineSig-Rec-Iso' {n = suc n} (λ z → snd (p z) (fst (a (seg z)))))
     (I-elim (Rec ∘ I-rec (λ z → snd (p z) (fst (a (seg z))))) (λ i₁ → snd (a (seg i₁))))
     i one

Iso.leftInv (combineSig-Rec-Iso' {n = suc (suc n)} p) a i (seg i₁) =
   (fst (a (seg i₁))) ,
       Iso.leftInv (combineSig-Rec-Iso' {n = suc n} (λ z → snd (p z) (fst (a (seg z)))))
     (I-elim (Rec ∘ I-rec (λ z → snd (p z) (fst (a (seg z))))) (λ i₁ → snd (a (seg i₁))))
     i (seg i₁)



combineSig-Rec-Iso : ∀ {ℓ} → ∀ {n} → (p : Interval → Sig ℓ n)
                     → Iso
                       (Π (Rec ∘ p ))
                       (Rec (combineSig λ i → p (seg i)))
combineSig-Rec-Iso p = 
  compIso (pathToIso ( λ i → Π (Rec ∘ (intervalEta-rec  p) (~ i))) )
             (combineSig-Rec-Iso' λ i → p (seg i))






concatSig : ∀ {ℓ} → ∀ {n m} → Sig ℓ n → Sig ℓ m → Sig ℓ (n + m)
concatSig {n = zero} {zero} x x₁ = _
concatSig {n = zero} {suc m} x x₁ = x₁
concatSig {n = suc n} {zero} x x₁ = subst (Sig _) (sym (+-zero (suc n))) x 
concatSig {n = suc zero} {suc m} x x₁ = x , (λ _ → x₁)
concatSig {n = suc (suc n)} {suc m} x x₁ = (fst x) , λ a → concatSig (snd x a) x₁

concatSig-rec-Iso : ∀ {ℓ} → ∀ {n m} → (sₙ : Sig ℓ n) → (sₘ : Sig ℓ m) →
                      Iso (Rec sₙ × Rec sₘ) (Rec (concatSig sₙ sₘ)) 
concatSig-rec-Iso {n = zero} {zero} sₙ sₘ = {!!}
concatSig-rec-Iso {n = zero} {suc m} sₙ sₘ = {!!}

concatSig-rec-Iso {n = suc n} sₙ sₘ = {!!}

concatSig-dep : ∀ {ℓ} → ∀ {n m}
                 → (s : Sig ℓ n)
                 → (Rec s → Sig ℓ m)
                 → Sig ℓ (n + m)
concatSig-dep {n = zero} {m = m} s x = x _
concatSig-dep {n = suc n} {m = zero} s x = subst (Sig _) (sym (+-zero (suc n))) s 
concatSig-dep {n = suc zero} {m = suc m} s x = s , x
concatSig-dep {n = suc (suc n)} {m = suc m} s x =
  (fst s) , (λ a → concatSig-dep (snd s a) (x ∘ (a ,_ )))


pathPSigma-Iso-sigmaPathP : ∀ {ℓ ℓ'} → {A : I → Type ℓ} → {B : ∀ i → A i → Type ℓ' }
                      → (a : Σ (A i0) (B i0)) → (b : Σ (A i1) (B i1))
                      → (PathP (λ i → Σ (A i) (B i)) a b)
                         ≡
                        (Σ[ p ∈ (PathP A (fst a) (fst b)) ]
                         (PathP (λ i → B i (p i)) (snd a) (snd b)))
pathPSigma-Iso-sigmaPathP _ _ =
  isoToPath (iso
    (λ x → (λ i → fst (x i)) , (λ i → snd (x i)))
    (λ x i → (fst x i) , (snd x i)) (λ _ → refl) λ _ → refl)

push-trim : ∀ {ℓ} → ∀ {n} → {s : Sig ℓ n}
             → ∀ x → trim-sig (push-Type s x) ≡ s
push-trim {n = zero} x = refl
push-trim {n = suc zero} x = refl
push-trim {n = suc (suc n)} {s} x i = fst s , λ a → push-trim ( x ∘ (a ,_)) i

pop-push-Type : ∀ {ℓ} → ∀ {n} → {s : Sig ℓ n}
                  → ∀ x → PathP (λ i → Rec (push-trim {n = n} x i) → Type ℓ)
                          (pop-Type-overRec (push-Type s x)) x
pop-push-Type {n = zero} x = refl
pop-push-Type {n = suc zero} x = refl
pop-push-Type {ℓ} {n = suc (suc zero)} {s} x = refl
pop-push-Type {ℓ} {n = suc (suc (suc n))} {s} x i x₁ =
 let z : {!!}
     z = pop-push-Type {n = (suc (suc n))}
        {s = (push-trim {s = trim-sig s} (pop-push-Type (x ∘ (λ a → (fst x₁) , {!snd x₁!})) i) i)}
        {!!}
 in  (pop-push-Type {n = suc (suc n)} {!!} i) (fst x₁ , {!pop-push-Type ? (snd x₁)!})


-- push-trim-Rec : ∀ {ℓ} → ∀ {n} → {s : Sig ℓ n} → ∀ x →
--                    Σ (Rec (trim-sig (push-Type s x)))
--                       (pop-Type-overRec (push-Type s x))
--                    ≡ Σ (Rec s) x
-- push-trim-Rec {ℓ} {s = s} x i =
--   Σ (Rec (push-trim {s = s} x i)) (pop-push-Type x i)

-- -- combineSig'-hlp : ∀ {ℓ} → ∀ {n}
-- --                  → (p : I → Sig ℓ n)
-- --                  → (x₀ : Rec (p i0)) → (x₁ : Rec (p i1))
-- --                  → Σ[ sₚ ∈ (Sig ℓ n) ]
-- --                     (Rec sₚ) ≡ (PathP (λ i → Rec (p i)) x₀ x₁) 
-- -- fst (combineSig'-hlp {ℓ} {zero} p x₀ x₁) = _
-- -- snd (combineSig'-hlp {ℓ} {zero} p x₀ x₁) = {!!}
-- -- fst (combineSig'-hlp {ℓ} {suc zero} p x₀ x₁) = PathP p x₀ x₁
-- -- snd (combineSig'-hlp {ℓ} {suc zero} p x₀ x₁) = refl
-- -- -- combineSig'-hlp {ℓ} {2} p x₀ x₁ = {!!}
-- -- combineSig'-hlp {ℓ} {suc (suc n)} p x₀ x₁ =
-- --   let zz = (combineSig'-hlp (λ i → trim-sig (p i))
-- --                   (trim-rec (p i0) x₀) (trim-rec (p i1) x₁))

-- --   in sNext zz , (zzz zz)


-- --   where
-- --     zzTy = Σ[ sₚ ∈ Sig ℓ _ ]
-- --                 Rec sₚ ≡ PathP (λ i → Rec (trim-sig (p i))) (trim-rec (p i0) x₀)
-- --                                            (trim-rec (p i1) x₁)
                                      

-- --     z : (zz : zzTy) → Rec (fst zz) → Type ℓ
-- --     z zz x =
-- --       let ww : PathP (λ z → Rec (trim-sig (p z))) (trim-rec (p i0) x₀) (trim-rec (p i1) x₁)
-- --           ww = transport (snd zz) x

-- --       in PathP (λ i → pop-Type-overRec (p i) (ww i)) (popVal (p i0) x₀) (popVal (p i1) x₁)

-- --     sNext : (zz : zzTy) → Sig ℓ _
-- --     sNext zz = push-Type (fst zz) (z zz)

-- --     zzh : (i j : I) → Type ℓ 
-- --     zzh i j = isoToPath (push-popVal-Iso (p i)) j

-- --     -- zzh' : (zz : zzTy) → (j : I) → Type ℓ 
-- --     -- zzh' zz j = isoToPath (push-popVal-Iso (sNext zz)) (~ j)

-- --     zzx' : (zz : zzTy) → Path (Type ℓ)
-- --                          (Σ (Rec (trim-sig (push-Type (fst zz) (z zz))))
-- --                              (pop-Type-overRec (push-Type (fst zz) (z zz))
-- --                                 ))
-- --                          (Σ (PathP (λ z₁ → Rec (trim-sig (p z₁)))
-- --                               (fst (coe1→i (zzh i0) i0 x₀))
-- --                               (fst (coe1→i (zzh i1) i0 x₁)))
-- --                             λ p₁ → PathP (λ i → pop-Type-overRec (p i) (p₁ i))
-- --                                    (snd (coe1→i (zzh i0) i0 x₀))
-- --                                    (snd (coe1→i (zzh i1) i0 x₁)))
-- --                          --    (coe1→i (zzh i0) i0 x₀)
-- --                          --    (coe1→i (zzh i1) i0 x₁))
-- --     zzx' zz i = Σ (pp1 i ) (pp2 i)
-- --       where
-- --         pp1 : (Rec (trim-sig (push-Type (fst zz) (z zz))))
-- --               ≡
-- --               (PathP (λ z₁ → Rec (trim-sig (p z₁)))
-- --                               (fst (coe1→i (zzh i0) i0 x₀))
-- --                               (fst (coe1→i (zzh i1) i0 x₁)))
-- --         pp1 = {!!}
-- --               ∙∙ snd zz
-- --               ∙∙ λ i₁ → PathP (λ i₁ → Rec (trim-sig (p i₁)))
-- --                 (trim-rec (p i0) (transp (λ i₂ → Σ (fst (p i0))
-- --                     (λ x → Rec (snd (p i0) x))) (i0 ∨ ~ i₁) x₀))
-- --                 ((trim-rec (p i1) (transp (λ i₂ → Σ (fst (p i1))
-- --                      (λ x → Rec (snd (p i1) x))) (i0 ∨ ~ i₁) x₁)))

-- --         pp2 : PathP (λ x → pp1 x → Type ℓ)
-- --                {!!} {!!}
-- --         pp2 i = {!!}


-- --     zzx : (zz : zzTy) → Iso
-- --                          (Σ (Rec (trim-sig (push-Type (fst zz) (z zz)))) _)
-- --                          (PathP (λ i → zzh i i0)
-- --                             (coe1→i (zzh i0) i0 x₀)
-- --                             (coe1→i (zzh i1) i0 x₁))
-- --     fst (Iso.fun (zzx zz) x i) = {!transport (snd zz) ?!}
-- --     snd (Iso.fun (zzx zz) x i) = {!!}
-- --     Iso.inv (zzx zz) = {!!}
-- --     Iso.rightInv (zzx zz) = {!!}
-- --     Iso.leftInv (zzx zz) = {!!}

-- --     zzz : (zz : zzTy) → (Rec (push-Type (fst zz) (z zz)))
-- --                        ≡ (PathP (λ i → Rec (p i)) x₀ x₁)
-- --     zzz zz = (λ i → isoToPath (push-popVal-Iso (sNext zz)) (~ i) )
-- --              ∙∙ ((zzx' zz) ∙ (sym (pathPSigma-Iso-sigmaPathP _ _))) ∙∙
-- --              λ j → PathP (λ i → zzh i j) (coe1→i (zzh i0) j x₀) (coe1→i (zzh i1) j x₁)



-- -- combineSig' : ∀ {ℓ} → ∀ {n} → (I → Sig ℓ n) → Sig ℓ ((n + n) + n)
-- -- combineSig' x =
-- --   concatSig-dep (concatSig (x i0) (x i1))
-- --     λ x₀₁ →
-- --       let (x₀ , x₁) = Iso.inv (concatSig-rec-Iso (x i0) (x i1)) x₀₁
-- --       in fst (combineSig'-hlp x x₀ x₁)

-- -- -- combineSig' : ∀ {ℓ} → ∀ {n} → ∀ k → k ≤ n → (I → Sig ℓ n) → Sig ℓ ((n + n) + k)
-- -- -- combineSig' {n = n} zero k≤n x = subst (Sig _) lem (concatSig (x i0) (x i1))
-- -- --   where
-- -- --    lem : n + n ≡ n + n + zero
-- -- --    lem = {!!}
-- -- -- combineSig' {n = zero} (suc k) k≤n _ = ⊥-rec (¬-<-zero k≤n)
-- -- -- combineSig' {n = suc zero} (suc zero) k≤n x = (x i0) , (λ x0 → (x i1) , λ x1 → PathP x x0 x1)
-- -- -- combineSig' {n = suc zero} (suc (suc k)) k≤n x = {!!}
-- -- -- combineSig' {n = suc (suc n)} (suc k) k≤n x =
-- -- --   concatSig-dep (concatSig (x i0) (x i1)) {!!}

-- -- -- combineSig' : ∀ {ℓ} → ∀ {n} → (I → Sig ℓ n) → Sig ℓ (3 * n)
-- -- -- combineSig' {n = zero} _ = _
-- -- -- combineSig' {n = suc zero} x = (x i0) , (λ x0 → (x i1) , λ x1 → PathP x x0 x1)
-- -- -- combineSig' {n = suc (suc n)} x =
-- -- --               concatSig (x i0)
-- -- --              (concatSig (x i1) {!!})


-- -- -- 3^ : ℕ → ℕ
-- -- -- 3^ zero = suc zero
-- -- -- 3^ (suc x) = (3^ x) * 3

-- -- -- -- this signature is describing record of all the cells of the cube 

-- -- -- CubeSig : ∀ {ℓ} → ∀ {n} → Typeⁿ n ℓ → Sig ℓ (3^ n)
-- -- -- CubeSig {n = zero} x = x []
-- -- -- CubeSig {n = suc n} x = combineSig (λ i → CubeSig (x ∘∷ (seg i)))

-- -- -- -- this isomorphism is betwen
-- -- -- -- dependent function from n dimensional cube
-- -- -- -- and record of 3^ n cells 

-- -- -- cubeSig-Iso : ∀ {ℓ} → ∀ {n} → (A : Typeⁿ n ℓ)
-- -- --            → Iso (Π A) (Rec (CubeSig A))
-- -- -- Iso.fun (cubeSig-Iso {n = zero} _) x = x []
-- -- -- Iso.inv (cubeSig-Iso {n = zero} _) x [] = x 
-- -- -- Iso.rightInv (cubeSig-Iso {n = zero} _) _ = refl
-- -- -- Iso.leftInv (cubeSig-Iso {n = zero} A) a i [] = a []
-- -- -- cubeSig-Iso {n = suc n} A =
-- -- --   compIso
-- -- --   (compIso ∘∷-Iso (pathToIso (cong Π (funExt (isoToPath ∘ cubeSig-Iso ∘ A ∘∷_)))))
-- -- --   (combineSig-Rec-Iso (CubeSig ∘ A ∘∷_ ))

-- -- -- PathPⁿ-explicit : ∀ {ℓ} → ∀ {n}
-- -- --                  → (A : Typeⁿ n ℓ)
-- -- --                   → Type-in-sig false [] (trim-sig (CubeSig A) )
-- -- -- PathPⁿ-explicit x = pop-Type _ _ (CubeSig x)

-- -- -- argsToPick : ℕ → List ℕ
-- -- -- argsToPick zero = []
-- -- -- argsToPick (suc x) = predℕ (3^ x) ∷ predℕ (3^ x) ∷ argsToPick x 

-- -- -- PathPⁿ : ∀ {ℓ} → ∀ {n}
-- -- --                  → (A : Typeⁿ n ℓ)
-- -- --                   → Type-in-sig true (argsToPick n) (trim-sig (CubeSig A) )
-- -- -- PathPⁿ x = pop-Type _ _ (CubeSig x)

-- -- -- Pathⁿ : ∀ {ℓ} → ∀ n
-- -- --                  → {A : Type ℓ}
-- -- --                   → Type-in-sig true (argsToPick n) (trim-sig (CubeSig {n = n} (const A)) )
-- -- -- Pathⁿ n {x} = PathPⁿ (const x)

-- -- -- -- generated cube is definationaly equall to one from Prelude
-- -- -- Cube-test : ∀ {ℓ} → ∀ (A : Type ℓ) → 
-- -- --   {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- -- --   {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- -- --   {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- -- --   (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- -- --   {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- -- --   {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- -- --   {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- -- --   (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- -- --   {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- -- --   (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- -- --   {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- -- --   (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- -- --   (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- -- --   (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- -- --   → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
-- -- --     ≡
-- -- --     Pathⁿ 3 _ _ _ _ _ _
-- -- -- Cube-test _ _ _ _ _ _ _ = refl


-- -- -- -- by discarding last field (the interior cell) we can create signature of boundary record

-- -- -- BoundaryPⁿ : ∀ {ℓ} → ∀ {n}
-- -- --                  → (A : Typeⁿ n ℓ)
-- -- --                  → Type ℓ
-- -- -- BoundaryPⁿ A = Rec (trim-sig (CubeSig A) )

-- -- -- Boundaryⁿ : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Type ℓ
-- -- -- Boundaryⁿ n A = BoundaryPⁿ {n = n} (const A)

-- -- -- InteriorP :  ∀ {ℓ} → ∀ {n}
-- -- --                  → (A : Typeⁿ n ℓ)
-- -- --                  → BoundaryPⁿ A → Type ℓ
-- -- -- InteriorP A = pop-Type-overRec (CubeSig A)


-- -- -- Σ-Bd-Ins : ∀ {ℓ} → ∀ {n} → (A : Typeⁿ n ℓ) → Type ℓ
-- -- -- Σ-Bd-Ins A = Σ (BoundaryPⁿ A) (InteriorP A)


-- -- -- -- this isomorphism splits cube into boundary and interior

-- -- -- IsoCub : ∀ {ℓ} → ∀ {n} → (A : Typeⁿ n ℓ)
-- -- --            → Iso (Π A) (Σ (BoundaryPⁿ A) (InteriorP A))
-- -- -- IsoCub A = compIso (cubeSig-Iso A) (invIso (push-popVal-Iso (CubeSig A)))


-- -- -- from-ends-Path :  ∀ {ℓ} → ∀ {n} → (A : Typeⁿ (suc n) ℓ)
-- -- --                   → Iso (Π (Σ-Bd-Ins ∘ A ∘∷_))
-- -- --                         (Σ-Bd-Ins A)
-- -- -- from-ends-Path  A = compIso (pathToIso p1) (compIso p2 p3)

-- -- --   where
-- -- --     p1 : ((i' : Interval) → Σ-Bd-Ins (A ∘∷ i'))
-- -- --            ≡ ((i' : Interval) → Rec (CubeSig (A ∘∷ i')))
-- -- --     p1 i = (i' : Interval) → isoToPath (push-popVal-Iso (CubeSig (A ∘∷ i'))) i

-- -- --     p2 : Iso ((i' : Interval) → Rec (CubeSig (A ∘∷ i'))) (Rec (CubeSig A))
-- -- --     p2 = combineSig-Rec-Iso λ x → (CubeSig (A ∘∷ x))

-- -- --     p3 : Iso (Rec (CubeSig A)) (Σ-Bd-Ins A)
-- -- --     p3 = invIso (push-popVal-Iso (CubeSig A))







-- -- -- -- PathPⁿ-Ty : ∀ {ℓ} → ∀ {n} → Typeⁿ n ℓ → Type ℓ
-- -- -- -- PathPⁿ-Ty {n = n} x = Π-sig-pick (argsToPick n) (CubeSig x) 
-- -- -- --   where
-- -- -- --     argsToPick : ℕ → List ℕ
-- -- -- --     argsToPick zero = []
-- -- -- --     argsToPick (suc x) = predℕ (3^ x) ∷ predℕ (3^ x) ∷ argsToPick x 


-- -- -- -- PathPⁿ-test : ∀ {ℓ} → ∀ (A : Typeⁿ' 3 ℓ) → PathPⁿ-Ty {n = 4} (Typeⁿ'→Typeⁿ {ℓ} 3 A)
-- -- -- -- PathPⁿ-test A a a₁ a₂ a₃ a₄ a₅ a₆ a₇ = {!!}

-- -- -- -- PathPⁿ-test-3' : ∀ {ℓ} → ∀ (A : Type ℓ) → {!!}
              
-- -- -- -- PathPⁿ-test-3'  A = {! !}


-- -- -- -- PathPⁿ-test-3 : ∀ {ℓ} → ∀ (A : Type ℓ) →
-- -- -- --                     PathPⁿ-Ty {n = 2} (const A)   
              
-- -- -- -- PathPⁿ-test-3  A = {!Square {A = A}!}

-- -- -- -- -- PathPⁿ-test : ∀ {ℓ} → ∀ (A : Typeⁿ' 3 ℓ) → PathPⁿ {n = 4} (Typeⁿ'→Typeⁿ {ℓ} 3 A)
-- -- -- -- -- PathPⁿ-test A a a₁ a₂ a₃ a₄ a₅ a₆ a₇ = {!!}

-- -- -- -- -- 1 - 0,0
-- -- -- -- -- 2 - 2,2,0,0
-- -- -- -- -- 3 - 8,8,2,2,0,0
-- -- -- -- -- 4 - 26,26,8,8,2,2,0,0
