{-# OPTIONS --cubical --no-exact-split --safe #-}

module Cubical.DataDefinitions.Nat where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Logic

open import Cubical.Data.Sum

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

open import Cubical.Data.Bool

open import Cubical.Data.Universe

import Cubical.Data.Nat as orgℕ

open import Cubical.DataDefinitions.Definition




record IsNat (ℕ : Type₀) : Type (ℓ-suc ℓ-zero) where
  constructor c-isNat

  field
    zero : ℕ
    suc : ℕ → ℕ
    ℕ-induction : ( A : ℕ → Type₀ )
                      → A zero
                      → ((n : ℕ) → A n → A (suc n))
                        → (n : ℕ) → A n
    



    ℕ-induction-zero : ∀ A → ∀ a₀ → ∀ f → ℕ-induction A a₀ f zero ≡ a₀
    ℕ-induction-suc : ∀ A → ∀ a₀ → ∀ f → ∀ n → ℕ-induction A a₀ f (suc n) ≡ f n (ℕ-induction A a₀ f n)

  ℕ-induction-zeroᵗ : Type (ℓ-suc ℓ-zero)
  ℕ-induction-zeroᵗ = ∀ A → ∀ a₀ → ∀ f → ℕ-induction A a₀ f zero ≡ a₀

  ℕ-induction-sucᵗ : Type (ℓ-suc ℓ-zero)
  ℕ-induction-sucᵗ = ∀ A → ∀ a₀ → ∀ f → ∀ n → ℕ-induction A a₀ f (suc n) ≡ f n (ℕ-induction A a₀ f n)

  ℕ-induction-zero′ : ∀ A → ∀ zero′ → ∀ e → ∀ (a₀ : A zero) → ∀ f  →  ℕ-induction A a₀ f zero′ ≡ subst A e a₀
  ℕ-induction-zero′ A zero′ e a₀ f = J (λ z′ e′ → ℕ-induction A a₀ f z′ ≡ subst A e′ a₀) ((ℕ-induction-zero A a₀ f) ∙ sym (substRefl {B = A} a₀)) e 

  ℕ-induction-suc′ : ∀ A → ∀ a₀ → ∀ f → ∀ n → (suc′ : ℕ → ℕ) → (e : suc ≡ suc′) →
                     ℕ-induction A a₀ f (suc′ n) ≡ subst A (cong (λ q → q n ) e) (f n (ℕ-induction A a₀ f n))
  ℕ-induction-suc′ A a₀ f n suc′ = J (λ s′ e′ → ℕ-induction A a₀ f (s′ n) ≡ subst A (cong (λ q → q n ) e′) (f n (ℕ-induction A a₀ f n)))
                                     ((ℕ-induction-suc A a₀ f n) ∙ sym (substRefl {B = A} (f n (ℕ-induction A a₀ f n))))


  ℕ-recursion : (A : Type₀ )
              → A
              → (ℕ → A → A)
              → ℕ → A

  ℕ-recursion A = ℕ-induction (λ _ → A)

  

  ℕ-iteration : (A : Type₀ )
              → A
              → (A → A)
              → ℕ → A

  ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)


isDefinition-isNat : IsDefinition IsNat
isDefinition-isNat = IsDefinition h-f h-p h-pp
  where

    h-f : ∀ A₁ A₂ → IsNat A₁ → IsNat A₂ → A₁ → A₂
    h-f A₁ A₂ isn₁ isn₂ = IsNat.ℕ-iteration isn₁ _ (IsNat.zero isn₂) (IsNat.suc isn₂)

    h-p : (A : Set) (ba : IsNat A) (x : A) → h-f A A ba ba x ≡ x
    h-p A ba = IsNat.ℕ-induction ba (λ x → h-f A A ba ba x ≡ x) (IsNat.ℕ-induction-zero ba _ _ _) (λ n x → (IsNat.ℕ-induction-suc ba _ _ _) n ∙ cong (IsNat.suc ba) x)

    -- h-pp : (A₁ A₂ : Set) (x : isNat A₂) (xx : isNat A₁) →
    --          section (h-f A₂ A₁ x xx) (h-f A₁ A₂ xx x)
    -- h-pp A₁ A₂ x xx = isNat.ℕ-induction xx (λ z → h-f A₂ A₁ x xx (h-f A₁ A₂ xx x z) ≡ z)
    --                     ( isNat.ℕ-induction-zero′ x _ _ (( sym (isNat.ℕ-induction-zero xx _ _ _))) _ _
    --                       ∙ substRefl {x = isNat.zero xx} (_) )
    --                     λ n pred= →
    --                      cong (h-f _ _ x xx) (isNat.ℕ-induction-suc xx (λ _ → A₂) (isNat.zero x) (λ _ → isNat.suc x) n)
    --                       ∙ isNat.ℕ-induction-suc x _ _ _ _
    --                       ∙ cong (isNat.suc xx) pred=

    h-pp : (A₁ A₂ A₃ : Set) (ba₁ : IsNat A₁) (ba₂ : IsNat A₂) (ba₃ : IsNat A₃)
             (x : A₁) →
             ((λ {a} → h-f A₂ A₃ ba₂ ba₃) ∘ h-f A₁ A₂ ba₁ ba₂) x ≡
               h-f A₁ A₃ ba₁ ba₃ x
    h-pp ℕ₁ ℕ₂ ℕ₃ isnat₁ isnat₂ isnat₃ =
      N₁.ℕ-induction
      (λ z →
          ((λ {a} → h-f ℕ₂ ℕ₃ isnat₂ isnat₃) ∘ h-f ℕ₁ ℕ₂ isnat₁ isnat₂) z ≡
          h-f ℕ₁ ℕ₃ isnat₁ isnat₃ z)
      ( (N₂.ℕ-induction-zero′ (λ _ → ℕ₃) _ (sym (N₁.ℕ-induction-zero (λ _ → ℕ₂) N₂.zero (λ _ → N₂.suc))) N₃.zero (λ _ → N₃.suc) ∙ transportRefl _) ∙ (sym (N₁.ℕ-induction-zero (λ _ → ℕ₃) N₃.zero (λ _ → N₃.suc))))
      λ n x →
           cong (N₂.ℕ-induction (λ _ → ℕ₃) N₃.zero (λ _ → N₃.suc)) (N₁.ℕ-induction-suc (λ _ → ℕ₂) N₂.zero (λ _ → N₂.suc) (n)) 
         ∙ N₂.ℕ-induction-suc (λ _ → ℕ₃) N₃.zero (λ _ → N₃.suc) (N₁.ℕ-induction (λ _ → ℕ₂) N₂.zero (λ _ → N₂.suc) n)
         ∙ cong N₃.suc x
         ∙ sym (N₁.ℕ-induction-suc (λ _ → ℕ₃) N₃.zero (λ _ → N₃.suc) n)

       where

       module N₁ = IsNat isnat₁
       module N₂ = IsNat isnat₂
       module N₃ = IsNat isnat₃
        
    

IsNat-ℕ : IsNat orgℕ.ℕ
IsNat-ℕ = c-isNat
  orgℕ.zero
  orgℕ.suc
  (λ A → orgℕ.ℕ-induction {_} {A})
  (λ A a₀ f → refl)
  λ A a₀ f n → refl



-- module 

  -- TrueOnZero : ℕ → Bool  
  -- TrueOnZero = ℕ-induction (λ _ → Bool) true λ n x → false

  -- z-?-s : (n : ℕ) → (n ≡ zero) ⊎ Σ-syntax ℕ (λ n′ → suc n′ ≡ n)
  -- z-?-s = ℕ-induction (λ n → (n ≡ zero) ⊎ (Σ[ n′ ∈ ℕ ] (suc n′ ≡ n)) )
  --                       ( _⊎_.inl refl)
  --                       λ n x → _⊎_.inr (n , refl)


  -- EvenOdd→Bool : ℕ → Bool
  -- EvenOdd→Bool = ℕ-iteration Bool false not

  -- isZero→Bool : ℕ → Bool
  -- isZero→Bool = ℕ-iteration Bool true (λ _ → false)


  -- isZero : ℕ → hProp ℓ-zero
  -- isZero n = caseBool ⊤ ⊥ (isZero→Bool n)


  -- isZero-zero : [ isZero zero ]
  -- isZero-zero = transport (sym ( cong (λ w → [ caseBool ⊤ ⊥ w ]) (ℕ-induction-zero (λ _ → Bool) true (λ _ _ → false)))) _

  -- ¬isZero-suc-n : ∀ n → [ (isZero (suc n)) ] → fst ⊥ 
  -- ¬isZero-suc-n n = transport ( ( cong (λ w → [ caseBool ⊤ ⊥ w ]) (ℕ-induction-suc (λ _ → Bool) true (λ _ _ → false) n)))

  -- isOdd : ℕ → hProp ℓ-zero 
  -- isOdd n =  caseBool ⊤ ⊥ (EvenOdd→Bool n)

  -- s≠z : ∀ {n} → (suc n ≡ zero) → fst ⊥
  -- s≠z {n} x =  ¬isZero-suc-n n (subst (λ x₁ →  fst (isZero x₁)) (sym x) isZero-zero) 


  -- pred-ℕ : ℕ → ℕ
  -- pred-ℕ = ℕ-induction (λ _ → ℕ) zero λ n _ → n

  -- pred-suc : ∀ n → pred-ℕ ( suc n ) ≡ n
  -- pred-suc = ℕ-induction (λ z → pred-ℕ (suc z) ≡ z) (ℕ-induction-suc (λ _ → ℕ) zero (λ n _ → n) zero)
  --            λ n x → (ℕ-induction-suc (λ _ → ℕ) zero (λ n _ → n)) (suc n)

  -- suc-inj : ∀ {n₁ n₂} → suc n₁ ≡ suc n₂ → n₁ ≡ n₂
  -- suc-inj {n₁} {n₂} x =  (sym (pred-suc n₁)) ∙ (cong pred-ℕ x) ∙ pred-suc n₂

  -- suc-n-≠-n : ∀ n → suc n ≡ n → fst ⊥
  -- suc-n-≠-n = ℕ-induction (_) s≠z  λ n x y → x (suc-inj y)


  -- _+_ : ℕ → ℕ → ℕ
  -- x + x₁ = ℕ-iteration ℕ x suc x₁

  -- z+z≡z : zero + zero ≡ zero
  -- z+z≡z = ℕ-induction-zero (λ _ → ℕ) zero (λ _ → suc)


  -- isZero? : ∀ x →  Dec (zero ≡ x)
  -- isZero? = ℕ-induction _ (yes refl) λ n x → no λ x₁ → s≠z {n} (sym x₁)

  -- isZero?′ : ∀ x →  Dec (x ≡ zero)
  -- isZero?′ = ℕ-induction _ (yes refl) λ n x → no s≠z

  -- =-suc : (n₁ n₂ : ℕ) → Dec (n₁ ≡ n₂) → Dec (suc n₁ ≡ suc n₂)
  -- =-suc n₁ n₂ (yes p) = yes (cong suc p)
  -- =-suc n₁ n₂ (no ¬p) = no λ x → ¬p (suc-inj x)
  
  -- Discrete-ℕ : Discrete ℕ
  -- Discrete-ℕ = ℕ-induction (λ x → (y : ℕ) → Dec (x ≡ y))
  --        (isZero?)
  --        λ n =? → ℕ-induction (λ z → Dec (suc n ≡ z)) (isZero?′ (suc n)) λ n₁ _ → =-suc _ _ (=? n₁)
  

  -- isSet-Nat : isSet ℕ
  -- isSet-Nat = Discrete→isSet Discrete-ℕ 
