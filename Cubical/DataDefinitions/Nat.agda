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


record isNat′ (ℕ : Type₀) : Type (ℓ-suc ℓ-zero) where
  constructor c-isNat′

  field
    zero : ℕ
    suc : ℕ → ℕ
    ℕ-induction : ( A : ℕ → Type₀ )
                      → A zero
                      → ((n : ℕ) → A n → A (suc n))
                        → (n : ℕ) → A n

  ℕ-ind-zero : Type (ℓ-suc ℓ-zero)
  ℕ-ind-zero = ∀ A → ∀ a₀ → ∀ f → ℕ-induction A a₀ f zero ≡ a₀

  ℕ-ind-suc : Type (ℓ-suc ℓ-zero)
  ℕ-ind-suc = ∀ A → ∀ a₀ → ∀ f → ∀ n → ℕ-induction A a₀ f (suc n) ≡ f n (ℕ-induction A a₀ f n)


record isNat (ℕ : Type₀) : Type (ℓ-suc ℓ-zero) where
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


  -- isSet-ℕ : isSet ℕ
  -- isSet-ℕ x y x₁ y₁ = {!ℕ-induction!}


  t1 : (n : ℕ) → (n ≡ zero) ⊎ Σ-syntax ℕ (λ n′ → suc n′ ≡ n)
  t1 = ℕ-induction (λ n → (n ≡ zero) ⊎ (Σ[ n′ ∈ ℕ ] (suc n′ ≡ n)) )
                        ( _⊎_.inl refl)
                        λ n x → _⊎_.inr (n , refl)


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

  EvenOdd→Bool : ℕ → Bool
  EvenOdd→Bool = ℕ-iteration Bool false not

  isZero→Bool : ℕ → Bool
  isZero→Bool = ℕ-iteration Bool true (λ _ → false)


  isZero : ℕ → hProp
  isZero n = caseBool ⊤ ⊥ (isZero→Bool n)


  isZero-zero : [ isZero zero ]
  isZero-zero = transport (sym ( cong (λ w → [ caseBool ⊤ ⊥ w ]) (ℕ-induction-zero (λ _ → Bool) true (λ _ _ → false)))) _

  ¬isZero-suc-n : ∀ n → [ (isZero (suc n)) ] → fst ⊥ 
  ¬isZero-suc-n n = transport ( ( cong (λ w → [ caseBool ⊤ ⊥ w ]) (ℕ-induction-suc (λ _ → Bool) true (λ _ _ → false) n)))

  isOdd : ℕ → hProp 
  isOdd n =  caseBool ⊤ ⊥ (EvenOdd→Bool n)

  s≠z : ∀ {n} → (suc n ≡ zero) → fst ⊥
  s≠z {n} x = {!  !}

  suc-n-≠-n : ∀ n → suc n ≡ n → fst ⊥
  suc-n-≠-n = {!!}

  -- ℕ-induction-zero? : ∀ A → ∀ a₀ → ∀ f → ℕ-induction A a₀ f zero ≡ a₀
  -- ℕ-induction-zero? A a₀ f = let w = ℕ-induction (λ x → ∀ e →  ℕ-induction A a₀ f x ≡ subst A e a₀) (J {!!} {!!}) {!!} zero
  --                            in w refl ∙ substRefl {B = A} a₀

  pred-ℕ : ℕ → ℕ
  pred-ℕ = ℕ-induction (λ _ → ℕ) zero λ n x → n

  pred-suc : ∀ n → pred-ℕ ( suc n ) ≡ n
  pred-suc = ℕ-induction (λ z → pred-ℕ (suc z) ≡ z) (ℕ-induction-suc (λ _ → ℕ) zero (λ n _ → n) zero)
             λ n x → (ℕ-induction-suc (λ _ → ℕ) zero (λ n _ → n)) (suc n)

  suc-inj : ∀ {n₁ n₂} → suc n₁ ≡ suc n₂ → n₁ ≡ n₂
  suc-inj {n₁} {n₂} x =  (sym (pred-suc n₁)) ∙ (cong pred-ℕ x) ∙ pred-suc n₂

  _+_ : ℕ → ℕ → ℕ
  x + x₁ = ℕ-iteration ℕ x suc x₁

  z+z≡z : zero + zero ≡ zero
  z+z≡z = ℕ-induction-zero (λ _ → ℕ) zero (λ _ → suc)


  isZero? : ∀ x →  Dec (zero ≡ x)
  isZero? = ℕ-induction _ (yes refl) λ n x → no λ x₁ → s≠z {n} (sym x₁)

  isZero?′ : ∀ x →  Dec (x ≡ zero)
  isZero?′ = ℕ-induction _ (yes refl) λ n x → no s≠z

  =-suc : (n₁ n₂ : ℕ) → Dec (n₁ ≡ n₂) → Dec (suc n₁ ≡ suc n₂)
  =-suc n₁ n₂ (yes p) = yes (cong suc p)
  =-suc n₁ n₂ (no ¬p) = no λ x → ¬p (suc-inj x)
  
  Discrete-ℕ : Discrete ℕ
  Discrete-ℕ = ℕ-induction (λ x → (y : ℕ) → Dec (x ≡ y))
         (isZero?)
         λ n =? → ℕ-induction (λ z → Dec (suc n ≡ z)) (isZero?′ (suc n)) λ n₁ _ → =-suc _ _ (=? n₁)
  

  isSet-Nat : isSet ℕ
  isSet-Nat = Discrete→isSet Discrete-ℕ 


-- isNat→isNat′ : ∀ {A} → isNat A →  isNat′ A
-- isNat→isNat′ (c-isNat zero suc ℕ-induction ℕ-induction-zero ℕ-induction-suc) = c-isNat′ zero suc ℕ-induction

-- isNat→isNat′-zero : ∀ {A} → (isn : isNat A) → isNat′.ℕ-ind-zero (isNat→isNat′ isn)
-- isNat→isNat′-zero (c-isNat zero suc ℕ-induction ℕ-induction-zero ℕ-induction-suc) = ℕ-induction-zero

-- isNat→isNat′-zero≡ : ∀ {A} → (isn₁ isn₂ : isNat A) → (e : isNat→isNat′ isn₁ ≡ isNat→isNat′ isn₂)
--                      → subst isNat′.ℕ-ind-zero (e) (isNat→isNat′-zero isn₁) ≡ (isNat→isNat′-zero isn₂)
-- isNat→isNat′-zero≡ isn₁ isn₂ e = {!!}

-- isNat→isNat′-suc : ∀ {A} → (isn : isNat A) → isNat′.ℕ-ind-suc (isNat→isNat′ isn)
-- isNat→isNat′-suc (c-isNat zero suc ℕ-induction ℕ-induction-zero ℕ-induction-suc) = ℕ-induction-suc

-- isNat′→isNat : ∀ {A} → (isn′ : isNat′ A) →  isNat′.ℕ-ind-zero (isn′) →  isNat′.ℕ-ind-suc (isn′) → isNat A
-- isNat′→isNat (c-isNat′ zero suc ℕ-induction) x x₁ = c-isNat zero suc ℕ-induction x x₁



-- isNat′≡ : ∀ {A} → (isn₁ : isNat′ A) → (isn₂ : isNat′ A)
--          → (z≡ : (isNat′.zero isn₁ ≡ isNat′.zero isn₂))
--          → (s≡ : (isNat′.suc isn₁ ≡ isNat′.suc isn₂)) 
--          → (∀ B → ∀ zB₁ → ∀ zB₂ → ∀ sB₁ → ∀ sB₂  → (e1 : subst B z≡ zB₁ ≡ zB₂ ) → (e2 : ∀ n x → subst B ((cong _ s≡)) (sB₁ n x) ≡ sB₂ n x)
--               → ∀ m → 
--               isNat′.ℕ-induction isn₁ B zB₁ sB₁ m
--               ≡ isNat′.ℕ-induction isn₂ B zB₂ sB₂ m) 
--          → isn₁ ≡ isn₂ 
-- isNat′.zero (isNat′≡ isn₁ isn₂ z≡ s≡ x i) = z≡ i
-- isNat′.suc (isNat′≡ isn₁ isn₂ z≡ s≡ x i) = s≡ i
-- -- isNat.ℕ-induction (isNat′≡ {A} isn₁ isn₂ z≡ s≡ x i) B = {! λ { (i = i0) → ? ; (i = i1) → ?}!}
-- isNat′.ℕ-induction (isNat′≡ {A} isn₁ isn₂ z≡ s≡ x i) B x₁ x₂ n =
--   hcomp {A = B n}
--           (λ j → λ { (i = i0) → isNat′.ℕ-induction isn₁ B x₁ x₂ n
--                  ; (i = i1) → (x B (subst B (sym z≡) x₁) x₁ (λ n₁ x₃ → subst B (sym (cong (λ f → f n₁) s≡)  ) (x₂ n₁ x₃)) x₂
--                                  (transportTransport⁻ (λ i → B (z≡ i)) x₁)  (λ n₁ x₃ → (transportTransport⁻ (cong (λ v → B (v n₁)) s≡) (x₂ n₁ x₃))) n) j
--                  })
--           (isNat′.ℕ-induction isn₁ B (coei→0 (λ ii → B (z≡ ii)) i x₁) (λ n₁ x₃ →  coei→0 (λ ii → B ( s≡ ii n₁ )) i (x₂ n₁ x₃)) n)



-- isNat≡ : ∀ {A} → (isn₁ : isNat A) → (isn₂ : isNat A)
--          → (z≡ : (isNat.zero isn₁ ≡ isNat.zero isn₂))
--          → (s≡ : (isNat.suc isn₁ ≡ isNat.suc isn₂)) 
--          → (∀ B → ∀ zB₁ → ∀ zB₂ → ∀ sB₁ → ∀ sB₂  → (e1 : subst B z≡ zB₁ ≡ zB₂ ) → (e2 : ∀ n x → subst B ((cong _ s≡)) (sB₁ n x) ≡ sB₂ n x)
--               → ∀ m → 
--               isNat.ℕ-induction isn₁ B zB₁ sB₁ m
--               ≡ isNat.ℕ-induction isn₂ B zB₂ sB₂ m) 
--          → isn₁ ≡ isn₂ 
-- isNat≡ isn₁ isn₂ z≡ s≡ x i =
--   let w = isNat′≡ (isNat→isNat′ isn₁) (isNat→isNat′ isn₂) z≡ s≡ x
--   in
--   isNat′→isNat (w i )
--   ({!!})
--   {!!}    


-- isDefinition-isNat : IsDefinition₂ isNat
-- isDefinition-isNat = isDefinition₂ h-f h-p h-pp h-ppp
--   where

--     h-f : ∀ A₁ A₂ → isNat A₁ → isNat A₂ → A₁ → A₂
--     h-f A₁ A₂ isn₁ isn₂ = isNat.ℕ-iteration isn₁ _ (isNat.zero isn₂) (isNat.suc isn₂)

--     h-p : (A : Set) (ba : isNat A) (x : A) → h-f A A ba ba x ≡ x
--     h-p A ba = isNat.ℕ-induction ba (λ x → h-f A A ba ba x ≡ x) (isNat.ℕ-induction-zero ba _ _ _) (λ n x → (isNat.ℕ-induction-suc ba _ _ _) n ∙ cong (isNat.suc ba) x)

--     h-pp : (A₁ A₂ : Set) (x : isNat A₂) (xx : isNat A₁) →
--              section (h-f A₂ A₁ x xx) (h-f A₁ A₂ xx x)
--     h-pp A₁ A₂ x xx b = {!!}


--     h-z≡ : (A₁ A₂ : Set) (x : isNat A₁) (a : isNat A₂) → _
--     h-z≡ A₁ A₂ x a = (transportRefl _ ∙ isNat.ℕ-induction-zero x _ _ _)


--     h-xa : (A₁ A₂ : Set) (x : isNat A₁) (a : isNat A₂) → ∀ x₁ → isNat.ℕ-induction x (λ _ → A₂) (isNat.zero a) (λ _ → isNat.suc a)
--            (isNat.suc x
--              (isNat.ℕ-induction a (λ _ → A₁) (isNat.zero x) (λ _ → isNat.suc x)
--                (x₁)))
--                  ≡ isNat.suc a x₁
--     h-xa A₁ A₂ x a x₁ = isNat.ℕ-induction a (λ x₁ → isNat.ℕ-induction x (λ _ → A₂) (isNat.zero a) (λ _ → isNat.suc a)
--            (isNat.suc x
--              (isNat.ℕ-induction a (λ _ → A₁) (isNat.zero x) (λ _ → isNat.suc x)
--                (x₁)))
--                  ≡ isNat.suc a x₁)
--                  ( let w = sym (isNat.ℕ-induction-zero a (λ _ → A₁) (isNat.zero x) (λ _ → isNat.suc x)) in
--                    let wq = (isNat.ℕ-induction-suc x (λ _ → A₂) (isNat.zero a) (λ _ → isNat.suc a)) (isNat.ℕ-induction a (λ _ → A₁) (isNat.zero x) (λ _ → isNat.suc x)
--                                                                                                       (isNat.zero a))
--                    in wq ∙ cong (isNat.suc a) (isNat.ℕ-induction-zero′ x (λ _ → A₂) _ w (isNat.zero a) (λ _ → isNat.suc a) ∙ {!substRefl (isNat.zero a)!}))
--                  (λ n x₂ → {!!})
--                  x₁

--     h-s≡ :  (A₁ A₂ : Set) (x : isNat A₁) (a : isNat A₂) → isNat.suc
--                                                             (subst isNat
--                                                              (isoToPath
--                                                               (iso (h-f A₁ A₂ x a) (h-f A₂ A₁ a x) (h-pp A₂ A₁ x a)
--                                                                (h-pp A₁ A₂ a x)))
--                                                              x)
--                                                             ≡ isNat.suc a
--     h-s≡ A₁ A₂ x a = funExt λ x₁ → (transportRefl _ ∙ subst (λ xx → isNat.ℕ-induction x (λ _ → A₂) (isNat.zero a)
--       (λ _ → isNat.suc a)
--       (isNat.suc x
--        (isNat.ℕ-induction a (λ _ → A₁) (isNat.zero x) (λ _ → isNat.suc x)
--         xx))
--       ≡ isNat.suc a x₁) (sym (transportRefl x₁)) (h-xa A₁ A₂ x a x₁))

--     h-ppp : (A₁ A₂ : Set) (x : isNat A₁) (a : isNat A₂) →
--               subst isNat (isoToPath (iso (h-f A₁ A₂ x a) (h-f A₂ A₁ a x) (h-pp A₂ A₁ x a) (h-pp A₁ A₂ a x))) x ≡ a
--     h-ppp A₁ A₂ x a = isNat≡
--       (subst isNat
--         (isoToPath
--          (iso (h-f A₁ A₂ x a) (h-f A₂ A₁ a x) (h-pp A₂ A₁ x a)
--           (h-pp A₁ A₂ a x)))
--         x)
--       a
--       (h-z≡ A₁ A₂ x a)
--       (h-s≡ A₁ A₂ x a)
--       λ B zB₁ zB₂ sB₁ sB₂ e1 e2 →  
--         isNat.ℕ-induction a ( λ m → isNat.ℕ-induction (subst isNat
--                                           (isoToPath
--                                                    (iso (h-f A₁ A₂ x a) (h-f A₂ A₁ a x) (h-pp A₂ A₁ x a)
--                                                     (h-pp A₁ A₂ a x)))
--                                                   x)
--                                                  B zB₁ sB₁ m
--                                                  ≡ isNat.ℕ-induction a B zB₂ sB₂ m)
--                                          (let ez1 = ((isNat.ℕ-induction-zero′ (subst isNat
--                                                      (isoToPath
--                                                      (iso (h-f A₁ A₂ x a) (h-f A₂ A₁ a x) (h-pp A₂ A₁ x a)
--                                                      (h-pp A₁ A₂ a x)))
--                                                        x)) B (isNat.zero a) ((h-z≡ A₁ A₂ x a))  zB₁ sB₁ )
--                                             in  ( ez1  ∙ e1) ∙ (sym (isNat.ℕ-induction-zero a B zB₂ sB₂)))
--                                            λ n x₁ →
--                                              let ez1 = isNat.ℕ-induction-suc′ (subst isNat
--                                                      (isoToPath
--                                                      (iso (h-f A₁ A₂ x a) (h-f A₂ A₁ a x) (h-pp A₂ A₁ x a)
--                                                      (h-pp A₁ A₂ a x)))
--                                                        x) B zB₁ sB₁ n (isNat.suc a) (h-s≡ A₁ A₂ x a) 
--                                              in  (((ez1)
--                                                   ∙ e2 n _)
--                                                   ∙ cong (sB₂ n) x₁) ∙ (sym (isNat.ℕ-induction-suc a B zB₂ sB₂ n)) 

