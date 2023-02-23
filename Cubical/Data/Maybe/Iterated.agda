{-# OPTIONS --safe #-}
module Cubical.Data.Maybe.Iterated where

open import Cubical.Foundations.Everything

open import Cubical.Relation.Nullary

open import Cubical.Data.Maybe.Base as Mb
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Maybe.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Foundations.Function
open import Cubical.Functions.Involution


open import Cubical.Data.Nat

private
  variable
    ℓ ℓ' : Level
    A∙ : Pointed ℓ
    B∙ : Pointed ℓ

-- (_≟_ : Discrete ⟨ A∙ ⟩)

if-dec : ∀ {ℓ ℓ'} (A : Type ℓ) {B : Type ℓ'} →
   B → B → Dec A → B
if-dec _ x₁ x₂ (yes p) = x₁
if-dec _ x₁ x₂ (no ¬p) = x₂


swap-dec≡ : ∀ {ℓ} (A : Type  ℓ) (a a' x : A)
       → (Dec (x ≡ a))
       → (Dec (x ≡ a'))
      → A
swap-dec≡ A a a' x (yes p) x₂ = a'
swap-dec≡ A a a' x (no ¬p) (yes p) = a
swap-dec≡ A a a' x (no ¬p) (no ¬p₁) = x

swap-decFn : ∀ {ℓ} {A : Type  ℓ} → X≟ A → X≟ A → A → A
swap-decFn {A = A} a a' y =
 swap-dec≡ A (a .elPt ) (a' .elPt ) y (a .elTest y) (a' .elTest y)


swap-dec≡-involHelp : ∀ {ℓ} {A : Type  ℓ} → (a a' x : A)
    → (a? : Dec (x ≡ a)) → (a'? : Dec (x ≡ a'))
    → (a*? : Dec (swap-dec≡ A a a' x a? a'? ≡ a))
    → (a'*? : Dec (swap-dec≡ A a a' x a? a'? ≡ a'))
    → swap-dec≡ A a a'
      (swap-dec≡ A a a' x a? a'?)
      a*? a'*?
      -- (a .elTest
      --  (swap-dec≡ A a a' x a? a'?))
      -- (a' .elTest
      --  (swap-dec≡ A a a' x a? a'?))
      ≡ x
swap-dec≡-involHelp a a' x (yes p) (yes p₂) (yes p₁) a'*? = sym p₂
swap-dec≡-involHelp a a' x (yes p) (no ¬p) (yes p₁) a'*? =
  ⊥.rec (¬p (p ∙ (sym p₁)))
swap-dec≡-involHelp a a' x (no ¬p) (yes p₁) (yes p) a'*? = sym p₁
swap-dec≡-involHelp a a' x (no ¬p) (no ¬p₁) (yes p) a'*? = ⊥.rec (¬p p)
swap-dec≡-involHelp a a' x (no ¬p) (yes p₁) (no ¬p₁) (yes p) = ⊥.rec (¬p₁ refl)
swap-dec≡-involHelp a a' x (no ¬p) (no ¬p₂) (no ¬p₁) (yes p) = ⊥.rec (¬p₂ p)
swap-dec≡-involHelp a a' x (no ¬p) (yes p) (no ¬p₁) (no ¬p₂) = ⊥.rec (¬p₁ refl)
swap-dec≡-involHelp a a' x (no ¬p) (no ¬p₃) (no ¬p₁) (no ¬p₂) = refl
swap-dec≡-involHelp a a' x (yes p) a'? (no ¬p) (yes p₁) = sym p
swap-dec≡-involHelp a a' x (yes p) a'? (no ¬p) (no ¬p₁) = ⊥.rec (¬p₁ refl)

swap-dec≡-invol : ∀ {ℓ} {A : Type  ℓ} → (a a' : X≟ A)
    → isInvolution (swap-decFn a a')
swap-dec≡-invol a a' x = swap-dec≡-involHelp
  (a .elPt ) (a' .elPt ) x (a .elTest x) (a' .elTest x)
   (a .elTest _) (a' .elTest _)

swap-dec≡Equiv : ∀ {ℓ} (A : Type  ℓ) → X≟ A → X≟ A → A ≃ A
swap-dec≡Equiv A a a' = involEquiv {f = swap-decFn a a'} (swap-dec≡-invol a a')


swap-dec≡-GP-n : ∀ {ℓ} (A : Type  ℓ) → (a a' : X≟ A) → ∀ a? a'?
    → swap-dec≡ A (a .elPt) (a' .elPt) (elPt a) a? a'? ≡ elPt a'
swap-dec≡-GP-n A a a' (yes p) a'? = refl
swap-dec≡-GP-n A a a' (no ¬p) a'? = ⊥.rec (¬p refl)

elimYes : ∀ {ℓ ℓ'} (A : Type ℓ) {B B' : Type ℓ'}
   → A → B → ∀ a' → if-dec A B B' a'  
elimYes A a x (yes p) = x
elimYes A a x (no ¬p) = ⊥.rec (¬p a)

elimNo : ∀ {ℓ ℓ'} (A : Type ℓ) {B B' : Type ℓ'}
   → ¬ A → B' → ∀ a' → if-dec A B B' a'  
elimNo A ¬a x₁ (yes p) = ⊥.rec (¬a p)
elimNo A ¬a x₁ (no ¬p) = x₁


-- 𝑇 : ∀ ℓ → Type (ℓ-suc ℓ)
-- 𝑇 ℓ = Σ (Type ℓ) λ T → Σ (Type ℓ) λ T' → (Maybe T' ≃ Maybe T)

-- Ty' : ∀ {ℓ} → 𝑇 ℓ → Type ℓ
-- Ty' = fst ∘ snd

-- -- Ty'? : ∀ {ℓ} → (x : 𝑇 ℓ) → X≟ (Ty' x)
-- -- Ty'? (fst₁ , x) = {!!}

-- 𝑇pa : ∀ {ℓ} → (A : Type ℓ) →
--       (a a' : X≟ A) →
--         Path (𝑇 ℓ)
--          (A , A , idEquiv _ , a)
--          (A , A , idEquiv _ , a')
-- fst (𝑇pa A a a' _) = A
-- fst (snd (𝑇pa A a a' i)) = {!!}
-- fst (snd (snd (𝑇pa A a a' i))) = {!ua-glueEquivExt!}
-- snd (snd (snd (𝑇pa A a a' i))) = {!!}

-- module Maybe↔ (𝑡 : 𝑇 ℓ)  where

--  A = fst 𝑡

--  data Maybe↔ : Type ℓ where
--    no : Maybe↔
--    ju : A → Maybe↔
--    ↔[_] : Maybe↔ → Maybe↔
--    invol-↔ : isInvolution ↔[_]
--    -- βj : ∀ x p → ↔[ ju x ] ≡ if-dec (x ≡ pt A∙) no (ju x) p

-- --  βn : ↔[ no ] ≡ ju (pt A∙)
-- --  βn = sym (cong  ↔[_] (βj (pt A∙) (yes refl))) ∙ invol-↔ _

-- --  ↔equiv : Maybe↔ ≃ Maybe↔
-- --  ↔equiv = involEquiv {f = ↔[_]} invol-↔


-- -- --  Maybe↔∙ : Pointed ℓ
-- -- --  Maybe↔∙ = Maybe↔ , no

-- -- --  fromMaybe : Maybe ⟨ A∙ ⟩ → Maybe↔ 
-- -- --  fromMaybe nothing = no
-- -- --  fromMaybe (just x) = ju x

-- -- --  module _ (_≟_ : Discrete ⟨ A∙ ⟩) where

  
-- -- --   to↔[] : (x : Maybe↔) → (x' : Maybe ⟨ A∙ ⟩)
-- -- --           → Mb.rec Unit* (λ y → Dec (y ≡ pt A∙)) x'
-- -- --              → Maybe ⟨ A∙ ⟩ 
-- -- --   to↔[] x nothing _ = just (pt A∙)
-- -- --   to↔[] x (just y) = if-dec _ nothing (just y)


-- -- --   to-invol-n : (x : Dec (pt A∙ ≡ pt A∙)) → 
-- -- --      if-dec _ nothing (just (pt A∙)) x ≡ nothing
-- -- --   to-invol-n (yes p) = refl
-- -- --   to-invol-n (no ¬p) = ⊥.rec (¬p refl)

-- -- --   to-invol-j-n : (x : Maybe↔) (x₁ : ⟨ A∙ ⟩) → (¬ x₁ ≡ pt A∙) → ∀ z →
-- -- --     if-dec (x₁ ≡ pt A∙) nothing (just x₁) z ≡ just x₁ 
-- -- --   to-invol-j-n x x₁ x₂ (yes p) = ⊥.rec (x₂ p)
-- -- --   to-invol-j-n x x₁ x₂ (no ¬p) = refl

-- -- --   to-invol-j : (x : Maybe↔) (x₁ : ⟨ A∙ ⟩) (p : Dec (x₁ ≡ pt A∙))
-- -- --       → to↔[] ↔[ x ]
-- -- --       (if-dec (x₁ ≡ pt A∙) nothing (just x₁) p)
-- -- --       (Mb.elim (Mb.rec Unit* (λ y → Dec (y ≡ pt A∙))) tt*
-- -- --        (λ z → z ≟ pt A∙)
-- -- --        (if-dec (x₁ ≡ pt A∙) nothing (just x₁) p))
-- -- --       ≡ just x₁
-- -- --   to-invol-j x x₁ (yes p) = cong just (sym p)
-- -- --   to-invol-j x x₁ (no ¬p) = to-invol-j-n x x₁ ¬p (x₁ ≟ pt A∙)

-- -- --   to-invol : ∀ x x' → 
-- -- --      to↔[] ↔[ x ]
-- -- --          (to↔[] x x'
-- -- --           (Mb.elim (Mb.rec Unit* (λ y → Dec (y ≡ pt A∙))) tt*
-- -- --            (λ z → z ≟ pt A∙) x'))
-- -- --          (Mb.elim (Mb.rec Unit* (λ y → Dec (y ≡ pt A∙))) tt*
-- -- --           (λ z → z ≟ pt A∙)
-- -- --           (to↔[] x x'
-- -- --            (Mb.elim (Mb.rec Unit* (λ y → Dec (y ≡ pt A∙))) tt*
-- -- --             (λ z → z ≟ pt A∙) x')))
-- -- --       ≡ x'
-- -- --   to-invol x nothing = to-invol-n (pt A∙ ≟ pt A∙)
-- -- --   to-invol x (just x₁) = to-invol-j x x₁ (x₁ ≟ pt A∙)


-- -- --   toMaybe : Maybe↔ → Maybe ⟨ A∙ ⟩

-- -- --   to-β : (x : ⟨ A∙ ⟩) (p z : Dec (x ≡ pt A∙)) →
-- -- --         if-dec (x ≡ pt A∙) nothing (just x) z
-- -- --           ≡ toMaybe (if-dec (x ≡ pt A∙) no (ju x) p)

-- -- --   toMaybe no = nothing
-- -- --   toMaybe (ju x) = just x
-- -- --   toMaybe ↔[ x ] = to↔[] x (toMaybe x)
-- -- --     (Mb.elim (Mb.rec Unit* (λ y → Dec (y ≡ pt A∙)))
-- -- --      _ (λ _ → _ ≟ _) (toMaybe x))

-- -- --   toMaybe (invol-↔ x i) = to-invol x (toMaybe x) i
-- -- --   toMaybe (βj x p i) = to-β x p (x ≟ pt A∙) i

-- -- --   to-β x (yes p) (yes p₁) = refl
-- -- --   to-β x (yes p) (no ¬p) = ⊥.rec (¬p p)
-- -- --   to-β x (no ¬p) (yes p) = ⊥.rec (¬p p)
-- -- --   to-β x (no ¬p) (no ¬p₁) = refl


-- -- --   sectionToMaybeFromMaybe : section toMaybe fromMaybe
-- -- --   sectionToMaybeFromMaybe nothing = refl
-- -- --   sectionToMaybeFromMaybe (just x) = refl

-- -- --   ret-ju : ∀ x z → fromMaybe (if-dec (x ≡ pt A∙) nothing (just x) z) ≡
-- -- --       ↔[ ju x ]
-- -- --   ret-ju x (yes p) = sym (βj x (yes p))
-- -- --   ret-ju x (no ¬p) = sym (βj x (no ¬p))

-- -- --   -- retractToMaybeFromMaybe : retract toMaybe fromMaybe
-- -- --   -- retractToMaybeFromMaybe no = refl
-- -- --   -- retractToMaybeFromMaybe (ju x) = refl
-- -- --   -- retractToMaybeFromMaybe ↔[ no ] = sym βn
-- -- --   -- retractToMaybeFromMaybe ↔[ ju x ] = ret-ju x (x ≟ pt A∙)
-- -- --   -- retractToMaybeFromMaybe ↔[ ↔[ x ] ] i =
-- -- --   --   invol-↔ ((cong fromMaybe (to-invol x (toMaybe x)) ∙
-- -- --   --       retractToMaybeFromMaybe x) i) (~ i)
-- -- --   -- retractToMaybeFromMaybe ↔[ invol-↔ x i ] j =
-- -- --   --   {!!}
    
-- -- --   -- retractToMaybeFromMaybe ↔[ βj x p i ] = {!!}
-- -- --   -- retractToMaybeFromMaybe (invol-↔ x i) = {!!}
-- -- --   -- retractToMaybeFromMaybe (βj x p i) = {!!}
  
-- -- -- --  retractToMaybeFromMaybe (↔≡₀ i) = {!!}
-- -- -- --  retractToMaybeFromMaybe (↔≡₁ x x₁ i) = {!!}
-- -- -- --  retractToMaybeFromMaybe (↔≡ⱼ x x₁ i) = {!!}


-- -- -- --  IsoMaybe↔Maybe : Iso Maybe↔ (Maybe ⟨ A∙ ⟩)
-- -- -- --  Iso.fun IsoMaybe↔Maybe = toMaybe
-- -- -- --  Iso.inv IsoMaybe↔Maybe = fromMaybe
-- -- -- --  Iso.rightInv IsoMaybe↔Maybe = sectionToMaybeFromMaybe
-- -- -- --  Iso.leftInv IsoMaybe↔Maybe = retractToMaybeFromMaybe

-- -- --   𝕤 : (x : Maybe↔) → singl x
-- -- --   𝕤 no = no , refl
-- -- --   𝕤 (ju x) = _ , refl
-- -- --   𝕤 ↔[ no ] = ju (pt A∙) , βn
-- -- --   𝕤 ↔[ ju x ] = _ , βj x (x ≟ pt A∙)
-- -- --   𝕤 ↔[ ↔[ x ] ] = x , invol-↔ x
-- -- --   𝕤 ↔[ invol-↔ x i ] = snd (𝕤 ↔[ x ]) i , λ j → {!!}  
-- -- --   𝕤 ↔[ βj x p i ] = {!!}
-- -- --   𝕤 (invol-↔ x i) = {!!}
-- -- --   𝕤 (βj x p i) = {!!}


-- -- --   ↔unglue : PathP (λ i → ua (↔equiv) i → Maybe↔) ↔[_] (idfun _)
-- -- --   ↔unglue = ua-ungluePathExt (↔equiv)


-- -- --   ↔unglue' : PathP (λ i → ua (↔equiv) i → Maybe↔) (idfun _) ↔[_]
-- -- --   ↔unglue' i x = snd (𝕤 (↔[ ↔unglue i x ])) (~ i)






module Maybe↔ (A∙ : Pointed ℓ)  where

 data Maybe↔ : Type ℓ where
   no : Maybe↔
   ju : ⟨ A∙ ⟩ → Maybe↔
   ↔[_] : Maybe↔ → Maybe↔
   invol-↔ : isInvolution ↔[_]
   βj : ∀ x p → ↔[ ju x ] ≡ if-dec (x ≡ pt A∙) no (ju x) p

 βn : ↔[ no ] ≡ ju (pt A∙)
 βn = sym (cong  ↔[_] (βj (pt A∙) (yes refl))) ∙ invol-↔ _

 ↔equiv : Maybe↔ ≃ Maybe↔
 ↔equiv = involEquiv {f = ↔[_]} invol-↔


 Maybe↔∙ : Pointed ℓ
 Maybe↔∙ = Maybe↔ , no

 fromMaybe : Maybe ⟨ A∙ ⟩ → Maybe↔ 
 fromMaybe nothing = no
 fromMaybe (just x) = ju x

 module _ (_≟_ : Discrete ⟨ A∙ ⟩) where

  
  to↔[] : (x : Maybe↔) → (x' : Maybe ⟨ A∙ ⟩)
          → Mb.rec Unit* (λ y → Dec (y ≡ pt A∙)) x'
             → Maybe ⟨ A∙ ⟩ 
  to↔[] x nothing _ = just (pt A∙)
  to↔[] x (just y) = if-dec _ nothing (just y)


  to-invol-n : (x : Dec (pt A∙ ≡ pt A∙)) → 
     if-dec _ nothing (just (pt A∙)) x ≡ nothing
  to-invol-n (yes p) = refl
  to-invol-n (no ¬p) = ⊥.rec (¬p refl)

  to-invol-j-n : (x : Maybe↔) (x₁ : ⟨ A∙ ⟩) → (¬ x₁ ≡ pt A∙) → ∀ z →
    if-dec (x₁ ≡ pt A∙) nothing (just x₁) z ≡ just x₁ 
  to-invol-j-n x x₁ x₂ (yes p) = ⊥.rec (x₂ p)
  to-invol-j-n x x₁ x₂ (no ¬p) = refl

  to-invol-j : (x : Maybe↔) (x₁ : ⟨ A∙ ⟩) (p : Dec (x₁ ≡ pt A∙))
      → to↔[] ↔[ x ]
      (if-dec (x₁ ≡ pt A∙) nothing (just x₁) p)
      (Mb.elim (Mb.rec Unit* (λ y → Dec (y ≡ pt A∙))) tt*
       (λ z → z ≟ pt A∙)
       (if-dec (x₁ ≡ pt A∙) nothing (just x₁) p))
      ≡ just x₁
  to-invol-j x x₁ (yes p) = cong just (sym p)
  to-invol-j x x₁ (no ¬p) = to-invol-j-n x x₁ ¬p (x₁ ≟ pt A∙)

  to-invol : ∀ x x' → 
     to↔[] ↔[ x ]
         (to↔[] x x'
          (Mb.elim (Mb.rec Unit* (λ y → Dec (y ≡ pt A∙))) tt*
           (λ z → z ≟ pt A∙) x'))
         (Mb.elim (Mb.rec Unit* (λ y → Dec (y ≡ pt A∙))) tt*
          (λ z → z ≟ pt A∙)
          (to↔[] x x'
           (Mb.elim (Mb.rec Unit* (λ y → Dec (y ≡ pt A∙))) tt*
            (λ z → z ≟ pt A∙) x')))
      ≡ x'
  to-invol x nothing = to-invol-n (pt A∙ ≟ pt A∙)
  to-invol x (just x₁) = to-invol-j x x₁ (x₁ ≟ pt A∙)


  toMaybe : Maybe↔ → Maybe ⟨ A∙ ⟩

  to-β : (x : ⟨ A∙ ⟩) (p z : Dec (x ≡ pt A∙)) →
        if-dec (x ≡ pt A∙) nothing (just x) z
          ≡ toMaybe (if-dec (x ≡ pt A∙) no (ju x) p)

  toMaybe no = nothing
  toMaybe (ju x) = just x
  toMaybe ↔[ x ] = to↔[] x (toMaybe x)
    (Mb.elim (Mb.rec Unit* (λ y → Dec (y ≡ pt A∙)))
     _ (λ _ → _ ≟ _) (toMaybe x))

  toMaybe (invol-↔ x i) = to-invol x (toMaybe x) i
  toMaybe (βj x p i) = to-β x p (x ≟ pt A∙) i

  to-β x (yes p) (yes p₁) = refl
  to-β x (yes p) (no ¬p) = ⊥.rec (¬p p)
  to-β x (no ¬p) (yes p) = ⊥.rec (¬p p)
  to-β x (no ¬p) (no ¬p₁) = refl


  sectionToMaybeFromMaybe : section toMaybe fromMaybe
  sectionToMaybeFromMaybe nothing = refl
  sectionToMaybeFromMaybe (just x) = refl

  ret-ju : ∀ x z → fromMaybe (if-dec (x ≡ pt A∙) nothing (just x) z) ≡
      ↔[ ju x ]
  ret-ju x (yes p) = sym (βj x (yes p))
  ret-ju x (no ¬p) = sym (βj x (no ¬p))

  -- retractToMaybeFromMaybe : retract toMaybe fromMaybe
  -- retractToMaybeFromMaybe no = refl
  -- retractToMaybeFromMaybe (ju x) = refl
  -- retractToMaybeFromMaybe ↔[ no ] = sym βn
  -- retractToMaybeFromMaybe ↔[ ju x ] = ret-ju x (x ≟ pt A∙)
  -- retractToMaybeFromMaybe ↔[ ↔[ x ] ] i =
  --   invol-↔ ((cong fromMaybe (to-invol x (toMaybe x)) ∙
  --       retractToMaybeFromMaybe x) i) (~ i)
  -- retractToMaybeFromMaybe ↔[ invol-↔ x i ] j =
  --   {!!}
    
  -- retractToMaybeFromMaybe ↔[ βj x p i ] = {!!}
  -- retractToMaybeFromMaybe (invol-↔ x i) = {!!}
  -- retractToMaybeFromMaybe (βj x p i) = {!!}
  
--  retractToMaybeFromMaybe (↔≡₀ i) = {!!}
--  retractToMaybeFromMaybe (↔≡₁ x x₁ i) = {!!}
--  retractToMaybeFromMaybe (↔≡ⱼ x x₁ i) = {!!}


--  IsoMaybe↔Maybe : Iso Maybe↔ (Maybe ⟨ A∙ ⟩)
--  Iso.fun IsoMaybe↔Maybe = toMaybe
--  Iso.inv IsoMaybe↔Maybe = fromMaybe
--  Iso.rightInv IsoMaybe↔Maybe = sectionToMaybeFromMaybe
--  Iso.leftInv IsoMaybe↔Maybe = retractToMaybeFromMaybe

  𝕤 : (x : Maybe↔) → singl x
  𝕤 no = no , refl
  𝕤 (ju x) = _ , refl
  𝕤 ↔[ no ] = ju (pt A∙) , βn
  𝕤 ↔[ ju x ] = _ , βj x (x ≟ pt A∙)
  𝕤 ↔[ ↔[ x ] ] = x , invol-↔ x
  𝕤 ↔[ invol-↔ x i ] = snd (𝕤 ↔[ x ]) i , λ j → {!!}  
  𝕤 ↔[ βj x p i ] = {!!}
  𝕤 (invol-↔ x i) = {!!}
  𝕤 (βj x p i) = {!!}


  ↔unglue : PathP (λ i → ua (↔equiv) i → Maybe↔) ↔[_] (idfun _)
  ↔unglue = ua-ungluePathExt (↔equiv)


  ↔unglue' : PathP (λ i → ua (↔equiv) i → Maybe↔) (idfun _) ↔[_]
  ↔unglue' i x = snd (𝕤 (↔[ ↔unglue i x ])) (~ i)



open Maybe↔

changePt : (a' : ⟨ A∙ ⟩) → (Maybe↔ A∙) → (Maybe↔ ( ⟨ A∙ ⟩ , pt A∙ ))
changePt a' no = no
changePt a' (ju x) = ju x
changePt a' ↔[ x ] = {!!}
changePt a' (invol-↔ x i) = {!!}
changePt a' (βj x p i) = {!!}

-- changePtIso : (a' : ⟨ A∙ ⟩) →
--     Iso (Maybe↔ A∙) (Maybe↔ ( ⟨ A∙ ⟩ , pt A∙ )) 
-- Iso.fun (changePtIso a') = changePt a'
-- Iso.inv (changePtIso {A∙ = A∙} a') = changePt (pt A∙) 
-- Iso.rightInv (changePtIso a') = {!!}
-- Iso.leftInv (changePtIso a') = {!!}

-- -- changePtIso zero pt0 pt1 = idEquiv _
-- -- changePtIso (suc zero) pt0 pt1 = {!!}
-- -- changePtIso (suc (suc n)) pt0 pt1 = {!!}

-- ↔Pa : Maybe↔∙ A∙ ≡ (⟨ Maybe↔∙ A∙ ⟩ , ↔[ no ])
-- ↔Pa = ΣPathP (ua (↔equiv _) , λ i → ua-gluePathExt (↔equiv _) i no)

-- -- -- ↔pa : Maybe↔ A∙ ≡ Maybe↔ A∙
-- -- -- ↔pa {A∙ = A∙} i =
-- -- --    Glue (ua (↔equiv A∙) i)
-- -- --      λ { (i = i0) → {!!}
-- -- --         ;(i = i1) → {!!}
-- -- --         } 

-- -- -- ↔Pa∙ : Maybe↔∙ A∙ ≡ Maybe↔∙ A∙
-- -- -- ↔Pa∙ = ΣPathP ({!!} , {!!})


-- -- -- module Maybe↔Pa (a a' : ⟨ A∙ ⟩) (e e' : Iso ⟨ A∙ ⟩ ⟨ A∙ ⟩)
-- -- --      (a'≟ : ∀ x → Dec (a' ≡ x)) (a≟ : ∀ x → Dec (pt A∙ ≡ x))
-- -- --      where

-- -- --  -- module E = Iso e
-- -- --  -- module E' = Iso e'

-- -- --  -- ⟨ A∙ ⟩ : ?

-- -- --  Pa→ : (Maybe↔ A∙) → (Maybe↔ (⟨ A∙ ⟩ , a'))
-- -- --  Pa→ no = ↔no
-- -- --  Pa→ (ju x) = ju {!swap-dec≡ (pt A∙) a' x !}
-- -- --  Pa→ ↔[ x ] = {!!}
-- -- --  Pa→ (invol-↔ x i) = {!!}
-- -- --  Pa→ (βj x p i) = {!!}

-- -- --  Pa← : (Maybe↔ (⟨ A∙ ⟩ , a')) → (Maybe↔ A∙)
-- -- --  Pa← no = no
-- -- --  Pa← (ju x) = {!!}
-- -- --  Pa← ↔[ x ] = {!!}
-- -- --  Pa← (invol-↔ x i) = {!!}
-- -- --  Pa← (βj x p i) = {!!}

-- -- --  Pa : Iso (Maybe↔ A∙) (Maybe↔ (⟨ A∙ ⟩ , a')) 
-- -- --  Iso.fun Pa = Pa→
-- -- --  Iso.inv Pa = {!!}
-- -- --  Iso.rightInv Pa = {!!}
-- -- --  Iso.leftInv Pa = {!!}


-- -- -- -- -- map↔∙ : (f : A∙ →∙ B∙) → (∀ x → fst f x ≡ fst f (pt A∙) → x ≡ pt A∙) →
-- -- -- -- --   Maybe↔ A∙ → Maybe↔ B∙
-- -- -- -- -- map↔ f y no = no
-- -- -- -- -- map↔ f y (ju x) = ju (fst f x)
-- -- -- -- -- map↔ f y ↔[ x ] = ↔[ map↔ f y x ]
-- -- -- -- -- map↔ f y (invol-↔ x i) = (invol-↔ (map↔ f y x ) i) 
-- -- -- -- -- map↔ f y (βj x (yes p) i) = (βj (fst f x) (yes (cong (fst f) p ∙ snd f)) i)
-- -- -- -- -- map↔ f y (βj x (no ¬p) i) = (βj (fst f x) (no (¬p ∘ y x ∘' (_∙ sym (snd f)))) i)


-- -- -- -- -- Pointed↔ : ∀ n → (A : Type) → (P : A ≃ A) →
-- -- -- -- --                 PathP
-- -- -- -- --                   (λ i → Σ Type₀ (λ T → T ≃ T) →  Type₁)
-- -- -- -- --                   (λ x → {!!}) {!!}
-- -- -- -- -- Pointed↔ n i = {!Σ ? ?!}



-- -- 𝔽in : ℕ → Pointed ℓ-zero

-- -- -- -- d𝔽in : ∀ n → Discrete ⟨ 𝔽in n ⟩

-- -- 𝔽in zero = Unit , _
-- -- 𝔽in (suc x) = Maybe↔∙ (𝔽in x)

-- -- changePtIso : ∀ n pt0 pt1 →
-- --     ⟨ Maybe↔∙ (⟨ 𝔽in n ⟩ , pt0) ⟩
-- --   ≃ ⟨ Maybe↔∙ (⟨ 𝔽in n ⟩ , pt1) ⟩
-- -- changePtIso zero pt0 pt1 = idEquiv _
-- -- changePtIso (suc zero) pt0 pt1 = {!!}
-- -- changePtIso (suc (suc n)) pt0 pt1 = {!!}


-- -- changePt : ∀ n pt0 pt1 →
-- --     ⟨ Maybe↔∙ (⟨ 𝔽in n ⟩ , pt0) ⟩
-- --   ≃ ⟨ Maybe↔∙ (⟨ 𝔽in n ⟩ , pt1) ⟩
-- -- changePt = {!!}

-- -- swap01≃ : ∀ n → ⟨ 𝔽in n ⟩ ≡ ⟨ 𝔽in n ⟩
-- -- swap01≃ zero = refl
-- -- swap01≃ (suc n) = ua (↔equiv (𝔽in n))

-- -- swap01≃' : ∀ n → ⟨ 𝔽in n ⟩ ≡ ⟨ 𝔽in n ⟩
-- -- swap01≃' zero = refl
-- -- swap01≃' (suc n) = ua (↔equiv _)


-- -- swapAt≡ : ∀ n → ℕ → ⟨ 𝔽in n ⟩ ≡ ⟨ 𝔽in n ⟩

-- -- swapAt≡S : ∀ n → ℕ → ⟨ Maybe↔∙ (𝔽in n) ⟩ ≡ ⟨ Maybe↔∙ (𝔽in n) ⟩



-- -- swapAt≡ zero k = refl
-- -- swapAt≡ (suc n) (suc k) = swapAt≡S n k
-- -- swapAt≡ (suc n) zero = swap01≃' (suc n)
-- --  -- cong fst (swap01≃∙ (suc n)) ∙ {!!}

-- -- swapAt≡S n k = cong (fst ∘' Maybe↔∙) (ΣPathP (swapAt≡ n k , {!!}))


-- -- -- adjT≡pt : ∀ n → ℕ → ⟨ 𝔽in n ⟩
-- -- -- adjT≡pt zero x = _
-- -- -- adjT≡pt (suc n) (suc x) = no
-- -- -- adjT≡pt (suc n) zero = ↔[ no ]

-- -- -- zero↔ : ∀ n → ⟨ 𝔽in n ⟩
-- -- -- zero↔ n = pt (𝔽in n)

-- -- -- swap01≃∙ : ∀ n → (𝔽in n) ≡ (⟨ 𝔽in n ⟩ , adjT≡pt n zero)
-- -- -- swap01≃∙ zero = refl
-- -- -- swap01≃∙ (suc n) =
-- -- --   ΣPathP (swap01≃ (suc n) ,
-- -- --    λ i → ua-gluePathExt (↔equiv (𝔽in n)) i no)


-- -- -- 𝔽in* : ℕ → ℕ → Pointed ℓ-zero
-- -- -- 𝔽in* zero x = 𝔽in zero
-- -- -- 𝔽in* (suc n) (suc x) = Maybe↔∙ (𝔽in* n x)
-- -- -- 𝔽in* (suc n) zero = (⟨ 𝔽in (suc n) ⟩ , adjT≡pt (suc n) zero)



-- -- -- swap01≃∙' : ∀ n → Iso (Maybe↔ (⟨ 𝔽in n ⟩ , adjT≡pt n zero))
-- -- --                       (Maybe↔ (𝔽in n )) 
-- -- -- swap01≃∙' zero = {!!}
-- -- -- swap01≃∙' (suc n) = {!!}
-- -- --   -- ΣPathP (swap01≃ (suc n) ,
-- -- --   --  λ i → ua-gluePathExt (↔equiv (𝔽in n)) i no)


-- -- -- adjT≡ : ∀ n → ℕ → 𝔽in n ≡ 𝔽in n
-- -- -- adjT≡ zero x = refl
-- -- -- adjT≡ (suc n) (suc x) = cong Maybe↔∙ (adjT≡ n x)
-- -- --  -- 𝔽in*≡ (suc n) (suc x) ∙ cong Maybe↔∙ (sym (𝔽in*≡ n x))
-- -- -- adjT≡ (suc n) zero = {!  !}


-- -- -- -- -- ptPa : ∀ n → (e : ⟨ 𝔽in n ⟩ ≡ ⟨ 𝔽in n ⟩) → ∀ x x' →
-- -- -- -- --      PathP (λ i → e i ) x x'
-- -- -- -- --      → Path (Pointed ℓ-zero) (Maybe↔∙ (⟨ 𝔽in n ⟩  , x ))
-- -- -- -- --                              (Maybe↔∙ (⟨ 𝔽in n ⟩  , x' ))
-- -- -- -- -- ptPa n e x x' p i = Maybe↔∙ ( e i  , p i)



-- -- -- -- -- 𝔽in↔ : ℕ → Pointed ℓ-zero
-- -- -- -- -- 𝔽in↔ n = swap01≃∙ n i1

-- -- -- -- 𝔽in*≡ : ∀ n k → 𝔽in n ≡ 𝔽in* n k
-- -- -- -- 𝔽in*≡ zero x = refl
-- -- -- -- 𝔽in*≡ (suc n) (suc k) = cong Maybe↔∙ (𝔽in*≡ n k)
-- -- -- -- 𝔽in*≡ (suc n) zero = swap01≃∙ (suc n)
-- -- -- -- -- swap01≃∙ (suc n) 


-- -- -- -- 𝔽in*≡𝔽in : ∀ n k → ⟨  𝔽in* n k  ⟩ ≡ ⟨ 𝔽in n ⟩
-- -- -- -- 𝔽in*≡𝔽in zero k = refl
-- -- -- -- 𝔽in*≡𝔽in (suc n) (suc k) = {!n !}
-- -- -- -- 𝔽in*≡𝔽in (suc n) zero = ua (changePt n _ _)

-- -- -- -- -- zz : ∀ n k → PathP (λ i → 𝔽in*≡𝔽in n k i) (snd (𝔽in* n k)) (snd (𝔽in n))





-- -- -- -- -- 𝔽in*≡𝔽in zero k = refl
-- -- -- -- -- 𝔽in*≡𝔽in (suc n) (suc k) = cong (fst ∘ Maybe↔∙)
-- -- -- -- --    (ΣPathP (𝔽in*≡𝔽in n k , zz n k))
-- -- -- -- -- 𝔽in*≡𝔽in (suc n) zero = refl

-- -- -- -- -- zz zero k = refl
-- -- -- -- -- zz (suc n) (suc k) = toPathP refl
-- -- -- -- -- zz (suc n) zero = {!!}




-- -- -- -- -- -- -- suc𝔽in≃ : ∀ n → (⟨ 𝔽in n ⟩ ≃ ⟨ 𝔽in n ⟩) → (⟨ 𝔽in (suc n) ⟩ ≃ ⟨ 𝔽in (suc n) ⟩)
-- -- -- -- -- -- -- suc𝔽in≃ zero x = idEquiv _
-- -- -- -- -- -- -- suc𝔽in≃ (suc n) x = {!map↔ ? ?!}



-- -- -- -- -- -- -- -- cong : Iso ⟨ A∙ ⟩ ⟨ A∙ ⟩ → Iso ⟨ Maybe↔∙ A∙ ⟩ ⟨ Maybe↔∙ A∙ ⟩
-- -- -- -- -- -- -- -- congMb↔≡ = {!!}

-- -- -- -- -- -- -- -- -- d𝔽in zero x y = yes refl
-- -- -- -- -- -- -- -- -- d𝔽in (suc n) x y = {!!}

-- -- -- -- -- -- -- -- Mb^ : ℕ → Type ℓ → Type ℓ 
-- -- -- -- -- -- -- -- Mb^ zero A = A
-- -- -- -- -- -- -- -- Mb^ (suc x) = Maybe ∘ Mb^ x

-- -- -- -- -- -- -- -- -- Iso𝔽inMbⁿ⊤0 : Iso ⟨ 𝔽in zero ⟩ Unit
-- -- -- -- -- -- -- -- -- Iso𝔽inMbⁿ⊤0 = 

-- -- -- -- -- -- -- -- -- Iso𝔽inMbⁿ⊤ : ∀ n → Iso ⟨ 𝔽in n ⟩ (Mb^ n Unit)
-- -- -- -- -- -- -- -- -- Iso𝔽inMbⁿ⊤ zero = idIso
-- -- -- -- -- -- -- -- -- Iso𝔽inMbⁿ⊤ (suc n) = {!!}


-- -- -- -- -- -- -- -- Pointed↔ : ∀ n → I → Type₀
-- -- -- -- -- -- -- -- Pointed↔ n = {!!}

-- -- -- -- -- -- -- -- -- adjT≡∙  : ∀ n → ℕ → 𝔽in n ≡ 𝔽in n  
-- -- -- -- -- -- -- -- -- adjT≡∙ zero k = refl
-- -- -- -- -- -- -- -- -- adjT≡∙(suc n) (suc k) i =
-- -- -- -- -- -- -- -- --  {!!}
-- -- -- -- -- -- -- -- --  -- cong Maybe↔∙ (adjT≡∙ n k)
-- -- -- -- -- -- -- -- -- adjT≡∙ (suc n) zero = ΣPathP {!!}
-- -- -- -- -- -- -- -- -- -- ua (↔equiv (𝔽in n)) i


-- -- -- -- -- -- -- -- -- adjT≡∙ : ∀ n → ℕ → ⟨ 𝔽in n ⟩ ≡ ⟨ 𝔽in n ⟩
-- -- -- -- -- -- -- -- -- adjT≡∙ zero k = refl
-- -- -- -- -- -- -- -- -- adjT≡∙ (suc n) (suc k) = {!!} --congMb↔≡ (adjT≡∙ n k)
-- -- -- -- -- -- -- -- -- adjT≡∙ (suc n) zero = ua (↔equiv (𝔽in n))
-- -- -- -- -- -- -- -- -- -- -- fst (adjT≡∙ (suc n) zero i) = ua (↔equiv (𝔽in n)) i
-- -- -- -- -- -- -- -- -- -- -- snd (adjT≡∙ (suc n) zero i) =
-- -- -- -- -- -- -- -- -- -- --   glue (λ { (i = i0) → no
-- -- -- -- -- -- -- -- -- -- --           ; (i = i1) → no
-- -- -- -- -- -- -- -- -- -- --           }) {!!}

-- -- -- -- -- -- -- -- -- -- adjT≡∙ : ∀ n k → 𝔽in n ≡ (⟨ 𝔽in n ⟩ , adjT≡pt n k)  
-- -- -- -- -- -- -- -- -- -- adjT≡∙ zero k = refl
-- -- -- -- -- -- -- -- -- -- adjT≡∙ (suc n) (suc k) = {!!}
-- -- -- -- -- -- -- -- -- --   -- cong Maybe↔∙ (adjT≡∙ n k) ∙ {!!} 
-- -- -- -- -- -- -- -- -- -- fst (adjT≡∙ (suc n) zero i) = ua (↔equiv (𝔽in n)) i
-- -- -- -- -- -- -- -- -- -- snd (adjT≡∙ (suc n) zero i) = ua-gluePathExt (↔equiv (𝔽in n)) i no


-- -- -- -- -- -- -- -- -- adjT≡ : ∀ n → ℕ → ⟨ 𝔽in n ⟩ ≡ ⟨ 𝔽in n ⟩  
-- -- -- -- -- -- -- -- -- adjT≡ zero k = refl
-- -- -- -- -- -- -- -- -- adjT≡ (suc n) (suc k) = {!!}
-- -- -- -- -- -- -- -- -- adjT≡ (suc n) zero i = ua (↔equiv (𝔽in n)) i
-- -- -- -- -- -- -- -- -- -- snd (adjT≡ (suc n) zero i) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- jn↔n : Mb^ 2 A → Mb^ 2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- jn↔n nothing = just nothing
-- -- -- -- -- -- -- -- -- -- -- -- -- jn↔n (just nothing) = nothing
-- -- -- -- -- -- -- -- -- -- -- -- -- jn↔n (just (just x)) = just (just x)

-- -- -- -- -- -- -- -- -- -- -- -- -- data Maybe² (A : Type) : Type where
-- -- -- -- -- -- -- -- -- -- -- -- --   no₀ no₁ : Maybe² A
-- -- -- -- -- -- -- -- -- -- -- -- --   ju : A → Maybe² A
-- -- -- -- -- -- -- -- -- -- -- -- --   ↔[_] : Maybe² A → Maybe² A
-- -- -- -- -- -- -- -- -- -- -- -- --   ↔≡₀ : ↔[ no₀ ] ≡ no₁
-- -- -- -- -- -- -- -- -- -- -- -- --   ↔≡₁ : ↔[ no₁ ] ≡ no₀
-- -- -- -- -- -- -- -- -- -- -- -- --   ↔≡ⱼ : ∀ x → ↔[ ju x ] ≡ ju x

-- -- -- -- -- -- -- -- -- -- -- -- discreteMaybe _≟_ (just (pt A∙))
-- -- -- -- -- -- -- -- -- -- -- --  -- isNo : (x : Maybe↔) → Dec (x ≡ no)
-- -- -- -- -- -- -- -- -- -- -- --  -- isNo no = yes refl
-- -- -- -- -- -- -- -- -- -- -- --  -- isNo (ju x) = no {!!}
-- -- -- -- -- -- -- -- -- -- -- --  -- isNo ↔[ no ] = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  -- isNo ↔[ ju x ] = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  -- isNo ↔[ ↔[ x ] ] = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  -- isNo ↔[ ↔≡₀ i ] = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  -- isNo ↔[ ↔≡₁ i ] = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  -- isNo ↔[ ↔≡ⱼ x x₁ i ] = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  -- isNo (↔≡₀ i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  -- isNo (↔≡₁ i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  -- isNo (↔≡ⱼ x x₁ i) = {!!}

-- -- -- -- -- -- -- -- -- -- -- --  -- Disc-Maybe↔ : Discrete Maybe↔
-- -- -- -- -- -- -- -- -- -- -- --  -- Disc-Maybe↔ x y = {!x!}
 
-- -- -- -- -- -- -- -- -- -- -- -- open Maybe↔

-- -- -- -- -- -- -- -- -- -- -- -- 𝔽in : ℕ → Pointed ℓ-zero

-- -- -- -- -- -- -- -- -- -- -- -- d𝔽in : ∀ n → Discrete ⟨ 𝔽in n ⟩

-- -- -- -- -- -- -- -- -- -- -- -- 𝔽in zero = Unit , _
-- -- -- -- -- -- -- -- -- -- -- -- 𝔽in (suc x) = Maybe↔∙ (𝔽in x) (d𝔽in x)

-- -- -- -- -- -- -- -- -- -- -- -- d𝔽in zero x y = yes refl
-- -- -- -- -- -- -- -- -- -- -- -- d𝔽in (suc n) x y = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- Mb^ : ℕ → Type ℓ → Type ℓ 
-- -- -- -- -- -- -- -- -- -- -- -- -- Mb^ zero A = A
-- -- -- -- -- -- -- -- -- -- -- -- -- Mb^ (suc x) = Maybe ∘ Mb^ x

-- -- -- -- -- -- -- -- -- -- -- -- -- jn↔n : Mb^ 2 A → Mb^ 2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- jn↔n nothing = just nothing
-- -- -- -- -- -- -- -- -- -- -- -- -- jn↔n (just nothing) = nothing
-- -- -- -- -- -- -- -- -- -- -- -- -- jn↔n (just (just x)) = just (just x)

-- -- -- -- -- -- -- -- -- -- -- -- -- data Maybe² (A : Type) : Type where
-- -- -- -- -- -- -- -- -- -- -- -- --   no₀ no₁ : Maybe² A
-- -- -- -- -- -- -- -- -- -- -- -- --   ju : A → Maybe² A
-- -- -- -- -- -- -- -- -- -- -- -- --   ↔[_] : Maybe² A → Maybe² A
-- -- -- -- -- -- -- -- -- -- -- -- --   ↔≡₀ : ↔[ no₀ ] ≡ no₁
-- -- -- -- -- -- -- -- -- -- -- -- --   ↔≡₁ : ↔[ no₁ ] ≡ no₀
-- -- -- -- -- -- -- -- -- -- -- -- --   ↔≡ⱼ : ∀ x → ↔[ ju x ] ≡ ju x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- ↔_ : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ↔_ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- Mb→Mb² : Mb^ 2 A → Maybe² A
-- -- -- -- -- -- -- -- -- -- -- -- -- Mb→Mb² nothing = no₀
-- -- -- -- -- -- -- -- -- -- -- -- -- Mb→Mb² (just nothing) = no₁
-- -- -- -- -- -- -- -- -- -- -- -- -- Mb→Mb² (just (just x)) = ju x

-- -- -- -- -- -- -- -- -- -- -- -- -- Mb²→Mb : Maybe² A → Mb^ 2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- Mb²→Mb no₀ = nothing
-- -- -- -- -- -- -- -- -- -- -- -- -- Mb²→Mb no₁ = just nothing
-- -- -- -- -- -- -- -- -- -- -- -- -- Mb²→Mb (ju x) = just (just x)
-- -- -- -- -- -- -- -- -- -- -- -- -- Mb²→Mb ↔[ x ] = jn↔n (Mb²→Mb x)
-- -- -- -- -- -- -- -- -- -- -- -- -- Mb²→Mb (↔≡₀ i) = just nothing
-- -- -- -- -- -- -- -- -- -- -- -- -- Mb²→Mb (↔≡₁ i) = nothing
-- -- -- -- -- -- -- -- -- -- -- -- -- Mb²→Mb (↔≡ⱼ x i) = just (just x)

-- -- -- -- -- -- -- -- -- -- -- -- -- sec-Mb²→Mb : section (Mb²→Mb {A = A}) Mb→Mb²
-- -- -- -- -- -- -- -- -- -- -- -- -- sec-Mb²→Mb nothing = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- sec-Mb²→Mb (just nothing) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- sec-Mb²→Mb (just (just x)) = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- ret-hlp : ∀ x → Mb→Mb² {A = A} (jn↔n x) ≡ ↔[ Mb→Mb² x ]
-- -- -- -- -- -- -- -- -- -- -- -- -- ret-hlp nothing = sym ↔≡₀
-- -- -- -- -- -- -- -- -- -- -- -- -- ret-hlp (just nothing) = sym ↔≡₁
-- -- -- -- -- -- -- -- -- -- -- -- -- ret-hlp (just (just x)) = sym (↔≡ⱼ x)

-- -- -- -- -- -- -- -- -- -- -- -- -- ret-Mb²→Mb : retract (Mb²→Mb {A = A}) Mb→Mb²
-- -- -- -- -- -- -- -- -- -- -- -- -- ret-Mb²→Mb no₀ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- ret-Mb²→Mb no₁ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- ret-Mb²→Mb (ju x) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- ret-Mb²→Mb ↔[ a ] = 
-- -- -- -- -- -- -- -- -- -- -- -- --   ret-hlp _ ∙ cong ↔[_] (ret-Mb²→Mb a)
-- -- -- -- -- -- -- -- -- -- -- -- -- ret-Mb²→Mb (↔≡₀ i) j = compPath-filler' ↔≡₀ refl (~ i) (~ j)
-- -- -- -- -- -- -- -- -- -- -- -- -- ret-Mb²→Mb (↔≡₁ i) j = compPath-filler' ↔≡₁ refl (~ i) (~ j)
-- -- -- -- -- -- -- -- -- -- -- -- -- ret-Mb²→Mb (↔≡ⱼ x i) j = compPath-filler' (↔≡ⱼ x) refl (~ i) (~ j)

-- -- -- -- -- -- -- -- -- -- -- -- -- Iso-Mb²-Mb^2 : Iso (Maybe² A) (Mb^ 2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun Iso-Mb²-Mb^2 = Mb²→Mb
-- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv Iso-Mb²-Mb^2 = Mb→Mb²
-- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv Iso-Mb²-Mb^2 = sec-Mb²→Mb
-- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv Iso-Mb²-Mb^2 = ret-Mb²→Mb

-- -- -- -- -- -- -- -- -- -- -- -- -- invo-↔[] : isInvolution (↔[_] {A = A})
-- -- -- -- -- -- -- -- -- -- -- -- -- invo-↔[] no₀ = cong ↔[_] ↔≡₀ ∙ ↔≡₁
-- -- -- -- -- -- -- -- -- -- -- -- -- invo-↔[] no₁ = cong ↔[_] ↔≡₁ ∙ ↔≡₀
-- -- -- -- -- -- -- -- -- -- -- -- -- invo-↔[] (ju x) = cong ↔[_] (↔≡ⱼ x) ∙ ↔≡ⱼ x
-- -- -- -- -- -- -- -- -- -- -- -- -- invo-↔[] ↔[ x ] = cong ↔[_] (invo-↔[] x)
-- -- -- -- -- -- -- -- -- -- -- -- -- invo-↔[] (↔≡₀ i) j =
-- -- -- -- -- -- -- -- -- -- -- -- --   hcomp
-- -- -- -- -- -- -- -- -- -- -- -- --     (λ z →
-- -- -- -- -- -- -- -- -- -- -- -- --         λ {(i = i0) → ↔[ compPath-filler' (cong ↔[_] ↔≡₀) ↔≡₁ z j ]
-- -- -- -- -- -- -- -- -- -- -- -- --           ;(j = i0) → ↔[ ↔[ ↔≡₀ (i ∨ ~ z) ] ]
-- -- -- -- -- -- -- -- -- -- -- -- --           ;(j = i1) → ↔≡₀ (z ∧ i) })
-- -- -- -- -- -- -- -- -- -- -- -- --           ↔[ ↔≡₁ j ]

-- -- -- -- -- -- -- -- -- -- -- -- -- invo-↔[] (↔≡₁ i) j =
-- -- -- -- -- -- -- -- -- -- -- -- --     hcomp
-- -- -- -- -- -- -- -- -- -- -- -- --     (λ z →
-- -- -- -- -- -- -- -- -- -- -- -- --         λ {(i = i0) → ↔[ compPath-filler' (cong ↔[_] ↔≡₁) ↔≡₀ z j ]
-- -- -- -- -- -- -- -- -- -- -- -- --           ;(j = i0) → ↔[ ↔[ ↔≡₁ (i ∨ ~ z) ] ]
-- -- -- -- -- -- -- -- -- -- -- -- --           ;(j = i1) → ↔≡₁ (z ∧ i) })
-- -- -- -- -- -- -- -- -- -- -- -- --           ↔[ ↔≡₀ j ]

-- -- -- -- -- -- -- -- -- -- -- -- -- invo-↔[] (↔≡ⱼ x i) j =
-- -- -- -- -- -- -- -- -- -- -- -- --       hcomp
-- -- -- -- -- -- -- -- -- -- -- -- --     (λ z →
-- -- -- -- -- -- -- -- -- -- -- -- --         λ {(i = i0) → ↔[ compPath-filler' (cong ↔[_] (↔≡ⱼ x)) (↔≡ⱼ x) z j ]
-- -- -- -- -- -- -- -- -- -- -- -- --           ;(j = i0) → ↔[ ↔[ ↔≡ⱼ x (i ∨ ~ z) ] ]
-- -- -- -- -- -- -- -- -- -- -- -- --           ;(j = i1) → ↔≡ⱼ x (z ∧ i) })
-- -- -- -- -- -- -- -- -- -- -- -- --           ↔[ ↔≡ⱼ x j ]


-- -- -- -- -- -- -- -- -- -- -- -- -- ↔equiv : Maybe² A ≃ Maybe² A
-- -- -- -- -- -- -- -- -- -- -- -- -- ↔equiv = involEquiv {f = ↔[_]} invo-↔[]


-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 : (x : Maybe² A) → singl x
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 no₀ = _  , refl
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 no₁ = _ , refl
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 (ju x) = _  , refl
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 ↔[ no₀ ] = _ , ↔≡₀
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 ↔[ no₁ ] = _ , ↔≡₁
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 ↔[ ju x ] = _ , ↔≡ⱼ x
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 ↔[ ↔[ x ] ] = x , invo-↔[] x
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 ↔[ ↔≡₀ i ] = no₀ , compPath-filler' (cong ↔[_] ↔≡₀) ↔≡₁ (~ i) 
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 ↔[ ↔≡₁ i ] = no₁ , compPath-filler' (cong ↔[_] ↔≡₁) ↔≡₀ (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 ↔[ ↔≡ⱼ x i ] = ju x , compPath-filler' (cong ↔[_] (↔≡ⱼ x)) (↔≡ⱼ x) (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 (↔≡₀ i) = no₁ , λ j → ↔≡₀ (j ∨ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 (↔≡₁ i) = no₀ , λ j → ↔≡₁ (j ∨ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- 𝕤 (↔≡ⱼ x i) = ju x , λ j → ↔≡ⱼ x (j ∨ i)


-- -- -- -- -- -- -- -- -- -- -- -- -- ↔unglue : PathP (λ i → ua (↔equiv {A = A}) i → Maybe² A) ↔[_] (idfun _)
-- -- -- -- -- -- -- -- -- -- -- -- -- ↔unglue {A = A} = ua-ungluePathExt (↔equiv {A = A})


-- -- -- -- -- -- -- -- -- -- -- -- -- ↔unglue' : PathP (λ i → ua (↔equiv {A = A}) i → Maybe² A) (idfun _) ↔[_]
-- -- -- -- -- -- -- -- -- -- -- -- -- ↔unglue' {A = A} i x = snd (𝕤 (↔[ ↔unglue i x ])) (~ i)

