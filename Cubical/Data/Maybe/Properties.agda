{-# OPTIONS --safe #-}
module Cubical.Data.Maybe.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function using (_∘_; idfun)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed.Base using (Pointed; _→∙_; pt)
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Functions.Embedding --using (isEmbedding)

open import Cubical.Functions.Involution

open import Cubical.Data.Empty as ⊥ using (⊥; isProp⊥)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma using (ΣPathP ; _×_)

open import Cubical.Relation.Nullary --using (¬_; Discrete; yes; no)

open import Cubical.Data.Maybe.Base as Maybe

open import Cubical.Foundations.Path

Maybe∙ : ∀ {ℓ} (A : Type ℓ) → Pointed ℓ
Maybe∙ A .fst = Maybe A
Maybe∙ A .snd = nothing

-- Maybe∙ is the "free pointing" functor, that is, left adjoint to the
-- forgetful functor forgetting the base point.
module _ {ℓ} (A : Type ℓ) {ℓ'} (B : Pointed ℓ') where

  freelyPointedIso : Iso (Maybe∙ A →∙ B) (A → ⟨ B ⟩)
  Iso.fun freelyPointedIso f∙ = fst f∙ ∘ just
  Iso.inv freelyPointedIso f = Maybe.rec (pt B) f , refl
  Iso.rightInv freelyPointedIso f = refl
  Iso.leftInv freelyPointedIso f∙ =
    ΣPathP
      ( funExt (Maybe.elim _ (sym (snd f∙)) (λ a → refl))
      , λ i j → snd f∙ (~ i ∨ j))

map-Maybe-id : ∀ {ℓ} {A : Type ℓ} → ∀ m → map-Maybe (idfun A) m ≡ m
map-Maybe-id nothing = refl
map-Maybe-id (just _) = refl

-- Path space of Maybe type
module MaybePath {ℓ} {A : Type ℓ} where
  Cover : Maybe A → Maybe A → Type ℓ
  Cover nothing  nothing   = Lift Unit
  Cover nothing  (just _)  = Lift ⊥
  Cover (just _) nothing   = Lift ⊥
  Cover (just a) (just a') = a ≡ a'

  reflCode : (c : Maybe A) → Cover c c
  reflCode nothing  = lift tt
  reflCode (just b) = refl

  encode : ∀ c c' → c ≡ c' → Cover c c'
  encode c _ = J (λ c' _ → Cover c c') (reflCode c)

  encodeRefl : ∀ c → encode c c refl ≡ reflCode c
  encodeRefl c = JRefl (λ c' _ → Cover c c') (reflCode c)

  decode : ∀ c c' → Cover c c' → c ≡ c'
  decode nothing  nothing  _ = refl
  decode (just _) (just _) p = cong just p

  decodeRefl : ∀ c → decode c c (reflCode c) ≡ refl
  decodeRefl nothing  = refl
  decodeRefl (just _) = refl

  decodeEncode : ∀ c c' → (p : c ≡ c') → decode c c' (encode c c' p) ≡ p
  decodeEncode c _ =
    J (λ c' p → decode c c' (encode c c' p) ≡ p)
      (cong (decode c c) (encodeRefl c) ∙ decodeRefl c)

  encodeDecode : ∀ c c' → (d : Cover c c') → encode c c' (decode c c' d) ≡ d
  encodeDecode nothing nothing _ = refl
  encodeDecode (just a) (just a') =
    J (λ a' p → encode (just a) (just a') (cong just p) ≡ p) (encodeRefl (just a))

  Cover≃Path : ∀ c c' → Cover c c' ≃ (c ≡ c')
  Cover≃Path c c' = isoToEquiv
    (iso (decode c c') (encode c c') (decodeEncode c c') (encodeDecode c c'))

  Cover≡Path : ∀ c c' → Cover c c' ≡ (c ≡ c')
  Cover≡Path c c' = isoToPath
    (iso (decode c c') (encode c c') (decodeEncode c c') (encodeDecode c c'))

  isOfHLevelCover : (n : HLevel)
    → isOfHLevel (suc (suc n)) A
    → ∀ c c' → isOfHLevel (suc n) (Cover c c')
  isOfHLevelCover n p nothing  nothing   = isOfHLevelLift (suc n) (isOfHLevelUnit (suc n))
  isOfHLevelCover n p nothing  (just a') = isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (just a) nothing   = isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (just a) (just a') = p a a'

isOfHLevelMaybe : ∀ {ℓ} (n : HLevel) {A : Type ℓ}
  → isOfHLevel (suc (suc n)) A
  → isOfHLevel (suc (suc n)) (Maybe A)
isOfHLevelMaybe n lA c c' =
  isOfHLevelRetract (suc n)
    (MaybePath.encode c c')
    (MaybePath.decode c c')
    (MaybePath.decodeEncode c c')
    (MaybePath.isOfHLevelCover n lA c c')

private
 variable
   ℓ : Level
   A : Type ℓ

fromJust-def : A → Maybe A → A
fromJust-def a nothing = a
fromJust-def _ (just a) = a

just-inj : (x y : A) → just x ≡ just y → x ≡ y
just-inj x _ eq = cong (fromJust-def x) eq

isEmbedding-just : isEmbedding (just {A = A})
isEmbedding-just  w z = MaybePath.Cover≃Path (just w) (just z) .snd

¬nothing≡just : ∀ {x : A} → ¬ (nothing ≡ just x)
¬nothing≡just {A = A} {x = x} p = lower (subst (caseMaybe (Maybe A) (Lift ⊥)) p (just x))

¬just≡nothing : ∀ {x : A} → ¬ (just x ≡ nothing)
¬just≡nothing {A = A} {x = x} p = lower (subst (caseMaybe (Lift ⊥) (Maybe A)) p (just x))



isSetMaybe : isSet A → isSet (Maybe A)
isSetMaybe isSetA nothing nothing = isOfHLevelMaybe 0 isSetA nothing nothing
isSetMaybe isSetA nothing (just _) p = ⊥.rec (¬nothing≡just p)
isSetMaybe isSetA (just _) nothing p = ⊥.rec (¬just≡nothing p)
isSetMaybe isSetA x@(just _) y@(just _) = isOfHLevelMaybe 0 isSetA x y


isProp-x≡nothing : (x : Maybe A) → isProp (x ≡ nothing)
isProp-x≡nothing nothing x w =
  subst isProp (MaybePath.Cover≡Path nothing nothing) (isOfHLevelLift 1 isPropUnit) x w
isProp-x≡nothing (just _) p _ = ⊥.rec (¬just≡nothing p)

isProp-nothing≡x : (x : Maybe A) → isProp (nothing ≡ x)
isProp-nothing≡x nothing x w =
  subst isProp (MaybePath.Cover≡Path nothing nothing) (isOfHLevelLift 1 isPropUnit) x w
isProp-nothing≡x (just _) p _ = ⊥.rec (¬nothing≡just p)

isContr-nothing≡nothing : isContr (nothing {A = A} ≡ nothing)
isContr-nothing≡nothing = inhProp→isContr refl (isProp-x≡nothing _)

discreteMaybe : Discrete A → Discrete (Maybe A)
discreteMaybe eqA nothing nothing    = yes refl
discreteMaybe eqA nothing (just a')  = no ¬nothing≡just
discreteMaybe eqA (just a) nothing   = no ¬just≡nothing
discreteMaybe eqA (just a) (just a') with eqA a a'
... | yes p = yes (cong just p)
... | no ¬p = no (λ p → ¬p (just-inj _ _ p))

module SumUnit where
  Maybe→SumUnit : Maybe A → Unit ⊎ A
  Maybe→SumUnit nothing  = inl tt
  Maybe→SumUnit (just a) = inr a

  SumUnit→Maybe : Unit ⊎ A → Maybe A
  SumUnit→Maybe (inl _) = nothing
  SumUnit→Maybe (inr a) = just a

  Maybe→SumUnit→Maybe : (x : Maybe A) → SumUnit→Maybe (Maybe→SumUnit x) ≡ x
  Maybe→SumUnit→Maybe nothing  = refl
  Maybe→SumUnit→Maybe (just _) = refl

  SumUnit→Maybe→SumUnit : (x : Unit ⊎ A) → Maybe→SumUnit (SumUnit→Maybe x) ≡ x
  SumUnit→Maybe→SumUnit (inl _) = refl
  SumUnit→Maybe→SumUnit (inr _) = refl

Maybe≡SumUnit : Maybe A ≡ Unit ⊎ A
Maybe≡SumUnit = isoToPath (iso Maybe→SumUnit SumUnit→Maybe SumUnit→Maybe→SumUnit Maybe→SumUnit→Maybe)
  where open SumUnit

congMaybeIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → Iso A B → Iso (Maybe A) (Maybe B)
congMaybeIso z = isom
  where
  open Iso
  isom : Iso _ _
  isom .fun = map-Maybe (fun z)
  isom .inv = map-Maybe (inv z)
  isom .rightInv nothing = refl
  isom .rightInv (just b) = cong just (rightInv z b)
  isom .leftInv nothing = refl
  isom .leftInv (just a) = cong just (leftInv z a)

congMaybeEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → A ≃ B → Maybe A ≃ Maybe B
congMaybeEquiv e = isoToEquiv isom
  where
  open Iso
  isom : Iso _ _
  isom .fun = map-Maybe (equivFun e)
  isom .inv = map-Maybe (invEq e)
  isom .rightInv nothing = refl
  isom .rightInv (just b) = cong just (secEq e b)
  isom .leftInv nothing = refl
  isom .leftInv (just a) = cong just (retEq e a)


_⨁_ : Maybe A → Maybe A → Type₀
nothing ⨁ nothing = ⊥
nothing ⨁ just x = Unit
just x ⨁ nothing = Unit
just x ⨁ just x₁ = ⊥

-- IsoΣ⨁A : Iso (Σ (Maybe A × Maybe A) (λ x → fst x ⨁ snd x ))  (A × Bool)
-- Iso.fun IsoΣ⨁A ((nothing , just x) , snd₁) = (x , false)
-- Iso.fun IsoΣ⨁A ((just x , nothing) , snd₁) = (x , true)
-- Iso.inv IsoΣ⨁A (x , false) = (nothing , just x) , _
-- Iso.inv IsoΣ⨁A (x , true) = (just x , nothing) , _
-- Iso.rightInv IsoΣ⨁A (fst₁ , false) = {!!}
-- Iso.rightInv IsoΣ⨁A (fst₁ , true) = {!!}
-- Iso.leftInv IsoΣ⨁A = {!!}

uwMbH : (x y : Maybe A) → ¬ x ≡ y → A  
uwMbH nothing nothing x₁ = ⊥.rec (x₁ refl)
uwMbH nothing (just x) x₁ = x
uwMbH (just x) y x₁ = x

record X≟ (A : Type ℓ) : Type ℓ where
  constructor el
  field
    elPt : A
    elTest : ∀ a → Dec (a ≡ elPt)

  NotPt : Type ℓ
  NotPt = Σ A λ x → ¬ x ≡ elPt 

  to : ∀ x → Dec (x ≡ elPt) → Maybe NotPt
  to x (yes p) = nothing
  to x (no ¬p) = just (x , ¬p)

  from : Maybe NotPt → A
  from = rec elPt fst

  s : (b : Maybe NotPt) → ∀ p →  to (from b) p ≡ b
  s nothing (yes p) = refl
  s nothing (no ¬p) = ⊥.rec (¬p refl)
  s (just x) (yes p) = ⊥.rec (snd x p)
  s (just x) (no ¬p) = cong just (ΣPathP (refl , isProp¬ _ _ _))

  r : ∀ x → (p : Dec (x ≡ elPt)) → from (to x p) ≡ x
  r x (yes p) = sym p
  r x (no ¬p) = refl

  IsoANotPt : Iso A (Maybe NotPt)
  Iso.fun IsoANotPt x = to x (elTest x)
  Iso.inv IsoANotPt = from
  Iso.rightInv IsoANotPt b = s b _
  Iso.leftInv IsoANotPt a = r a (elTest a)


  pt↔no' : (a : A) → Dec (a ≡ elPt) → Maybe A
  pt↔no' a (yes p) = nothing
  pt↔no' a (no ¬p) = just a

  pt↔no : Maybe A → Maybe A
  pt↔no nothing = just elPt 
  pt↔no (just x) = pt↔no' x (elTest x)

  isInvolutionPt↔noN : ∀ x → pt↔no' elPt (x) ≡ nothing
  isInvolutionPt↔noN (yes p) = refl
  isInvolutionPt↔noN (no ¬p) = ⊥.rec (¬p refl)

  isInvolutionPt↔noJ : ∀ a x → pt↔no (pt↔no' a x) ≡ just a
  isInvolutionPt↔noJ a (yes p) = cong just (sym p)
  isInvolutionPt↔noJ a (no ¬p) with elTest a
  ... | yes p = ⊥.rec (¬p p)
  ... | no ¬p₁ = refl

  isInvolutionPt↔no : isInvolution pt↔no
  isInvolutionPt↔no nothing = isInvolutionPt↔noN _
  isInvolutionPt↔no (just x) = isInvolutionPt↔noJ _ (elTest x)
  
  isoMbA : Iso (Maybe A) (Maybe A) 
  isoMbA = involIso {f = pt↔no} isInvolutionPt↔no

is? : Discrete A → A → X≟ A 
X≟.elPt (is? x x₁) = x₁
X≟.elTest (is? x x₁) = λ y → x y x₁

open X≟ public

isJust : Maybe A → Type
isJust nothing = ⊥
isJust (just _) = Unit

isPropIsJust : ∀ x → isProp (isJust {A = A} x)
isPropIsJust nothing = isProp⊥
isPropIsJust (just x) = isPropUnit

isNothing : Maybe A → Type
isNothing nothing = Unit
isNothing (just _) = ⊥


fromIsJust : (x : Maybe A) → isJust x → A
fromIsJust (just a) _ = a

just∘fromIsJust : (x : Maybe A) → ∀ y → just (fromIsJust x y) ≡ x 
just∘fromIsJust (just x) y = refl

isJust' : ∀ {ℓ} {A : Type ℓ} → (x : Maybe A) → Type ℓ
isJust' x = Σ _ λ a → x ≡ just a 


MbCases : (x : Maybe A) → Type _
MbCases x = isJust x ⊎ isNothing x


MbCases' : (x : Maybe A) → Type _
MbCases' x = isJust' x ⊎ (x ≡ nothing)


-- MbIsoCases : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
--                (Iso (Maybe A) (Maybe B)) →
-- MbIsoCases = {!!}

-- MbIso→X≟ : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
--                (Iso (Maybe A) (Maybe B)) → Maybe (X≟ A)
-- MbIso→X≟ {A = A} {B = B} isom = 
  

  
mbCases' : (x : Maybe A) → MbCases' x
mbCases' nothing = inr refl
mbCases' (just x) = inl (x , refl)



-- MbIso→X≟ : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
--                (Iso (Maybe A) (Maybe B)) → Maybe (X≟ A)
-- MbIso→X≟ {A = A} {B = B} isom = 
--   ⊎.rec (λ (a' , p) → just (el a'
--     (λ a → ⊎.rec (λ x → no λ q → 
--          let p'' = {!cong just q ∙ (sym p)!}
--          in {!!})
--                  (λ p' → yes {!snd p!})
--                  (mbCases (fun (just a))))))
--     (λ _ → nothing)
--     (mbCases (inv nothing))
--   where
--     open Iso isom

--     a' : Maybe A
--     a' = inv nothing


MbIso→X≟ : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
               (Iso (Maybe A) (Maybe B)) → Maybe (X≟ A)
MbIso→X≟ {A = A} {B = B} isom =
  ⊎.rec (λ (a' , p) → just (el a'
    (λ a → ⊎.rec (λ (x , xx) → no λ q → 
         let p'' = (sym xx) ∙ cong fun (cong just q ∙ (sym p))
         in ¬just≡nothing (p'' ∙ rightInv nothing))
         (λ p' → yes (just-inj _ _ (sym (leftInv (just a)) ∙ cong inv p' ∙ p)))
                 (mbCases' (fun (just a))))))
    (λ _ → nothing)
    (mbCases' (inv nothing))
  where
    open Iso isom

    a' : Maybe A
    a' = inv nothing


IsoMaybeFunProd : ∀ {ℓ'} {B : Type ℓ'} → Iso (Maybe A → B) (B × (A → B))
Iso.fun IsoMaybeFunProd x = (x nothing) , (x ∘ just)
Iso.inv IsoMaybeFunProd x = rec (fst x) (snd x)
Iso.rightInv IsoMaybeFunProd b = refl
Iso.leftInv IsoMaybeFunProd a i nothing = a nothing
Iso.leftInv IsoMaybeFunProd a i (just x) = a (just x)

≃MaybeFunProd : ∀ {ℓ'} {B : Type ℓ'} → (Maybe A → B) ≃ (B × (A → B))
≃MaybeFunProd = isoToEquiv IsoMaybeFunProd

-- uniwndMb : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
--              Iso (Iso (Maybe A) (Maybe B))
--                  ((Maybe (X≟ A)) × Iso A B)
-- Iso.fun uniwndMb e = (MbIso→X≟ e) , {!!}
-- Iso.inv uniwndMb (x , y) = (compIso (rec idIso isoMbA x) (congMaybeIso y))
-- Iso.rightInv uniwndMb = {!!}
-- Iso.leftInv uniwndMb = {!!}




-- -- IsoMbCases : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
-- --   (isom : Iso (Maybe A) (Maybe B)) →
-- --    (isJust' (Iso.fun isom nothing)
-- --      × isJust' (Iso.inv isom nothing)) ⊎
-- --      ( ((Iso.fun isom nothing) ≡ nothing)
-- --      × (Iso.inv isom nothing ≡ nothing))
     
-- -- IsoMbCases isom with mbCases' (Iso.fun isom nothing) | mbCases' (Iso.inv isom nothing)
-- -- ... | inl x | inl x₁ = inl (x , x₁)
-- -- ... | inl x | inr x₁ =
-- --     let z = sym (Iso.rightInv isom nothing)
-- --          ∙ cong (Iso.fun isom) (x₁) ∙ snd x
-- --     in ⊥.rec (¬nothing≡just z)
-- -- ... | inr x | inl x₁ =
-- --     let z = sym (Iso.leftInv isom nothing)
-- --          ∙ cong (Iso.inv isom) (x) ∙ snd x₁
-- --     in ⊥.rec (¬nothing≡just z)
-- -- ... | inr x | inr x₁ = inr (x , x₁)


-- -- -- unwindMbIso' : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
-- -- --              (isom : Iso (Maybe A) (Maybe B)) →
-- -- --              ((isJust' (Iso.fun isom nothing)
-- -- --      × isJust' (Iso.inv isom nothing)) ⊎
-- -- --      ( ((Iso.fun isom nothing) ≡ nothing)
-- -- --      × (Iso.inv isom nothing ≡ nothing)))
-- -- --              → Iso A B
-- -- -- unwindMbIso' isom (inr x) = w
-- -- --   where
-- -- --     open Iso isom

-- -- --     AtoB : _ → _
-- -- --     AtoB a = ⊎.rec fst
-- -- --       (λ p → ⊥.rec (¬just≡nothing (sym (leftInv (just a))
-- -- --           ∙ cong inv p ∙ snd x)))
-- -- --         (mbCases' (fun (just a)))

-- -- --     w : Iso _ _
-- -- --     Iso.fun w = AtoB
-- -- --     Iso.inv w = {!!}
-- -- --     Iso.rightInv w = {!!}
-- -- --     Iso.leftInv w = {!!}
-- -- -- unwindMbIso' isom (inl x) = {!!}


-- -- -- unwindMbIso : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
-- -- --              Iso (Maybe A) (Maybe B) → Iso A B
-- -- -- unwindMbIso = {!!}    




-- uwMb : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (f : Maybe A →  Maybe B) →
--            (p : isEmbedding f) → 
--            (A → B)
-- uwMb {A = A} {B = B} e p a =
--   uwMbH (e nothing) (e (just a))
--    (¬nothing≡just ∘ invEq (_ , (p _ _)))


-- isEquivUwMb : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
--   (e : Iso (Maybe A) (Maybe B)) →
--            Iso A B
-- isEquivUwMb i = w
--   where
--     open Iso i

--     -- wi : section (uwMb fun (iso→isEmbedding i))
--     --              (uwMb inv (iso→isEmbedding (invIso i)))
--     -- wi b with inv (just b) | inspect inv (just b) | fun (nothing) | inspect fun nothing
--     -- ... | nothing | a2 | a3 | a4 = {!!}
--     -- ... | just x | a2 | nothing | a4 = {!!}
--     -- ... | just x | [ path ]ᵢ | just x₁ | [ path₁ ]ᵢ =
--     --   let z = sym (leftInv nothing) ∙ cong inv path₁
--     --   in just-inj _ _ (isoInvInjective i _ _ (just-inj _ _
--     --       (sym (cong just {!path ∙ ?!} ∙ cong just z))))
    
--     w : Iso _ _
--     Iso.fun w = uwMb fun (iso→isEmbedding i)
--     Iso.inv w = uwMb inv (iso→isEmbedding (invIso i))
--     Iso.rightInv w = {!!}
--     Iso.leftInv w = {!!}
  -- let a' = retEq e (just a)
  -- in elim (λ mbB → invEq e mbB ≡ nothing → B)
  --      (λ p → {!!})
  --      (λ b _ → b) (fst e nothing) (retEq e nothing)


-- -- uniwndMb : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
-- --              Iso (Iso (Maybe A) (Maybe B))
-- --                  ((Maybe (X≟ A)) × Iso A B)
-- -- Iso.fun uniwndMb e = (MbIso→X≟ e) , {!!}
-- -- Iso.inv uniwndMb (x , y) = (compIso (rec idIso isoMbA x) (congMaybeIso y))
-- -- Iso.rightInv uniwndMb = {!!}
-- -- Iso.leftInv uniwndMb = {!!}


-- -- -- uniwndMb≃ : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
-- -- --                (e : Iso (Maybe A) (Maybe B)) →
-- -- --                  Σ (Iso A B) λ x → (compIso
-- -- --                    (rec idIso isoMbA (MbIso→X≟ e))
-- -- --                      (congMaybeIso x)) ≡ e   
-- -- -- uniwndMb≃ = {!!}

-- -- -- -- swapMbIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} →
-- -- -- --         (a : X≟ A) → (b : X≟ B)
-- -- -- --          → Iso (NotPt a) (NotPt b)
-- -- -- --          → Iso A B
-- -- -- -- swapMbIso a b iNp =
-- -- -- --   compIso (IsoANotPt a) (compIso (congMaybeIso iNp) (invIso (IsoANotPt b)))

-- -- -- -- isNothing? : (x : Maybe A) → Dec (x ≡ nothing)
-- -- -- -- isNothing? nothing = yes refl
-- -- -- -- isNothing? (just x) = no ¬just≡nothing

-- -- -- -- isNothing isJust : Maybe A → Type₀
-- -- -- -- isNothing = rec Unit λ _ → ⊥
-- -- -- -- isJust = rec ⊥ λ _ → Unit


-- -- -- -- mbCases : (x : Maybe A) → isJust x ⊎ isNothing x
-- -- -- -- mbCases nothing = inr _
-- -- -- -- mbCases (just x) = inl _





-- -- -- -- isoMbCases2MbPts : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
-- -- -- --   (isom : Iso (Maybe A) (Maybe B))
-- -- -- --   → Maybe (X≟ A × X≟ B)
-- -- -- -- isoMbCases2MbPts isom =
-- -- -- --   ⊎.rec
-- -- -- --     (λ ((b , p) , (a , q)) →
-- -- -- --       just ((el a λ a' → a? isom a q a' (mbCases' _))
-- -- -- --           , (el b λ b' → a? (invIso isom) b p b' (mbCases' _))))
-- -- -- --     (λ _ → nothing)
-- -- -- --     (IsoMbCases isom)
-- -- -- --   where
-- -- -- --     a? : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
-- -- -- --            (isom : Iso (Maybe A) (Maybe B)) → 
-- -- -- --             ∀ a → Iso.inv isom nothing ≡ just a → ∀ a' →
-- -- -- --             MbCases' (Iso.fun isom (just a')) →  Dec (a' ≡ a )
-- -- -- --     a? isom a x a' (inl (b , pB)) =
-- -- -- --       no (((λ pp → ¬just≡nothing (pp ∙ sym (cong (Iso.fun isom) x) ∙
-- -- -- --          Iso.rightInv isom nothing) )
-- -- -- --         ∘ (sym pB) ∙_ ) ∘ cong (Iso.fun isom ∘ just))
-- -- -- --     a? isom a q a' (inr x₁) =
-- -- -- --        yes (just-inj _ _
-- -- -- --         (sym (Iso.leftInv isom (just a')) ∙ cong (Iso.inv isom) x₁
-- -- -- --         ∙ q))





-- -- -- -- -- uwMb : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (f : Maybe A →  Maybe B) →
-- -- -- -- --            (p : isEmbedding f) → 
-- -- -- -- --            (A → B)
-- -- -- -- -- uwMb {A = A} {B = B} e p a =
-- -- -- -- --   uwMbH (e nothing) (e (just a))
-- -- -- -- --    (¬nothing≡just ∘ invEq (_ , (p _ _)))


-- -- -- -- -- isEquivUwMb : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
-- -- -- -- --   (e : Iso (Maybe A) (Maybe B)) →
-- -- -- -- --            Iso A B
-- -- -- -- -- isEquivUwMb i = w
-- -- -- -- --   where
-- -- -- -- --     open Iso i

-- -- -- -- --     w : Iso _ _
-- -- -- -- --     Iso.fun w = uwMb fun (iso→isEmbedding i)
-- -- -- -- --     Iso.inv w = uwMb inv (iso→isEmbedding (invIso i))
-- -- -- -- --     Iso.rightInv w b =
-- -- -- -- --       {!elim ? ? ? (inv (just b)) (inv nothing)!}
-- -- -- -- --     Iso.leftInv w = {!!}
-- -- -- -- --   -- let a' = retEq e (just a)
-- -- -- -- --   -- in elim (λ mbB → invEq e mbB ≡ nothing → B)
-- -- -- -- --   --      (λ p → {!!})
-- -- -- -- --   --      (λ b _ → b) (fst e nothing) (retEq e nothing)

-- -- -- -- -- -- -- unwindMb≃Fn : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (e : Maybe A ≃ Maybe B) →
-- -- -- -- -- -- --            (A → B)
-- -- -- -- -- -- -- unwindMb≃Fn e =
-- -- -- -- -- -- --   let b₀ = fst e nothing
-- -- -- -- -- -- --   in {!rec b₀ ?!} ∘ fst e ∘ just


-- -- -- -- -- -- -- isSwap≃ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (e : Maybe A ≃ Maybe B) →
-- -- -- -- -- -- --              Type  (ℓ-max ℓ ℓ')
-- -- -- -- -- -- -- isSwap≃ e = {!!} 

-- -- -- -- -- -- -- ≃Cases : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (e : Maybe A ≃ Maybe B) →
-- -- -- -- -- -- --            (A ≃ B)
-- -- -- -- -- -- -- ≃Cases e = {!!}
