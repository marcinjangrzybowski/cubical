{-# OPTIONS --safe #-}
module Cubical.Data.List.Properties where

open import Agda.Builtin.List
open import Cubical.Core.Everything
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism


open import Cubical.HITs.SequentialColimit as SC

open import Cubical.Data.List.Base

module _ {ℓ} {A : Type ℓ} where

  ++-unit-r : (xs : List A) → xs ++ [] ≡ xs
  ++-unit-r [] = refl
  ++-unit-r (x ∷ xs) = cong (_∷_ x) (++-unit-r xs)

  ++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

  rev-snoc : (xs : List A) (y : A) → rev (xs ++ [ y ]) ≡ y ∷ rev xs
  rev-snoc [] y = refl
  rev-snoc (x ∷ xs) y = cong (_++ [ x ]) (rev-snoc xs y)

  rev-++ : (xs ys : List A) → rev (xs ++ ys) ≡ rev ys ++ rev xs
  rev-++ [] ys = sym (++-unit-r (rev ys))
  rev-++ (x ∷ xs) ys =
    cong (λ zs → zs ++ [ x ]) (rev-++ xs ys)
    ∙ ++-assoc (rev ys) (rev xs) [ x ]

  rev-rev : (xs : List A) → rev (rev xs) ≡ xs
  rev-rev [] = refl
  rev-rev (x ∷ xs) = rev-snoc (rev xs) x ∙ cong (_∷_ x) (rev-rev xs)

  rev-rev-snoc : (xs : List A) (y : A) →
    Square (rev-rev (xs ++ [ y ])) (cong (_++ [ y ]) (rev-rev xs)) (cong rev (rev-snoc xs y)) refl
  rev-rev-snoc [] y = sym (lUnit refl)
  rev-rev-snoc (x ∷ xs) y i j =
    hcomp
      (λ k → λ
        { (i = i1) → compPath-filler (rev-snoc (rev xs) x) (cong (x ∷_) (rev-rev xs)) k j ++ [ y ]
        ; (j = i0) → rev (rev-snoc xs y i ++ [ x ])
        ; (j = i1) → x ∷ rev-rev-snoc xs y i k
        })
      (rev-snoc (rev-snoc xs y i) x j)

  data SnocView : List A → Type ℓ where
    nil : SnocView []
    snoc : (x : A) → (xs : List A) → (sx : SnocView xs) → SnocView (xs ∷ʳ x)

  snocView : (xs : List A) → SnocView xs
  snocView xs = helper nil xs
    where
    helper : {l : List A} -> SnocView l -> (r : List A) -> SnocView (l ++ r)
    helper {l} sl [] = subst SnocView (sym (++-unit-r l)) sl
    helper {l} sl (x ∷ r) = subst SnocView (++-assoc l (x ∷ []) r) (helper (snoc x l sl) r)

-- Path space of list type
module ListPath {ℓ} {A : Type ℓ} where

  Cover : List A → List A → Type ℓ
  Cover [] [] = Lift Unit
  Cover [] (_ ∷ _) = Lift ⊥
  Cover (_ ∷ _) [] = Lift ⊥
  Cover (x ∷ xs) (y ∷ ys) = (x ≡ y) × Cover xs ys

  reflCode : ∀ xs → Cover xs xs
  reflCode [] = lift tt
  reflCode (_ ∷ xs) = refl , reflCode xs

  encode : ∀ xs ys → (p : xs ≡ ys) → Cover xs ys
  encode xs _ = J (λ ys _ → Cover xs ys) (reflCode xs)

  encodeRefl : ∀ xs → encode xs xs refl ≡ reflCode xs
  encodeRefl xs = JRefl (λ ys _ → Cover xs ys) (reflCode xs)

  decode : ∀ xs ys → Cover xs ys → xs ≡ ys
  decode [] [] _ = refl
  decode [] (_ ∷ _) (lift ())
  decode (x ∷ xs) [] (lift ())
  decode (x ∷ xs) (y ∷ ys) (p , c) = cong₂ _∷_ p (decode xs ys c)

  decodeRefl : ∀ xs → decode xs xs (reflCode xs) ≡ refl
  decodeRefl [] = refl
  decodeRefl (x ∷ xs) = cong (cong₂ _∷_ refl) (decodeRefl xs)

  decodeEncode : ∀ xs ys → (p : xs ≡ ys) → decode xs ys (encode xs ys p) ≡ p
  decodeEncode xs _ =
    J (λ ys p → decode xs ys (encode xs ys p) ≡ p)
      (cong (decode xs xs) (encodeRefl xs) ∙ decodeRefl xs)

  isOfHLevelCover : (n : HLevel) (p : isOfHLevel (suc (suc n)) A)
    (xs ys : List A) → isOfHLevel (suc n) (Cover xs ys)
  isOfHLevelCover n p [] [] =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isPropUnit)
  isOfHLevelCover n p [] (y ∷ ys) =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (x ∷ xs) [] =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (x ∷ xs) (y ∷ ys) =
    isOfHLevelΣ (suc n) (p x y) (\ _ → isOfHLevelCover n p xs ys)

isOfHLevelList : ∀ {ℓ} (n : HLevel) {A : Type ℓ}
  → isOfHLevel (suc (suc n)) A → isOfHLevel (suc (suc n)) (List A)
isOfHLevelList n ofLevel xs ys =
  isOfHLevelRetract (suc n)
    (ListPath.encode xs ys)
    (ListPath.decode xs ys)
    (ListPath.decodeEncode xs ys)
    (ListPath.isOfHLevelCover n ofLevel xs ys)

private
  variable
    ℓ : Level
    A : Type ℓ

caseList : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (n c : B) → List A → B
caseList n _ []      = n
caseList _ c (_ ∷ _) = c

safe-head : A → List A → A
safe-head x []      = x
safe-head _ (x ∷ _) = x

safe-tail : List A → List A
safe-tail []       = []
safe-tail (_ ∷ xs) = xs

cons-inj₁ : ∀ {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
cons-inj₁ {x = x} p = cong (safe-head x) p

cons-inj₂ : ∀ {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
cons-inj₂ = cong safe-tail

¬cons≡nil : ∀ {x : A} {xs} → ¬ (x ∷ xs ≡ [])
¬cons≡nil {A = A} p = lower (subst (caseList (Lift ⊥) (List A)) p [])

¬nil≡cons : ∀ {x : A} {xs} → ¬ ([] ≡ x ∷ xs)
¬nil≡cons {A = A} p = lower (subst (caseList (List A) (Lift ⊥)) p [])

¬snoc≡nil : ∀ {x : A} {xs} → ¬ (xs ∷ʳ x ≡ [])
¬snoc≡nil {xs = []} contra = ¬cons≡nil contra
¬snoc≡nil {xs = x ∷ xs} contra = ¬cons≡nil contra

¬nil≡snoc : ∀ {x : A} {xs} → ¬ ([] ≡ xs ∷ʳ x)
¬nil≡snoc contra = ¬snoc≡nil (sym contra)

cons≡rev-snoc : (x : A) → (xs : List A) → x ∷ rev xs ≡ rev (xs ∷ʳ x)
cons≡rev-snoc _ [] = refl
cons≡rev-snoc x (y ∷ ys) = λ i → cons≡rev-snoc x ys i ++ y ∷ []

isContr[]≡[] : isContr (Path (List A) [] [])
isContr[]≡[] = refl , ListPath.decodeEncode [] []

isPropXs≡[] : {xs : List A} → isProp (xs ≡ [])
isPropXs≡[] {xs = []} = isOfHLevelSuc 0 isContr[]≡[]
isPropXs≡[] {xs = x ∷ xs} = λ p _ → ⊥.rec (¬cons≡nil p)

discreteList : Discrete A → Discrete (List A)
discreteList eqA []       []       = yes refl
discreteList eqA []       (y ∷ ys) = no ¬nil≡cons
discreteList eqA (x ∷ xs) []       = no ¬cons≡nil
discreteList eqA (x ∷ xs) (y ∷ ys) with eqA x y | discreteList eqA xs ys
... | yes p | yes q = yes (λ i → p i ∷ q i)
... | yes _ | no ¬q = no (λ p → ¬q (cons-inj₂ p))
... | no ¬p | _     = no (λ q → ¬p (cons-inj₁ q))

foldrCons : (xs : List A) → foldr _∷_ [] xs ≡ xs
foldrCons [] = refl
foldrCons (x ∷ xs) = cong (x ∷_) (foldrCons xs)

length-map : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} → (f : A → B) → (as : List A)
  → length (map f as) ≡ length as
length-map f [] = refl
length-map f (a ∷ as) = cong suc (length-map f as)

length++ : (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length++ [] ys = refl
length++ (x ∷ xs) ys = cong suc (length++ xs ys)

map-++ : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} → (f : A → B) → (as bs : List A)
          → map f (as ++ bs) ≡ map f as ++ map f bs
map-++ _ = ind (λ _ → refl) (cong (_ ∷_) ∘_)  

map-rev : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} → (f : A → B) → (xs : List A)
          → map f (rev xs) ≡ rev (map f xs)
map-rev _ = ind refl (λ {_} {l} p → map-++ _ (rev l) [ _ ] ∙ cong (_++ [ _ ]) p)  


lookupMb : ℕ → List A → Maybe A
lookupMb x [] = nothing
lookupMb zero (a ∷ _) = just a
lookupMb (suc x) (_ ∷ l) = lookupMb x l


IsoListUnitℕ : Iso (List Unit) ℕ
Iso.fun IsoListUnitℕ = length
Iso.inv IsoListUnitℕ x = iter x (tt ∷_) [] 
Iso.rightInv IsoListUnitℕ = ℕ.elim refl λ _ → cong suc
Iso.leftInv IsoListUnitℕ = ind refl (cong (tt ∷_))

-- foldr : ∀ {ℓ'} {B : Type ℓ'} → (A → B → B) → B → List A → B

-- foldr-map : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
--              → (f : B → C → C) → (b : B) → (l : List A) → (g : A → B)
--              → {!foldr f b l!}
-- foldr-map = {!!}

-- module _ {ℓ} {A : Type ℓ} where

--  map' : List A → (ℕ → A) → List A × (ℕ → A)
--  map' [] f = [] , f
--  map' (x ∷ xs) f = xs , cases x f
 
--  []×ℕ : Sequence ℓ
--  Sequence.space []×ℕ _ = List A × (ℕ → A)
--  Sequence.map []×ℕ = uncurry map'
 
-- --  (l , f) = f zero ∷ l , f ∘ suc

--  Lim→[]×ℕ-ℕ→ : (Lim→ []×ℕ) → (ℕ → A)
--  Lim→[]×ℕ-ℕ→ = SC.elim []×ℕ
--    (λ _ → ℕ → A)
--    w
--   where
--    wf : (x : List A) (y : ℕ → A) → ℕ → A
--    wf [] f  = f
--    wf (x ∷ x₂) f =
--      wf x₂ (cases x f) 
--    -- wf [] f = f
--    -- wf (x ∷ _) _ zero = x
--    -- wf (_ ∷ x₂) y (suc x₁) = wf x₂ y x₁

--    wp : (x : List A) (y : ℕ → A) →
--           wf x y ≡ wf (fst (map' x y)) (snd (map' x y))
--    wp [] y = refl
--    wp (x ∷ x₁) y = refl

--    w : ElimData []×ℕ (λ _ → ℕ → A)
--    ElimData.finl w = uncurry wf
--    ElimData.fpush w = uncurry wp

--  Iso-Lim→[]×ℕ-ℕ→ : Iso (Lim→ []×ℕ) (ℕ → A)
--  Iso.fun Iso-Lim→[]×ℕ-ℕ→ = Lim→[]×ℕ-ℕ→
--  Iso.inv Iso-Lim→[]×ℕ-ℕ→ = inl {n = zero} ∘ ([] ,_)
--  Iso.rightInv Iso-Lim→[]×ℕ-ℕ→ _ = refl
--  Iso.leftInv Iso-Lim→[]×ℕ-ℕ→ = SC.elim []×ℕ _ w
--   where
--    w-finl : ∀ k → (x : List A) (y : ℕ → A) →
--       Path (Lim→ []×ℕ)
--       (inl {n = zero} ([] , Lim→[]×ℕ-ℕ→ (inl {n = k} (x , y))))
--       (inl {n = k} (x , y))
--    w-finl zero [] y = refl
--    w-finl zero (x ∷ x₁) y = w-finl (suc zero) x₁ (cases x y) ∙
--      {!push ?!}
--    w-finl (suc k) x y = {!!}

--    w : ElimData []×ℕ
--          (λ z → Iso.inv Iso-Lim→[]×ℕ-ℕ→ (Iso.fun Iso-Lim→[]×ℕ-ℕ→ z) ≡ z)
--    ElimData.finl w {k} = uncurry (w-finl k)
--    ElimData.fpush w = {!!}
