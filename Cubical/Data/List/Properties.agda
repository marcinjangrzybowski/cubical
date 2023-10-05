{-# OPTIONS --safe #-}
module Cubical.Data.List.Properties where

open import Agda.Builtin.List
open import Cubical.Core.Everything
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary

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

snoc-inj₂ : ∀ {x y : A} {xs ys} → xs ∷ʳ x ≡ ys ∷ʳ y → x ≡ y
snoc-inj₂ {xs = xs} {ys} p =
 cons-inj₁ ((sym (rev-++ xs _)) ∙∙ cong rev p ∙∙ (rev-++ ys _))
 
snoc-inj₁ : ∀ {x y : A} {xs ys} → xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys
snoc-inj₁ {xs = xs} {ys} p =
   sym (rev-rev _) ∙∙ cong rev (cons-inj₂ ((sym (rev-++ xs _)) ∙∙ cong rev p ∙∙ (rev-++ ys _)))
        ∙∙ rev-rev _ 

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

map++ : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} → (f : A → B) → (as bs : List A)
   → map f as ++ map f bs ≡ map f (as ++ bs)
map++ f [] bs = refl
map++ f (x ∷ as) bs = cong (f x ∷_) (map++ f as bs)

rev-map-comm : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} → (f : A → B) → (as : List A)
  → map f (rev as) ≡ rev (map f as)
rev-map-comm f [] = refl
rev-map-comm f (x ∷ as) =
 sym (map++ f (rev as) _) ∙ cong (_++ [ f x ]) (rev-map-comm f as)

length++ : (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length++ [] ys = refl
length++ (x ∷ xs) ys = cong suc (length++ xs ys)

drop++ : (xs ys : List A) → drop (length xs) (xs ++ ys) ≡ ys
drop++ [] ys = refl
drop++ (x ∷ xs) ys = drop++ xs ys

take++ : (xs ys : List A) → take (length xs) (xs ++ ys) ≡ xs
take++ [] ys = refl
take++ (x ∷ xs) ys = cong (x ∷_) (take++ xs ys)

map-∘ : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
        (g : B → C) (f : A → B) (as : List A)
        → map g (map f as) ≡ map (λ x → g (f x)) as
map-∘ g f [] = refl
map-∘ g f (x ∷ as) = cong (_ ∷_) (map-∘ g f as) 

map-id : (as : List A) → map (λ x → x) as ≡ as
map-id [] = refl
map-id (x ∷ as) = cong (_ ∷_) (map-id as)

length≡0→≡[] : ∀ (xs : List A) → length xs ≡ 0 → xs ≡ []
length≡0→≡[] [] x = refl
length≡0→≡[] (x₁ ∷ xs) x = ⊥.rec (snotz x)

init : List A → List A 
init [] = []
init (x ∷ []) = []
init (x ∷ xs@(_ ∷ _)) = x ∷ init xs

tail : List A → List A
tail [] = []
tail (x ∷ xs) = xs

init-red-lem : ∀ (x : A) xs → ¬ (xs ≡ []) → (x ∷ init xs) ≡ (init (x ∷ xs))
init-red-lem x [] x₁ = ⊥.rec (x₁ refl)
init-red-lem x (x₂ ∷ xs) x₁ = refl

init∷ʳ : ∀ (x : A) xs → init (xs ∷ʳ x) ≡ xs
init∷ʳ x [] = refl
init∷ʳ x (x₁ ∷ []) = refl
init∷ʳ x (x₁ ∷ x₂ ∷ xs) = cong (x₁ ∷_) (init∷ʳ x (x₂ ∷ xs))

init++ : ∀ (x : A) xs ys → xs ++ init (x ∷ ys) ≡ init (xs ++ x ∷ ys) 
init++ x [] ys = refl
init++ x (x₁ ∷ []) ys = refl
init++ x (x₁ ∷ x₂ ∷ xs) ys =
 cong (x₁ ∷_) (init++ x (x₂ ∷ xs) ys)


module List₂ where
 open import Cubical.HITs.SetTruncation renaming
   (rec to rec₂ ; map to map₂ ; elim to elim₂ )


 ∥List∥₂→List∥∥₂ : ∥ List A ∥₂ → List ∥ A ∥₂ 
 ∥List∥₂→List∥∥₂ = rec₂ (isOfHLevelList 0 squash₂) (map ∣_∣₂)

 List∥∥₂→∥List∥₂ : List ∥ A ∥₂ → ∥ List A ∥₂ 
 List∥∥₂→∥List∥₂ [] = ∣ [] ∣₂
 List∥∥₂→∥List∥₂ (x ∷ xs) =
   rec2 squash₂ (λ x xs → ∣ x ∷ xs ∣₂) x (List∥∥₂→∥List∥₂ xs)




 -- Iso∥List∥₂List∥∥₂ : Iso (List ∥ A ∥₂) ∥ List A ∥₂ 
 -- Iso.fun Iso∥List∥₂List∥∥₂ = List∥∥₂→∥List∥₂
 -- Iso.inv Iso∥List∥₂List∥∥₂ = ∥List∥₂→List∥∥₂
 -- Iso.rightInv Iso∥List∥₂List∥∥₂ =
 --   elim₂ (isProp→isSet ∘ λ _ → squash₂ _ _)
 --     {!!}
 --  where
 --  w : (a : List A) → List∥∥₂→∥List∥₂ (map ∣_∣₂ a) ≡ ∣ a ∣₂
 --  w [] = refl
 --  w (x ∷ a) = {!!}
 -- Iso.leftInv Iso∥List∥₂List∥∥₂ [] = refl
 -- Iso.leftInv Iso∥List∥₂List∥∥₂ (x ∷ a) = {!!}

 -- comm-List-∥∥₂ : List {ℓ} ∘ ∥_∥₂ ≡ ∥_∥₂ ∘ List {ℓ}
 -- comm-List-∥∥₂ = funExt λ _ → isoToPath Iso∥List∥₂List∥∥₂
