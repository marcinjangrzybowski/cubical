{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.IntervalPrim where


import Agda.Primitive.Cubical

open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import Cubical.Data.Vec
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum 

open import Cubical.HITs.Interval
open import Cubical.HITs.PropositionalTruncation renaming (map to mapₚ)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1 hiding (_*_)
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
import Cubical.Foundations.Logic as Lo

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint


dichotomy≤ : ∀ b n → (n < b) ⊎ (Σ[ m ∈ ℕ ] n ≡ b + m)
dichotomy≤ b n
  = case n Cubical.Data.Nat.Order.≟ b return (λ _ → (n < b) ⊎ (Σ[ m ∈ ℕ ] n ≡ b + m)) of λ
  { (lt o) → inl o
  ; (eq p) → inr (0 , p ∙ sym (+-zero b))
  ; (gt (m , p)) → inr (suc m , sym p ∙ +-suc m b ∙ +-comm (suc m) b)
  }


replaceAt : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → ℕ → A → Vec A n → Vec A n  
replaceAt {n = zero} _ _ _ = []
replaceAt {n = suc n} zero a v = a ∷ (tail v)
replaceAt {n = suc n} (suc k) a v = head v ∷ replaceAt k a (tail v)

removeAt : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → ℕ → Vec A (suc n) → Vec A n  
removeAt zero v = (tail v)
removeAt {n = zero} (suc k) v = []
removeAt {n = suc n} (suc k) v = head v ∷ removeAt k (tail v)

repeat : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → A →  Vec A n
repeat {n = zero} a = []
repeat {n = suc n} a  = a ∷ (repeat a) 


padWithFirst : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → ∀ k → Vec A (suc n) → Vec A (k + suc n)  
padWithFirst k x = repeat {n = k} (head x) ++ x

padWithFirst< : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n}
                → ∀ m → (suc n ≤ m)
                → Vec A (suc n) → Vec A (m)  
padWithFirst< m sn<m v = subst (Vec _) (snd sn<m) (padWithFirst (fst sn<m) v)

dropFirst : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → ∀ k →  Vec A (k + suc n) → Vec A (suc n)
dropFirst zero x = x
dropFirst (suc k) x = dropFirst k (tail x) 

trimFin : ∀ {n} → ℕ → Fin (suc n) 
trimFin {zero} _ = fzero
trimFin {suc n} zero = fzero
trimFin {suc n} (suc x) = fsuc (trimFin x)

_─_ :  ℕ → ℕ → ℕ
x ─ zero = x
zero ─ suc x₁ = zero
suc x ─ suc x₁ = x ─ x₁

n─n≡0 : ∀ n → n ─ n ≡ zero
n─n≡0 zero = refl
n─n≡0 (suc n) = n─n≡0 n

─+ : ∀ m n → ∀ k → m ≡ n ─ (toℕ {suc n} k) → m + (toℕ k) ≡ n
─+ m n (zero , snd₁) x = +-comm m zero ∙ x
─+ zero zero (suc fst₁ , snd₁) x = ⊥-rec (¬-<-zero (pred-≤-pred snd₁))
─+ (suc m) zero (suc fst₁ , snd₁) x = ⊥-rec (snotz x)
─+ zero (suc n) (suc fst₁ , snd₁) x = cong suc (─+ zero n (fst₁ , (pred-≤-pred snd₁)) x)
─+ (suc m) (suc n) (suc fst₁ , snd₁) x =
 cong suc (+-suc m fst₁) ∙ cong suc (─+ (suc m) n (fst₁ , (pred-≤-pred snd₁)) x)



-- this version of Interval will let us handle both ends in single case
-- the convention of i0 ↔ false , i1 ↔ true is used everywhere in this module






ifω : Typeω → Typeω → Bool → Typeω 
ifω x y false = x
ifω x y true = y

⊥-recω : {A : Typeω} → ⊥ → A
⊥-recω ()

×ω : Typeω → Typeω → Typeω 
×ω x y = ∀ b → ifω x y b

Iⁿ→ :  ∀ {ℓ} → ∀ (A  : Type ℓ) → ℕ → Typeω
Iⁿ→ A zero = I → A
Iⁿ→ A (suc x) = I → Iⁿ→ A x

C→ :  ∀ {ℓ} → ∀ (A  : Type ℓ) → ℕ → Typeω
C→ A zero = Partial i1 A -- lifting A from Type ℓ to Typeω
C→ A (suc x) = I → C→ A x



C→I : ℕ → Typeω
C→I zero = I
C→I (suc x) = I → C→I x

C→-dim-subst : ∀ (n₁ n₂ : ℕ) → n₁ ≡ n₂ → C→I n₁ → C→I n₂ 
C→-dim-subst zero zero p x₁ = x₁
C→-dim-subst zero (suc n₂) p x₁ = ⊥-recω (znots p)
C→-dim-subst (suc n₁) zero p x₁ =  ⊥-recω (snotz p)
C→-dim-subst (suc n₁) (suc n₂) p x₁ i = C→-dim-subst n₁ n₂ (cong predℕ p) (x₁ i)

C→z : ∀ {ℓ} → ∀ {A  : Type ℓ} → C→ A 0 → A
C→z x = x 1=1

data Interval' : Type₀ where
   end : Bool → Interval'
   inside : end false ≡ end true 

Bool→I : Bool → I
Bool→I false = i0
Bool→I true = i1

isOne-∨B : ∀ b → IsOne (Bool→I b ∨ ~ Bool→I b)
isOne-∨B false = 1=1
isOne-∨B true = 1=1

bool-elimω : ∀ {A : Typeω} → Bool → A → A → A
bool-elimω false f _ = f
bool-elimω true _ t = t

negIf : Bool → I → I
negIf b i = bool-elimω b (~ i) i 


NCube : ℕ -> Type₀
NCube = Vec Interval' 



isContr-Inrerval' : isContr Interval'
fst isContr-Inrerval' = end false
snd isContr-Inrerval' (end false) = refl
snd isContr-Inrerval' (end true) = inside
snd isContr-Inrerval' (inside i) j = inside (i ∧ j) 

isProp-Inrerval' = (isContr→isProp isContr-Inrerval')

endT= : ∀ i' → end true ≡ i'
endT= (end false) = sym inside
endT= (end true) = refl
endT= (inside i) i₁ = inside (i ∨ ~ i₁)

endF= : ∀ i' → i' ≡ end false 
endF= (end false) = refl
endF= (end true) = sym inside
endF= (inside i) i₁ = inside (i ∧ ~ i₁)

----------
----------

corner0 : ∀ {n} → NCube n
corner0 {zero} = []
corner0 {suc n} =  end false ∷ corner0

corner1 : ∀ {n} → NCube n
corner1 {zero} = []
corner1 {suc n} =  end true ∷ corner1

corner0-≡ : ∀ {n} → ∀ (a : NCube n) → _≡_ {A = NCube n} (corner0) a  
corner0-≡ {zero} [] = refl
corner0-≡ {suc n} (end false ∷ x₁) i = end false ∷ corner0-≡ x₁ i
corner0-≡ {suc n} (end true ∷ x₁) i = inside i ∷ corner0-≡ x₁ i
corner0-≡ {suc n} (inside i ∷ x₁) j = inside (i ∧ j) ∷ corner0-≡ x₁ j

≡-corner1 : ∀ {n} → ∀ (a : NCube n) → _≡_ {A = NCube n}  a (corner1)  
≡-corner1 {zero} [] = refl
≡-corner1 {suc n} (end true ∷ x₁) i = end true ∷ ≡-corner1 x₁ i
≡-corner1 {suc n} (end false ∷ x₁) i = inside i ∷ ≡-corner1 x₁ i
≡-corner1 {suc n} (inside i ∷ x₁) j = inside (i ∨ j) ∷ ≡-corner1 x₁ j

corner0-≡-corner1 : ∀ {n} → _≡_ {A = NCube n}  corner0 corner1  
corner0-≡-corner1 {zero} = refl
corner0-≡-corner1 {suc n} i = (inside i) ∷ corner0-≡-corner1 i


isPropCube : ∀ {n} → isProp (NCube n)
isPropCube {zero} [] [] i = []
isPropCube {suc n} (x ∷ x₁) (x₂ ∷ x₃) i =
    (isContr→isProp isContr-Inrerval') x x₂ i ∷ (isPropCube x₁ x₃ i)




--------------
--------------

Interval'-≡-∥Bool∥  : Interval' → Interval' ≡ ∥ Bool ∥
Interval'-≡-∥Bool∥ i' i = fst (Lo.⇔toPath {P = Interval' , isProp-Inrerval'}
                                          {Q = Lo.∥ Bool ∥ₚ } f g i)
  where
    f : _
    f (end x) = ∣ x ∣ 
    f (inside i) = squash  ∣ false ∣  ∣ true ∣  i

    g : _
    g x = i'



lenNC : ∀ n → NCube n → Vec S¹ n 
lenNC zero [] = []
lenNC (suc n) (end x ∷ x₁) = base ∷ (lenNC _ x₁)
lenNC (suc n) (inside i ∷ x₁) = loop i ∷ (lenNC _ x₁) 

Cu→I :  ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ n → (NCube (suc n) → A) → Iⁿ→ A n
Cu→I zero x x₁ = x (inside x₁ ∷ [])
Cu→I (suc n) x i = Cu→I n (x ∘ (inside i ∷_))
 
Cu←I :  ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ n → Iⁿ→ A n → (NCube (suc n) → A)
Cu←I zero x (end x₁ ∷ x₂) = x (Bool→I x₁)
Cu←I zero x (inside i ∷ x₂) = x i
Cu←I (suc n) x (end x₁ ∷ x₂) = Cu←I n (x (Bool→I x₁)) x₂
Cu←I (suc n) x (inside i ∷ x₂) = Cu←I n (x i) x₂


_∘V_ : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → (Iⁿ→ A n) → (NCube (suc n) → NCube (suc n)) → (Iⁿ→ A n) 
x ∘V x₁ =  Cu→I _ ((Cu←I _ x) ∘ x₁) 


Iapp : ∀ {ℓ} → {A : Type ℓ}
         → (I → A) → Interval' → A
Iapp x (end x₁) = x (Bool→I x₁) 
Iapp x (inside i) = x i

Iapp= : ∀ {ℓ} → {A : Type ℓ} → {a₀ a₁ : A}
         → a₀ ≡ a₁ → Interval' → A
Iapp= {a₀ = a₀} {a₁} x (end x₁) = caseBool a₁ a₀ x₁ 
Iapp= x (inside i) = x i

C→-app : ∀ {ℓ} → ∀ {n} → ∀ {A  : Type ℓ} → C→ A n → NCube n → A
C→-app {n = zero} x _ = C→z x
C→-app {n = suc n} x v = Iapp (λ i → C→-app (x i) (tail v)) (head v)

C→elim : ∀ {ℓ} → ∀ {n} → ∀ {A  : Type ℓ} → (NCube n → A) → C→ A n 
C→elim {n = zero} x _ = x []
C→elim {n = suc n} x i = C→elim (x ∘ (inside i ∷_))



C→map : ∀ {ℓ ℓ'} → ∀ {n} → ∀ {A  : Type ℓ} → ∀ {B  : Type ℓ'} → (A → B) → C→ A n → C→ B n
C→map {n = zero} f x _ = f (x 1=1)
C→map {n = suc n} f x i = C→map {n = n} f (x i)

-- C→NCube : ∀ n → C→ (NCube n) n
-- C→NCube zero _ = []
-- C→NCube (suc n) i = {!(C→NCube n)!}
-- -- C→NCube (suc (suc n)) i j = {!(C→NCube (suc n)) j  !}


IappP : ∀ {ℓ} → {A : I → Type ℓ} → {a₀ : A i0} → {a₁ : A i1}
      → PathP (λ i → A i) a₀ a₁ 
      → ∀ i' →  Iapp (λ i → A i) i'
IappP {a₀ = a₀} x (end false) = a₀
IappP {a₁ = a₁} x (end true) = a₁
IappP x (inside i) = x i

self∨ : I → I
self∨ x = x ∨ (~ x)

self∨' : Interval' → Interval'
self∨' (end x) = end true
self∨' (inside i) = inside (i ∨ ~ i)


_∨'_ : Interval' → Interval' → Interval'
end false ∨' end false = end false
end false ∨' end true = end true
end true ∨' _ = end true 
end false ∨' inside i = inside i
inside i ∨' end false = inside i
inside i ∨' end true = end true
_∨'_ (inside i) (inside i₁) = inside (i ∨ i₁)

_∧'_ : Interval' → Interval' → Interval'
end false ∧' end false = end false
end false ∧' end true = end false
end true ∧' end false = end false
end true ∧' end true = end true
end false ∧' inside i = end false
end true ∧' inside i = inside i
inside i ∧' end false = end false
inside i ∧' end true = inside i
_∧'_ (inside i) (inside i₁) = inside (i ∧ i₁)

⋁ : ∀ {n} → NCube n → Interval'
⋁ {zero} x = end false
⋁ {suc n} (z ∷ x₁) = z ∨' ⋁ x₁

∼' : Interval' → Interval'
∼' (end x) = end (not x)
∼' (inside i) = inside (~ i)

∼'' : ∀ {n} → NCube n → NCube n
∼'' {zero} [] = []
∼'' {suc n} (x ∷ x₁) = ∼' x ∷  (∼'' x₁)

brd : ∀ {n} → NCube n → Interval'
brd {zero} x = end false
brd {suc n} (end x ∷ x₁) = end true
brd {suc n} (inside i ∷ x₁) = (inside (self∨ i)) ∨' (brd x₁)

-- hcomp' : ∀ {ℓ} → {A : Type ℓ} → (i' : Interval') → (Interval' → A) → A 
-- hcomp' (end false) x = hcomp (λ i → empty) (x (end false))
-- hcomp' (end true) x = x (end true)
-- hcomp' (inside i) x = hcomp (λ j → λ {(i = i1) → x (inside j) }) (x (end false))

-- hfill' : ∀ {ℓ} → {A : Type ℓ} → (i' : Interval') → (x : Interval' → A) → x (end false) ≡ hcomp' i' x 
-- hfill' (end false) x j = hfill {φ = i0} (λ j → λ ()) (inS (x (end false))) j
-- hfill' (end true) x j = x (inside j)
-- hfill' (inside i) x j = hfill (λ j → λ {(i = i1) → x (inside j) }) (inS (x (end false))) j

-- hfill'-const :  ∀ {ℓ} → {A : Type ℓ} → (a : A)
--                 → ∀ n → (x : Vec Interval' n)
--                 → a ≡ (hcomp' (brd x) (λ i' → a))
-- hfill'-const a n x j = hfill' (brd x) (const a) j

∨-map : ∀ {n} → NCube n → NCube n → NCube n
∨-map [] [] = []
∨-map (x ∷ x₁) (x₂ ∷ x₃) = x ∨' x₂ ∷ ∨-map x₁ x₃

∧-map : ∀ {n} → NCube n → NCube n → NCube n
∧-map [] [] = []
∧-map (x ∷ x₁) (x₂ ∷ x₃) = x ∧' x₂ ∷ ∧-map x₁ x₃



C-substAll : ∀ {ℓ} → {A : Type ℓ} → ∀ n → 
       (Iⁿ→ A n) → I → A
C-substAll zero x = x
C-substAll (suc n) x i = C-substAll n (x i) i

C-substLast : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → C→I n → (C→ A n) → (C→ A n) 
C-substLast {n = zero} x e = e
C-substLast {n = suc zero} x e i = e (x i)
C-substLast {n = suc (suc n)} x e i = C-substLast {n = (suc n)} (x i) (e i)

-- C-subst : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ℕ → C→I (suc n) → (C→ A (suc n)) → (C→ A n) 
-- C-subst {n = n} k x e = {!!}

C-const : ∀ {ℓ} → {A : Type ℓ} → ∀ n → 
              A → (C→ A n)
C-const zero a _ = a
C-const (suc n) a _ = C-const n a



-- SubstC→I : ℕ → ℕ → Typeω
-- SubstC→I n m = (C→I n) → (C→I m)

C∨ : ∀ n → (C→I n)
C∨ zero = i0
C∨ (suc zero) i = i
C∨ (suc (suc zero)) = _∨_
C∨ (suc (suc (suc n))) i j = C∨ _ (i ∨ j)


C∧ : ∀ n → (C→I n)
C∧ zero = i1
C∧ (suc zero) i = i
C∧ (suc (suc zero)) = _∧_
C∧ (suc (suc (suc n))) i j = C∧ _ (i ∧ j)


-- -- I→Imb : Maybe Bool → I → I
-- -- I→Imb nothing i = i
-- -- I→Imb (just x) _ = Bool→I x

-- I→Imb' : Maybe Bool → I → I
-- I→Imb' nothing _ = i0
-- I→Imb' (just false) i = ~ i
-- I→Imb' (just true) i = i

-- -- Iface : ∀ n → 
-- --        (Vec (Maybe Bool) (suc n)) → (I^→I^ (n) (n))
-- -- Iface zero x = I→Imb (head x)
-- -- Iface (suc n) x x₁ i = Iface n (tail x) (x₁ (I→Imb (head x) i))

-- Imap : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → (A → (I → I)) → 
--           (Vec (A) (suc n)) → (I^→I^ (n) (n))
-- Imap {n = zero} f v x i =  x ((f (head v)) i) 
-- Imap {n = suc n} f v x i = Imap f (tail v) (x ((f (head v)) i))

-- ImapS : ∀ {n} → ((I → I)) → (I^→I^ (n) (n))
-- ImapS {zero} f x₁ i = f (x₁ i)
-- ImapS {suc n} f x₁ i = ImapS f (x₁ i)

-- IFaceE : ∀ {n} → 
--          (Vec (Maybe Bool) (suc n)) → (I^→I (n))
-- IFaceE v =  Imap I→Imb' v (I^∨ _)



C→A-subst1 : ∀ {ℓ} → {A : Type ℓ} → ∀ n → (I → A) → (C→I (n)) → C→ A n
C→A-subst1 zero f e _ = f e
C→A-subst1 (suc n) f e i = C→A-subst1 n f (e i)

hfillRefl :  ∀ {ℓ} → {A : Type ℓ} → (a : A) → I → ∀ n → (C→I n) → C→ A n
hfillRefl a i n = C→A-subst1 n (λ φ → hfill {φ = φ} (λ i₁ _ → a) (inS a) i)

hfillRefl2 :  ∀ {ℓ} → {A : Type ℓ} → (a : A) → I → ∀ n → ∀ a1 → (z : a ≡ a1) → (C→I n) → C→ A n
hfillRefl2 a0 i n a1 a1=a0 = C→A-subst1 n (λ φ → hfill {φ = φ} (λ i₁ _ → a1=a0 i₁) (inS a0) i)



C→Cu-app : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → C→ (Vec Interval' n → A) n → C→ A n 
C→Cu-app {n = zero} x x₁ = x 1=1 []
C→Cu-app {n = suc n} x i = C→Cu-app {n = n} (C→map {n = n} (_∘ (inside i ∷_)) (x i))


IsOneⁿ-expr : ∀ n → C→I n → Typeω
IsOneⁿ-expr zero x = IsOne x
IsOneⁿ-expr (suc n) x = ∀ i → IsOneⁿ-expr n (x i)

-- C→I-eval : ∀ n → C→I n → NCube (suc n) → I
-- C→I-eval zero x x₁ = x
-- C→I-eval (suc n) x (x₁ ∷ x₂) = {!x₁!}


_∨ⁿ_ : ∀ {n} → C→I n → C→I n → C→I n
_∨ⁿ_ {zero} x x₁ = x ∨ x₁
_∨ⁿ_ {suc n} x x₁ i = x i ∨ⁿ x₁ i 

_∧ⁿ_ : ∀ {n} → C→I n → C→I n → C→I n
_∧ⁿ_ {zero} x x₁ = x ∧ x₁
_∧ⁿ_ {suc n} x x₁ i = x i ∧ⁿ x₁ i

~ⁿ : ∀ {n} → C→I n → C→I n
~ⁿ {zero} x = ~ x 
~ⁿ {suc n} x i = ~ⁿ (x i)


⊂I : ∀ {n} → C→I n → C→I n → Typeω
⊂I {zero} x x₁ = IsOne x → IsOne x₁ 
⊂I {suc n} x x₁ = ∀ (i : I) → ⊂I (x i) (x₁ i)

≡I :  ∀ {n} → C→I n → C→I n → Typeω
≡I x x₁ = ×ω (⊂I x x₁) (⊂I x₁ x) 

⊂I-trans : ∀ {n} → ∀ {a b c : C→I n} → ⊂I a b → ⊂I b c → ⊂I a c
⊂I-trans {zero} x x₁ z = x₁ (x z)
⊂I-trans {suc n} x x₁ i = ⊂I-trans (x i) (x₁ i)

[_]Iexpr : ∀ {n} → I → C→I n 
[_]Iexpr {zero} x = x
[_]Iexpr {suc n} x i = [_]Iexpr x

i0ⁿ : ∀ {n} → C→I n
i0ⁿ {n} = ([_]Iexpr i0)

i1ⁿ : ∀ {n} → C→I n
i1ⁿ {n} = ([_]Iexpr i1)

boundaryExpr : ∀ n → C→I n
boundaryExpr zero = i0
boundaryExpr (suc zero) x = (x ∨ ~ x)
boundaryExpr (suc (suc n)) x = (([_]Iexpr (x)) ∨ⁿ ([_]Iexpr (~ x))) ∨ⁿ (boundaryExpr (suc n))

liftExpr : ∀ {n} → ∀ k → C→I n → C→I (k + n) 
liftExpr {n} zero x = x
liftExpr {n} (suc k) x _ = liftExpr k x

liftExpr⊂I : ∀ {n} → ∀ k → (x y : C→I n)
             → ⊂I x y → ⊂I (liftExpr k x) (liftExpr k y)   
liftExpr⊂I zero x y x₁ = x₁
liftExpr⊂I {n} (suc k) x y x₁ i = liftExpr⊂I k x y x₁

⋁expr : ∀ n → C→I n
⋁expr zero = i0
⋁expr (suc n) x =  ([_]Iexpr x) ∨ⁿ (⋁expr n)


skelExpr : ∀ n → Fin (suc (suc n)) → C→I n
skelExpr zero _ = i0
skelExpr (suc n) (_ , zero , _) = i1ⁿ
skelExpr (suc n) (zero , _ , _) = i0ⁿ
skelExpr (suc n) (suc fst₁ , suc fst₂ , snd₁) =
     (
     (λ i → ([_]Iexpr i) ∧ⁿ skelExpr n ((suc fst₁) , fst₂ , cong predℕ snd₁ ))
     ∨ⁿ
     (λ i → ([_]Iexpr (~ i)) ∧ⁿ skelExpr n ((suc fst₁) , fst₂ , cong predℕ snd₁ ))
     )
      ∨ⁿ
      (λ _ → skelExpr n (fst₁ , (suc fst₂) , (sym (+-suc _ _)) ∙ cong predℕ snd₁))

endExpr : ∀ {n} → Bool → C→I n
endExpr {zero} b = bool-elimω b i0 i1
endExpr {suc n} b i = [_]Iexpr (bool-elimω b (~ i) i)


faceExpr : ∀ {n} → Bool → ℕ → C→I n
faceExpr b zero = endExpr b
faceExpr {zero} b (suc k) = bool-elimω b i0 i1
faceExpr {suc n} b (suc k) i = faceExpr {n} b (k)



i1-max : ∀ n → (x : C→I n) →  ⊂I x i1ⁿ
i1-max zero x _ = 1=1
i1-max (suc n) x i = i1-max n (x i)

i0-min : ∀ n → (x : C→I n) →  ⊂I i0ⁿ x
i0-min zero x () 
i0-min (suc n) x i = i0-min n (x i)

⊂-∨1 : ∀ {n} → (x y : C→I n) → ⊂I x (x ∨ⁿ y)
⊂-∨1 {zero} = IsOne1
⊂-∨1 {suc n} x y i = ⊂-∨1 (x i) (y i)

⊂-∨2 : ∀ {n} → (x y : C→I n) → ⊂I y (x ∨ⁿ y)
⊂-∨2 {zero} = IsOne2
⊂-∨2 {suc n} x y i = ⊂-∨2 (x i) (y i)



⊂-∨~ : ∀ {n} → (b : Bool) → let x = [_]Iexpr {n} (Bool→I b) in ⊂I i1ⁿ (x ∨ⁿ (~ⁿ x))
⊂-∨~ {zero} false _ = 1=1
⊂-∨~ {zero} true _ = 1=1
⊂-∨~ {suc n} b _ = ⊂-∨~ {n} b

⊂-∨~' : ∀ {n} → (b : Bool) → ⊂I i1ⁿ (([_]Iexpr {n} (Bool→I b)) ∨ⁿ ([_]Iexpr {n} (~ (Bool→I b))))
⊂-∨~' {zero} false _ = 1=1
⊂-∨~' {zero} true _ = 1=1
⊂-∨~' {suc n} b _ = ⊂-∨~' {n} b

0∨ⁿ : ∀ {n} → (x : C→I n) →  ⊂I (i0ⁿ ∨ⁿ x) x  
0∨ⁿ {zero} x y = y
0∨ⁿ {suc n} x i = 0∨ⁿ (x i)

∧-comm : ∀ {n} → (x y : C→I n) → ⊂I (x ∧ⁿ y) (y ∧ⁿ x)
∧-comm {zero} x y x₁ = x₁
∧-comm {suc n} x y i = ∧-comm (x i) (y i)


boundaryExpr-cyl : ∀ n → ∀ i → ⊂I (boundaryExpr n) (boundaryExpr (suc n) i)
boundaryExpr-cyl zero i ()
boundaryExpr-cyl (suc zero) i i₁ = IsOne2 (i ∨ ~ i) (boundaryExpr 1 i₁)
boundaryExpr-cyl (suc (suc n)) i i₁ i₂ = ⊂-∨2 _ _

face-⊂-boundaryExpr : ∀ n → ∀ b → (k : Fin n) → ⊂I (faceExpr b (fst k) ) (boundaryExpr n)
face-⊂-boundaryExpr zero _ k _ = ⊥-recω (¬Fin0 k)
face-⊂-boundaryExpr (suc zero) false (zero , _) i = IsOne2 i (~ i)
face-⊂-boundaryExpr (suc zero) true (zero , _) i = IsOne1 i (~ i)
face-⊂-boundaryExpr (suc zero) b (suc k , snd₁) = ⊥-recω (¬-<-zero (pred-≤-pred snd₁))
face-⊂-boundaryExpr (suc (suc n)) false (zero , snd₁) i j = ⊂I-trans (⊂-∨2 _ _) (⊂-∨1 _ _)
face-⊂-boundaryExpr (suc (suc n)) true (zero , snd₁) i j = ⊂I-trans (⊂-∨1 _ _) (⊂-∨1 _ _)
face-⊂-boundaryExpr (suc (suc n)) b (suc fst₁ , snd₁) i j =
  ⊂I-trans (face-⊂-boundaryExpr (suc n) b (fst₁ , pred-≤-pred snd₁) j) ((⊂-∨2 _ _))


1⊂lid : ∀ n → ∀ b → ⊂I i1ⁿ (boundaryExpr (suc n) (Bool→I b))
1⊂lid zero b = ⊂-∨~ {0} b
1⊂lid (suc n) b i = ⊂I-trans (⊂-∨~' {suc n} b i) (⊂-∨1 _ _)

-- 

lid-⊂-boundaryExpr : ∀ n → ∀ b →  ⊂I (boundaryExpr n) (boundaryExpr (suc n) (Bool→I b)  )
lid-⊂-boundaryExpr n b = ⊂I-trans (i1-max _ _) (1⊂lid n b)


-- those to wont work, this relation treats expresion as interval expresions
-- this is provable for ⊂'I , defined bellow, becouse is treating expressions as face expressions
-- ⊂-~ : ∀ {n} → (x : C→I n) → ⊂I (x ∧ⁿ (~ⁿ x)) ([_]Iexpr n i0)
-- ⊂-~ {zero} x x₁ = {!!}
-- ⊂-~ {suc n} = {!!}

-- ⊂-∧1 : ∀ {n} → (x y : C→I n) → ⊂I (x ∧ⁿ y) x
-- ⊂-∧1 {zero} x y x₁ = {!!}
-- ⊂-∧1 {suc n} x y = {!!}


-- IsOneⁿ : {!!}
-- IsOneⁿ = {!!}

-- IsOneⁿ-test1 : {!!}
-- IsOneⁿ-test1 = {!IsOneⁿ 3!}

Partialⁿ : ∀ {ℓ} → (A : Type ℓ) → ∀ n → C→I n → Typeω
Partialⁿ A zero x = Partial x A
Partialⁿ A (suc n) x = ∀ i → Partialⁿ A n (x i)


PartialPⁿ : ∀ {ℓ} →  ∀ n → (e : C→I n) → (A : Partialⁿ (Type ℓ) n e ) → Typeω
PartialPⁿ zero e A = PartialP e A  
PartialPⁿ (suc n) e A = ∀ i → PartialPⁿ n (e i) (A i)


Partial∨ :  ∀ {ℓ} → {A : Type ℓ} → (i j : I)
           → {xy : Partial (i ∧ j) A} 
           → ( (i=1 : (IsOne i)) → (Sub A j (λ { (j = i1) → xy i=1  })))
           → ( (j=1 : (IsOne j)) → (Sub A i (λ { (i = i1) → xy j=1  })))
           → Partial (i ∨ j) A
Partial∨ i j x y = (λ { (i = i1) → outS (x 1=1) ; (j = i1) → outS (y 1=1)})



⊂'I : ∀ {n} → C→I n → C→I n → Typeω
⊂'I {n} x x₁ = ∀ {ℓ} → ∀ {A : Type ℓ} → Partialⁿ A n x₁ → Partialⁿ A n x



≡'I :  ∀ {n} → C→I n → C→I n → Typeω
≡'I x x₁ = ×ω (⊂'I x x₁) (⊂'I x₁ x) 

⊂'-~ : ∀ {n} → (x : C→I n) → ⊂'I (x ∧ⁿ (~ⁿ x)) ([_]Iexpr {n} i0)
⊂'-~ {suc n} x {ℓ} {A} x₁ i = ⊂'-~ (x i) (x₁ i)

⊂'-∧ : ∀ {n} → (x y : C→I n) → ⊂'I (x ∧ⁿ y) x
⊂'-∧ {zero} x y {ℓ} {A} x₂ = λ { (x = i1)(y = i1) → x₂ 1=1 }
⊂'-∧ {suc n} x y {ℓ} {A} x₂ i = ⊂'-∧ {n} (x i) (y i) (x₂ i)

⊂'-∧2 : ∀ {n} → (x y : C→I n) → ⊂'I (x ∧ⁿ y) y
⊂'-∧2 {zero} x y {ℓ} {A} x₂ = λ { (x = i1)(y = i1) → x₂ 1=1 }
⊂'-∧2 {suc n} x y {ℓ} {A} x₂ i = ⊂'-∧2 {n} (x i) (y i) (x₂ i)

Partialⁿ-lift-i0 :  ∀ {ℓ} → {A : Type ℓ} → ∀ n
                   → Partialⁿ A _ (liftExpr n i0)
Partialⁿ-lift-i0 zero ()
Partialⁿ-lift-i0 (suc n) i = Partialⁿ-lift-i0 n



⊂→⊂' : ∀ {n} → (x y : C→I n) → ⊂I x y → ⊂'I x y
⊂→⊂' {zero} x y x₁ x₂ x₃ = x₂ (x₁ x₃)
⊂→⊂' {suc n} x y x₁ x₂ i = ⊂→⊂' {n} (x i) (y i) (x₁ i) (x₂ i)


Partialⁿ-const :  ∀ {ℓ} → (A : Type ℓ) → ∀ n → (e : C→I n) → C→ A n → Partialⁿ A n e
Partialⁿ-const A zero e a _ = a 1=1
Partialⁿ-const A (suc n) e a i = Partialⁿ-const A n _ (a i)


-- Partialⁿ-const⊂:  ∀ {ℓ} → (A : Type ℓ) → ∀ n → (e : C→I n) → C→ A n → Partialⁿ A n e
-- Partialⁿ-const⊂ A zero e a _ = ?
-- Partialⁿ-const⊂ A (suc n) e a i = ?



Partialⁿ-map :  ∀ {ℓa ℓb} → {A : Type ℓa} → {B : Type ℓb}
                → ∀ n → {e : C→I n}
                → (A → B)
                → Partialⁿ A n e
                → Partialⁿ B n e
Partialⁿ-map zero f x e=1 = f (x e=1)
Partialⁿ-map (suc n) f x i = Partialⁿ-map n f (x i)

PartialPⁿ-mapTo :  ∀ {ℓa ℓb}
                → ∀ {n} → {e : C→I n}
                → {A : (Type ℓa)} → {B : A → Type ℓb}
                → (f : ∀ (x : A) → B x)
                → (a : Partialⁿ A n e)
                → PartialPⁿ n e
                    (Partialⁿ-map {A = A} {B = Type ℓb} n {e = e} B a)
PartialPⁿ-mapTo {n = zero} f a x =  f (a x) 
PartialPⁿ-mapTo {n = suc n} f a i = PartialPⁿ-mapTo {n = n} f (a i)

PartialPⁿ-mapFrom :  ∀ {ℓa ℓb}
                → ∀ n → {e : C→I n}
                → {A : Partialⁿ (Type ℓa) n e}
                → {B : (Type ℓb)}                
                → (f : PartialPⁿ n e (Partialⁿ-map n (λ x → x → B) A))
                → (a : PartialPⁿ n e A)
                → Partialⁿ B n e
PartialPⁿ-mapFrom zero f a x = (f x) (a x)
PartialPⁿ-mapFrom (suc n) f a i = PartialPⁿ-mapFrom n (f i) (a i)


-- PartialPⁿ-map :  ∀ {ℓa ℓb}
--                 → ∀ {n} → {e : C→I n}
--                 → {A : Partialⁿ (Type ℓa) n e}
--                 → {B : Partialⁿ (Type ℓb) n e}
--                 → ({!!})
--                 → PartialPⁿ n e A
--                 → PartialPⁿ n e
--                     (Partialⁿ-map {A = {!A!}} {B = Type ℓb} {n = n} {e = e} {!!} {!!})
-- PartialPⁿ-map = {!!}


-- PartialPⁿ-map :  ∀ {ℓa ℓb} → {A : Type ℓa} → {B : Type ℓb}
--                 → ∀ {n} → {e : C→I n}
--                 → (A → B)
--                 → Partialⁿ A n e
--                 → Partialⁿ B n e
-- PartialPⁿ-map = {!!}

Partialⁿ-map2 :  ∀ {ℓa ℓa' ℓb} → {A : Type ℓa} → {A' : Type ℓa'} → {B : Type ℓb}
                → ∀ {n} → {e : C→I n}
                → (A → A' → B)
                → Partialⁿ A n e
                → Partialⁿ A' n e
                → Partialⁿ B n e
Partialⁿ-map2 {n = zero} f x x' e=1 = f (x e=1) (x' e=1)
Partialⁿ-map2 {n = suc n} f x x' i = Partialⁿ-map2 {n = n} f (x i) (x' i)  

Partialⁿ-app :  ∀ {ℓa ℓb} → {A : Type ℓa} → {B : Type ℓb}
                → ∀ {n} → {e : C→I n}
                → Partialⁿ (A → B) n e
                → Partialⁿ A n e
                → Partialⁿ B n e
Partialⁿ-app {n = zero} f x e=1 = f (e=1) (x e=1)
Partialⁿ-app {n = suc n} f x i = Partialⁿ-app {n = n} (f i) (x i)

-- Partialⁿ' : ∀ {ℓ} → (A : Type ℓ) → ∀ n → C→I n → Typeω
-- Partialⁿ' A n x = {!!} → C→ A n

-- Partialⁿ→' : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {x} → Partialⁿ A n x → Partialⁿ' A n x   
-- Partialⁿ→' {n = zero} x x₁ = x x₁
-- Partialⁿ→' {n = suc n} {x₂} x x₁ = Partialⁿ→' {n = n} {!!} {!!}

Partialⁿ-IsOne : ∀ {ℓ} → (A : Type ℓ) → ∀ n → (e : C→I n) →
                Partialⁿ A n e → IsOneⁿ-expr n e → C→ A n
Partialⁿ-IsOne A zero e x x₁ _ = x x₁
Partialⁿ-IsOne A (suc n) e x x₁ i = Partialⁿ-IsOne A n (e i) (x i) (x₁ i)

Partialⁿ-IsOne⊂ : ∀ {ℓ} → (A : Type ℓ) → ∀ n → (e : C→I n) →
                Partialⁿ A n e → ⊂I i1ⁿ e → C→ A n
Partialⁿ-IsOne⊂ A zero e x x₁ e=1 = x (x₁ e=1)
Partialⁿ-IsOne⊂ A (suc n) e x x₁ i = Partialⁿ-IsOne⊂ A n (e i) (x i) (x₁ i)


-- Partialⁿ-test→ : {!!}
-- Partialⁿ-test→  = {!y!}

-- Partialⁿ-test : {!!}
-- Partialⁿ-test x y = {!!}

-- Partialⁿ-test1 : {!!}
-- Partialⁿ-test1 = {!Partialⁿ Bool 3!}

Subⁿ : ∀ {ℓ} → (A : Type ℓ) → ∀ n → (e :  C→I n) → Partialⁿ A n e → Typeω
Subⁿ A zero e x = Sub A e x
Subⁿ A (suc n) e x = ∀ i → Subⁿ A n (e i) (x i)

Subⁿ-map :  ∀ {ℓ ℓb} → {A : Type ℓ}→ {B : Type ℓb} → ∀ n → {e :  C→I n} → {pa : Partialⁿ A n e}
             → (f : A → B)
             → Subⁿ A n e pa
             → Subⁿ B n e (Partialⁿ-map n f pa)
 
Subⁿ-map zero f x = inS (f (outS x))
Subⁿ-map (suc n) f x i = Subⁿ-map (n) f (x i)


inSⁿ : {ℓ : Level} {A : Set ℓ} → ∀ n → ∀ e → (x : C→ A n) → Subⁿ A n e ((Partialⁿ-const A n e x)) 
inSⁿ zero e x = inS (x 1=1)
inSⁿ (suc n) e x i = inSⁿ n (e i) (x i)

inSⁿ' : {ℓ : Level} {A : Set ℓ} → ∀ n → ∀ e → (x : Partialⁿ A n e ) → ⊂I i1ⁿ e  → Subⁿ A n e x 
inSⁿ' {ℓ} {A} zero e x x₁ = inS (x (x₁ 1=1))
inSⁿ' {ℓ} {A} (suc n) e x x₁ i = inSⁿ' n (e i) (x i) (x₁ i)

outSⁿ : {ℓ : Level} {A : Set ℓ} → ∀ n → ∀ e → ∀ x → Subⁿ A n e x →  C→ A n         
outSⁿ zero e x x₁ _ = outS x₁
outSⁿ (suc n) e x x₁ i = outSⁿ n (e i) (x i) (x₁ i)


Partialⁿ-Sub : ∀ {ℓ} → (A : Type ℓ) → ∀ n
               → (i : C→I n) → (j : C→I n)
               → Partialⁿ A n (i ∧ⁿ j) → Typeω
Partialⁿ-Sub A zero ei ej x = .(e=1 : (IsOne ei)) → Sub A ej (λ { (ej = i1) → x e=1 })
Partialⁿ-Sub A (suc n) ei ej x = ∀ i → Partialⁿ-Sub A n (ei i) (ej i) (x i)


-- PartialPⁿ-Sub-help : ∀ {ℓ} {i = ei} {j = ej} (A : Partialⁿ (Set ℓ) zero ei)
--                       (x : PartialPⁿ zero (ei ∧ⁿ ej) (⊂'-∧ ei ej A)) .(e=1 : IsOne ei) →
--                        Partial ej (A e=1)
-- PartialPⁿ-Sub-help {i = ei} {j = ej} A x e=1 x₁ = {!!}

-- PartialPⁿ-Sub : ∀ {ℓ} → ∀ n → (i : C→I n) → (j : C→I n)
--                  → (A : Partialⁿ (Set ℓ) n i)
--                  → PartialPⁿ n (i ∧ⁿ j) (⊂'-∧ i j A ) → Typeω
-- PartialPⁿ-Sub zero ei ej A x = .(e=1 : (IsOne ei)) → Sub (A e=1) ej λ {(ej = i1) → {!x!} } 
-- PartialPⁿ-Sub (suc n) i j A x = {!!}

Partialⁿ-Sub' : ∀ {ℓ} → (A : Type ℓ) → ∀ n → (i j : C→I n) → Partialⁿ A n j → Typeω
Partialⁿ-Sub' A zero i j x = (.(IsOne i)) → Sub A j x
Partialⁿ-Sub' A (suc n) ei ej x = ∀ i → Partialⁿ-Sub' A n (ei i) (ej i) (x i)


inPartialⁿ-Sub : ∀ {ℓ} → (A : Type ℓ) → ∀ n → (i j : C→I n)
                  → (x : C→ A n)
                  → Partialⁿ-Sub A n i j (Partialⁿ-const A n (i ∧ⁿ j) x)
inPartialⁿ-Sub A zero i j x i=1 = inS (x 1=1)
inPartialⁿ-Sub A (suc n) ei ej x i = inPartialⁿ-Sub  A n (ei i) (ej i) (x i)




-- inPartialⁿ-Sub⊂ : ∀ {ℓ} → (A : Type ℓ) → ∀ n
--          → (ei ej :  C→I n) → (ej-⊂I-ei : ⊂I ej ei)
--          → (paX : Partialⁿ A n ei) 
--          → Partialⁿ-Sub' A n ei ej (⊂→⊂' _ _ ej-⊂I-ei paX)

-- inPartialⁿ-Sub⊂ A zero ei ej ej-⊂I-ei paX ei=1 = inS (paX (ei=1))
-- inPartialⁿ-Sub⊂ A (suc n) ei ej ej-⊂I-ei paX i = inPartialⁿ-Sub⊂ A n (ei i) (ej i) (ej-⊂I-ei i) (paX i)


-- outPartialⁿ-Sub' :  ∀ {ℓ} → (A : Type ℓ) → ∀ n → (i j : C→I n)
--                   → (x : Partialⁿ A n j)
--                   → Partialⁿ-Sub' A n i j x
--                   → ⊂I i1ⁿ i → Subⁿ A n j x
-- outPartialⁿ-Sub' A zero i j px x x₂ = x (x₂ 1=1)
-- outPartialⁿ-Sub' A (suc n) i j px x x₂ i₁ = outPartialⁿ-Sub' A n (i i₁) (j i₁) (px i₁) (x i₁) (x₂ i₁)


Partial∨ⁿ :  ∀ {ℓ} → {A : Type ℓ} → ∀ n
              → (i j : C→I n)
              → (∩a : Partialⁿ A n (i ∧ⁿ j))
              → Partialⁿ-Sub A n i j ∩a
              → Partialⁿ-Sub A n j i (⊂→⊂' _ _ (∧-comm j i) ∩a)
              → Partialⁿ A n (i ∨ⁿ j)   
Partial∨ⁿ zero i j ∩a ai aj = Partial∨ i j {∩a} ai aj
Partial∨ⁿ (suc n) i j ∩a x x₁ l = Partial∨ⁿ n (i l) (j l) (∩a l) (x l) (x₁ l)


Partial∨ⁿ-ends :  ∀ {ℓ} → {A : Type ℓ} → ∀ n
              → (i : I)
              → Partialⁿ A n ([_]Iexpr {n} i)
              → Partialⁿ A n ([_]Iexpr {n} (~ i))
              → Partialⁿ A n ([_]Iexpr {n} i ∨ⁿ [_]Iexpr {n} (~ i))
Partial∨ⁿ-ends {A = A} zero i x1 x0 = λ { (i = i0) → x0 1=1 ; (i = i1) → x1 1=1  }
Partial∨ⁿ-ends {A = A} (suc n) i x1 x0 i₁ = Partial∨ⁿ-ends n i (x1 i₁) (x0 i₁)


-- inSⁿ⊂ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → {ei ej :  C→I n} → {⊂ij : ⊂I ej ei}
--        →  {x : Partialⁿ A n ei}
--        → ⊂I i1ⁿ ei →  Subⁿ A n ej (⊂→⊂' ej ei ⊂ij x) 
-- inSⁿ⊂ {A = A} {n} {ei} {ej} {⊂ij} {x} z = outPartialⁿ-Sub' A n ei ej (⊂→⊂' ej ei ⊂ij x)
--                         (inPartialⁿ-Sub⊂ A n ei ej ⊂ij x)
--                         (z) 





-- It would be very nice to have this proven but is it posssible ?
-- Sub-⊂ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → {ei ej :  C→I n} → {⊂ij : ⊂I ej ei}
--        → {x : Partialⁿ A n ei}
--        → Subⁿ A n ei x → Subⁿ A n ej (⊂→⊂' ej ei ⊂ij x) 
-- Sub-⊂ {n = zero} {⊂ij = ⊂ij} x = {!outS ?!}
-- Sub-⊂ {n = suc n} x = {!!}

-- in case where above is needed,
-- Sometimes it sufficeint to use this:
Sub-⊂∨ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → {ei ej :  C→I n}
       → {x : Partialⁿ A n (ej ∨ⁿ ei)}
       → Subⁿ A n (ej ∨ⁿ ei) (x) 
       → Subⁿ A n ei (⊂→⊂' _ _ (⊂-∨2 ej ei) x)
Sub-⊂∨ {n = zero} x = inS (outS x)
Sub-⊂∨ {n = suc n} x i = Sub-⊂∨ {n = n} (x i)



-- or this
Sub-⊂∧ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → {ei ej :  C→I n}
       → {x : Partialⁿ A n ei}
       → Subⁿ A n ei x 
       → Subⁿ A n (ej ∧ⁿ ei) (⊂'-∧2 ej ei x)
Sub-⊂∧ {n = zero} x = inS (outS x)
Sub-⊂∧ {n = suc n} x i = Sub-⊂∧ {n = n} (x i)




inPartialⁿ-Sub⊂' : ∀ {ℓ} → {A : Type ℓ} → ∀ n → {i j : C→I n}                  
                  → (pa : Partialⁿ A n j)
                  → Partialⁿ-Sub A n j i (⊂→⊂' _ _ (∧-comm j i)
                           (⊂'-∧2 i j pa))
                  
inPartialⁿ-Sub⊂' zero {i} {j} pa e=1 = inS (⊂'-∧2 i1 j pa e=1)
inPartialⁿ-Sub⊂' (suc n) pa i = inPartialⁿ-Sub⊂' n (pa i)


hcompⁿ :  ∀ {ℓ} → (A : Type ℓ) → ∀ n → (e :  C→I n) → (sides : I → Partialⁿ A n e)
            → Subⁿ A n e (sides i0) → C→ A n
hcompⁿ A zero e sides x _ = hcomp {φ = e} sides (outS x)
hcompⁿ A (suc n) e sides x i = hcompⁿ A n (e i) (λ j → sides j i) (x i)


hfillⁿ : ∀ {ℓ} → (A : Type ℓ) → ∀ n
          → (e :  C→I n) →  (sides : I → Partialⁿ A n e)
          → Subⁿ A n e (sides i0)
          → I → C→ A n
hfillⁿ A zero e sides x i _ = hfill sides x i 
hfillⁿ A (suc n) e sides x i j = hfillⁿ A (n) (e j) (λ l → sides l j) (x j) i


Boundaryω : ∀ {ℓ} → (A : Type ℓ) → ℕ → Typeω
Boundaryω A n = Partialⁿ A n (boundaryExpr n)

-- Boundaryω-subst-n : ∀ {ℓ} → {A : Type ℓ}→ ∀ {n₁ n₂}
--                     → n₁ ≡ n₂ → Boundaryω A n₁ → Boundaryω A n₂                      
-- Boundaryω-subst-n {ℓ} {A} {n₂ = zero} x x₁ ()
-- Boundaryω-subst-n {ℓ} {A} {zero} {n₂ = suc n₂} p = ⊥-recω (znots p)
-- Boundaryω-subst-n {ℓ} {A} {suc zero} {n₂ = suc zero} _ x = x
-- Boundaryω-subst-n {ℓ} {A} {suc (suc n₁)} {n₂ = suc zero} p x i = ⊥-recω (snotz (cong predℕ p))
-- Boundaryω-subst-n {ℓ} {A} {suc zero} {n₂ = suc (suc n₂)} p x i = ⊥-recω (znots (cong predℕ p))
-- Boundaryω-subst-n {ℓ} {A} {suc (suc n₁)} {n₂ = suc (suc n₂)} p x i j =
--   let z : Partialⁿ A n₁ (boundaryExpr (suc (suc n₁)) i j)
--       z = x i j

--       w : Partialⁿ A n₂ (boundaryExpr (suc (suc n₂)) i j)
--       w = {!!}
--   in w
--   -- {!x i j!}
    

Skelω : ∀ {ℓ} → (A : Type ℓ) → ∀ n → (Fin (suc (suc n))) → Typeω
Skelω A n k = Partialⁿ A n (skelExpr n k)


nCubeω : ∀ n → C→ (NCube n) n
nCubeω n = (C→elim (idfun (NCube n)))

NCubeBoundaryω : ℕ → Typeω
NCubeBoundaryω n = Partialⁿ (NCube n) n (boundaryExpr n) 

nCubeBoundaryω' : ∀ n → NCubeBoundaryω n 
nCubeBoundaryω' n = Partialⁿ-const _ _ (boundaryExpr n) (nCubeω n)


cylω : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → Boundaryω A (suc n) → I → Boundaryω A n
cylω {ℓ} {A} {n} x i = (⊂→⊂' _ _ (boundaryExpr-cyl n i)) (x i)

InsideOfω : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → Boundaryω A n → Typeω
InsideOfω {A = A} {n} bd = Subⁿ A n (boundaryExpr n) bd

-- lidω : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → (bd : Boundaryω A (suc n)) → (b : Bool) → InsideOfω {A = A} {n = n} (cylω {A = A} {n} bd (Bool→I b)) 
-- lidω {A = A} {n} bd b = inSⁿ⊂ ((1⊂lid _ _))

⊂bd-Sub→ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → (bd :  Boundaryω A (suc n)) 
           → ∀ i
           → Subⁿ A n (boundaryExpr (suc n) i) (bd i)
           → Subⁿ A n (boundaryExpr n)
                       (⊂→⊂' (boundaryExpr n) (boundaryExpr (suc n) i)
                        (boundaryExpr-cyl n i) (bd i))
⊂bd-Sub→ {n = zero} bd _ x = inS (outS x)
⊂bd-Sub→ {A = A} {n = suc zero} bd _ x i₁ = inS (outS (x i₁))
⊂bd-Sub→ {A = A} {n = suc (suc n)} bd i x i₁ = Sub-⊂∨ (x i₁)


Partialⁿ-bd-const : ∀ {ℓ} → (A : ℕ → Type ℓ) → ∀ n
                     → (∀ n → A (suc n))
                     → Partialⁿ (A n) n (boundaryExpr n) 
Partialⁿ-bd-const _ zero x ()
Partialⁿ-bd-const A (suc n) x =
  Partialⁿ-const (A (suc n)) (suc n)
  (boundaryExpr (suc n)) (C→elim {n = suc n} (const (x n)))


----------------
-- TODO : decide if it is usefulll
-- ppC : ∀ {ℓ} → ∀ {A : Type ℓ} → A → ∀ n → C→ A n
-- ppC a zero _ = a
-- ppC {A = A} a (suc n) i =
--    C→elim {n = n} {A = A}
--    ((refl ∙∙ (λ _ → C→-app {n = n} (ppC a n)) ∙∙ refl) i)


-- ppC' : ∀ n → (NCube n) → (NCube n)
-- ppC' n x = C→-app (ppC x n) x 

-- nCubeBoundaryω' : ∀ n → NCubeBoundaryω n
-- nCubeBoundaryω' n = Partialⁿ-const _ n (boundaryExpr n) (C→elim (ppC' n))


-- Partialⁿ-Sub-Ends : ∀ {ℓ} → (A : Type ℓ) → ∀ n → (i : I) → (j : C→I n)
--                       → (end0 : C→ A n)
--                       → (end1 : C→ A n)
--                     → Typeω
-- Partialⁿ-Sub-Ends A zero i j end0 end1 =
--   (j=1 : IsOne j) → Sub A (i ∨ ~ i) λ {(i = i0) → end0 1=1 ; (i = i1) → end1 1=1}
-- Partialⁿ-Sub-Ends A (suc n) i j end0 end1 = ∀ i' → Partialⁿ-Sub-Ends A n i (j i') (end0 i') (end1 i')




-- -----------

-- MaxN : ℕ
-- MaxN = 5




-- nCubeBoundaryω-cut-Max3 : (i₀0 i₁0 i₂0 : I) → (i₀1 i₁1 i₂1 : I) → (i₀ i₁ i₂ : I) → Partial
--                                           ((i₀0 ∧ ~ i₀) ∨
--                               (i₀1 ∧ i₀) ∨ (i₁0 ∧ ~ i₁) ∨ (i₁1 ∧ i₁) ∨ (i₂0 ∧ ~ i₂) ∨ i₂1 ∧ i₂)
--                                           (NCube 3)
-- nCubeBoundaryω-cut-Max3 i₀0 i₁0 i₂0 i₀1 i₁1 i₂1 i₀ i₁ i₂ = 
--   let
--       cu = (nCubeω 3 i₀ i₁ i₂ 1=1)
--       fc = λ (b : Bool) (k : ℕ) →
--              replaceAt {A = Interval'} {n = 3} k (end b)
--              cu
             
--       fc0 = fc false
--       fc1 = fc true
--   in

--   λ {
--       (i₀ = i0)(i₀0 = i1) →  fc0 0 ; (i₀ = i1)(i₀1 = i1) →  fc1 0
--     ; (i₁ = i0)(i₁0 = i1) →  fc0 1 ; (i₁ = i1)(i₁1 = i1) →  fc1 1
--     ; (i₂ = i0)(i₂0 = i1) →  fc0 2 ; (i₂ = i1)(i₂1 = i1) →  fc1 2
--    }


-- -- -----


-- nCubeBoundaryω-cut-Max :  NCubeBoundaryω MaxN
-- nCubeBoundaryω-cut-Max i₀ i₁ i₂ i₃ i₄ = 
--   let
--       cu = (nCubeω MaxN i₀ i₁ i₂ i₃ i₄ 1=1)
--       fc = λ (b : Bool) (k : ℕ) →
--              replaceAt {A = Interval'} {n = MaxN} k (end b)
--              cu
             
--       fc0 = fc false
--       fc1 = fc true
--   in

--   λ {
--       (i₀ = i0) →  fc0 0 ; (i₀ = i1) →  fc1 0
--     ; (i₁ = i0) →  fc0 1 ; (i₁ = i1) →  fc1 1
--     ; (i₂ = i0) →  fc0 2 ; (i₂ = i1) →  fc1 2
--     ; (i₃ = i0) →  fc0 3 ; (i₃ = i1) →  fc1 3
--     ; (i₄ = i0) →  fc0 4 ; (i₄ = i1) →  fc1 4
--    }

-- -- nCubeBoundaryω-cut-4' : ∀ (i : I) → Partialⁿ (NCube 4) 4 (boundaryExpr 4)
-- -- nCubeBoundaryω-cut-4' i =
-- --     ⊂→⊂' {n = 5} _ _ (boundaryExpr-cyl 4)
-- --    (Partialⁿ-map {A = NCube 5} tail nCubeBoundaryω-cut-Max) i
   


-- nCubeBoundaryω-cut-4-test : {!!}
-- nCubeBoundaryω-cut-4-test = {!nCubeBoundaryω-cut-Max!}
   


-- -- nCubeBoundaryω-cut : ∀ n → NCubeBoundaryω n
-- -- nCubeBoundaryω-cut = {! nCubeBoundaryω-cut-4!}
-- --- PROBLEMS WITH nCubeBoundaryω

-- nCubeBoundaryω2' : Partialⁿ (NCube 2) 2 (boundaryExpr 2) 
-- nCubeBoundaryω2' i₀ i₁ =
--   λ {
--       (i₀ = i0) →  end false ∷ inside i₁ ∷ []
--     ; (i₀ = i1) →  end true ∷ inside i₁ ∷ []
--     ; (i₁ = i0) →  inside i₀ ∷ end false ∷ []
--     ; (i₁ = i1) → inside i₀ ∷ end true ∷ []
--    }

-- -- problem-with-nCubeBoundaryω : (i₀ i₁ : I) → (x : IsOne (boundaryExpr 2 i₀ i₁) )
-- --                 →  nCubeBoundaryω2' i₀ i₁ x ≡ nCubeBoundaryω 2 i₀ i₁ x
-- -- problem-with-nCubeBoundaryω i₀ i₁ x = {!!} -- refl do not typecheck here

-- -- test-nCubeBoundaryω' : (i₀ i₁ : I) → (x : IsOne (boundaryExpr 2 i₀ i₁) )
-- --                 →  nCubeBoundaryω2' i₀ i₁ x ≡ nCubeBoundaryω' 2 i₀ i₁ x
-- -- test-nCubeBoundaryω' i₀ i₁ x = {!nCubeBoundaryω' 2 i1 i₁  !} 

-- -- problem-with-nCubeBoundaryω : (i₀ i₁ : I) → (x : IsOne (boundaryExpr 2 i₀ i₁) )
-- --                 →  nCubeBoundaryω2' i₀ i1 1=1 ≡ nCubeBoundaryω 2 i₀ i1 1=1
-- -- problem-with-nCubeBoundaryω i₀ i₁ x = {!refl!} -- refl do not typecheck here

-- nCubeBoundaryω2= : (i₀ i₁ : I) → (x : IsOne (boundaryExpr 2 i₀ i₁) )
--                 →  nCubeBoundaryω2' i₀ i₁ x ≡ nCubeBoundaryω 2 i₀ i₁ x
-- nCubeBoundaryω2= i₀ i₁ x =
--    let h = Partialⁿ-map2
--            {A = NCube 2} {A' = NCube 2} {B = Σ[ x ∈ NCube 2 ] Σ[ x' ∈ _ ] x ≡ x'}
--             {e = boundaryExpr 2}
--             (λ x x₁ → x , x₁ , isPropCube {n = 2} x x₁)
--              nCubeBoundaryω2' (nCubeBoundaryω 2) 
--    in snd (snd (h i₀ i₁ x))
   
-- test11 : (i₀ i₁ : I)
--                 →  nCubeBoundaryω2' i0 i1 1=1 ≡ nCubeBoundaryω 2 i0 i1 1=1
-- test11 i₀ i₁ = refl

-- ----------





-- -- nCubeBoundaryω-lemma : ∀ n → (pc : Partialⁿ (NCube n) n (boundaryExpr n))
-- --                        → {!!}
-- -- nCubeBoundaryω-lemma n =
-- --         Partialⁿ-map2
-- --            {A = NCube n} {A' = NCube n} {B = Σ[ x ∈ NCube n ] Σ[ x' ∈ _ ] x ≡ x'}
-- --             {e = boundaryExpr n}
-- --             (λ x x₁ → x , x₁ , isPropCube {n = n} x x₁)
-- --                (nCubeBoundaryω n)








-- -- -- toPartialⁿ-Sub-Ends-boundaryExpr : ∀ {ℓ} → (A : Type ℓ) → ∀ n → (i : I)
-- -- --                       → (end0 : C→ A (suc n))
-- -- --                       → (end1 : C→ A (suc n))
-- -- --                       → (∀ (i' : I) → (IsOne i') → {!!} )
-- -- --                       → Partialⁿ-Sub-Ends A (suc n) i (boundaryExpr (suc n)) end0 end1
-- -- -- toPartialⁿ-Sub-Ends-boundaryExpr {ℓ} A n i end0 end1 p = {!!}

-- -- Partialⁿ-boundaryExpr : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n
-- --                    → ∀ i i₁
-- --                    → (end0 : C→ A n )
-- --                    → (end1 : C→ A n)
-- --                    -- → (cyl : (c : NCube n) → C→-app end0 c ≡ C→-app end1 c)
-- --                    → (cyl : Partialⁿ-Sub-Ends A n i (boundaryExpr (suc n) i₁) end0 end1 )
-- --                    → Partialⁿ (A) n
-- --                      (boundaryExpr (suc (suc n)) i i₁)
-- -- Partialⁿ-boundaryExpr n i i₁ end0 end1 cyl  =
-- --    Partialⁿ∨-Ends n i (boundaryExpr (suc n) i₁) end0 end1 cyl
-- --      -- (toPartialⁿ-Sub-Ends _ n i _ end0 end1 cyl) 

-- -- unitBoundaryω : ∀ n → Boundaryω Unit n
-- -- unitBoundaryω zero ()
-- -- unitBoundaryω (suc zero) i = primPOr i (~ i) (λ _ → _) (λ _ → _)
-- -- unitBoundaryω (suc (suc n)) i i₁ =
-- --  let z : Partialⁿ Unit n (boundaryExpr (suc n) i₁)
-- --      z = unitBoundaryω (suc n) i₁
-- --      z1 = {!!}


-- --      w : Partialⁿ Unit n (([_]Iexpr n i ∨ⁿ [_]Iexpr n (~ i)) ∨ⁿ boundaryExpr (suc n) i₁)
-- --      w = {!!}
-- --  in  w


-- -- nCubeBoundaryω' : ∀ n → NCubeBoundaryω n
-- -- nCubeBoundaryω' zero ()
-- -- nCubeBoundaryω' (suc zero) i = primPOr i (~ i) (λ _ → (end true) ∷ []) (λ _ → (end false) ∷ [])
-- -- nCubeBoundaryω' (suc (suc n)) i i₁ =
-- --  let z = nCubeBoundaryω' (suc n) i₁
-- --      z1 = Partialⁿ-app (Partialⁿ-const (NCube (suc n) → NCube n )
-- --                n ((boundaryExpr (suc n) i₁) ) (C→elim {!!})) z
-- --  in {!z!}








-- -- -- failed?

-- -- ----------

-- -- -- Partialⁿ-Sub-Ends : ∀ {ℓ} → (A : Type ℓ) → ∀ n → (i : I) → (j : C→I n)
-- -- --                     →  Partialⁿ A n (([_]Iexpr n (~ i)) ∧ⁿ j)
-- -- --                     →  Partialⁿ A n (([_]Iexpr n (i)) ∧ⁿ j)
-- -- --                     → Typeω
-- -- -- Partialⁿ-Sub-Ends A zero i j x x₁ = (j=1 : IsOne j) → Sub A (i ∨ ~ i) λ {(i = i0) → x j=1 ; (i = i1) → x₁ j=1}
-- -- -- Partialⁿ-Sub-Ends A (suc n) i j x x₁ = ∀ i' →  Partialⁿ-Sub-Ends A n i (j i') (x i') (x₁ i')

-- -- -- Partialⁿ∨-Ends : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n
-- -- --                    → ∀ i → ∀ j
-- -- --                    → (intersection0 : Partialⁿ A n (([_]Iexpr n (~ i)) ∧ⁿ j))
-- -- --                    → (intersection1 : Partialⁿ A n (([_]Iexpr n i) ∧ⁿ j))
-- -- --                    → (cyl : Partialⁿ-Sub-Ends A n i (j) intersection0 intersection1 )
-- -- --                    → (end0 : Partialⁿ-Sub _ n _ _ intersection0 )
-- -- --                    → (end1 : Partialⁿ-Sub _ n _ _ intersection1)
-- -- --                    → Partialⁿ (A) n
-- -- --                          ((([_]Iexpr n i) ∨ⁿ ([_]Iexpr n (~ i)))
-- -- --                                ∨ⁿ j)
-- -- -- Partialⁿ∨-Ends {ℓ} {A} zero i i₁ intersection0 intersection1 cyl end0 end1 =
-- -- --   λ { (i = i1) → outS (end1 1=1) ; (i = i0) → outS (end0 1=1) ; (i₁ = i1) → outS (cyl 1=1)  }
-- -- -- Partialⁿ∨-Ends {ℓ} {A} (suc n) i i₁ intersection0 intersection1 cyl end0 end1 i' =
-- -- --   Partialⁿ∨-Ends {A = A} n i (i₁ i') (intersection0 i') (intersection1 i') (cyl i') (end0 i') (end1 i')
  
-- -- -- Partialⁿ-boundaryExpr : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n
-- -- --                    → ∀ i i₁
-- -- --                    → (intersection0 : Partialⁿ A n (([_]Iexpr n (~ i)) ∧ⁿ boundaryExpr (suc n) i₁))
-- -- --                    → (intersection1 : Partialⁿ A n (([_]Iexpr n i) ∧ⁿ boundaryExpr (suc n) i₁))
-- -- --                    → (cyl : Partialⁿ-Sub-Ends A n i (boundaryExpr (suc n) i₁) intersection0 intersection1 )
-- -- --                    → (end0 : Partialⁿ-Sub _ n _ _ intersection0 )
-- -- --                    → (end1 : Partialⁿ-Sub _ n _ _ intersection1)
-- -- --                    → Partialⁿ (A) n
-- -- --                      (boundaryExpr (suc (suc n)) i i₁)
-- -- -- Partialⁿ-boundaryExpr n i i₁ intersection0 intersection1 cyl end0 end1 =
-- -- --    Partialⁿ∨-Ends n i (boundaryExpr (suc n) i₁) intersection0 intersection1 cyl end0 end1  




-- -- -- -- Pathⁿ-P :  ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → Boundaryω A n → Type ℓ

-- -- -- -- -- Pathⁿω→P :  ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → (bd : Boundaryω A n)
-- -- -- -- --            → Pathⁿω {A = A} {n = n} bd
-- -- -- -- --            → Pathⁿ-P {A = A} {n = n} bd

-- -- -- -- -- Pathⁿω←P :  ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → (bd : Boundaryω A n)
-- -- -- -- --            → Pathⁿ-P {A = A} {n = n} bd
-- -- -- -- --            → Pathⁿω {A = A} {n = n} bd

-- -- -- -- PathⁿωEnd :  ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → (bd : Boundaryω A (suc n))
-- -- -- --            → ∀ b → Pathⁿ-P {A = A} {n = n} ((cylω {A = A} {n = n} bd (Bool→I b)))



-- -- -- -- Pathⁿ-P {A = A} {n = zero} _ = A
-- -- -- -- Pathⁿ-P {A = A} {n = suc n} bd = 
-- -- -- --      PathP (λ i → Pathⁿ-P {A = A} {n = n} (cylω {A = A} {n = n} bd i))
-- -- -- --        (PathⁿωEnd {A = A} {n = n} bd false)
-- -- -- --        (PathⁿωEnd {A = A} {n = n} bd true)



-- -- -- --  --{!  (x i)!}





-- -- -- -- PathⁿωEnd {n = zero} bd b = bd (Bool→I b) (isOne-∨B b )
-- -- -- -- PathⁿωEnd {n = suc zero} bd b i =  bd (Bool→I b) i (IsOne1 (Bool→I b ∨ ~ Bool→I b) (i ∨ ~ i) ((isOne-∨B b )))
-- -- -- -- PathⁿωEnd {A = A} {n = suc (suc n)} bd false i j =
-- -- -- --   let
-- -- -- --       zz0 : {!!}
-- -- -- --       zz0 = {!!}

-- -- -- --   in {!!}
-- -- -- -- PathⁿωEnd {A = A} {n = suc (suc n)} bd true i j = {!!}

-- -- -- -- -- Pathⁿω←P {n = zero} bd x = inS x
-- -- -- -- -- Pathⁿω←P {n = suc zero} bd x i = {!!}
-- -- -- -- -- Pathⁿω←P {n = suc (suc n)} bd x i = {!!}

-- -- -- -- -- Pathⁿω→P {n = zero} bd x = outS x
-- -- -- -- -- Pathⁿω→P {A = A} {n = suc n} bd x i = {!!}
-- -- -- -- --   -- let zz0 : Pathⁿω (cylω {A = A} {n = n} bd i)
-- -- -- -- --   --     zz0 = ⊂bd-Sub→ bd i (x i)

-- -- -- -- --   --     zz' : {!!}
-- -- -- -- --   --     zz' = {!!} 

-- -- -- -- --   --     zz : Pathⁿω (cylω {A = A} {n = n} bd i)
-- -- -- -- --   --     zz = {!zz0!}

-- -- -- -- --   -- in Pathⁿω→P {n = n} (cylω {A = A} {n = n} bd i) zz
