{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.IntervalPrim where


import Agda.Primitive.Cubical

open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum as Sum

open import Cubical.HITs.Interval
open import Cubical.HITs.PropositionalTruncation renaming (map to mapₚ)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Logic

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint

-- this version of Interval will let us handle both ends in single case
-- the convention of i0 ↔ false , i1 ↔ true is used everywhere in this module

ifω : Typeω → Typeω → Bool → Typeω 
ifω x y false = x
ifω x y true = y

×ω : Typeω → Typeω → Typeω 
×ω x y = ∀ b → ifω x y b

repeat : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → A →  Vec A n
repeat {n = zero} a = []
repeat {n = suc n} a  = a ∷ (repeat a) 

Iⁿ→ :  ∀ {ℓ} → ∀ (A  : Type ℓ) → ℕ → Typeω
Iⁿ→ A zero = I → A
Iⁿ→ A (suc x) = I → Iⁿ→ A x

C→ :  ∀ {ℓ} → ∀ (A  : Type ℓ) → ℕ → Typeω
C→ A zero = Partial i1 A -- lifting A from Type ℓ to Typeω
C→ A (suc x) = I → C→ A x

C→I : ℕ → Typeω
C→I zero = I
C→I (suc x) = I → C→I x


C→z : ∀ {ℓ} → ∀ {A  : Type ℓ} → C→ A 0 → A
C→z x = x 1=1

data Interval' : Type₀ where
   end : Bool → Interval'
   inside : end false ≡ end true 

Bool→I : Bool → I
Bool→I false = i0
Bool→I true = i1

-- I did not check how it would behave, but (Vec n Interval') , or (Fin n → Interval')
-- should also work here

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




Interval'-≡-∥Bool∥  : Interval' → Interval' ≡ ∥ Bool ∥
Interval'-≡-∥Bool∥ i' i = fst (⇔toPath {P = Interval' , isProp-Inrerval'}
                                          {Q = ∥ Bool ∥ₚ } f g i)
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

C→I-const : ∀ n → I → C→I n 
C→I-const zero x = x
C→I-const (suc n) x i = C→I-const n x

i1-max : ∀ n → ∀ x →  ⊂I x (C→I-const n i1)
i1-max zero x _ = 1=1
i1-max (suc n) x i = i1-max n (x i)

i0-min : ∀ n → ∀ x →  ⊂I (C→I-const n i0) x
i0-min zero x () 
i0-min (suc n) x i = i0-min n (x i)

⊂-∨1 : ∀ {n} → (x y : C→I n) → ⊂I x (x ∨ⁿ y)
⊂-∨1 {zero} = IsOne1
⊂-∨1 {suc n} x y i = ⊂-∨1 (x i) (y i)

⊂-∨2 : ∀ {n} → (x y : C→I n) → ⊂I y (x ∨ⁿ y)
⊂-∨2 {zero} = IsOne2
⊂-∨2 {suc n} x y i = ⊂-∨2 (x i) (y i)

-- ⊂-~ : ∀ {n} → (x : C→I n) → ⊂I (x ∧ⁿ (~ⁿ x)) (C→I-const n i0)
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


⊂'I : ∀ {n} → C→I n → C→I n → Typeω
⊂'I {n} x x₁ = ∀ {ℓ} → ∀ {A : Type ℓ} → Partialⁿ A n x₁ → Partialⁿ A n x

≡'I :  ∀ {n} → C→I n → C→I n → Typeω
≡'I x x₁ = ×ω (⊂'I x x₁) (⊂'I x₁ x) 

⊂'-~ : ∀ {n} → (x : C→I n) → ⊂'I (x ∧ⁿ (~ⁿ x)) (C→I-const n i0)
⊂'-~ {suc n} x {ℓ} {A} x₁ i = ⊂'-~ (x i) (x₁ i)

⊂'-∧ : ∀ {n} → (x y : C→I n) → ⊂'I (x ∧ⁿ y) x
⊂'-∧ {zero} x y {ℓ} {A} x₂ = λ { (x = i1)(y = i1) → x₂ 1=1 }
⊂'-∧ {suc n} x y {ℓ} {A} x₂ i = ⊂'-∧ {n} (x i) (y i) (x₂ i)

⊂→⊂' : ∀ {n} → (x y : C→I n) → ⊂I x y → ⊂'I x y
⊂→⊂' {zero} x y x₁ x₂ x₃ = x₂ (x₁ x₃)
⊂→⊂' {suc n} x y x₁ x₂ i = ⊂→⊂' {n} (x i) (y i) (x₁ i) (x₂ i)


Partialⁿ-const :  ∀ {ℓ} → (A : Type ℓ) → ∀ n → (e : C→I n) → C→ A n → Partialⁿ A n e
Partialⁿ-const {ℓ} A zero e a _ = a 1=1
Partialⁿ-const {ℓ} A (suc n) e a i = Partialⁿ-const A n _ (a i)

-- Partialⁿ' : ∀ {ℓ} → (A : Type ℓ) → ∀ n → C→I n → Typeω
-- Partialⁿ' A n x = {!!} → C→ A n

-- Partialⁿ→' : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {x} → Partialⁿ A n x → Partialⁿ' A n x   
-- Partialⁿ→' {n = zero} x x₁ = x x₁
-- Partialⁿ→' {n = suc n} {x₂} x x₁ = Partialⁿ→' {n = n} {!!} {!!}

Partialⁿ-app : ∀ {ℓ} → (A : Type ℓ) → ∀ n → (e : C→I n) →
                Partialⁿ A n e → IsOneⁿ-expr n e → C→ A n
Partialⁿ-app A zero e x x₁ _ = x x₁
Partialⁿ-app A (suc n) e x x₁ i = Partialⁿ-app A n (e i) (x i) (x₁ i)

-- Partialⁿ-test→ : {!!}
-- Partialⁿ-test→  = {!y!}

-- Partialⁿ-test : {!!}
-- Partialⁿ-test x y = {!!}

-- Partialⁿ-test1 : {!!}
-- Partialⁿ-test1 = {!Partialⁿ Bool 3!}

Subⁿ : ∀ {ℓ} → (A : Type ℓ) → ∀ n → (e :  C→I n) → Partialⁿ A n e → Typeω
Subⁿ A zero e x = Sub A e x
Subⁿ A (suc n) e x = ∀ i → Subⁿ A n (e i) (x i)

inSⁿ : {ℓ : Level} {A : Set ℓ} → ∀ n → ∀ e → (x : C→ A n) → Subⁿ A n e ((Partialⁿ-const A n e x)) 
inSⁿ zero e x = inS (x 1=1)
inSⁿ (suc n) e x i = inSⁿ n (e i) (x i)

outSⁿ : {ℓ : Level} {A : Set ℓ} → ∀ n → ∀ e → ∀ x → Subⁿ A n e x →  C→ A n         
outSⁿ zero e x x₁ _ = outS x₁
outSⁿ (suc n) e x x₁ i = outSⁿ n (e i) (x i) (x₁ i)

hcompⁿ :  ∀ {ℓ} → (A : Type ℓ) → ∀ n → (e :  C→I n) → (sides : I → Partialⁿ A n e)
            → Subⁿ A n e (sides i0) → C→ A n
hcompⁿ A zero e sides x _ = hcomp {φ = e} sides (outS x)
hcompⁿ A (suc n) e sides x i = hcompⁿ A n (e i) (λ j → sides j i) (x i)

-- Subⁿ : ∀ {ℓ} → (A : Type ℓ) → ∀ n → C→ A n → C→I n → Typeω
-- Subⁿ A zero x i = Sub A i λ x₁ → x 1=1 
-- Subⁿ A (suc n) x x₁ = ∀ i → Subⁿ A n (x i) (x₁ i) 

-- Subⁿ-test : {!!}
-- Subⁿ-test = {!Sub!}


-- inSⁿ : {ℓ : Level} {A : Set ℓ} → ∀ n → ∀ x → ∀ e → Subⁿ A n x e 
-- inSⁿ zero x e = inS (x 1=1)
-- inSⁿ (suc n) x e i = inSⁿ n (x i) (e i)


-- Subⁿ' : ∀ {ℓ} → {A : Type ℓ} → ∀ n → C→ A n → C→I n → Typeω
-- Subⁿ' {A = A} zero x x₁ = {!!}
-- Subⁿ' {A = A} (suc n) x x₁ = {!Sub (Vec Interval' n → A) {!!} (λ _ → C→-app (x))!}
--Sub (Vec Interval' n → A) {!!} (λ _ → C→-app (x))
-- Subⁿ-hlp : ∀ {ℓ} → {A : Type ℓ} → ∀ n → ∀ (x : C→ A n) → (e : C→I n)
--                →  Subⁿ n (x) e → (φ : I) → (Vec Interval' n → A) [ φ ↦ (λ _ → C→-app x) ]
-- Subⁿ-hlp zero x e s φ = inS {!s!}
-- Subⁿ-hlp (suc n) x e s φ = {!!}
-- SubⁿC : ∀ {ℓ} → {A : Type ℓ} → ∀ n → C→ A n → C→I n → Typeω
-- SubⁿC {A = A} zero x i = Sub A i λ x₁ → x 1=1 
-- SubⁿC {A = A} (suc n) x x₁ = ∀ i → SubⁿC {A = NCube (suc n) → A} n {!x i!} (x₁ i) 


-- Subⁿ-test : {!!} 
-- Subⁿ-test = {!!}

hfill' :  ∀ {ℓ} → {A : Type ℓ} → ∀ n → (I → C→ A n) → (C→I n) →  I → C→ A n
hfill' {A = A} n x e i =
   let zz : C→ (Vec Interval' n → _) n
       zz = C→A-subst1 n (λ φ → hfill {φ = φ} (λ i₁ _ → C→-app (x i₁)) (inS (C→-app (x i0))) i) e
   in C→Cu-app {A = A} {n = n} zz

-- hfill'' :  ∀ {ℓ} → {A : Type ℓ} → ∀ n → (x : I → C→ A n) → (e : C→I n) →
--               Subⁿ A n (x i0) e → C→ A n
-- hfill'' {A = A} 5 x e x0 i₀ i₁ i₂ i₃ i₄ _ =
--    hcomp {φ = e i₀ i₁ i₂ i₃ i₄} (λ l _ → {!x l i₀ i₁ i₂ i₃ i₄ 1=1!}) (outS (x0 i₀ i₁ i₂ i₃ i₄) ) 
   -- let n = 5
   --     zz : C→ (Vec Interval' n → _) n
   --     zz = C→A-subst1 n (λ φ → hcomp {φ = e} (λ i₁ _ → C→-app (x i₁))
   --           ((C→-app {n = 5} {A = A}
   --             λ x₁ x₂ x₃ x₄ x₅ _ → {!inS (x0 x₁ x₂ x₃ x₄ x₅)!}
   --             ))) e
   -- in C→Cu-app {A = A} {n = n} zz
-- hfill'' {A = A} (n) x e x0 = {!!}


hfill'-test : ∀ {ℓ} → {A : Type ℓ} → (x : Iⁿ→ A 1) →
                Square (λ i → x i0 i) (λ i → x i1 i) (λ i → x i i0) λ i → x i i1
hfill'-test x i₀ i₁ = x i₀ i₁

hfill'-test2 : ∀ {ℓ} → {A : Type ℓ} → (x : Iⁿ→ A 2) →
                Square
                  (λ i → x i1 i0 i)
                  (((λ i → x (~ i) i1 i0)) ∙∙ (λ i → x i0 i1 i) ∙∙ (λ i → x i i1 i1))
                  (λ i → x i1 i i0)
                  (((λ i → x (~ i) i0 i1)) ∙∙ (λ i → x i0 i i1) ∙∙ (λ i → x i i1 i1))
hfill'-test2 x i₀ i₁ = hfill' 2 (λ x₁ x₂ x₃ _ → x x₁ x₂ x₃)
           (λ x₀ x₁ → (x₀ ∧ x₁) ∨ (~ x₀) ∨ (~ x₁) ) i1 i₀ i₁ 1=1


-- bdMk : ∀ n → I^→I n
-- bdMk zero = {!!}
-- bdMk (suc n) = {!!}
