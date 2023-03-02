{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.Recursive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Path


import Cubical.Functions.Logic as L
open import Cubical.Functions.Involution
open import Cubical.Functions.FunExtEquiv


open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Bool hiding (_≤_ ; isProp≤ ; _≟_)

open import Cubical.Data.Nat.Base as Nat
open import Cubical.Data.Nat.Properties

open import Cubical.Induction.WellFounded

open import Cubical.Relation.Nullary

import Cubical.Data.List as L


infix 4 _≤_ _<_

_≤_ : ℕ → ℕ → Type₀
zero ≤ _ = Unit
suc m ≤ zero = ⊥
suc m ≤ suc n = m ≤ n

_<_ : ℕ → ℕ → Type₀
m < n = suc m ≤ n

_≤?_ : (m n : ℕ) → Dec (m ≤ n)
zero  ≤? _     = yes tt
suc m ≤? zero  = no λ ()
suc m ≤? suc n = m ≤? n

data Trichotomy (m n : ℕ) : Type₀ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

private
  variable
    ℓ : Level
    R : Type ℓ
    P : ℕ → Type ℓ
    k l m n : ℕ

isProp≤ : isProp (m ≤ n)
isProp≤ {zero} = isPropUnit
isProp≤ {suc m} {zero}  = isProp⊥
isProp≤ {suc m} {suc n} = isProp≤ {m} {n}

≤-k+ : m ≤ n → k + m ≤ k + n
≤-k+ {k = zero}  m≤n = m≤n
≤-k+ {k = suc k} m≤n = ≤-k+ {k = k} m≤n

≤-+k : m ≤ n → m + k ≤ n + k
≤-+k {m} {n} {k} m≤n
  = transport (λ i → +-comm k m i ≤ +-comm k n i) (≤-k+ {m} {n} {k} m≤n)

≤-refl : ∀ m → m ≤ m
≤-refl zero = _
≤-refl (suc m) = ≤-refl m

≡→≤ :  ∀ {m n} → m ≡ n → m ≤ n
≡→≤ {m} = flip (subst (m ≤_)) (≤-refl m) 

≤-trans : k ≤ m → m ≤ n → k ≤ n
≤-trans {zero} _ _ = _
≤-trans {suc k} {suc m} {suc n} = ≤-trans {k} {m} {n}

≤-antisym : m ≤ n → n ≤ m → m ≡ n
≤-antisym {zero} {zero} _ _ = refl
≤-antisym {suc m} {suc n} m≤n n≤m = cong suc (≤-antisym m≤n n≤m)

≤<-trans : k ≤ m → m < n → k < n
≤<-trans {k} {m} {suc n} = ≤-trans {k} {m} {n}

≤-k+-cancel : k + m ≤ k + n → m ≤ n
≤-k+-cancel {k =  zero} m≤n = m≤n
≤-k+-cancel {k = suc k} m≤n = ≤-k+-cancel {k} m≤n

≤-+k-cancel : m + k ≤ n + k → m ≤ n
≤-+k-cancel {m} {k} {n}
  = ≤-k+-cancel {k} {m} {n} ∘ transport λ i → +-comm m k i ≤ +-comm n k i

¬m<m : ¬ m < m
¬m<m {suc m} = ¬m<m {m}

≤0→≡0 : n ≤ 0 → n ≡ 0
≤0→≡0 {zero} _ = refl

¬m+n<m : ¬ m + n < m
¬m+n<m {suc m} = ¬m+n<m {m}

<-weaken : m < n → m ≤ n
<-weaken {zero} _ = _
<-weaken {suc m} {suc n} = <-weaken {m}

<-trans : k < m → m < n → k < n
<-trans {k} {m} {n} k<m m<n
  = ≤-trans {suc k} {m} {n} k<m (<-weaken {m} m<n)

<-asym : m < n → ¬ n < m
<-asym {m} m<n n<m = ¬m<m {m} (<-trans {m} {_} {m} m<n n<m)

<→≥→⊥ : n < m → m ≤ n → ⊥
<→≥→⊥ {zero} {zero} ()
<→≥→⊥ {zero} {suc m} x ()
<→≥→⊥ {suc n} {suc m} x x₁ = <→≥→⊥ {n} {m} x x₁

<→≢ : n < m → ¬ n ≡ m
<→≢ {n} {m} p q = ¬m<m {m = m} (subst {x = n} (_< m) q p)

Trichotomy-suc : Trichotomy m n → Trichotomy (suc m) (suc n)
Trichotomy-suc (lt m<n) = lt m<n
Trichotomy-suc (eq m≡n) = eq (cong suc m≡n)
Trichotomy-suc (gt n<m) = gt n<m

_≟_ : ∀ m n → Trichotomy m n
zero  ≟ zero = eq refl
zero  ≟ suc n = lt _
suc m ≟ zero = gt _
suc m ≟ suc n = Trichotomy-suc (m ≟ n)

¬<-≥ : ∀ m n → ¬ m < n → n ≤ m
¬<-≥ m n ¬m<n with m ≟ n 
... | lt x = Empty.rec (¬m<n x)
... | eq x = subst (_≤ m) x (≤-refl m)
... | gt x = <-weaken {n} {m} x


k≤k+n : ∀ k → k ≤ k + n
k≤k+n zero    = _
k≤k+n (suc k) = k≤k+n k

n≤k+n : ∀ n → n ≤ k + n
n≤k+n {k} n = transport (λ i → n ≤ +-comm n k i) (k≤k+n n)

≤-split : m ≤ n → (m < n) ⊎ (m ≡ n)
≤-split {zero} {zero} m≤n = inr refl
≤-split {zero} {suc n} m≤n = inl _
≤-split {suc m} {suc n} m≤n
  = Sum.map (idfun _) (cong suc) (≤-split {m} {n} m≤n)

module WellFounded where
  wf-< : WellFounded _<_
  wf-rec-< : ∀ n → WFRec _<_ (Acc _<_) n

  wf-< n = acc (wf-rec-< n)

  wf-rec-< (suc n) m m≤n with ≤-split {m} {n} m≤n
  ... | inl m<n = wf-rec-< n m m<n
  ... | inr m≡n = subst⁻ (Acc _<_) m≡n (wf-< n)

wf-elim : (∀ n → (∀ m → m < n → P m) → P n) → ∀ n → P n
wf-elim = WFI.induction WellFounded.wf-<

wf-rec : (∀ n → (∀ m → m < n → R) → R) → ℕ → R
wf-rec {R = R} = wf-elim {P = λ _ → R}

module Minimal where
  Least : ∀{ℓ} → (ℕ → Type ℓ) → (ℕ → Type ℓ)
  Least P m = P m × (∀ n → n < m → ¬ P n)

  isPropLeast : (∀ m → isProp (P m)) → ∀ m → isProp (Least P m)
  isPropLeast pP m
    = isPropΣ (pP m) (λ _ → isPropΠ3 λ _ _ _ → isProp⊥)

  Least→ : Σ _ (Least P) → Σ _ P
  Least→ = map-snd fst

  search
    : (∀ m → Dec (P m))
    → ∀ n → (Σ[ m ∈ ℕ ] Least P m) ⊎ (∀ m → m < n → ¬ P m)
  search dec zero = inr (λ _ b _ → b)
  search {P = P} dec (suc n) with search dec n
  ... | inl tup = inl tup
  ... | inr ¬P<n with dec n
  ... | yes Pn = inl (n , Pn , ¬P<n)
  ... | no ¬Pn = inr λ m m≤n
      → case ≤-split m≤n of λ where
          (inl m<n) → ¬P<n m m<n
          (inr m≡n) → subst⁻ (¬_ ∘ P) m≡n ¬Pn

  →Least : (∀ m → Dec (P m)) → Σ _ P → Σ _ (Least P)
  →Least dec (n , Pn) with search dec n
  ... | inl least = least
  ... | inr ¬P<n  = n , Pn , ¬P<n

  Least-unique : ∀ m n → Least P m → Least P n → m ≡ n
  Least-unique m n (Pm , ¬P<m) (Pn , ¬P<n) with m ≟ n
  ... | lt m<n = Empty.rec (¬P<n m m<n Pm)
  ... | eq m≡n = m≡n
  ... | gt n<m = Empty.rec (¬P<m n n<m Pn)

  isPropΣLeast : (∀ m → isProp (P m)) → isProp (Σ _ (Least P))
  isPropΣLeast pP (m , LPm) (n , LPn)
    = ΣPathP λ where
        .fst → Least-unique m n LPm LPn
        .snd → isOfHLevel→isOfHLevelDep 1 (isPropLeast pP)
                LPm LPn (Least-unique m n LPm LPn)

  Decidable→Collapsible
    : (∀ m → isProp (P m)) → (∀ m → Dec (P m)) → Collapsible (Σ ℕ P)
  Decidable→Collapsible pP dP = λ where
    .fst → Least→ ∘ →Least dP
    .snd x y → cong Least→ (isPropΣLeast pP (→Least dP x) (→Least dP y))

module AllFrom {ℓ} (P : ℕ → Type ℓ) (P? : ∀ n → Dec (P n)) where

  open Minimal

  allFromP : ℕ → Type ℓ
  allFromP n = ∀ k → n ≤ k → P k  

  pred?allFromP : ∀ n
      → allFromP (suc n)
      → allFromP n ⊎ Least (allFromP) (suc n)
  pred?allFromP n X with P? n
  ... | yes p = inl λ k x →
      Sum.rec (X k) (λ q → subst P q p)
       ((≤-split {n} {k} x))
  ... | no ¬p =
     inr (X , λ n' n'<sn X' → ¬p (X' n n'<sn))

  ΣallFromP→LeastAllFromP : Σ _ allFromP → Σ _ (Least (allFromP))
  ΣallFromP→LeastAllFromP = uncurry
     (Nat.elim (λ X → zero , X , λ _ ())
       λ n p X → Sum.rec p
         (λ x → suc n , x) (pred?allFromP n X))

  ΣallFromP→LeastAllFromP< : ∀ n → ∀ k x → k ≤ n
      → fst (ΣallFromP→LeastAllFromP (k , x)) ≤ n
  ΣallFromP→LeastAllFromP< n zero x x₁ = _
  ΣallFromP→LeastAllFromP< (suc n) (suc k) x x₁ with (pred?allFromP k x)
  ... | inl x₂ =
    let z = ΣallFromP→LeastAllFromP< n k x₂ x₁
    in <-weaken {fst (ΣallFromP→LeastAllFromP (k , x₂))} {suc n} z
  ... | inr x₂ = x₁

open Minimal using (Decidable→Collapsible) public

left-≤-max : ∀ m n → m ≤ max m n
left-≤-max zero n = _
left-≤-max (suc m) zero = ≤-refl m
left-≤-max (suc m) (suc n) = left-≤-max m n

right-≤-max : ∀ m n → n ≤ max m n
right-≤-max zero m = ≤-refl m
right-≤-max (suc n) zero = tt
right-≤-max (suc n) (suc m) = right-≤-max n m

left-≤-→max≡ : ∀ m n → n ≤ m → max m n ≡ m
left-≤-→max≡ m zero x = maxComm m zero 
left-≤-→max≡ (suc m) (suc n) x = cong suc (left-≤-→max≡ m n x)

right-≤-→max≡ : ∀ m n → n ≤ m → max n m ≡ m
right-≤-→max≡ m n x =
     maxComm n m
   ∙ left-≤-→max≡ m n x

max≤ : ∀ m n k → m ≤ k → n ≤ k → max m n ≤ k
max≤ zero n k x x₁ = x₁
max≤ (suc m) zero (suc k) x x₁ = x
max≤ (suc m) (suc n) (suc k) x x₁ = max≤ m n k x x₁

Fin : ℕ → Type
Fin n = Σ _ (_< n)

Fin-elim : ∀ {ℓ} {A : Type ℓ} → ∀ n → A → (Fin n → A) → (Fin (suc n) → A)
Fin-elim n a _ (zero , _) = a
Fin-elim (suc n) _ f (suc k , k<) = f (k , k<)

Fin₋₁ : ℕ → Type
Fin₋₁ n = Σ ℕ λ k → (suc k < n)

sucF : ∀ {n} → Fin n → Fin (suc n) 
sucF (k , k<) = suc k , k<


≡Fin : ∀ {n} → {k k' : Fin n} → fst k ≡ fst k' → k ≡ k'
≡Fin {n} = Σ≡Prop (λ k → isProp≤ {suc k} {n})  

fst∘Inj : ∀ {ℓ} {A : Type ℓ} {n} → {f g : A → Fin n} →
           fst ∘ f ≡ fst ∘ g → f ≡ g
fst∘Inj {n = n} x = funExt (≡Fin {n = n} ∘ funExt⁻ x)

weakenFin : {n : ℕ} → Fin n → Fin (suc n)
weakenFin {n} x = (fst x , <-weaken {n = n} (snd x))

predℕ< : ∀ k n → k < (suc (suc n)) → predℕ k < (suc n)
predℕ< zero n x = _
predℕ< (suc k) n x = x

≤predℕ : ∀ k n → suc k ≤ n → k ≤ predℕ n
≤predℕ k (suc n) x = x

predFin : {n : ℕ} → Fin (suc (suc n)) → Fin (suc n)
predFin {n} (k , k<) = (predℕ k , predℕ< k n k<)

¬≡ℕ-cases : (m n : ℕ) → ¬ m ≡ n → (m < n) ⊎ (n < m)
¬≡ℕ-cases zero zero ¬p = Empty.rec (¬p refl)
¬≡ℕ-cases zero (suc n) ¬p = inl _
¬≡ℕ-cases (suc m) zero ¬p = inr _
¬≡ℕ-cases (suc m) (suc n) ¬p = ¬≡ℕ-cases m n (¬p ∘ cong suc)

─Σ : (m n : ℕ) → m ≤ n → Σ ℕ λ k → k + m ≡ n 
─Σ zero n x = n , (+-zero n)
─Σ (suc m) (suc n) x =
 let (z , p) = ─Σ m n x
 in z , +-suc _ _ ∙ cong suc p

fzero' : ∀ {n} → Fin n → Fin n
fzero' {suc n} _ = zero , _

isSetFin : ∀ {n} → isSet (Fin n)
isSetFin {n} = isSetΣ isSetℕ λ k → isProp→isSet (isProp≤ {suc k} {n})


X×ⁿ  : ∀ {ℓ} → (Type ℓ) → (Type ℓ) → ℕ → Type ℓ 
X×ⁿ A B zero = B
X×ⁿ A B (suc n) = A × (X×ⁿ A B n)

_×^_ : ∀ {ℓ} → Type ℓ → ℕ → Type ℓ 
A ×^ zero = Unit*
A ×^ suc x = A × (A ×^ x)

bindDec : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} →
             (A → Dec B) → (¬ A → ¬ B) → Dec A → Dec B
bindDec x x₁ (yes p) = x p
bindDec x x₁ (no ¬p) = no (x₁ ¬p)

discrete-×^ : ∀ {ℓ} {A : Type ℓ} → Discrete A → ∀ n → Discrete (A ×^ n) 
discrete-×^ _ zero x₁ y = yes refl
discrete-×^ _=?_ (suc n) (x , xs) (y , ys) =
  bindDec
    (λ p → bindDec (yes ∘ cong₂ (_,_) p ) (_∘ cong snd)
      (discrete-×^ _=?_ n xs ys)) (_∘ cong fst) (x =? y)

disc^-help-Ty : ∀ {ℓ} {A : Type ℓ} → Discrete A → ∀ n → Rel (A ×^ n) ℓ-zero
disc^-help-Ty _ zero x x₁ = Unit
disc^-help-Ty _=?_ (suc n) (x , xs) (y , ys) =
  True (x =? y) × disc^-help-Ty _=?_  n xs ys

disc^-help : ∀ {ℓ} {A : Type ℓ} →
    (_=?_ : Discrete A) → ∀ n → ∀ x y →
     x ≡ y → disc^-help-Ty _=?_ n x y
disc^-help _=?_ zero x y x₁ = tt
disc^-help _=?_ (suc n) x y p =
 Dec→DecBool _ (cong fst p) , disc^-help _=?_ n _ _ (cong snd p)


×^≡Code : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → A ×^ n → A ×^ n → Type ℓ
×^≡Code {n = zero} _ _ = Unit*
×^≡Code {n = suc n} (x , xs) (y , ys) = (x ≡ y) × ×^≡Code xs ys


Iso-×^≡-≡ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {x y}
      → Iso (×^≡Code {A = A} {n = n} x y) (x ≡ y)
Iso-×^≡-≡ {n = zero} =
  iso (λ _ → refl) (λ _ → tt*) (λ _ → refl) λ _ → refl 
Iso-×^≡-≡ {n = suc n} =
    compIso
      (prodIso idIso (Iso-×^≡-≡ {n = n}))
       ΣPathIsoPathΣ

×^≡ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {x y} →
      ×^≡Code {A = A} {n} x y → x ≡ y
×^≡ = Iso.fun Iso-×^≡-≡

×^≡Code+ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ m →
   A ×^ (m + n) → A ×^ (m + n) → Type ℓ
×^≡Code+ {n = n} zero = _≡_
×^≡Code+ {n = n} (suc m) (x , xs) (y , ys) =
 (x ≡ y) × ×^≡Code+ {n = n} (m) (xs) (ys)

×^≡+ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ m → ∀ {x y} →
      ×^≡Code+ {A = A} {n} m x y → x ≡ y
×^≡+ zero x = x
×^≡+ (suc m) = ΣPathP ∘' map-snd (×^≡+ m)


isProp→PathP' : {B : I → Type ℓ} → ((i : I) → isProp (B i))
               → (b0 : B i0) (b1 : B i1)
               → PathP B b0 b1
isProp→PathP' {B = B} hB b0 b1 i =
  hB i (coe0→i B i b0) (coe1→i B i b1) i




commT : ℕ → ℕ → Type₀
commT x zero = ⊥
commT x (suc zero) = ⊥
commT zero (suc (suc x₁)) = Unit
commT (suc k) (suc (suc l)) = commT k (suc l)


suc-commT : ∀ n m → (commT n m) → (commT (suc n) (suc m))
suc-commT n (suc m) x = x

pred-commT : ∀ n m → (commT (suc n) (suc m)) → (commT n m)
pred-commT n (suc m) x = x


commT→< : ∀ n m → (commT n m) → (n < m)
commT→< zero (suc (suc m)) x = x
commT→< (suc n) (suc (suc m)) x = commT→< n (suc m) x


-- weakFin : ∀ n → Σ ℕ λ k → (suc k < n) → Fin n
-- weakFin n = {!!}

𝑮 : ∀ {ℓ ℓ'} {A : Type ℓ} {B₀ B₁ : Type ℓ'} {C : Type ℓ} →
      A ≃ B₀ → (B₀ ≡ B₁) → C ≃ B₁
      → A ≡ C
𝑮 e₀ p e₁ i =
  Glue (p i)
     λ { (i = i0) → _ , e₀
        ;(i = i1) → _ , e₁ }


isOfHLevelGlue : {A : Type ℓ} (φ : I) → 
                {f : PartialP φ (λ o → Σ[ T ∈ Type ℓ ] T ≃ A)} →
                ∀ n →
                isOfHLevel n A → isOfHLevel n (Glue A f)  -- isEquiv {A = } (unglue φ)
isOfHLevelGlue φ {f} n x =
  isOfHLevelRespectEquiv n (invEquiv (unglueEquiv _ φ f)) x

isOfHLevelUA : {A B : Type ℓ} (i : I) → 
                (e : A ≃ B) →
                ∀ n →
                isOfHLevel n B → isOfHLevel n (ua e i)  -- isEquiv {A = } (unglue φ)
isOfHLevelUA i e n x =
  isOfHLevelRespectEquiv n (invEquiv (ua-unglueEquiv e i)) x


isOfHLevel𝑮 : ∀ {ℓ} {A : Type ℓ} {B₀ B₁ : Type ℓ} {C : Type ℓ} →
      {e₀ : A ≃ B₀} → {p : B₀ ≡ B₁} → {e₁ : C ≃ B₁}
      → ∀ m → (∀ i → isOfHLevel m (p i))
      → ∀ i → isOfHLevel m (𝑮 e₀ p e₁ i) 
isOfHLevel𝑮 m p i =
  isOfHLevelGlue (i ∨ ~ i) {f = λ { (i = i0) → _ ; (i = i1) → _ }} m (p i)

𝑮-gluePath :
   ∀ {ℓ ℓ'} {A : Type ℓ} {B₀ B₁ : Type ℓ'} {C : Type ℓ} →
      (e₀ : A ≃ B₀) → (B : B₀ ≡ B₁) → (e₁ : C ≃ B₁)
      → ∀ {a c}
      → PathP (λ i → B i)
          (fst e₀ a ) (fst e₁ c)
      → PathP (λ i → 𝑮 e₀ B e₁ i) a c
𝑮-gluePath e₀ B e₁ p i =
    glue (λ {(i = i0) → _
          ;(i = i1) → _
          }) (p i)


𝑮-ungluePathExt :
   ∀ {ℓ ℓ'} {A : Type ℓ} {B₀ B₁ : Type ℓ'} {C : Type ℓ} →
      (e₀ : A ≃ B₀) → (B : B₀ ≡ B₁) → (e₁ : C ≃ B₁)
      → PathP (λ i → 𝑮 e₀ B e₁ i → B i)
         (fst e₀)
         (fst e₁)
𝑮-ungluePathExt e₀ B e₁ i = unglue (i ∨ ~ i)
    

𝑮-gluePathExt-R :
   ∀ {ℓ} {A : Type ℓ} →
       (B : A ≡ A) (e₀ e₁ : A ≃ A) (e= : PathP (λ i → A →  B i)
          (fst e₀) (λ z → fst e₁ (fst e₁ z)))  
      → PathP (λ i → A ≃ 𝑮 (idEquiv _) B e₁ i)
          e₀
          e₁
𝑮-gluePathExt-R B e₀ e₁ e= = ΣPathPProp
    isPropIsEquiv
    λ i x → glue (λ {(i = i0) → fst e₀ x
            ;(i = i1) → fst e₁ x
          }) ((e= i) x)

𝑮-gluePathExt-L :
   ∀ {ℓ} {A : Type ℓ} →
       (B : A ≡ A) (e₀ e₁ : A ≃ A) (e= : PathP (λ i → A →  B i)
          (fst e₀ ∘ fst e₀) (fst e₁))  
      → PathP (λ i → A ≃ 𝑮  e₀ B (idEquiv _) i)
          e₀
          e₁
𝑮-gluePathExt-L B e₀ e₁ e= = ΣPathPProp
    isPropIsEquiv
    λ i x → glue (λ {(i = i0) → fst e₀ x
            ;(i = i1) → fst e₁ x
          }) ((e= i) x)

𝑮-gluePathExt-L' :
   ∀ {ℓ} {A : Type ℓ} →
       (B : A ≡ A) (e₀ : A ≃ A) (e= : PathP (λ i → A →  B i)
          (fst e₀ ∘ fst e₀) (idfun _))  
      → PathP (λ i → A → 𝑮  e₀ B (idEquiv _) i)
          (fst e₀)
          (idfun _)
𝑮-gluePathExt-L' B e₀ e= = 
    λ i x → glue (λ {(i = i0) → fst e₀ x
            ;(i = i1) → x
          }) ((e= i) x)


𝑮-refl : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ} →
      A ≃ B → C ≃ B
      → A ≡ C
𝑮-refl e₀ e₁ = 𝑮 e₀ refl e₁


𝑮-refl-gluePath :
  ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ} →
      (e₀ : A ≃ B) → (e₁ : C ≃ B)
      {a : A} {c : C}
      → fst e₀ a ≡ fst e₁ c
      → PathP (λ i → 𝑮-refl e₀ e₁ i) a c
  
𝑮-refl-gluePath e₀ e₁ p i =
  glue (λ {(i = i0) → _
          ;(i = i1) → _
          }) (p i)


-- 𝑮sq : ∀ {ℓ ℓ'} {A : Type ℓ} {B₀ B₁ : Type ℓ'} {C : Type ℓ} →
--       A ≃ B₀ → (B₀ ≡ B₁) → C ≃ B₁
--       → A ≡ C
-- 𝑮sq e₀ p e₁ i =
--   Glue (p i)
--      λ { (i = i0) → _ , e₀
--         ;(i = i1) → _ , e₁ }

equivPathP : ∀ {ℓ ℓ'} → {A : I → Type ℓ} {B : I → Type ℓ'}
            {f₀ : A i0 → B i0} {f₁ : A i1 → B i1}
          → PathP (λ i → A i → B i)
                f₀
                f₁
          → ∀ isEquivF₀ isEquivF₁ 
          → PathP (λ i → A i ≃ B i)
                (f₀ , isEquivF₀)
                (f₁ , isEquivF₁)
fst (equivPathP f isEquivF₀ isEquivF₁ i) = f i
snd (equivPathP f isEquivF₀ isEquivF₁ i) =
  isProp→PathP (λ i → isPropIsEquiv (f i))
     isEquivF₀ isEquivF₁ i

equivPathP' : ∀ {ℓ ℓ'} → {A : I → Type ℓ} {B : I → Type ℓ'}
           (e₀ : A i0 ≃ B i0) (e₁ : A i1 ≃ B i1)
         → PathP (λ i → A i → B i)
               (fst e₀)
               (fst e₁)
         → PathP (λ i → A i ≃ B i)
               e₀
               e₁
equivPathP' e₀ e₁ p =
  equivPathP p (snd e₀) (snd e₁)


cong₃ : ∀ {ℓ ℓ' ℓ'' ℓ'''} → {A : Type ℓ}
        {B : A → Type ℓ'}
        {C : (a : A) → (b : B a) → Type ℓ''}
        {D : (a : A) → (b : B a) → C a b → Type ℓ'''}
        (f : (a : A) → (b : B a) → (c : C a b) → D a b c) →
        {a₀ a₁ : A}
        (a : a₀ ≡ a₁) →
        {b₀ : B a₀} {b₁ : B a₁} (b : PathP (λ i → B (a i)) b₀ b₁) →
        {c₀ : C a₀ b₀} {c₁ : C a₁ b₁} (c : PathP (λ i → C (a i) (b i)) c₀ c₁)
        → PathP (λ i → D (a i) (b i) (c i)) (f _ _ _) (f _ _ _)
        
cong₃ f a b c i = f (a i) (b i) (c i)
{-# INLINE cong₃ #-}

congP₃ : ∀ {ℓ ℓ' ℓ'' ℓ'''} → {A : I → Type ℓ}
        {B : ∀ i → A i → Type ℓ'}
        {C : ∀ i → (a : A i) → (b : B i a) → Type ℓ''}
        {D : ∀ i → (a : A i) → (b : B i a) → C i a b → Type ℓ'''}
        (f : ∀ i → (a : A i) → (b : B i a) → (c : C i a b) → D i a b c) →
        {a₀ : A i0} {a₁ : A i1}
        (a : PathP A a₀ a₁) →
        {b₀ : B i0 a₀} {b₁ : B i1 a₁} (b : PathP (λ i → B i (a i)) b₀ b₁) →
        {c₀ : C i0 a₀ b₀} {c₁ : C i1 a₁ b₁} (c : PathP (λ i → C i (a i) (b i)) c₀ c₁)
        → PathP (λ i → D i (a i) (b i) (c i)) (f i0 _ _ _) (f i1 _ _ _)
        
congP₃ f a b c i = f i (a i) (b i) (c i)
{-# INLINE congP₃ #-}



--  adjT×^≡-invol-sides0 :
--    ∀ i j → Partial (j ∨ ~ j)
--      (Σ-syntax (Type ℓ) (λ T → T ≃ ua (adjT×^≃ {2 + n} zero) i ))
--  adjT×^≡-invol-sides0 {n} i j =
--        λ {  (j = i0) → A ×^ (2 + n) ,
--          glueAdjT× (2 + n) zero i ∘ adjT×^ zero ,
--          isProp→PathP' (λ i → isPropIsEquiv
--            (glueAdjT× (2 + n) zero i ∘ adjT×^ {n = 2 + n} zero))
--             (isEquivAdjT×^ (2 + n) zero) (idIsEquiv _) i
--        ; (j = i1) → A ×^ (2 + n) ,
--          glueAdjT× (2 + n) zero i ,
--          isProp→PathP' (λ i → isPropIsEquiv
--            (glueAdjT× (2 + n) zero i))
--             (idIsEquiv _)
--             (isEquivAdjT×^ (2 + n) zero) i }

-- Σ-swap-01-≡-invol-sides : ∀ {ℓ ℓ'} {A : Type ℓ} → {B : Type ℓ'} →
--                     (p : B ≡ B) → 
--                     {!!} 
-- Σ-swap-01-≡-invol-sides = {!!}


glue-Σ-swap-01 : ∀ {ℓ ℓ'} {A : Type ℓ} → {B B' : Type ℓ'} →
    (P : B ≡ B') →
      PathP (λ i → A × A × P i →
          𝑮 Σ-swap-01-≃ (λ i → A × A × P i) (idEquiv _) i)
         swap-01
         (idfun _)
glue-Σ-swap-01 P i x =
  glue
   (λ { (i = i0) → _ ; (i = i1) → _ })
    x

-- Σ-swap-01-≡-invol-glue :
--   ∀ {ℓ} {A : Type ℓ} → {B : Type ℓ} {P : B ≡ B} →
--     (S : sym P ≡ P)
--     (L : PathP
--        (λ i → A × A × B ≃ P i)
--        {!!}
--        {!!})
--    → 
--    SquareP (λ i j →
--      A × A × S j i →
--        (𝑮 {!L i!} (refl {x = P i}) {!!}) j)
--        {!!}
--        {!!}
--        -- (ua-gluePathExt Σ-swap-01-≃)
--        -- (congP (λ i → _∘ swap-01)
--        --    (symP (ua-gluePathExt (Σ-swap-01-≃ {A = A} {A} {B}))))
--        (λ i → glue-Σ-swap-01 P (~ i) ∘ swap-01)
--        (glue-Σ-swap-01 P)
-- Σ-swap-01-≡-invol-glue {A = A} {B} i j = {!!}
--   -- glue (λ {(j = i0) → a , a' , b
--   --         ;(j = i1) → a' , a , b
--   --         })
--   --          (ua-gluePath
--   --           (Σ-swap-01-≃
--   --             {A = A} {A} {B})
--   --              (refl {x = a , a' , b}) i)


Σ-swap-01→hProp : ∀ {ℓ ℓ' ℓ''}
  (A : Type ℓ) (B : Type ℓ') (D : Type ℓ'') 
  → ∀ f
  → (∀ x y z → f (y , x , z) ≡ f (x , y , z)) 
  → 
    PathP (λ i → ua (Σ-swap-01-≃ {A = A} {A} {B}) i → D)
      f
      f
Σ-swap-01→hProp A B D f f= i g =
 let (x , y , z) = (ua-unglue Σ-swap-01-≃ i g)
 in f= x y z i 

glue'-Σ-swap-01 : ∀ {ℓ ℓ'} {A : Type ℓ} → {B B' : Type ℓ'} →
    (P : B ≡ B') →
      PathP (λ i → A × A × P i →
          𝑮 Σ-swap-01-≃ (λ i → A × A × P i) (idEquiv _) i)
         (idfun _)
         swap-01
glue'-Σ-swap-01 P i x =
  glue
   (λ { (i = i0) → _ ; (i = i1) → _ })
    (swap-01 x)

Σ-swap-01-≡-invol : ∀ {ℓ ℓ'} {A : Type ℓ} → {B B' : Type ℓ'} →
                    (p : B ≡ B') → 
                    𝑮 (Σ-swap-01-≃ {A = A} {A} {B})
                      (λ i → A × A × p i) (idEquiv _) ≡
                    𝑮 (idEquiv _) (λ i → A × A × p i)
                       (Σ-swap-01-≃ {A = A} {A} {B'}) 
Σ-swap-01-≡-invol {A = A} {B} {B'} p j =
  𝑮 (ΣPathPProp {A = λ j →
         _ → ua (Σ-swap-01-≃ {A = A} {A} {p i0}) j }
               {λ _ → isEquiv}
           {u = Σ-swap-01-≃ {A = A} {A} {B}}
           {v = idEquiv _}
      isPropIsEquiv
       (λ j x → glue
         (λ { (j = i0) → fst (snd x) , fst x , snd (snd x)
            ; (j = i1) → x
            })
         x) j)
    (λ i → ua (Σ-swap-01-≃ {A = A} {A} {p i}) j)
    ((ΣPathPProp {A = λ j →
         _ → ua (Σ-swap-01-≃ {A = A} {A} {p i1}) j }
               {λ _ → isEquiv}
           {u = idEquiv _}
           {v = Σ-swap-01-≃ {A = A} {A} {B'}}
      isPropIsEquiv
       (λ j x → glue
         (λ { (j = i0) → x
            ; (j = i1) → fst (snd x) , fst x , snd (snd x)
            })
         (swap-01 x)) j))

Σ-swap-01-≡-invol-ua : ∀ {ℓ} {A : Type ℓ} → {B : Type ℓ} →
             ua (Σ-swap-01-≃ {A = A} {A} {B}) ≡
             sym (ua (Σ-swap-01-≃ {A = A} {A} {B}))  
Σ-swap-01-≡-invol-ua = Σ-swap-01-≡-invol refl

Σ-swap-01-≡-invol-ua-glue :
  ∀ {ℓ} {A : Type ℓ} → {B : Type ℓ} →
   SquareP (λ i j →
     A × A × B →
       Σ-swap-01-≡-invol-ua {A = A} {B} i j)
       (ua-gluePathExt Σ-swap-01-≃)
       (congP (λ i → _∘ swap-01)
          (symP (ua-gluePathExt (Σ-swap-01-≃ {A = A} {A} {B}))))
       refl
       refl
Σ-swap-01-≡-invol-ua-glue {A = A} {B} i j (a , a' , b) =
  glue (λ {(j = i0) → a , a' , b
          ;(j = i1) → a' , a , b
          })
           (ua-gluePath
            (Σ-swap-01-≃
              {A = A} {A} {B})
               (refl {x = a , a' , b}) i)

Σ-swap-012-≡-comp-ua : ∀ {ℓ} {A : Type ℓ} → {B : Type ℓ} (p : _ ≡ _) →
             Square
               (cong (A ×_) (ua (Σ-swap-01-≃ {A = A} {A} {B})))
               (ua (Σ-swap-01-≃ {A = A} {A} {A × B}))
               (𝑮 (≃-× (idEquiv A) (Σ-swap-01-≃ {A = A} {A} {B}))
                 p (Σ-swap-01-≃ {A = A} {A} {A × B}))
               p

Σ-swap-012-≡-comp-ua {A = A} {B = B} p i j =
  Glue (p i)
     λ { (i = i1)(j = i0) → _ , Σ-swap-01-≃ {A = A} {A} {A × B}
        ; (i = i0) → (A × ua (Σ-swap-01-≃ {A = A} {A} {B}) j) ,
               ≃-× (idEquiv _)
                  (ua-unglueEquiv (Σ-swap-01-≃ {A = A} {A} {B}) j)
        ; (j = i1) → _ , (idfun _ ,
               isProp→PathP (λ i → isPropIsEquiv (idfun (p i)))
                  (snd (≃-× (idEquiv _) (idEquiv _) )) (idIsEquiv _) i)}

Σ-swap-012-≡-comp-ua-glue : ∀ {ℓ} {A : Type ℓ} → {B : Type ℓ} (p : _ ≡ _) →
      SquareP (λ i j → p i
        → Σ-swap-012-≡-comp-ua {A = A} {B} p i j)
         (((λ i (a , x) →
          a , glue
            (λ { (i = i0) → _
               ; (i = i1) → _
               })
               x)))
         ((λ i x →
          glue (λ { (i = i0) → _ ; (i = i1) → _ }) x))
        (λ i x →
          glue
            (λ { (i = i0) → _
               ; (i = i1) → _
               })
               x)
        λ _ x → x

Σ-swap-012-≡-comp-ua-glue p i j x =
  glue
     (λ { (i = i1)(j = i0) → _
        ; (i = i0) → fst x ,
           glue (λ { (j = i0) → _
                   ; (j = i1) → _
                   }) (snd x)
        ; (j = i1) → _ })
     x




module _ {ℓ} {A : Type ℓ} where  


 adjT×^ : ∀ {n} → ℕ →
              (A ×^ n) → (A ×^ n)
 adjT×^ {zero} x x₁ = x₁
 adjT×^ {suc n} (suc k) (x , xs) = x , adjT×^ k xs
 adjT×^ {suc zero} zero x = x
 adjT×^ {suc (suc n)} zero (x , x' , xs) = (x' , x , xs)

 invol-adjT×^ : ∀ n k → isInvolution (adjT×^ {n = n} k) 
 invol-adjT×^ zero k x = refl
 invol-adjT×^ (suc n) (suc k) (x , xs) =
    cong (x ,_) (invol-adjT×^ n k xs)
 invol-adjT×^ (suc zero) zero x = refl
 invol-adjT×^ (suc (suc n)) zero x = refl

 cong-Σ-swap-01 : ∀ {ℓ'} {B₀ B₁ : Type ℓ'} → B₀ ≡ B₁
                    
                 →  A × A × B₀ ≡ A × A × B₁
 cong-Σ-swap-01 p i =
   Glue (A × A × p i)
      λ {  (i = i0) → _ , Σ-swap-01-≃
         ; (i = i1) → _ , idEquiv _
         }


 -- unglue-cong-Σ-swap-01-invol : ∀ {ℓ'} {B₀ B₁ : Type ℓ'} → (p : B₀ ≡ B₁)
 --    → cong-Σ-swap-01 p ≡ cong-Σ-swap-01 (sym p) 
 -- unglue-cong-Σ-swap-01-invol = {!!}



 isEquivAdjT×^ : ∀ n k → isEquiv (adjT×^ {n = n} k)
 isEquivAdjT×^ zero k = idIsEquiv _
 fst (fst (equiv-proof (isEquivAdjT×^ (suc n) (suc k)) y)) =
   fst y , fst (fst (equiv-proof (isEquivAdjT×^ n (k)) (snd y)))
 snd (fst (equiv-proof (isEquivAdjT×^ (suc n) (suc k)) y)) i  =
   fst y , snd (fst (equiv-proof (isEquivAdjT×^ n (k)) (snd y))) i
 fst (snd (equiv-proof (isEquivAdjT×^ (suc n) (suc k)) y) (y' , y'') i) =
   fst (y'' (~ i)) ,
     fst (snd (equiv-proof (isEquivAdjT×^ n (k)) (snd y)) (_ , cong snd y'')
       i)
 snd (snd (equiv-proof (isEquivAdjT×^ (suc n) (suc k)) y) (y' , y'') i) j  =
   fst (y'' (~ i ∨ j)) ,
     snd (snd (equiv-proof (isEquivAdjT×^ n (k)) (snd y)) (_ , cong snd y'')
       i) j

 isEquivAdjT×^ (suc zero) zero = idIsEquiv _
 isEquivAdjT×^ (suc (suc n)) zero = snd Σ-swap-01-≃

 adjT×^≃ : ∀ {n} → ℕ → (A ×^ n) ≃ (A ×^ n)
 adjT×^≃ {n} k = _ , isEquivAdjT×^ n k

 adjT×^≡ : ∀ {n} → ℕ → (A ×^ n) ≡ (A ×^ n)
 adjT×^≡ {zero} x = refl
 adjT×^≡ {suc n} (suc x) = cong (A ×_) (adjT×^≡ {n} x) 
 adjT×^≡ {suc zero} zero = refl
 adjT×^≡ {suc (suc n)} zero = ua (adjT×^≃ zero)
 -- ua (adjT×^≃ zero)


 unglue-adjT×^≡ : ∀ n k →
   PathP (λ i → adjT×^≡ {n = n} k i → A ×^ n)
      (fst (adjT×^≃ k))
      (idfun (A ×^ n))
 unglue-adjT×^≡ zero k _ = idfun _
 unglue-adjT×^≡ (suc n) (suc k) i (x , xs ) =
   x , unglue-adjT×^≡ n k i xs 
 unglue-adjT×^≡ (suc zero) zero _ = idfun _
 unglue-adjT×^≡ (suc (suc n)) zero =
   ua-ungluePathExt (adjT×^≃ {n = (suc (suc n))} zero)
   
 adjT×^≡-≡-ua : ∀ n k → adjT×^≡ {n} k ≡ ua (adjT×^≃ {n} k)
 adjT×^≡-≡-ua zero k = sym (uaIdEquiv)
 adjT×^≡-≡-ua (suc n) (suc k) =
   isInjectiveTransport (funExt λ _ →
    ΣPathP (refl , funExt⁻ (cong transport (adjT×^≡-≡-ua n k)) _))
 adjT×^≡-≡-ua (suc zero) zero = sym (uaIdEquiv)
 adjT×^≡-≡-ua (suc (suc n)) zero = refl

 glueAdjT× : ∀ n k → PathP (λ i → A ×^ n → adjT×^≡ {n = n} k i)
                         (idfun (A ×^ n))
                         (fst (adjT×^≃ k))
 glueAdjT× zero k = refl
 glueAdjT× (suc n) (suc k) i (x , xs) = x , glueAdjT× n k i xs
 glueAdjT× (suc zero) zero = refl
 glueAdjT× (suc (suc n)) zero =
   ua-gluePathExt (adjT×^≃ {n = (suc (suc n))} zero)

 glueAdjT×≃ : ∀ n k → PathP (λ i → A ×^ n ≃ adjT×^≡ {n = n} k i)
                         (idEquiv _)
                         (adjT×^≃ k)
 fst (glueAdjT×≃ n k i) = glueAdjT× n k i
 snd (glueAdjT×≃ n k i) =
   isProp→PathP
     (λ i → isPropIsEquiv (glueAdjT× n k i))
      (idIsEquiv _)
      (snd (adjT×^≃ k))
       i

 glue'AdjT× : ∀ n k → PathP (λ i → A ×^ n → adjT×^≡ {n = n} k i)
                         (fst (adjT×^≃ k))
                         (idfun (A ×^ n))
                         
 glue'AdjT× zero k = refl
 glue'AdjT× (suc n) (suc k) i (x , xs) = x , glue'AdjT× n k i xs
 glue'AdjT× (suc zero) zero = refl
 glue'AdjT× (suc (suc n)) zero i x =
   glue
     (λ { (i = i0) → _ ; (i = i1) → _ })
     (invol-adjT×^ (suc (suc n)) zero x i)

 glue'AdjT×≃ : ∀ n k → PathP (λ i → A ×^ n ≃ adjT×^≡ {n = n} k i)
                         (adjT×^≃ k)
                         (idEquiv _)
                         
 fst (glue'AdjT×≃ n k i) = glue'AdjT× n k i
 snd (glue'AdjT×≃ n k i) =
   isProp→PathP
     (λ i → isPropIsEquiv (glue'AdjT× n k i))
      (snd (adjT×^≃ k))
      (idIsEquiv _)
       i

 
 ΣTePathP' : ∀ {ℓ ℓ'} → {A : I → Type ℓ'}
            → (Te₀ : Σ (Type ℓ) λ T → T ≃ A i0)
              (Te₁ : Σ (Type ℓ) λ T → T ≃ A i1)
            → (T : fst Te₀ ≡ fst Te₁)
            → PathP (λ i → T i → A i) (fst (snd Te₀)) (fst (snd Te₁))
            → PathP (λ i → Σ (Type ℓ) λ T → T ≃ A i)
                Te₀
                Te₁
 ΣTePathP' Te₀ Te₁ T f =
   ΣPathP (T , equivPathP' _ _ f) 


 cong-Σ-swap-01-invol : ∀ {ℓ'} {B₀ B₁ : Type ℓ'} → (p : B₀ ≡ B₁)
    → symP (cong-Σ-swap-01 (sym p)) ≡ cong-Σ-swap-01 p 
 cong-Σ-swap-01-invol p =
   congP₃ (λ j → 𝑮)
     (equivPathP (λ j x → glue (λ { (j = i0) → _ ; (j = i1) → _
                              }) (swap-01 x)) _ _ )
      
      (λ j i → (ua (Σ-swap-01-≃ {A = A} {A} {p i}) j))
      ((equivPathP (λ j x → glue (λ { (j = i0) → _ ; (j = i1) → _ }) x) _ _ ))
                              
         
 unglue'AdjT× : ∀ n k → PathP (λ i → adjT×^≡ {n = n} k i → A ×^ n)        
                         (fst (adjT×^≃ k))
                         (idfun (A ×^ n))
 unglue'AdjT× zero k = refl
 unglue'AdjT× (suc n) (suc k) i (x , xs) = x , unglue'AdjT× n k i xs
 unglue'AdjT× (suc zero) zero = refl
 unglue'AdjT× (suc (suc n)) zero i =
  
    (ua-ungluePathExt (adjT×^≃ {n = (suc (suc n))} zero)) i


 unglueAdjT× : ∀ n k → PathP (λ i → adjT×^≡ {n = n} k i → A ×^ n)
                         (idfun (A ×^ n))
                         (fst (adjT×^≃ k))
                         
 unglueAdjT× zero k = refl
 unglueAdjT× (suc n) (suc k) i (x , xs) = x , unglueAdjT× n k i xs
 unglueAdjT× (suc zero) zero = refl
 unglueAdjT× (suc (suc n)) zero i =
   adjT×^ {(suc (suc n))} zero ∘
    (ua-ungluePathExt (adjT×^≃ {n = (suc (suc n))} zero)) i

 -- unglueAdjT×≃ : ∀ n k → PathP (λ i → adjT×^≡ {n = n} k i ≃ A ×^ n)
 --                         (idEquiv _)
 --                         (adjT×^≃ k)
 -- unglueAdjT×≃ n k = {!!}


 unglueAdjT×≃ : ∀ n k → PathP (λ i → adjT×^≡ {n = n} k i ≃ A ×^ n)
                         (idEquiv _)
                         (adjT×^≃ k)
 fst (unglueAdjT×≃ n k i) = unglueAdjT× n k i
 snd (unglueAdjT×≃ n k i) =
   isProp→PathP
     (λ i → isPropIsEquiv (unglueAdjT× n k i))
      (idIsEquiv _)
      (snd (adjT×^≃ k)) i


 unglue'AdjT×≃ : ∀ n k → PathP (λ i → adjT×^≡ {n = n} k i ≃ A ×^ n)
                         (adjT×^≃ k)
                         (idEquiv _)
                         
 fst (unglue'AdjT×≃ n k i) = unglue'AdjT× n k i
 snd (unglue'AdjT×≃ n k i) =
   isProp→PathP
     (λ i → isPropIsEquiv (unglue'AdjT× n k i))
      (snd (adjT×^≃ k))
      (idIsEquiv _) i


 glue-unglue-AdjT× : ∀ n k → ∀ i → 
    unglueAdjT× n k i ∘ glueAdjT× n k i ≡ idfun _
 glue-unglue-AdjT× zero k i = refl
 glue-unglue-AdjT× (suc n) (suc k) i j (x , xs) =
   x , glue-unglue-AdjT× n k i j xs
 glue-unglue-AdjT× (suc zero) zero i = refl
 glue-unglue-AdjT× (suc (suc n)) zero i = refl

 -- adjT×^≡-invol-sides0 :
 --   ∀ i j → Partial (j ∨ ~ j)
 --     (Σ-syntax (Type ℓ) (λ T → T ≃ ua (adjT×^≃ {2 + n} zero) i ))
 -- adjT×^≡-invol-sides0 {n} i j =
 --       λ {  (j = i0) → A ×^ (2 + n) ,
 --         glueAdjT× (2 + n) zero i ∘ adjT×^ zero ,
 --         isProp→PathP' (λ i → isPropIsEquiv
 --           (glueAdjT× (2 + n) zero i ∘ adjT×^ {n = 2 + n} zero))
 --            (isEquivAdjT×^ (2 + n) zero) (idIsEquiv _) i
 --       ; (j = i1) → A ×^ (2 + n) ,
 --         glueAdjT× (2 + n) zero i ,
 --         isProp→PathP' (λ i → isPropIsEquiv
 --           (glueAdjT× (2 + n) zero i))
 --            (idIsEquiv _)
 --            (isEquivAdjT×^ (2 + n) zero) i }




 adjT×^≡-invol : ∀ n k → adjT×^≡ {n = n} k ≡
                         sym (adjT×^≡ {n = n} k) 
 adjT×^≡-invol zero k = refl
 adjT×^≡-invol (suc n) (suc k) i j =
    A × adjT×^≡-invol n k i j
 adjT×^≡-invol (suc zero) zero = refl
 adjT×^≡-invol (suc (suc n)) zero =
   Σ-swap-01-≡-invol-ua   
  -- Glue (adjT×^≡ {n = suc (suc n)} zero i)
  --   (adjT×^≡-invol-sides0 i j) 



 adjT×^≡-invol-glue : ∀ n l →
   SquareP (λ i j → A ×^ n → adjT×^≡-invol n l j (~ i))
     (λ _ x → x)
     (λ _ → adjT×^ {n = n} l)
     (symP (glue'AdjT× n l))
     (glueAdjT× n l)
 adjT×^≡-invol-glue zero l = refl
 adjT×^≡-invol-glue (suc n) (suc l) i j (a , x) =
   a , adjT×^≡-invol-glue n l i j x
 adjT×^≡-invol-glue (suc zero) zero = refl
 adjT×^≡-invol-glue (suc (suc n)) zero i j =
   Σ-swap-01-≡-invol-ua-glue j (~ i) ∘ swap-01 

 adjT×^≡-invol-glue' : ∀ n l →
    SquareP (λ i j → A ×^ n → adjT×^≡-invol n l j (~ i))      
      (λ _ → adjT×^ {n = n} l)
      (λ _ x → x)
      (symP (glueAdjT× n l))
      (glue'AdjT× n l)
 adjT×^≡-invol-glue' zero l = refl
 adjT×^≡-invol-glue' (suc n) (suc l) i j (a , x) =
   a , adjT×^≡-invol-glue' n l i j x
 adjT×^≡-invol-glue' (suc zero) zero = refl
 adjT×^≡-invol-glue' (suc (suc n)) zero i j =
   Σ-swap-01-≡-invol-ua-glue j (~ i) 


 adjT×^≡-invol-unglue : ∀ n l →
   SquareP (λ i j → adjT×^≡-invol n l j (~ i) → A ×^ n)
     (λ _ x → x)
     (λ _ → adjT×^ {n = n} l)
     (symP (unglue'AdjT× n l))
     (unglueAdjT× n l)
 adjT×^≡-invol-unglue zero l = refl
 adjT×^≡-invol-unglue (suc n) (suc l) i j (a , x) =
   a , adjT×^≡-invol-unglue n l i j x

 adjT×^≡-invol-unglue (suc zero) zero = refl
 adjT×^≡-invol-unglue (suc (suc n)) zero i j =
   swap-01 ∘ unglue (j ∨ ~ j) ∘ unglue (i ∨ ~ i)

 adjT×^≡-invol-unglue' : ∀ n l →
   SquareP (λ i j → adjT×^≡-invol n l j (~ i) → A ×^ n)
     
     (λ _ → adjT×^ {n = n} l)
     (λ _ x → x)
     (symP (unglueAdjT× n l))
     (unglue'AdjT× n l)
 adjT×^≡-invol-unglue' zero l = refl
 adjT×^≡-invol-unglue' (suc n) (suc l) i j (a , x) =
   a , adjT×^≡-invol-unglue' n l i j x
 adjT×^≡-invol-unglue' (suc zero) zero = refl
 adjT×^≡-invol-unglue' (suc (suc n)) zero i j =
   unglue (j ∨ ~ j) ∘ unglue (i ∨ ~ i)

 biAdjT×^≡<-A : ∀ {n} → (Σ _ ((_< n) ∘ suc ∘ suc)) → 
    ((A ×^ (n) ≃ A ×^ (n))) × (A ×^ (n) ≡ A ×^ (n))
 biAdjT×^≡<-A {suc n} (zero , k<) = ≃-× (idEquiv A) (adjT×^≃ {n} zero) , refl
 biAdjT×^≡<-A {suc n} (suc k , k<) = idEquiv _ , adjT×^≡ {suc n} (suc (suc k))



 biAdjT×^≡< : ∀ {n} → (Σ _ ((_< n) ∘ suc ∘ suc))  → (A ×^ n) ≡ (A ×^ n)
 biAdjT×^≡< {n} k = uncurry 𝑮 (biAdjT×^≡<-A {n} k) (adjT×^≃ {n} zero)


 glueBiAdjT×< : ∀ n → PathP (λ i → A ×^ (3 + n) →
                     biAdjT×^≡< {n = 3 + n} (zero , tt) i)
                         (map-snd swap-01)
                         swap-01
                         
                         
 glueBiAdjT×< n i (x , x' , x'' , xs) =
    glue (λ { (i = i0) → x , x'' , x' , xs
            ; (i = i1) → x' , x , x'' , xs
           }) (x , x' , x'' , xs)

 glueBiAdjT×<SS' : ∀ n k → PathP (λ i → A ×^ (2 + n) →
                      biAdjT×^≡< {n = suc (suc n)}
                        (suc (fst k) , snd k) i)
                          (adjT×^ {n = 2 + n} (suc (suc (fst k))))
                          swap-01


 glueBiAdjT×<SS' n (k , k<) i (x , x' , xs) =     
     glue (λ { (i = i0) → x , x' , adjT×^ k (xs)
             ; (i = i1) → x' , x ,  xs 
            }) (x , x' , glue'AdjT× n k i xs)

 glueBiAdjT×<SS : ∀ n k → PathP (λ i →
                       adjT×^≡ {n = suc (suc n)} (suc (suc (fst k))) i →
                      biAdjT×^≡< {n = suc (suc n)}
                        (suc (fst k) , snd k) i)
                          (idfun _)
                          swap-01


 glueBiAdjT×<SS n (k , k<) = symP (glue-Σ-swap-01 (symP (adjT×^≡ k)))      
     -- glue (λ { (i = i0) → x , x' , xs
     --         ; (i = i1) → x' , x ,  xs 
     --        }) (x , x' , xs)




 biAdjT×^≡ : ∀ {n} → Fin₋₁ n → Fin₋₁ n → (A ×^ n) ≡ (A ×^ n)
 biAdjT×^≡ {n} (zero , k<) (zero , l<) = refl
 biAdjT×^≡ {n} (zero , k<) (suc l , l<) = sym (biAdjT×^≡< (l , l<))
 biAdjT×^≡ {n} (suc k , k<) (zero , l<) = biAdjT×^≡< (k , k<)
 biAdjT×^≡ {suc n} (suc k , k<) (suc l , l<) =
   cong (A ×_) (biAdjT×^≡ {n} (k , k<) (l , l<))
 


 unglueBiAdjT× : ∀ n k l → PathP (λ i → biAdjT×^≡ {n = n} k l i → A ×^ n)
                         (fst (adjT×^≃ (fst k)))
                         (fst (adjT×^≃ (fst l)))
 unglueBiAdjT× (n) (zero , k<) (zero , l<) = refl                         
 unglueBiAdjT× (suc n) (suc k , k<) (suc l , l<) i (x , xs) =
   x , unglueBiAdjT× n (k , k<) (l , l<) i xs
 unglueBiAdjT× (suc n) (zero , k<) (suc zero , l<) i = unglue (i ∨ ~ i)
 unglueBiAdjT× (suc n) (zero , k<) (suc (suc l) , l<) i =
   (unglue'AdjT× (suc n) (suc (suc l)) (~ i)) ∘' (unglue (i ∨ ~ i))
 unglueBiAdjT× (suc n) (suc zero , k<) (zero , l<) i = unglue (i ∨ ~ i)    
 unglueBiAdjT× (suc n) (suc (suc k) , k<) (zero , l<) i =
   (unglue'AdjT× (suc n) (suc (suc k)) i) ∘' (unglue (i ∨ ~ i))

 -- glueBiAdjT× : ∀ n k l → PathP (λ i → A ×^ n → biAdjT×^≡ {n = n} k l i)
 --                         (fst (adjT×^≃ (fst l)))
 --                         (fst (adjT×^≃ (fst k)))
                         
 -- glueBiAdjT× n k l = {!!}
 
 biAdjT×^≡-comp< : ∀ {n} → (k : ℕ) → (k< : suc (suc k) < n) (l< : 1 < n) →
    Square
      (adjT×^≡ {n} (suc k))
      (adjT×^≡ {n} zero)
      (biAdjT×^≡ {n} (suc k , k<) (zero , l<))
      refl
 biAdjT×^≡-comp< {suc (suc n)} (suc k) k< l< i j = 
      Glue (adjT×^≡ {suc (suc n)} (suc (suc k)) (i ∨ j)) (λ {
           (i = i1)(j = i0) → _ , adjT×^≃ {2 + n} zero
         ; (i = i0) →  _ , idEquiv _
         ; (j = i1) → _ , idEquiv _
         })
 biAdjT×^≡-comp< {suc (suc (suc n))} zero k< l< =
   Σ-swap-012-≡-comp-ua refl


 glue-biAdjT×^≡-comp<SS :
   ∀ {n} → (k : ℕ) → (k< : suc (suc (suc k)) < (suc (suc n)))
       (l< : 1 < (suc (suc n))) →
     SquareP
       (λ i j → adjT×^≡ {suc (suc n)} (suc (suc k)) (i ∨ j) →
           biAdjT×^≡-comp< {suc (suc n)} (suc k) k< l< i j)
        (λ _ x → x)
        (glue'AdjT× (2 + n) zero)
        (glueBiAdjT×<SS n (k , k<))
        λ _ x → x
 glue-biAdjT×^≡-comp<SS k k< l< i j x =
   glue  (λ {
           (i = i1)(j = i0) → swap-01 x
         ; (i = i0) → x
         ; (j = i1) → x
         }) x

 glue-biAdjT×^≡-comp<SS' :
   ∀ {n} → (k : ℕ) → (k< : suc (suc (suc k)) < (suc (suc n)))
       (l< : 1 < (suc (suc n))) →
     SquareP
       (λ i j → A × A × (A ×^ n) →
           biAdjT×^≡-comp< {suc (suc n)} (suc k) k< l< i j)
        (glue'AdjT× (suc (suc n)) (suc (suc k)))
        (glue'AdjT× (2 + n) zero)
        (glueBiAdjT×<SS' n (k , k<))
        λ _ x → x
 glue-biAdjT×^≡-comp<SS' {n = n} k k< l< i j x' =
  let x = glue'AdjT× (suc (suc n)) (suc (suc k)) (i ∨ j) x'
  in glue  (λ {
           (i = i1)(j = i0) → swap-01 x
         ; (i = i0) → x
         ; (j = i1) → x
         }) x


 -- glue-biAdjT×^≡-comp<SS :
 --    ∀ {n} → (k : ℕ) → (k< : suc (suc (suc k)) < (suc (suc n)))
 --       (l< : 1 < (suc (suc n))) →
 --      SquareP
 --        (λ i j → A × A × (A ×^ n) →
 --           biAdjT×^≡-comp< {suc (suc n)} (suc k) k< l< i j)
 --         (congP (λ i → map-× (idfun _) ∘ map-× (idfun _))
 --           (glue'AdjT× n k))
 --         (glue'AdjT× (2 + n) zero)
 --         (glueBiAdjT×<SS' n (k , k<))
 --         refl
 -- glue-biAdjT×^≡-comp<SS {n = n} k k< l< i j = {!!}
 --   glue
 --     ((λ {
 --           (i = i1)(j = i0) → _
 --         ; (i = i0) → _
 --         ; (j = i1) → _
 --         }))
 --     (x , x' , glue'AdjT× n k (i ∨ j) xs)




 biAdjT×^≡-comp : ∀ {n} → (k l : Fin₋₁ n) →
    Square
      (adjT×^≡ {n} (fst k))
      (adjT×^≡ {n} (fst l))
      (biAdjT×^≡ {n} k l)
      refl
 biAdjT×^≡-comp {n} (zero , k<) (zero , l<) = refl
 biAdjT×^≡-comp {n} (zero , k<) (suc l , l<) = 
  symP (biAdjT×^≡-comp<  {n} l l< k< )
 biAdjT×^≡-comp {n} (suc k , k<) (zero , l<) = 
  biAdjT×^≡-comp<  {n} k k< l<

 biAdjT×^≡-comp {suc n} (suc k , k<) (suc l , l<) =
   congSq (A ×_) (biAdjT×^≡-comp {n} (k , k<) (l , l<))
 

 -- biAdjT×^≡-comm< : ∀ n l l< →
 --    Square refl refl (λ i → biAdjT×^≡< {n = (suc n)} (l , l<) (~ i))
 --                     (biAdjT×^≡< (l , l<))
 -- biAdjT×^≡-comm< (suc (suc n)) zero l< = 
 --   flipSquare {!!}
 -- -- i j = adjT×^≡-invol {!2 + n!} zero (~ j) i 
 -- biAdjT×^≡-comm< (suc n) (suc l) l< = {!!}
 
 biAdjT×^≡-comm : ∀ {n} → (k l : Fin₋₁ n) → (x : commT (fst k) (fst l)) →
    Square
      refl
      refl
      (biAdjT×^≡ {n} k l)
      (biAdjT×^≡ {n} l k)
 biAdjT×^≡-comm {suc n} (suc k , k<) (suc l , l<) x i j =
   A × biAdjT×^≡-comm {n} (k , k<) (l , l<) (pred-commT k l x) i j
 biAdjT×^≡-comm {suc (suc n)} (zero , k<) (suc (suc l) , l<) x  =
   flipSquare
      (congP₃ (λ j → 𝑮)
     (equivPathP (λ j x → glue (λ { (j = i0) → _ ; (j = i1) → _
                              }) (x)) _ _ )
      
      (λ j i → (ua (Σ-swap-01-≃ {A = A} {A} {adjT×^≡-invol (n) l j (~ i)}) j))
      ((equivPathP (λ j x → glue (λ { (j = i0) → _ ; (j = i1) → _ }) (swap-01 x)) _ _ )))


 glue-biAdjT×^≡-comm : ∀ {n} → (l : Fin₋₁ n) →
    SquareP (λ i j →
          A × A × (adjT×^≡-invol n ((fst l)) (j) (~ i))
           
          -- adjT×^≡ {n = (suc (suc (suc n)))} (suc (suc (fst l))) (j)
          → 
          biAdjT×^≡-comm {n = (suc (suc n))}
       (zero , _) (suc (suc (fst l)) , snd l) _ i j)
        (refl {x = λ x → fst x , fst (snd x) , snd (snd x)}) 
        (refl {x = λ x → fst (snd x) , fst x , snd (snd x)})
        (λ i → glueBiAdjT×<SS n ((fst l) , snd l) (~ i) ∘ swap-01)
        (λ i → glueBiAdjT×<SS n ((fst l) , snd l) (i))
 glue-biAdjT×^≡-comm {n} (l , l<) i j x =
    glue (λ {(i = i0) → _ ;(i = i1) → _ })
   (glue (λ {(j = i0) → _ ;(j = i1) → _ }) x)


 

 adjT×^≡-braid : ∀ {n} → ∀ k k< →
    Square
      (adjT×^≡ {n} (suc k))
      (adjT×^≡ {n} k)
      (biAdjT×^≡ {n} (k , <-weaken {n = n} k<) (suc k , k<))
      (biAdjT×^≡ {n} (k , <-weaken {n = n} k<) (suc k , k<))
 adjT×^≡-braid {suc n} (suc k) k< = 
  congSq (A ×_) (adjT×^≡-braid {n} k k<)
 adjT×^≡-braid {suc (suc (suc n))} zero k< =
  let z = ua (adjT×^≃ {3 + n} 0 ∙ₑ adjT×^≃ {3 + n} 1 ∙ₑ adjT×^≃ {3 + n} 0) 
  in flipSquare
    ( (congP₂ (λ i → 𝑮-refl {B = z i})
          (equivPathP' _ _ λ i → (λ (x , x' , x'' , x''') →
             glue (λ {(i = i0) → _ ;(i = i1) → _ }) (x' , x , x'' , x'''))
                     ∘' map-snd (ua-ungluePathExt (adjT×^≃ {2 + n} 0) i))
          (equivPathP' _ _  λ i → (λ (x , x' , x'' , x''') →
             glue (λ {(i = i0) → _ ;(i = i1) → _ }) (x , x'' , x' , x'''))
                     ∘' ua-ungluePathExt (adjT×^≃ {3 + n} 0) i)))

 glue-adjT×^≡-braid : ∀ {n} →
    SquareP (λ i j →
      ua (adjT×^≃ {3 + n} 0 ∙ₑ adjT×^≃ {3 + n} 1 ∙ₑ adjT×^≃ {3 + n} 0) j
        →
        adjT×^≡-braid {3 + n} zero _ i j)
     -- (λ j → {!!})
     (λ j →
       map-snd (ua-gluePathExt (adjT×^≃ zero) j) ∘' ua-unglue
         (adjT×^≃ {3 + n} 0 ∙ₑ adjT×^≃ {3 + n} 1 ∙ₑ adjT×^≃ {3 + n} 0) j
          )
     (λ j → 
       ua-gluePathExt (adjT×^≃ zero) j ∘' rot-120 ∘'
         ua-unglue
           (adjT×^≃ {3 + n} 0 ∙ₑ adjT×^≃ {3 + n} 1 ∙ₑ adjT×^≃ {3 + n} 0) j
           )
     (λ i → glueBiAdjT×< n (~ i) ∘' rot-120)
     λ i → glueBiAdjT×< n (~ i) ∘' rot-201
 glue-adjT×^≡-braid i j xG =
  let (x , x' , x'' , z) = unglue (j ∨ ~ j) xG
  in glue
     (λ {(i = i0) →
            _ , glue (λ {(j = i0) → _ ;(j = i1) → _ }) (x'' , x' , z)
        ;(i = i1) →
         (glue (λ {(j = i0) → _ ;(j = i1) → _ }) (x'' , x' , x , z))
        }) (glue (λ {(j = i0) → _ ;(j = i1) → _ }) (x'' , x , x' , z))

module hex (A : Type ℓ) (B : Type ℓ) where

 hexSq : Square {A = Type ℓ}
           (λ i₁ →  A × ua (Σ-swap-01-≃ {A = A} {A} {B}) i₁)
           (ua Σ-swap-01-≃)           
           (𝑮 Σ-swap-01-≃ (λ _ → A × A × A × B)
             (≃-× (idEquiv A) Σ-swap-01-≃))
           (𝑮  Σ-swap-01-≃ (λ _ → A × A × A × B)
            (≃-× (idEquiv A) Σ-swap-01-≃))
 hexSq = 
   let z = ua (≃-× (idEquiv A) Σ-swap-01-≃
             ∙ₑ (Σ-swap-01-≃ {A = A} {A} {A × B})
             ∙ₑ ≃-× (idEquiv A) Σ-swap-01-≃)
   in flipSquare
       (congP₂ (λ i → 𝑮-refl {B = z i})
          (equivPathP' _ _ λ i → (λ (x , x' , x'' , x''') →
             glue (λ {(i = i0) → _ ;(i = i1) → _ }) (x' , x , x'' , x'''))
                     ∘' map-snd (ua-ungluePathExt (Σ-swap-01-≃) i))
          (equivPathP' _ _  λ i → (λ (x , x' , x'' , x''') →
             glue (λ {(i = i0) → _ ;(i = i1) → _ }) (x , x'' , x' , x'''))
                     ∘' ua-ungluePathExt (Σ-swap-01-≃) i))


Glue' : ∀ {ℓ ℓ'} → (A : Type ℓ) {φ : I}
       → (f : Partial φ (Σ (Type ℓ') λ T → T → A))
       → PartialP φ (λ o → isEquiv (snd (f o))) 
      → Type ℓ'
Glue' A Tf x = Glue A λ o → fst (Tf o) , (snd (Tf o) , x o) 

-- GlueCube : ∀ {ℓ} →
--   {a₀₀₀ a₀₀₁ : Type ℓ} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
--   {a₀₁₀ a₀₁₁ : Type ℓ} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
--   {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
--   (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
--   {a₁₀₀ a₁₀₁ : Type ℓ} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
--   {a₁₁₀ a₁₁₁ : Type ℓ} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
--   {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
--   (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
--   {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
--   (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
--   {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
--   (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
--   (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
--   (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
--   → (A' : I → I → I → Type ℓ)
--   → (∀ i j jj →
--       PartialP {ℓ} (i ∨ ~ i ∨ j ∨ ~ j ∨ jj ∨ ~ jj)
--          λ { (i = i0) → a₀₋₋ j jj → A' i j jj
--            ; (i = i1) → a₁₋₋ j jj → A' i j jj
--            ; (j = i0) → a₋₀₋ i jj → A' i j jj
--            ; (j = i1) → a₋₁₋ i jj → A' i j jj
--            ; (jj = i0) → a₋₋₀ i j → A' i j jj
--            ; (jj = i1) → a₋₋₁ i j → A' i j jj
--            })
--   → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁  
-- GlueCube = {!!}

module _ {ℓ} {A : Type ℓ} where  

  isOfHLevel×^ : ∀ n m → isOfHLevel m A → isOfHLevel m (A ×^ n) 
  isOfHLevel×^ zero m x = isOfHLevelPlus' {n = m} zero isContrUnit*
  isOfHLevel×^ (suc n) m x = isOfHLevel× m x (isOfHLevel×^ n m x)


  lookup : ∀ {n} → A ×^ n → Fin n → A
  lookup {suc n} x₁ (zero , snd₁) = fst x₁
  lookup {suc n} x₁ (suc fst₁ , snd₁) = lookup {n}  (snd x₁) (fst₁ , snd₁)

  tabulate : ∀ {n} → (Fin n → A) → A ×^ n 
  tabulate {zero} x = tt*
  tabulate {suc n} x = x (zero , _) , tabulate {n} (x ∘ sucF)

  Iso-×^-F→ : ∀ n → Iso (A ×^ n) (Fin n → A)
  Iso.fun (Iso-×^-F→ n) = lookup
  Iso.inv (Iso-×^-F→ n) = tabulate
  Iso.rightInv (Iso-×^-F→ zero) b i ()
  Iso.rightInv (Iso-×^-F→ (suc n)) b i (zero , snd₁) = b (zero , _)
  Iso.rightInv (Iso-×^-F→ (suc n)) b i (suc fst₁ , snd₁) =
    Iso.rightInv (Iso-×^-F→ n) (b ∘ sucF) i (fst₁ , snd₁)
  Iso.leftInv (Iso-×^-F→ zero) _ = refl
  fst (Iso.leftInv (Iso-×^-F→ (suc n)) a i) = fst a
  snd (Iso.leftInv (Iso-×^-F→ (suc n)) a i) =
    (Iso.leftInv (Iso-×^-F→ n) (snd a) i)

  injTab : ∀ n → {a b : (Fin n → A)} →
    Iso.inv (Iso-×^-F→ n) a ≡ Iso.inv (Iso-×^-F→ n) b → a ≡ b
  injTab n {a} {b} = isoInvInjective (Iso-×^-F→ n) a b

  repeat : ∀ n → A → A ×^ n
  repeat zero x = tt*
  repeat (suc n) x = x , repeat n x 

  adjT×^-repeat : ∀ n k a →
    adjT×^ {n = n} k (repeat n a) ≡ repeat n a 
  adjT×^-repeat zero k a = refl
  adjT×^-repeat (suc n) (suc k) a =
   cong (a ,_) (adjT×^-repeat n k a)
  adjT×^-repeat (suc zero) zero a = refl
  adjT×^-repeat (suc (suc n)) zero a = refl

allFalse : ∀ n → Bool ×^ n → hProp ℓ-zero
allFalse zero x = L.⊤
allFalse (suc n) (x , xs) =
  if x
  then L.⊥
  else allFalse n xs
-- allFalse (suc n) (x , xs) = (Bool→Prop (not x)) L.⊔  allFalse n xs

Fin×Snd : ∀ n → Bool ×^ n → hProp ℓ-zero
Fin×Snd zero _ = L.⊥ 
Fin×Snd (suc n) (x , xs) =
  if x
  then allFalse n xs
  else Fin×Snd n xs

allFalse∘adjT× : ∀ n k x → ⟨ allFalse n x ⟩ → ⟨ allFalse n (adjT×^ k x) ⟩ 
allFalse∘adjT× zero k x x₁ = x₁
allFalse∘adjT× (suc n) (suc k) (false , xs) = allFalse∘adjT× n k xs 
allFalse∘adjT× (suc zero) zero x x₁ = x₁
allFalse∘adjT× (suc (suc n)) zero (false , false , xs) x₁ = x₁

allFalse∘adjT×≡ : ∀ n k x → ⟨ allFalse n x ⟩ ≡ ⟨ allFalse n (adjT×^ k x) ⟩ 
allFalse∘adjT×≡ zero k x = refl
allFalse∘adjT×≡ (suc n) (suc k) (false , xs) = allFalse∘adjT×≡ n k xs  
allFalse∘adjT×≡ (suc n) (suc k) (true , xs) = refl  
allFalse∘adjT×≡ (suc zero) zero x = refl
allFalse∘adjT×≡ (suc (suc n)) zero (x , false , xs) = refl
allFalse∘adjT×≡ (suc (suc n)) zero (false , true , xs) = refl
allFalse∘adjT×≡ (suc (suc n)) zero (true , true , xs) = refl


Fin×Snd∘adjT× : ∀ n k x → ⟨ Fin×Snd n x ⟩ → ⟨ Fin×Snd n (adjT×^ k x) ⟩
Fin×Snd∘adjT× (zero) _ _ x₁ = x₁
Fin×Snd∘adjT× (suc n) (suc k) (false , xs) = Fin×Snd∘adjT× n k xs
Fin×Snd∘adjT× (suc n) (suc k) (true , xs) = allFalse∘adjT× n k xs
Fin×Snd∘adjT× (suc zero) zero xs x₁ = x₁
Fin×Snd∘adjT× (suc (suc n)) zero (false , x' , xs) x₁ = x₁
Fin×Snd∘adjT× (suc (suc n)) zero (true , false , xs) x₁ = x₁


Fin×Snd∘adjT×≡ : ∀ n k x → ⟨ Fin×Snd n x ⟩ ≡ ⟨ Fin×Snd n (adjT×^ k x) ⟩
Fin×Snd∘adjT×≡ zero _ _ = refl
Fin×Snd∘adjT×≡ (suc n) (suc k) (false , xs) = Fin×Snd∘adjT×≡ n k xs
Fin×Snd∘adjT×≡ (suc n) (suc k) (true , xs) = allFalse∘adjT×≡ n k xs
Fin×Snd∘adjT×≡ (suc zero) zero xs = refl
Fin×Snd∘adjT×≡ (suc (suc n)) zero (false , x' , xs) = refl
Fin×Snd∘adjT×≡ (suc (suc n)) zero (true , x' , xs) = refl


ℕ→Fin× : ∀ n → ℕ → (Bool ×^ n)
ℕ→Fin× zero x = tt*
ℕ→Fin× (suc n) zero = true , repeat _ false
ℕ→Fin× (suc n) (suc k) = false , ℕ→Fin× _ k

Fin×→ℕ : ∀ n → (Bool ×^ n) → ℕ 
Fin×→ℕ zero x = zero
Fin×→ℕ (suc n) (false , xs) = suc (Fin×→ℕ n xs)
Fin×→ℕ (suc n) (true , _) = zero

-- injFin×→ℕ : {!∀ {n} x y → Fin×→ℕ n x ≡ Fin×→ℕ n   !}
-- injFin×→ℕ = {!!}

allFalse-repeat-false : ∀ n → ⟨ allFalse n (repeat n false) ⟩
allFalse-repeat-false zero = tt*
allFalse-repeat-false (suc n) = allFalse-repeat-false n


allFalse→≡repeat-false : ∀ n → ∀ v → ⟨ allFalse n v ⟩ → (repeat n false) ≡ v
allFalse→≡repeat-false zero v x = refl
allFalse→≡repeat-false (suc n) (false , v) x =
  cong₂ _,_ refl (allFalse→≡repeat-false n v x)

allFalse-≡ : ∀ n → ∀ u v
   → ⟨ allFalse n u ⟩ → ⟨ allFalse n v ⟩
   →  u ≡ v
allFalse-≡ zero _ _ _ _ = refl
allFalse-≡ (suc n) (false , us) (false , vs) U V =
  cong (false ,_) (allFalse-≡ n us vs U V)

isContrΣallFalse : ∀ n → isContr (Σ _ (fst ∘ allFalse n))
fst (isContrΣallFalse n) = _ , allFalse-repeat-false n
snd (isContrΣallFalse n) (xs , ys) =
  Σ≡Prop (snd ∘ allFalse n) (allFalse→≡repeat-false n xs ys)


isContr→PathP : {A B : Type ℓ} → (isContr B)
    → (p : A ≡ B)
    → ∀ a b → PathP (λ i → p i) a b
isContr→PathP isContrB p _ _ =
  toPathP (isContr→isProp isContrB _ _)

allFalse-PathP : ∀ n → (A : Type) → ∀ p → (a : A)
              → (b : Σ (Bool ×^ n) (λ x → fst (allFalse n x)))
               → PathP (λ i → p i) a b
allFalse-PathP n A = isContr→PathP {A = A} (isContrΣallFalse n)

ℕ→Fin×-snd : ∀ n k → k < n → ⟨ Fin×Snd n (ℕ→Fin× n k) ⟩ 
ℕ→Fin×-snd (suc n) zero x = allFalse-repeat-false n
ℕ→Fin×-snd (suc n) (suc k) x = ℕ→Fin×-snd n k x

Fin×→ℕ-snd : ∀ n v → ⟨ Fin×Snd n v ⟩ →  (Fin×→ℕ n v) < n 
Fin×→ℕ-snd (suc n) (false , xs) x = Fin×→ℕ-snd n xs x
Fin×→ℕ-snd (suc n) (true , xs) x = tt

sec-ℕ→Fin×-ℕ→Fin× : ∀ n → (v : Bool ×^ n) →
  ⟨ Fin×Snd n v ⟩ → ℕ→Fin× n (Fin×→ℕ n v) ≡ v
sec-ℕ→Fin×-ℕ→Fin× zero v _ = refl
sec-ℕ→Fin×-ℕ→Fin× (suc n) (false , v) p =
 cong₂ _,_ refl (sec-ℕ→Fin×-ℕ→Fin× n v p)
sec-ℕ→Fin×-ℕ→Fin× (suc n) (true , v) p =
 cong₂ _,_ refl (allFalse→≡repeat-false n v p)

ret-ℕ→Fin×-ℕ→Fin× : ∀ n → (k : Fin n) →
      Fin×→ℕ n (ℕ→Fin× n (fst k)) ≡ (fst k)
ret-ℕ→Fin×-ℕ→Fin× (suc n) (zero , snd₁) = refl
ret-ℕ→Fin×-ℕ→Fin× (suc n) (suc k , k<) =
  cong suc (ret-ℕ→Fin×-ℕ→Fin× n (k , k<))


Fin× : ∀ n → Type₀
Fin× n = (Σ _ (fst ∘ Fin×Snd n ))


-- injFin×→ℕ : ∀ {n} x y → Fin×→ℕ n x ≡ Fin×→ℕ n y → x ≡ y  
-- injFin×→ℕ {n} x y x₁ = {!!}


Fin×PathP : ∀ n → (P : (Bool ×^ n) ≡ (Bool ×^ n))
                  (Q : PathP (λ i → P i → Type)
                    (fst ∘ Fin×Snd n) (fst ∘ Fin×Snd n))
    → ∀ {x₀ x₁}
    → ∀ {y₀ y₁}
    → PathP (λ i → P i) x₀ x₁
    → PathP (λ i → Σ (P i) (Q i))
      (x₀ , y₀) (x₁ , y₁)
Fin×PathP n P Q = 
 ΣPathPProp (snd ∘ Fin×Snd n)

Fin×PathP' : ∀ n →
     (P : Path (Σ Type (λ X → X → hProp ℓ-zero))
        (Bool ×^ n , Fin×Snd n)
        (Bool ×^ n , Fin×Snd n))
    → ∀ {x₀ x₁}
    → ∀ {y₀ y₁}
    → PathP (λ i → fst (P i)) x₀ x₁
    → PathP (λ i →
       Σ (fst (P i)) (fst ∘' snd (P i))) (x₀ , y₀) (x₁ , y₁)
Fin×PathP' n P = 
  ΣPathPProp (snd ∘ Fin×Snd n)

sucFin× : Fin× n → Fin× (suc n)
sucFin× (xs , ys) = (false , xs) , ys

Fin×0 : Fin× (suc n)
Fin×0 {n} = (true , repeat _ false) , allFalse-repeat-false n

Fin×cases : ∀ {ℓ} {A : Type ℓ} → A → (Fin× n → A) → Fin× (suc n) → A
Fin×cases _ f ((false , xs) , ys) = f (xs , ys)
Fin×cases a _ ((true , _) , _) = a


-- Fin×casesβ : {!!}
-- Fin×casesβ = {!!}

Fin×elim : ∀ {ℓ} {A : Fin× (suc n) → Type ℓ}
                    → (∀ x y → A ((true , x) , y))
                      → ((x : Fin× n) → A (sucFin× x))
                    → ∀ x → A x
Fin×elim _ f ((false , xs) , ys) = f (xs , ys)
Fin×elim a _ ((true , _) , _) = a _ _


Fin×elimFunExt : ∀ {ℓ} {A : Type ℓ}
                    {f : Fin× n → A} {a : A}
                    {f' : Fin× (suc n) → A}
                    → (a ≡ f' Fin×0)
                    → (f ≡ f' ∘' sucFin×)
                    → Fin×cases a f ≡ f'
Fin×elimFunExt x x₁ i ((false , xs) , ys)  = x₁ i (xs , ys)
Fin×elimFunExt {n = n} {f' = f'} x x₁ i ((true , z) , zz) =
  hcomp (λ j →
         λ { (i = i0) → x i0
           ; (i = i1) →  f'
             (Fin×PathP (suc n) refl refl
                {fst Fin×0} {true , z} {snd (Fin×0 {n = suc n})} {zz}
                 (cong (true ,_)
                   (allFalse→≡repeat-false n _ zz)) j)
           }) (x i)

Fin×0= : ∀ n → ∀ {x x' y y'} → Path (Fin× (suc n))
           ((true , x) , y)
           ((true , x') , y')
Fin×0= n {x} {x'} {y} {y'} =
  cong′ (λ (x , y) → (true , x) , y)
    (allFalse-PathP n _ refl (x , y) (x' , y')) 


-- Fin×cases f0 (Fin×cases f1 f)

isSetFin× : ∀ n → isSet (Fin× n)
isSetFin× n = isSetΣ (isOfHLevel×^ n 2 isSetBool)
  (isProp→isSet ∘ snd ∘ Fin×Snd n)

IsoFinFin× : ∀ n → Iso (Fin n) (Fin× n)
Iso.fun (IsoFinFin× n) (x , y) = ℕ→Fin× n x , ℕ→Fin×-snd n x y
Iso.inv (IsoFinFin× n) (x , y) = Fin×→ℕ n x , Fin×→ℕ-snd n x y
Iso.rightInv (IsoFinFin× n) b =
  Σ≡Prop (snd ∘ Fin×Snd n)
  (uncurry (sec-ℕ→Fin×-ℕ→Fin× n) b)
Iso.leftInv (IsoFinFin× n) a =
  ≡Fin {n = n} (ret-ℕ→Fin×-ℕ→Fin× n a)



F×adjT : ∀ {n} → ℕ → (Fin× n) → (Fin× n)
F×adjT k (x , y) = adjT×^ k x , Fin×Snd∘adjT× _ k x y

F×adjT≃ : ∀ {n} → ℕ → (Fin× n) ≃ (Fin× n)
F×adjT≃ {n} k =
   Σ-cong-equiv-prop (adjT×^≃ k)
     (snd ∘ (Fin×Snd n))
     (snd ∘ (Fin×Snd n))
     (Fin×Snd∘adjT× n k)
     λ a → subst (fst ∘ Fin×Snd n) (invol-adjT×^ n k a)
       ∘ (Fin×Snd∘adjT× n k ∘ adjT×^ k) a


sucFin-F×adjT : ∀ n k →
     sucFin× ∘' F×adjT {n = n} k
   ≡ F×adjT {n = suc n} (suc k) ∘' sucFin× 
sucFin-F×adjT n k = refl

look× :  ∀ {ℓ} {A : Type ℓ} → A ×^ n → Fin× n → A
look× v = lookup v ∘ Iso.inv (IsoFinFin× _) 

lookTy :  ∀ {ℓ} → (Type ℓ) ×^ n → Bool ×^ n → Type ℓ
lookTy {zero} _ _ = Unit*
lookTy {suc n} (Ty , Tys) (b , bs) =
  (if b then Ty else Unit*) × lookTy {n} (Tys) (bs)


⊎^ : ∀ {ℓ} {n} → (Type ℓ) ×^ n → Type ℓ
⊎^ {n = n} S = Σ (Fin× n) (lookTy S ∘ fst)

⊎^' : ∀ {ℓ} {n} → (Bool ×^ n → Bool ×^ n) → (Type ℓ) ×^ n → Type ℓ
⊎^' {n = n} f S = Σ (Σ _ (fst ∘ Fin×Snd n ∘ f)) (lookTy S ∘ fst)


M⊎^ : ∀ {ℓ} {n} → (Type ℓ) ×^ n → Type ℓ
M⊎^ {n = n} S = Σ (_) (lookTy S)


Iso-⊎ : ∀ {ℓ} {A B : Type ℓ} →
    Iso (⊎^ {n = 2} (A , B , _))
        (A ⊎ B)
Iso.fun Iso-⊎ = uncurry
  (Fin×elim (λ _ _ (x , _) → inl x)
   (Fin×elim (λ _ _ (_ , x , _) → inr x)
    λ ()) )
Iso.inv Iso-⊎ (inl x) = Fin×0 , (x , _)
Iso.inv Iso-⊎ (inr x) = sucFin× Fin×0 , _ , x , _
Iso.rightInv Iso-⊎ (inl x) = refl
Iso.rightInv Iso-⊎ (inr x) = refl
Iso.leftInv Iso-⊎ (((false , true , snd₃) , snd₂) , snd₁) = refl
Iso.leftInv Iso-⊎ (((true , false , snd₃) , snd₂) , snd₁) = refl

--not that interesting
Iso-swap⊎^ : ∀ {ℓ} {A B : Type ℓ} →
    Iso (⊎^ {n = 2} (A , B , _))
        (⊎^' {n = 2} (swap-01) (B , A , _))
Iso.fun Iso-swap⊎^ ((x , y) , u) = ((swap-01 x , y)) , swap-01 u
Iso.inv Iso-swap⊎^ ((x , y) ,  u) = ((swap-01 x , y)) , swap-01 u
Iso.rightInv Iso-swap⊎^ _ = refl
Iso.leftInv Iso-swap⊎^ _ = refl

F×adjTP' : ∀ {n} k → PathP (λ i → adjT×^≡ {A = Bool} {n = n} k i → Type)
             (fst ∘ (allFalse n))
             (fst ∘ (allFalse n))
F×adjTP' {zero} k = refl
F×adjTP' {suc n} (suc k) i (false , xs) = F×adjTP' {n} k i xs
F×adjTP' {suc n} (suc k) i (true , xs) = ⊥
F×adjTP' {suc zero} zero = refl
F×adjTP' {suc (suc n)} zero i x =
  allFalse∘adjT×≡ (suc (suc n)) zero
    (unglueAdjT× (suc (suc n)) zero i x) i

F×adjTP : ∀ {n} k → PathP (λ i → adjT×^≡ {A = Bool} {n = n} k i → Type)
             (fst ∘ (Fin×Snd n))
             (fst ∘ (Fin×Snd n))
F×adjTP {zero} k = refl
F×adjTP {suc n} (suc k) i (false , xs) = F×adjTP {n} k i xs
F×adjTP {suc n} (suc k) i (true , xs) = F×adjTP' {n} k i xs
F×adjTP {suc zero} zero = refl
F×adjTP {suc (suc n)} zero i x =
    Fin×Snd∘adjT×≡ (suc (suc n)) zero
    (unglueAdjT× (suc (suc n)) zero i x) i


isPropF×adjTP' : ∀ {n} k →
    PathP (λ i → ∀ x → isProp (F×adjTP' {n = n} k i x))
             (snd ∘ allFalse n)
             (snd ∘ allFalse n)
isPropF×adjTP' {n} k = isProp→PathP {ℓ = ℓ-zero} {B = λ i →
       ∀ x → isProp (F×adjTP' {n} (k) i x)}
     (λ i → isPropΠ λ _ → isPropIsProp)
      (snd ∘ (allFalse n)) (snd ∘ (allFalse n))


isPropF×adjTP : ∀ {n} k →
    PathP (λ i → ∀ x → isProp (F×adjTP {n = n} k i x))
             (snd ∘ Fin×Snd n)
             (snd ∘ Fin×Snd n)
isPropF×adjTP {n} k = isProp→PathP {ℓ = ℓ-zero} {B = λ i →
       ∀ x → isProp (F×adjTP {n} (k) i x)}
     (λ i → isPropΠ λ _ → isPropIsProp)
      (snd ∘ (Fin×Snd n)) (snd ∘ (Fin×Snd n))



F×adjSnd : ∀ {n} k → PathP (λ i → adjT×^≡ {A = Bool} {n = n} k i → hProp _)
             (Fin×Snd n)
             (Fin×Snd n)
F×adjSnd {n} k i x = F×adjTP {n} k i x , isPropF×adjTP {n} k i x

F×adjT≡ : ∀ {n} → ℕ → (Fin× n) ≡ (Fin× n)
F×adjT≡ {n} k i = Σ (adjT×^≡ {A = Bool} {n = n} k i) (F×adjTP {n} k i)



-- Fin×cases-ua-swap : ∀ {ℓ} {A : Type ℓ}
--   → (a a' : A) → (f : Fin× n → A)
--   → PathP (λ i →
--       F×adjT≡ {n = 2 + n} zero i → A)
--       (Fin×cases a (Fin×cases a' f))
--       (Fin×cases a' (Fin×cases a f))
-- Fin×cases-ua-swap = {!!}



-- -- F×adjT≡-suc : ∀ {n} → ℕ → (Fin× n) ≡ (Fin× n)
-- -- F×adjT≡-suc {n} k i = Σ (adjT×^≡ {A = Bool} {n = n} k i) (F×adjTP {n} k i)




-- F×biAdjTP' : ∀ {n} k l → PathP (λ i → biAdjT×^≡ {A = Bool} {n = n} k l i → Type)
--              (fst ∘ (allFalse n))
--              (fst ∘ (allFalse n))
-- F×biAdjTP' {n} k l =
--   {!!} ◁ (λ i → fst ∘ allFalse n ∘' unglueBiAdjT× n k l i)
--    ▷ {!!}
-- F×biAdjTP' {suc n} (suc k , k<) (suc l , l<) i (false , xs) =
--   F×biAdjTP' {n} (k , k<) (l , l<) i xs
-- F×biAdjTP' {suc n} (suc k , k<) (suc l , l<) i (true , xs) = ⊥
-- F×biAdjTP' {suc n} (zero , k<) (zero , l<) = refl
-- F×biAdjTP' {suc (suc (suc n))} (zero , k<) (suc zero , l<) i x =
--  let z = {!!}
--  in {!!}
--   {!allFalse∘adjT×≡ (suc (suc (suc n))) zero
--     (unglueAdjT× (suc (suc (suc n))) zero i x) i!}
-- F×biAdjTP' {suc (suc (suc n))} (zero , k<) (suc (suc l) , l<) = {!!}
--   -- toPathP (funExt w)
--   --  where
--   --  w : _
--   --  w (false , x' , xs) = {!!}
--   --  w (true , x' , xs) = {!!}
   
-- F×biAdjTP' {suc n} (suc k , k<) (zero , l<) = {!!}

-- F×biAdjTP : ∀ {n} k l → PathP (λ i → biAdjT×^≡ {A = Bool} {n = n} k l i → Type)
--              (fst ∘ (Fin×Snd n))
--              (fst ∘ (Fin×Snd n))
--              -- Fin×Snd∘adjT×≡
-- -- F×biAdjTP {suc n} (suc k , k<) (suc l , l<) i (false , xs) =
-- --    F×biAdjTP {n} (k , k<) (l , l<) i (xs)
-- -- F×biAdjTP {suc n} (suc k , k<) (suc l , l<) i (true , xs) =
-- --   F×biAdjTP' {n} (k , k<) (l , l<) i (xs)
-- -- F×biAdjTP {suc (suc n)} (zero , k<) (zero , l<) = refl
-- -- F×biAdjTP {suc (suc n)} (zero , k<) (suc l , l<) = {!!}
-- -- F×biAdjTP {suc (suc n)} (suc k , k<) (zero , l<) = {!!}

-- F×biAdjT≡Snd : ∀ {n} → ∀ k l →
--   PathP (λ i → biAdjT×^≡ {A = Bool} {n = n} k l i → hProp ℓ-zero)
--       (λ x → (Fin×Snd n x)) (λ x → (Fin×Snd n x))
-- F×biAdjT≡Snd {suc n} (suc k , k<) (suc l , l<) i (x , xs) =
--   (if x then {!!}
--      else F×biAdjT≡Snd {n} (k , k<) (l , l<) i xs)

-- F×biAdjT≡Snd {suc (suc n)} (zero , k<) (zero , l<) = refl
-- F×biAdjT≡Snd {suc (suc n)} (zero , k<) (suc l , l<) =
--   {!!}
-- F×biAdjT≡Snd {suc n} (suc k , k<) (zero , l<) = {!!}


-- F×biAdjT≡-allFalse< : ∀ n k k<
--  → PathP (λ i → biAdjT×^≡< {A = Bool} {n = suc n} (k , k<) i → hProp ℓ-zero)
--       (allFalse (suc n)) (allFalse (suc n))
-- F×biAdjT≡-allFalse< (suc (suc n)) zero k< i g =
--   let x , x' , x'' = unglue (i ∨ ~ i) g
--   in {!!}
-- F×biAdjT≡-allFalse< (suc (suc n)) (suc k) k< = {!!}

-- F×biAdjT≡-allFalse : ∀ n k l → PathP (λ i → biAdjT×^≡ {A = Bool}
--                                {n = n} k l i → hProp ℓ-zero)
--       (allFalse n)
--       (allFalse n)
-- F×biAdjT≡-allFalse (suc n) (zero , k<) (zero , l<) = refl
-- F×biAdjT≡-allFalse (suc n) (suc k , k<) (suc l , l<) =
--   congP (λ _ → uncurry) (funExt λ b →
--     λ i y → if b then L.⊥ else F×biAdjT≡-allFalse n (k , k<) (l , l<) i y)
-- F×biAdjT≡-allFalse (suc n) (zero , k<) (suc l , l<) = {!!}
-- F×biAdjT≡-allFalse (suc n) (suc k , k<) (zero , l<) = {!!}


congEquivP' : ∀ {ℓ} → ∀ {A₀ : Type ℓ} {A₁} {B : Type ℓ} → (A : A₀ ≡ A₁) 
                → ∀ {e₀ e₁} (e : PathP (λ i → A i ≃ B) e₀ e₁) → ∀ {x y} → 
                 (equivFun (e₀) x ≡ equivFun (e₁) y)
                  → (PathP (λ i → A i) x y)
                 
congEquivP' {A₀ = A₀} {A₁} {B} A e p =
  let z = congP₂ (λ i e x → invEq e x ) e p
  in  sym (retEq (e i0) _) ◁ z ▷ (retEq (e i1) _) 


congEquivP'' : ∀ {ℓ} → ∀ {A₀ : Type ℓ} {A₁} {B : Type ℓ} → (A : A₀ ≡ A₁) 
                → ∀ {e₀ e₁} (e : PathP (λ i → A i ≃ B) e₀ e₁) → ∀ {x y} → 
                 (equivFun (e₀) x ≡ equivFun (e₁) y)
                  → (PathP (λ i → A i)
                       (invEq e₀ (equivFun e₀ x))
                       (invEq e₁ (equivFun e₁ y)))
                 
congEquivP'' {A₀ = A₀} {A₁} {B} A e p =
  congP₂ (λ i e x → invEq e x ) e p
  -- in   z ▷ (retEq (e i1) _) 


F×biAdjT≡-allFalse< : ∀ k n k< →
   PathP (λ i → biAdjT×^≡< {A = Bool} {n = n} (k , k<) i → hProp ℓ-zero)
      (allFalse (n)) (allFalse (n))
F×biAdjT≡-allFalse< zero (suc (suc (suc n))) _ =
       (funExt λ x → TypeOfHLevel≡ 1
                    ((allFalse∘adjT×≡ (3 + n) 1 x)))
         ◁ congP (λ _ → allFalse (3 + n) ∘_)
                 (𝑮-ungluePathExt _ _ _) ▷
                  funExt λ x → TypeOfHLevel≡ 1
                   (sym ((allFalse∘adjT×≡ (3 + n) zero x)))

F×biAdjT≡-allFalse< (suc k) (suc (suc n)) _ = 
  congEquivP' _
       (λ i → preCompEquiv
         (𝑮-gluePathExt-R
           (adjT×^≡ {A = Bool} {n = 2 + n}  (suc (suc k)))
           (adjT×^≃ (suc (suc k))) Σ-swap-01-≃
            (glue'AdjT× (2 + n) (2 + k)) i))
            (funExt λ x →
              TypeOfHLevel≡ 1
               ( sym (allFalse∘adjT×≡ (2 + n) (2 + k)
                 x) ∙ allFalse∘adjT×≡ (2 + n) 0 x))

F×biAdjT≡-allFalse : ∀ n k l →
     PathP (λ i → biAdjT×^≡ {A = Bool}
       {n = n} k l i → hProp ℓ-zero)
      (allFalse n)
      (allFalse n)
F×biAdjT≡-allFalse (n) (zero , k<) (zero , l<) = refl
F×biAdjT≡-allFalse (n) (zero , k<) (suc l , l<) =
  symP (F×biAdjT≡-allFalse< l n l<)
F×biAdjT≡-allFalse (n) (suc k , k<) (zero , l<) = F×biAdjT≡-allFalse< k n k<
F×biAdjT≡-allFalse (suc n) (suc k , k<) (suc l , l<) =
  congP (λ _ → uncurry)
   (funExt λ b →
     congP (λ _ → (if b then L.⊥ else_) ∘_ )
       (F×biAdjT≡-allFalse n (k , k<) (l , l<)))


F×biAdjT≡-snd< : ∀ k n k< →
    PathP (λ i → biAdjT×^≡< {A = Bool} {n = n} (k , k<) i → hProp ℓ-zero)
      (Fin×Snd n) (Fin×Snd n)
F×biAdjT≡-snd< zero (suc (suc (suc n))) _ =
         (funExt λ x → TypeOfHLevel≡ 1
                    ((Fin×Snd∘adjT×≡ (3 + n) 1 x)))
         ◁ congP (λ _ → Fin×Snd (3 + n) ∘_)
                 (𝑮-ungluePathExt _ _ _) ▷
                  funExt λ x → TypeOfHLevel≡ 1
                   (sym ((Fin×Snd∘adjT×≡ (3 + n) zero x)))

F×biAdjT≡-snd< (suc k) (suc (suc n)) _ =
  congEquivP' _
       (λ i → preCompEquiv
         (𝑮-gluePathExt-R
           (adjT×^≡ {A = Bool} {n = 2 + n}  (suc (suc k)))
           (adjT×^≃ (suc (suc k))) Σ-swap-01-≃
            (glue'AdjT× (2 + n) (2 + k)) i))
            (funExt λ x →
              TypeOfHLevel≡ 1
               ( sym (Fin×Snd∘adjT×≡ (2 + n) (2 + k)
                 x) ∙ Fin×Snd∘adjT×≡ (2 + n) 0 x))

F×biAdjT≡-snd : ∀ n k l → PathP (λ i → biAdjT×^≡ {A = Bool}
                               {n = n} k l i → hProp ℓ-zero)
      (Fin×Snd n)
      (Fin×Snd n)
F×biAdjT≡-snd n (zero , k<) (zero , l<) = refl
F×biAdjT≡-snd n (suc k , k<) (zero , l<) = F×biAdjT≡-snd< k n k<

F×biAdjT≡-snd n (zero , k<) (suc l , l<) = symP (F×biAdjT≡-snd< l n l<)
F×biAdjT≡-snd (suc n) (suc k , k<) (suc l , l<) =
  congP (λ _ → uncurry) (funExt λ b →
    λ i y → if b
            then F×biAdjT≡-allFalse n (k , k<) (l , l<) i y
            else F×biAdjT≡-snd n (k , k<) (l , l<) i y)




F×biAdjT≡' : ∀ {n} → Fin₋₁ n → Fin₋₁ n →
  Path (Σ Type λ X → X → hProp ℓ-zero)
   ((Bool ×^ n) , Fin×Snd n )
   ((Bool ×^ n) , Fin×Snd n)
F×biAdjT≡' {n} k l =
   ΣPathP
    ( (biAdjT×^≡ {A = Bool} {n = n} k l)
    , F×biAdjT≡-snd n k l )
       
F×biAdjT≡ : ∀ {n} → Fin₋₁ n → Fin₋₁ n → (Fin× n) ≡ (Fin× n)
F×biAdjT≡ {n} k l =
  cong (λ a → Σ (fst a) (fst ∘ snd a)) (F×biAdjT≡' {n} k l)
 




unglue-F×adjT≡-snd' : ∀ n k →
  PathP (λ i → (xs : adjT×^≡ {n = n} k i) → F×adjTP' {n} k i xs
      → fst (allFalse n (unglueAdjT× n k i xs)))
     (λ _ → idfun _)
     (allFalse∘adjT× n k)
unglue-F×adjT≡-snd' zero k = refl
unglue-F×adjT≡-snd' (suc n) (suc k) i (false , xs) =
  unglue-F×adjT≡-snd' n k i xs
unglue-F×adjT≡-snd' (suc n) (suc k) i (true , xs) ()
unglue-F×adjT≡-snd' (suc zero) zero = refl
unglue-F×adjT≡-snd' (suc (suc n)) zero =
  isProp→PathP'
      (λ i → isPropΠ2 λ xs (ys : F×adjTP' {suc (suc n)} zero i xs)
         → snd (allFalse (suc (suc n)) (unglueAdjT× (suc (suc n)) zero i xs)))
      (λ xs ys → ys)
      (allFalse∘adjT× (suc (suc n)) zero)


unglue-F×adjT≡-snd : ∀ n k →
  PathP (λ i → (xs : adjT×^≡ {n = n} k i) → F×adjTP {n} k i xs
      → fst (Fin×Snd n (unglueAdjT× n k i xs)))
     (λ _ → idfun _)
     (Fin×Snd∘adjT× n k)
unglue-F×adjT≡-snd (suc n) (suc k) i (false , xs) x =
 unglue-F×adjT≡-snd n k i xs x
unglue-F×adjT≡-snd (suc n) (suc k) i (true , xs) x =
  unglue-F×adjT≡-snd' n k i xs x
unglue-F×adjT≡-snd (suc zero) zero = refl
unglue-F×adjT≡-snd (suc (suc n)) zero =
  isProp→PathP'
      (λ i → isPropΠ2 λ xs (ys : F×adjTP {suc (suc n)} zero i xs)
         → snd (Fin×Snd (suc (suc n)) (unglueAdjT× (suc (suc n)) zero i xs)))
      (λ xs ys → ys)
      (Fin×Snd∘adjT× (suc (suc n)) zero)

unglue-F×adjT≡ : ∀ n k →
  PathP (λ i → F×adjT≡ {n} k i → Fin× n)
     (idfun _)
     (F×adjT k)
unglue-F×adjT≡ n k i (xs , ys) =
 unglueAdjT× n k i xs , unglue-F×adjT≡-snd n k i xs ys

-- unglue'-F×adjT≡ : ∀ n k →
--   PathP (λ i → F×adjT≡ {n} k i → Fin× n)
--      (F×adjT k)
--      (idfun _)
-- unglue'-F×adjT≡ n k i (xs , ys) =
--  unglue'AdjT× n k i xs , {!!}


glue-F×adjT≡ : ∀ n k →
  PathP (λ i → Fin× n → F×adjT≡ {n} k i)
     (idfun _)
     (F×adjT k)
glue-F×adjT≡ n k =
  funExt λ (xs , ys) →
    ΣPathPProp (snd ∘ Fin×Snd n) (funExt⁻ (glueAdjT× n k) xs)

glue-F×adjT≃ : ∀ n k →
  PathP (λ i → Fin× n ≃ F×adjT≡ {n} k i)
     (idEquiv _)
     (F×adjT≃ k) --(F×adjT k)
glue-F×adjT≃ n k = ΣPathPProp isPropIsEquiv (glue-F×adjT≡ n k)
  

-- glue'-F×adjT≡ : ∀ n k →
--   PathP (λ i → Fin× n → F×adjT≡ {n} k i)
--      (F×adjT k)
--      (idfun _)
     
-- glue'-F×adjT≡ n k =
--   funExt λ (xs , ys) →
--     ΣPathPProp (snd ∘ Fin×Snd n) (funExt⁻ (glue'AdjT× n k) xs)



glue-F×biAdjT≡<1 : ∀ n → 
  PathP (λ i → Fin× (3 + n) → F×biAdjT≡ {3 + n} (1 , _) (0 , _) i)
     (F×adjT 1)
     (F×adjT 0)
glue-F×biAdjT≡<1 n = 
  funExt λ (xs , ys) →
    ΣPathPProp (snd ∘ Fin×Snd (3 + n))
     (funExt⁻ (glueBiAdjT×< n) xs)

-- glue-F×biAdjT≡<SS : ∀ n k → 
--   PathP (λ i → Fin× (suc (suc n)) →
--       F×biAdjT≡ {suc (suc n)} (suc (suc (fst k)) , (snd k)) (0 , _) i)
--      (F×adjT (suc (suc (fst k))))
--      (F×adjT 0)
-- glue-F×biAdjT≡<SS n k = 
--   funExt λ (xs , ys) →
--     ΣPathPProp (snd ∘ Fin×Snd (2 + n))
--      (funExt⁻ (glueBiAdjT×<SS n k) xs)


glue-F×biAdjT≡<SS : ∀ n k → 
  PathP (λ i → F×adjT≡ {suc (suc n)} (suc (suc (fst k))) i →
      F×biAdjT≡ {suc (suc n)} (suc (suc (fst k)) , (snd k)) (0 , _) i)
     (idfun _) --(F×adjT (suc (suc (fst k))))
     (F×adjT 0)
fst (glue-F×biAdjT≡<SS n k i (xs , ys)) = 
   glueBiAdjT×<SS n k i xs
snd (glue-F×biAdjT≡<SS n k i (xs , ys)) =
  isProp→PathP
    {B =
      λ i → ((xs , ys) : F×adjT≡ {suc (suc n)} (suc (suc (fst k))) i)
        → fst (snd (F×biAdjT≡' {n = suc (suc n)}
            (suc (suc (fst k)) , (snd k)) (0 , _) i)
              (glueBiAdjT×<SS n k i xs))}
    (λ i →
       isPropΠ λ (xs , _) →
         snd (snd (F×biAdjT≡' {n = suc (suc n)}
            (suc (suc (fst k)) , (snd k)) (0 , _) i)
              (glueBiAdjT×<SS n k i xs)))
       snd
       (uncurry (Fin×Snd∘adjT× (2 + n) zero))
   i (xs , ys)



glue'-F×adjT≡ : ∀ n k →
  PathP (λ i → Fin× n → F×adjT≡ {n} k i)
     (F×adjT k)
     (idfun _)
     
glue'-F×adjT≡ n k =
   funExt λ (xs , ys) →
    ΣPathPProp (snd ∘ Fin×Snd n) (funExt⁻ (glue'AdjT× n k) xs)



IsoMaybe∘Fin×Fin×∘suc : ∀ n → Iso (Maybe (Fin× n)) (Fin× (suc n))
Iso.fun (IsoMaybe∘Fin×Fin×∘suc n) nothing =
  (true , _) , allFalse-repeat-false n
Iso.fun (IsoMaybe∘Fin×Fin×∘suc n) (just (xs , ys)) =
  (false , xs) , ys
Iso.inv (IsoMaybe∘Fin×Fin×∘suc n) ((false , xs) , ys) =
  just (xs , ys)
Iso.inv (IsoMaybe∘Fin×Fin×∘suc n) ((true , _) , _) = nothing
Iso.rightInv (IsoMaybe∘Fin×Fin×∘suc n) ((false , _) , _) =
  Σ≡Prop (snd ∘ Fin×Snd (suc n)) refl
Iso.rightInv (IsoMaybe∘Fin×Fin×∘suc n) ((true , xs) , ys) =
  Σ≡Prop (snd ∘ Fin×Snd (suc n))
  (cong (true ,_) (allFalse→≡repeat-false n xs ys))
Iso.leftInv (IsoMaybe∘Fin×Fin×∘suc n) nothing = refl
Iso.leftInv (IsoMaybe∘Fin×Fin×∘suc n) (just x) = refl


Maybe∘Fin×≃Fin×∘suc : ∀ n → Maybe (Fin× n) ≃ Fin× (suc n)
Maybe∘Fin×≃Fin×∘suc = isoToEquiv ∘ IsoMaybe∘Fin×Fin×∘suc

glue-repeat-false : ∀ n k →
   PathP (λ i → adjT×^≡ {A = Bool} {n = n} k i) (repeat n false) (repeat n false)
glue-repeat-false zero k = refl
glue-repeat-false (suc n) (suc k) i =
  false , glue-repeat-false n k i
glue-repeat-false (suc zero) zero = refl
glue-repeat-false (suc (suc n)) zero = ua-gluePath _ refl

glue-repeat-false-bi< :
  ∀ n l → PathP (λ i → biAdjT×^≡< {A = Bool} {n = suc (suc n)} l (~ i))
      (false , false , repeat n false) (false , false , repeat n false)
glue-repeat-false-bi< n (suc l , l<) =
  𝑮-gluePath _ _ _ λ i → false , false , glue-repeat-false n l (~ i)
glue-repeat-false-bi< (suc n) (zero , l<) = 𝑮-gluePath _ _ _ refl

glue-repeat-false-bi : ∀ n k l →
   PathP (λ i → biAdjT×^≡ {A = Bool} {n = n} k l i)
      (repeat n false) (repeat n false)
glue-repeat-false-bi n (zero , k<) (zero , l<) = refl
glue-repeat-false-bi (suc n) (suc k , k<) (suc l , l<) =
 congP (λ _ → false ,_)
   (glue-repeat-false-bi n (k , k<) (l , l<))

glue-repeat-false-bi (suc (suc n)) (zero , k<) (suc l , l<) =
 glue-repeat-false-bi< n (l , l<)
glue-repeat-false-bi (suc (suc n)) (suc k , k<) (zero , l<) =
 symP (glue-repeat-false-bi< n (k , k<))
 


glueF×adjT≡0 : ∀ n k → PathP (λ i → F×adjT≡ {suc n} (suc k) i)
               Fin×0
               Fin×0 
glueF×adjT≡0 n k =
  ΣPathPProp (snd ∘ Fin×Snd (suc n))
    λ i → true , glue-repeat-false n k i

glueF×biAdjT≡0 : ∀ n k l k< l< →
            PathP (λ i → F×biAdjT≡ {n = suc n} (suc k , k<) (suc l , l<) i)
               Fin×0
               Fin×0 
glueF×biAdjT≡0 n k l k< l<  = 
  ΣPathPProp (snd ∘ Fin×Snd (suc n))
    λ i → true , glue-repeat-false-bi n (k , k<) (l , l<) i



module Tab× {A : Type ℓ} where

 IsoFin×0→AUnit* : Iso (Fin× zero → A) (A ×^ zero)
 Iso.fun IsoFin×0→AUnit* _ = _
 Iso.inv IsoFin×0→AUnit* x ()
 Iso.rightInv IsoFin×0→AUnit* _ = refl
 Iso.leftInv IsoFin×0→AUnit* _ _ () 

 tab×≡-suc : ∀ {ℓ' ℓ''} → ∀ {X C} {D : Type ℓ''} {B : Type ℓ'}
    → Maybe D ≃ B → (D → A) ≡ X → C ≃ A × X →
    (B → A) ≡ C --(Fin× (suc n) → A) ≡ C
 tab×≡-suc {B = B} f p e = 𝑮 (preCompEquiv f ∙ₑ ≃MaybeFunProd)
                    (cong′ (A ×_) p) e

-- Maybe∘Fin×≃Fin×∘suc n

 tab×≡ : ∀ n →  (Fin× n → A) ≡ ( A ×^ n)

 tab×≡ zero = ua (isoToEquiv IsoFin×0→AUnit*)
 tab×≡ (suc n) = tab×≡-suc
   {X = A ×^ n}
   {A × (A ×^ n)}
   {Fin× n}
   (Maybe∘Fin×≃Fin×∘suc n) (tab×≡ n) (idEquiv _)

 List→ΣℕFin×→ : (l : L.List A) → Fin (L.length l) → A
 List→ΣℕFin×→ L.[] ()
 List→ΣℕFin×→ (x L.∷ l) =
   Fin-elim (L.length l) x (List→ΣℕFin×→ l)
  
 ΣℕFin×→List : ∀ n → (Fin n → A) → L.List A
 ΣℕFin×→List zero _ = L.[]
 ΣℕFin×→List (suc k) f =  f (zero , _) L.∷ ΣℕFin×→List k (f ∘ sucF)

--  sec-IsoListΣℕFin×→-fst : ∀ n f → fst (List→ΣℕFin×→ (ΣℕFin×→List n f)) ≡ n
--  sec-IsoListΣℕFin×→-fst zero f = refl
--  sec-IsoListΣℕFin×→-fst (suc n) f = {!!}

--  sec-IsoListΣℕFin×→ : ∀ n → (f : (Fin n → A)) →
--     List→ΣℕFin×→ (ΣℕFin×→List n f) ≡ (n , f)
--  sec-IsoListΣℕFin×→ n f = ΣPathP (sec-IsoListΣℕFin×→-fst n f , {!!})
--  -- sec-IsoListΣℕFin×→ zero f = ΣPathP (refl , funExt λ ())
--  -- sec-IsoListΣℕFin×→ (suc n) f =
--  --  let p = sec-IsoListΣℕFin×→ n (f ∘ sucF)
--  --  in  (λ i → suc (fst (p i)) ,
--  --           Fin-elim _ (f (zero , _)) (snd (p i))) ∙
--  --            ΣPathP (refl ,
--  --             funExt λ { (zero , _) → refl ; (suc _ , _) → {!!} } )
            
--  --      -- ΣPathP (cong (suc ∘ fst) p ,
--  --      --  congP (λ i f' → {!Fin-elim ? ? ? !}) (cong snd p)) 

 -- IsoListΣℕFin×→ : Iso (L.List A) (Σ ℕ λ n → Fin n → A)
 -- Iso.fun IsoListΣℕFin×→ = (λ {l} → (L.length l ,_)) ∘ List→ΣℕFin×→
 -- Iso.inv IsoListΣℕFin×→ = uncurry ΣℕFin×→List
 -- Iso.rightInv IsoListΣℕFin×→ = {!!}
 --   -- uncurry λ x y → ΣPathP ({!!} , {!!})
 -- -- uncurry sec-IsoListΣℕFin×→
 -- Iso.leftInv IsoListΣℕFin×→ = 
 --   L.ind' refl λ {a} l p →
 --    cong (a L.∷_)
 --     (cong (ΣℕFin×→List (L.length l))
 --      (funExt {!!}) ∙ p) 

 tab×≡-sides : ∀ n → ∀ i → Partial (~ i ∨ i) (Σ-syntax (Type ℓ) (λ T → T ≃ A × tab×≡ n i)) 
 tab×≡-sides n i =
   λ { (i = i0) → (Fin× (suc n) → A) ,
            preCompEquiv (Maybe∘Fin×≃Fin×∘suc n) ∙ₑ ≃MaybeFunProd
       ; (i = i1) → _ , idEquiv _
       }



 -- tab-gluingⁿ : ∀ m n → ((Fin× n → A) ×^ m) ≡ (A ×^ (m · n))
 -- tab-gluingⁿ zero n = refl
 -- tab-gluingⁿ (suc m) n i = {!!}

 tab×≡-ungluing-equiv : ∀ m n → ∀ i → 
     tab×≡ (m + n) i ≃ (X×ⁿ A (Fin× n → A) m)
 tab×≡-ungluing-equiv zero zero i =
  ua-unglueEquiv (isoToEquiv IsoFin×0→AUnit*) i ∙ₑ
     isoToEquiv (invIso IsoFin×0→AUnit*)
 tab×≡-ungluing-equiv zero (suc n) i =
   unglueEquiv _ (i ∨ ~ i) (tab×≡-sides n i)
     ∙ₑ (≃-× (idEquiv _) (tab×≡-ungluing-equiv zero n i) ∙ₑ invEquiv ≃MaybeFunProd)
     ∙ₑ invEquiv (preCompEquiv (Maybe∘Fin×≃Fin×∘suc n))
 tab×≡-ungluing-equiv (suc m) n i =
   unglueEquiv _ (i ∨ ~ i) (tab×≡-sides (m + n) i) ∙ₑ
     ≃-× (idEquiv _) (tab×≡-ungluing-equiv m n i)

 -- tab×≡-ungluing-equiv'i0 : ∀ m n → 
 --     tab×≡ (m + n) i0 ≃ (X×ⁿ A (tab×≡ n i0) m)
 -- tab×≡-ungluing-equiv'i0 m n = {!!}
 -- -- tab×≡-ungluing-equiv'i0 = ?

 tab×≡-ungluing-equiv' : ∀ m n → ∀ i → 
     tab×≡ (m + n) i ≃ (X×ⁿ A (tab×≡ n i) m)
 tab×≡-ungluing-equiv' zero n i = idEquiv _
 tab×≡-ungluing-equiv' (suc m) n i =
   unglueEquiv _ (i ∨ ~ i) (tab×≡-sides (m + n) i) ∙ₑ
     ≃-× (idEquiv _) (tab×≡-ungluing-equiv' m n i)

 tab-2-Iso : ∀ n → Iso (Fin× (suc (suc n)) → A) (A × A × (Fin× n → A))
 Iso.fun (tab-2-Iso n) f =
   f (Fin×0) , f (sucFin× Fin×0) , f ∘' sucFin× ∘' sucFin× 
 Iso.inv (tab-2-Iso n) (f0 , f1 , f) =
    Fin×cases f0 (Fin×cases f1 f)
 Iso.rightInv (tab-2-Iso n) (f0 , f1 , f) = refl

 Iso.leftInv (tab-2-Iso n) f =
   Fin×elimFunExt refl
     (Fin×elimFunExt refl
       refl)


 tab-2 : ∀ n → (Fin× (suc (suc n)) → A) ≃ A × A × (Fin× n → A)
 tab-2 = isoToEquiv ∘ tab-2-Iso


 tab×≡-ungluing-equiv'2 : ∀ n → 
     PathP (λ i → tab×≡ (2 + n) i ≃
                 (A × A × tab×≡ n i))
       (tab-2 n)
       (idEquiv _)
     
 tab×≡-ungluing-equiv'2 n =
   ΣPathPProp isPropIsEquiv
    λ i f →
      let (a , f') = unglue (i ∨ ~ i) f
          (a' , f'') = unglue (i ∨ ~ i) f'
      in a , a' , f''

 -- -- tab×≡-ungluing-equiv'2-sq : ∀ n → 
 -- --     SquareP (λ j i → tab×≡ (2 + n) i ≃
 -- --            (ua (Σ-swap-01-≃ {A = A} {A} {(tab×≡ n i)}) j))
 -- --       (tab×≡-ungluing-equiv'2 n)
 -- --       {!symP (tab×≡-ungluing-equiv'2 n)!}
 -- --       {!!}
 -- --       {!!}
 -- -- tab×≡-ungluing-equiv'2-sq = {!!} 
 -- -- -- zero n i = idEquiv _
 -- -- -- tab×≡-ungluing-equiv' (suc m) n i =
 -- -- --   unglueEquiv _ (i ∨ ~ i) (tab×≡-sides (m + n) i) ∙ₑ
 -- -- --     ≃-× (idEquiv _) (tab×≡-ungluing-equiv' m n i)


 -- tab×≡-ungluing-equiv'P0 : ∀ m n → (Fin× (m + n) → A) ≃ X×ⁿ A (Fin× n → A) m
 -- tab×≡-ungluing-equiv'P0 zero n = idEquiv _
 -- tab×≡-ungluing-equiv'P0 (suc m) n =
 --   {!!}

 -- tab×≡-ungluing-equiv'P : ∀ m n →  
 --     PathP (λ i → tab×≡ (m + n) i ≃ (X×ⁿ A (tab×≡ n i) m))
 --       {!!}
 --       {!!}
 -- tab×≡-ungluing-equiv'P = {!!}
 -- -- tab×≡-ungluing-equiv' zero n i = idEquiv _
 -- -- tab×≡-ungluing-equiv' (suc m) n i =
 -- --   unglueEquiv _ (i ∨ ~ i) (tab×≡-sides (m + n) i) ∙ₑ
 -- --     ≃-× (idEquiv _) (tab×≡-ungluing-equiv' m n i)


 -- glue-repeat-false-bi : ∀ n k l →
 --    PathP (λ i → biAdjT×^≡ {A = Bool} {n = n} k l i)
 --      (repeat n false) (repeat n false)
 -- glue-repeat-false-bi (suc n) (suc k , k<) (suc l , l<) i =
 --   false , glue-repeat-false-bi n (k , k<) (l , l<) i      
 -- glue-repeat-false-bi (suc n) (zero , k<) (zero , l<) =
 --   refl
 -- glue-repeat-false-bi (suc (suc (suc n))) (zero , k<) (suc zero , l<) i =
 --   glue (λ { (i = i0) → repeat (3 + n) false
 --           ; (i = i1) → repeat (3 + n) false })
 --     {!!}
 -- glue-repeat-false-bi (suc n) (zero , k<) (suc (suc l) , l<) i = {!!}
 -- glue-repeat-false-bi (suc n) (suc k , k<) (zero , l<) = {!!}
   
 MaybeFin×AdjTSq : ∀ n k → PathP
      (λ i → (Maybe (F×adjT≡ {n = n} k i))
          →  (F×adjT≡ {n = suc n} (suc k) i))
      (fst (Maybe∘Fin×≃Fin×∘suc n))
      (fst (Maybe∘Fin×≃Fin×∘suc n))

 MaybeFin×AdjTSq n k i nothing =
   (true , glue-repeat-false n k i) ,
     isProp→PathP (λ i →
       isPropF×adjTP' {n} k i (glue-repeat-false n k i))
      (allFalse-repeat-false n)
      (allFalse-repeat-false n)
       i
 MaybeFin×AdjTSq n k i (just x) =
   (false , fst x) , snd x



 MaybeFin×AdjTSq≃ : ∀ n k → PathP
      (λ i → (Maybe (F×adjT≡ {n = n} k i))
          ≃  (F×adjT≡ {n = suc n} (suc k) i))
      (Maybe∘Fin×≃Fin×∘suc n)
      (Maybe∘Fin×≃Fin×∘suc n)
 MaybeFin×AdjTSq≃ n k =
  ΣPathPProp isPropIsEquiv (MaybeFin×AdjTSq n k)


 tab×adjT×0'-lem : ∀ i → tab×≡ (suc (suc n)) i ≃ A × A × tab×≡ n i
 tab×adjT×0'-lem {n} i = unglueEquiv _ (i ∨ ~ i) (tab×≡-sides (suc n) i) ∙ₑ
                ≃-× (idEquiv _) (unglueEquiv _ (i ∨ ~ i)
                 (tab×≡-sides n i)) 


 tab×adjT×0'-lem'-hlp : ∀ n →
     PathP (λ j → Σ (Bool ×^ suc (suc n))
           (λ x → fst (Fin×Snd (suc (suc n)) x)) →
      F×adjT≡ {n = suc (suc n)} zero j)
        (idfun _)
        (F×adjT {n = suc (suc n)} zero)
 tab×adjT×0'-lem'-hlp n j = 
    λ (x : Fin× (suc (suc n)))  →
          ua-gluePathExt (adjT×^≃ zero) (j) (fst x)
            , isProp→PathP
                ((λ j → isPropF×adjTP {n = suc (suc n)} zero
                           (j) (ua-gluePathExt (adjT×^≃ zero) (j) (fst x))))
                  (snd x)
                  (Fin×Snd∘adjT× (suc (suc n)) zero (fst x) (snd  x)) j

 tab×adjT×0'-lem'-hlp-invol : ∀ n →
    (p : ∀ n (k : Fin₋₁ n) →
               SquareP (λ j i → adjT×^≡-invol {A = Bool} n (fst k) j (i) → hProp ℓ-zero)
                  ((F×adjSnd {n} (fst k)))
                  (symP  (F×adjSnd {n} (fst k)))
                  (λ _ → Fin×Snd n)
                  (λ _ → Fin×Snd n))
   → SquareP (λ i j → Σ (Bool ×^ suc (suc n))
           (λ x → fst (Fin×Snd (suc (suc n)) x))
            → Σ (Σ-swap-01-≡-invol-ua {A = Bool} {Bool ×^ n} i j)
                (fst ∘ (p (suc (suc n)) (zero , _) i j)))
            -- F×adjT≡ {n = suc (suc n)} zero j
      (tab×adjT×0'-lem'-hlp n)
      (congP (λ _ → _∘' (F×adjT {n = suc (suc n)} zero))
         (symP (tab×adjT×0'-lem'-hlp n)))
      
      (funExt (λ x →
        Fin×PathP (suc (suc n)) refl refl
           refl))
      refl
 tab×adjT×0'-lem'-hlp-invol n p =
   toPathP (isSet→SquareP
         (λ j i → isSet→
           (isSetΣ (isOfHLevelUA (~ i) Σ-swap-01-≃ 2
             ((isOfHLevel×^ (suc (suc n)) 2 isSetBool)))
             (isProp→isSet ∘ (snd ∘ (F×adjSnd {n = suc (suc n)} zero) (~ i))))) _ _ _ _)


 tab×adjT×0'-lem' : PathP
  (λ j → (F×adjT≡ {n = suc (suc n)} zero (j) → A)
     ≃ ua (Σ-swap-01-≃ {A = A} {A} {Fin× n → A}) j)
       (tab×adjT×0'-lem i0)
       (tab×adjT×0'-lem i0)
 tab×adjT×0'-lem' {n} = 
  ΣPathPProp isPropIsEquiv
     λ j → ua-gluePathExt (Σ-swap-01-≃ {A'' = (a : Fin× n) → A}) j ∘'
       (λ f →
         f Fin×0 , (f (sucFin× Fin×0) , f ∘ sucFin× ∘ sucFin×))
       ∘' _∘' 
            tab×adjT×0'-lem'-hlp n j

 sym-ua-gluePathExt-Σ-swap-01-≃ :
   SquareP (λ i j → A × A × (Fin× n → A)
         → (Σ-swap-01-≡-invol-ua {A = A} {Fin× n → A}) i j)
    (ua-gluePathExt (Σ-swap-01-≃ {A = A} {A} {Fin× n → A}))
    (congP (λ i → _∘ swap-01)
      (symP (ua-gluePathExt (Σ-swap-01-≃ {A = A} {A} {Fin× n → A}))))
    refl
    refl
 sym-ua-gluePathExt-Σ-swap-01-≃ {n} i j (a , a' , f) =
   glue (λ { (j = i0) → _ ; (j = i1) → _ })
  (glue (λ { (i = i0) → _ ; (i = i1) → _ }) (a , a' , f))
 
 tab×adjT×-invol0-jj0 :
   ∀ n →
   (p : ∀ n (k : Fin₋₁ n) →
               SquareP (λ j i → adjT×^≡-invol {A = Bool} n (fst k) j (i) → hProp ℓ-zero)
                  ((F×adjSnd {n} (fst k)))
                  (symP  (F×adjSnd {n} (fst k)))
                  (λ _ → Fin×Snd n)
                  (λ _ → Fin×Snd n))
   → SquareP (λ i j → (Σ (Σ-swap-01-≡-invol-ua j i)
       (λ x → fst (p (suc (suc n)) (zero , tt) j i x)) →
       A) →
      Σ-swap-01-≡-invol-ua {A = A} {B = Fin× n → A} j i)
      (λ _ → fst (tab-2 n))
      (λ _ → fst (tab-2 n))
      (λ i → fst (tab×adjT×0'-lem' {n = n} i))
      (λ i → fst (tab×adjT×0'-lem' {n = n} (~ i)))
      
 tab×adjT×-invol0-jj0 n p = 
    (congSq {A = (Fin× (suc (suc n)) → Fin× (suc (suc n)))}
          {a₀₋ = λ _ → idfun (Fin× (suc (suc n)))}
          {a₁₋ = (funExt (λ x →
        Fin×PathP (suc (suc n)) refl refl
           refl))}
          {refl}
          {refl}
          (λ g f → f (g Fin×0) , f (g (sucFin× Fin×0)) ,
                f ∘ g ∘ sucFin× ∘ sucFin×)
        (isSet→ (isSetFin× (suc (suc n)))
          _ _ _ _)
        
        ) ◁ (λ i j → sym-ua-gluePathExt-Σ-swap-01-≃ {n} j i
     ∘'
       (λ f →
         f Fin×0 , (f (sucFin× Fin×0) , f ∘ sucFin× ∘ sucFin×))
       ∘' (_∘' tab×adjT×0'-lem'-hlp-invol n p j i))

 tab×adjT×0'-sides : ∀ n → ∀ j i
        → Partial (i ∨ ~ i ∨ j ∨ ~ j)
           (Σ-syntax (Type ℓ)
             (λ T → T ≃ ua (Σ-swap-01-≃ {A = A} {A} {tab×≡ (n) i}) j))
 tab×adjT×0'-sides n j i =
   let e = tab×adjT×0'-lem {n} i
   in 
    λ {
             (i = i0) → (F×adjT≡ {n = suc (suc n)} zero (j) → A) ,
               tab×adjT×0'-lem' {n} j
            ;(i = i1) → adjT×^≡ {A = A} {n = 2 + n} zero j ,
               _ ,
                isProp→PathP
                 (λ j → isPropIsEquiv
                  (ua-gluePathExt Σ-swap-01-≃ j ∘' unglueAdjT× (2 + n) zero j))
                  (snd e) (snd e) j 

            ;(j = i0) → tab×≡ (suc (suc n)) i , e
            ;(j = i1) → tab×≡ (suc (suc n)) i , e

      }

 tab×adjT×0'-A : ∀ n →
    Square
      (λ i → A × A × tab×≡ n i)
      (λ i → A × A × tab×≡ n i)
      (ua (Σ-swap-01-≃ {A = A} {A} {Fin× n → A}))
      (ua (Σ-swap-01-≃ {A = A} {A} {A ×^ n}))
 tab×adjT×0'-A n j i = 
      (ua (Σ-swap-01-≃ {A = A} {A} {tab×≡ (n) i}) j)

 tab×adjT×0' :
   ∀ n → (zero < n) → PathP (λ i → 
           
             (F×adjT≡ {suc n} zero (i) → A) ≡ adjT×^≡ {A = A} {suc n} zero i )
      ( (tab×≡ (suc n))) ((tab×≡ (suc n)))
 tab×adjT×0' (suc n) x j i =
   Glue (tab×adjT×0'-A n j i)
        {i ∨ ~ i ∨ j ∨ ~ j}
          (tab×adjT×0'-sides n j i)




 tab×adjT× :
   ∀ n (k : Fin₋₁ n) → PathP (λ i → (F×adjT≡ {n} (fst k) (i) → A)
         ≡ adjT×^≡ {A = A} {n} (fst k) i)
      (tab×≡ n) (tab×≡ n)
 tab×adjT× = Nat.cases (λ ())
   (Nat.elim (λ ())
     λ n → flip (uncurry (Nat.cases
      (λ k< X → tab×adjT×0' (suc n) k<)
      λ k k< X j i →
         Glue
           (A × X (k , k<) j i)
           λ { (i = i0) → (F×adjT≡ {n = suc (suc n)} (suc k) (j) → A) ,
                  preCompEquiv (MaybeFin×AdjTSq≃ (suc n) k (j))
                    ∙ₑ ≃MaybeFunProd
             ; (i = i1) → _ , idEquiv _
       })))





 module _ {ℓ} {A A' : Type ℓ} 
      {B : A → Type ℓ} {B' : A' → Type ℓ} where
   map-Σ : (Σ (A → A') λ f → ∀ a → B a → B' (f a)) → (Σ A B → Σ A' B')
   map-Σ (f , g) (x , y) = f x , g _ y



congSqP₂ : ∀ {ℓ ℓ' ℓ''}
  {A : I → I → Type ℓ}
  {B : I → I → Type ℓ'}
  {C : I → I → Type ℓ''}
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁}
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} {a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁}
  {a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀} {a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
  {b₀₀ : B i0 i0} {b₀₁ : B i0 i1} {b₀₋ : PathP (λ j → B i0 j) b₀₀ b₀₁}
  {b₁₀ : B i1 i0} {b₁₁ : B i1 i1} {b₁₋ : PathP (λ j → B i1 j) b₁₀ b₁₁}
  {b₋₀ : PathP (λ i → B i i0) b₀₀ b₁₀} {b₋₁ : PathP (λ i → B i i1) b₀₁ b₁₁}
  → (f : ∀ i j → A i j → B i j → C i j)
  → SquareP A a₀₋ a₁₋ a₋₀ a₋₁
  → SquareP B b₀₋ b₁₋ b₋₀ b₋₁
  → SquareP C
             (congP₂ (f i0) a₀₋ b₀₋)
             (congP₂ (f i1) a₁₋ b₁₋)
             (congP₂ (λ i → f i i0) a₋₀ b₋₀)
             (congP₂ (λ i → f i i1) a₋₁ b₋₁)
congSqP₂ f sq sq' i j = f i j (sq i j) (sq' i j)
{-# INLINE congSqP₂ #-}

 -- glue-invol-Path : ∀ n →
 --   PathP
 --      (λ i →
 --         Bool ×^ (2 + n) →
 --         Glue (Bool × Bool × (Bool ×^ n)) (adjT×^≡-invol-sides0 i0 i))
 --       swap-01
 --       (idfun _)
 -- glue-invol-Path n = glue'AdjT× (2 + n) zero
 --   -- glue
 --   --   (λ { (i = i0) → _
 --   --      ; (i = i1) → _
 --   --      })
 --   --   x


 -- Fin-adjT×^≡-invol-unglue : ∀ n →

 --               (p : ∀ n k →
 --               SquareP (λ j i → adjT×^≡-invol {A = Bool} n k j (i) → hProp ℓ-zero)
 --                  ((F×adjSnd {n} k))
 --                  (symP  (F×adjSnd {n} k))
 --                  (λ _ → Fin×Snd n)
 --                  (λ _ → Fin×Snd n))
 --                   → 
 --      SquareP (λ j i → 
 --         F×adjT≡ {n = suc (suc n)} zero j →
 --        Σ (Σ-swap-01-≡-invol-ua j i)
        
 --        (fst ∘ p (suc (suc n)) zero j i))
 --        {map-Σ (_ , Fin×Snd∘adjT× (suc (suc n)) zero)}
 --        {map-Σ (_ , λ _ → idfun _)}
 --         (congP (λ i → map-Σ {B = fst ∘ Fin×Snd (suc (suc n))}
 --                    {fst ∘ p (suc (suc n)) zero i0 i})
 --          (ΣPathPProp (λ a →
 --             isPropΠ λ a' → isProp→
 --              (snd (Fin×Snd (suc (suc n)) (a a'))))
 --               (glue'AdjT× {A = Bool} (suc (suc n)) zero)))
 --         {map-Σ (_ , λ _ → idfun _)}
 --         {map-Σ (_ , Fin×Snd∘adjT× (suc (suc n)) zero)}
 --         (congP (λ i → map-Σ {B = fst ∘ Fin×Snd (suc (suc n))}
 --                    {fst ∘ p (suc (suc n)) zero i1 i})
 --           (ΣPathPProp ((λ a →
 --             isPropΠ λ a' → isProp→
 --              (snd (Fin×Snd (suc (suc n)) (a a')))))
 --             (symP (glue'AdjT× {A = Bool} (suc (suc n)) zero))))
 --         (congP (λ _ → map-Σ )
 --             (ΣPathPProp ((λ a →
 --             isPropΠ λ a' → isProp→
 --              (snd (Fin×Snd (suc (suc n)) (a a')))))
 --                 λ i → unglue (i ∨ ~ i)))
 --         (congP (λ _ → map-Σ)
 --            ((ΣPathPProp ((λ a →
 --             isPropΠ λ a' → isProp→
 --              (snd (Fin×Snd (suc (suc n)) (a a')))))
 --                 λ i → swap-01 ∘' unglue (i ∨ ~ i))))


 -- Fin-adjT×^≡-invol-unglue n p  =
 --     isSet→SquareP (λ i j →
 --      isSet→ (isSetΣ (isOfHLevelGlue (j ∨ ~ j)
 --        {f =
 --          λ { (j = i0) → _
 --             ; (j = i1) → _
 --             }} 2
 --         (isOfHLevelUA i (adjT×^≃ zero) 2 (isOfHLevel×^ (2 + n) 2 isSetBool)))
 --           (isProp→isSet ∘ snd ∘ p (2 + n) zero i j)))
 --      _ _ _ _



