{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.Recursive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Logic using (mutex⊎)

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties

open import Cubical.Induction.WellFounded

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation renaming (rec to rec₁)
open import Cubical.HITs.SequentialColimit


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

isProp< : isProp (m < n)
isProp< {m} {n} = isProp≤ {m = suc m} {n = n}

≤-k+ : m ≤ n → k + m ≤ k + n
≤-k+ {k = zero}  m≤n = m≤n
≤-k+ {k = suc k} m≤n = ≤-k+ {k = k} m≤n

≤-+k : m ≤ n → m + k ≤ n + k
≤-+k {m} {n} {k} m≤n
  = transport (λ i → +-comm k m i ≤ +-comm k n i) (≤-k+ {m} {n} {k} m≤n)

≤-refl : ∀ m → m ≤ m
≤-refl zero = _
≤-refl (suc m) = ≤-refl m

≤-trans : k ≤ m → m ≤ n → k ≤ n
≤-trans {zero} _ _ = _
≤-trans {suc k} {suc m} {suc n} = ≤-trans {k} {m} {n}

≤-antisym : m ≤ n → n ≤ m → m ≡ n
≤-antisym {zero} {zero} _ _ = refl
≤-antisym {suc m} {suc n} m≤n n≤m = cong suc (≤-antisym m≤n n≤m)

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

≤-fromsplit : (m < n) ⊎ (m ≡ n) → m ≤ n 
≤-fromsplit {m = m} (inl x) = <-weaken {m = m} x
≤-fromsplit {m = m} (inr x) = subst (m ≤_) x (≤-refl m)

¬<-≥ : ∀ m n → ¬ m < n → n ≤ m
¬<-≥ m n ¬m<n with m ≟ n 
... | lt x = Empty.rec (¬m<n x)
... | eq x = subst (_≤ m) x (≤-refl m)
... | gt x = <-weaken {n} {m} x

≤-∸+ : ∀ {m n} → m ≤ n → (n ∸ m) + m ≡ n 
≤-∸+ {zero} _ = +-zero _
≤-∸+ {suc m} {suc n} p = +-suc _ _ ∙ cong suc (≤-∸+ {m} p)

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

module Minimal (P : ℕ → Type ℓ) where
  Least : (ℕ → Type ℓ)
  Least m = P m × (∀ n → n < m → ¬ P n)

  isPropLeast : (∀ m → isProp (P m)) → ∀ m → isProp (Least m)
  isPropLeast pP m
    = isPropΣ (pP m) (λ _ → isPropΠ3 λ _ _ _ → isProp⊥)

  Least→ : Σ _ Least → Σ _ P
  Least→ = map-snd fst

  search
    : (∀ m → Dec (P m))
    → ∀ n → (Σ[ m ∈ ℕ ] Least m) ⊎ (∀ m → m < n → ¬ P m)
  search dec zero = inr (λ _ b _ → b)
  search dec (suc n) with search dec n
  ... | inl tup = inl tup
  ... | inr ¬P<n with dec n
  ... | yes Pn = inl (n , Pn , ¬P<n)
  ... | no ¬Pn = inr λ m m≤n
      → case ≤-split m≤n of λ where
          (inl m<n) → ¬P<n m m<n
          (inr m≡n) → subst⁻ (¬_ ∘ P) m≡n ¬Pn

  →Least : (∀ m → Dec (P m)) → Σ _ P → Σ _ Least
  →Least dec (n , Pn) with search dec n
  ... | inl least = least
  ... | inr ¬P<n  = n , Pn , ¬P<n

  Least-unique : ∀ m n → Least m → Least n → m ≡ n
  Least-unique m n (Pm , ¬P<m) (Pn , ¬P<n) with m ≟ n
  ... | lt m<n = Empty.rec (¬P<n m m<n Pm)
  ... | eq m≡n = m≡n
  ... | gt n<m = Empty.rec (¬P<m n n<m Pn)

  isPropΣLeast : (∀ m → isProp (P m)) → isProp (Σ _ Least)
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

  ΣLeast≡∃P : (∀ m → isProp (P m)) → (∀ m → Dec (P m)) →
                Σ _ Least ≡ ∃ _ P 
  ΣLeast≡∃P pP dec =
   hPropExt (isPropΣLeast pP) squash₁
    (∣_∣₁ ∘ Least→)
    (rec₁ (isPropΣLeast pP) (→Least dec))
  
module MinimalPred {ℓ ℓ'} (A : Type ℓ)
 (B : A → ℕ → hProp ℓ')
 (<B : ∀ {a m n} → m ≤ n → ⟨ B a m ⟩ → ⟨ B a n ⟩)
 (B? : ∀ {a} n → Dec ⟨ B a n ⟩) where
 
 
 open Sequence


 S : Sequence (ℓ-max ℓ ℓ')
 space S n = Σ _ λ a → (fst (B a n))
 Sequence.map S {n} = map-snd (<B (<-weaken {n} (≤-refl n)))

 module _ {a : A} where
  open Minimal (fst ∘ (B a)) public

 lim→→ΣLeast : (Lim→ S) → (Σ A λ a → Σ ℕ Least)
 fst (lim→→ΣLeast (inl (a , _))) = a
 snd (lim→→ΣLeast (inl (_ , b))) = →Least B? (_ , b)
 fst (lim→→ΣLeast (push (a , _) _)) = a
 snd (lim→→ΣLeast (push {n = n} (a , b) i)) = 
   isPropΣLeast (snd ∘ B a)
     (→Least B? (_ , b))
     (→Least B? (suc n , <B ((<-weaken {n} (≤-refl n))) b)) i

 ΣLeast→lim→ : (Σ A λ a → Σ ℕ Least) → (Lim→ S)
 ΣLeast→lim→ (a , (_ , b , _)) = inl (a , b)

 secLim→→ΣLeast : section lim→→ΣLeast ΣLeast→lim→
 secLim→→ΣLeast (a , b) =
   cong (a ,_) (isPropΣLeast (snd ∘ B a) _ _)

 
 ML = λ (a : A) → Σ _ (Least {a})

 ml : ∀ a n b → ML a
 ml a n b = →Least (B? {a = a}) (n , b)

 ml< : ∀ n a b → (fst (ml a n b) < n) ⊎ (fst (ml a n b) ≡ n)
 ml< n a b =
   ≤-split (( (¬<-≥ n (fst (ml a n b))
           λ p → snd (snd (→Least B? (n , b)))
             n p b)))


 wInl : ∀ a ((m , (bₘ , _)) : ML a) n bₙ → (m < n) ⊎ (m ≡ n)
       → Path (Lim→ S) (inl {n = m} (a , bₘ)) (inl {n = n} (a , bₙ))
 wInl a (m , bₘ , _) n bₙ (inr x) i =
    inl (a , isProp→PathP (λ i → snd (B a (x i)))
     bₘ bₙ i)
 wInl a ml@(m , bₘ , _) (suc n) bₛₙ (inl x) =
   let bₙ = <B x bₘ
   in  wInl a ml n bₙ (≤-split x)
        ∙∙ push _
        ∙∙ λ i → inl (a , snd (B a (suc n))
             (<B (<-weaken {m = n} (≤-refl n)) bₙ)
             bₛₙ i)


 wSq : ∀ a n (bₙ : ⟨ B a n ⟩) (bₛₙ : ⟨ B a (suc n) ⟩) → ∀ ml ml' p p'
         →
         Square
            (wInl a ml n bₙ p)
            (wInl a ml' (suc n) _ p')
            
            (λ i → ΣLeast→lim→ ( a , isPropΣLeast (snd ∘ B a) ml ml' i ))
            (push {n = n} (a , bₙ))
 
 wSq a n bₙ bₛₙ mlₙ mlₛₙ x₁ (inr x) =
   Empty.rec (<→≢ (≤-fromsplit x₁)
    (cong fst (isPropΣLeast (snd ∘ B a) mlₙ mlₛₙ) ∙ x))
   
 wSq a n bₙ bₛₙ mlₙ mlₛₙ p (inl x) i j =
  let bₙ≡ = snd (B a n) bₙ (<B x (fst (snd mlₛₙ)))
      ml= = isPropΣLeast (snd ∘ B a) mlₙ mlₛₙ

  in hcomp
       (λ k → λ {
         (i = i0) → wInl a mlₙ n bₙ p (j ∨ ~ k)
        ;(j = i0) → wInl a
                    (ml= i)
                    n (bₙ≡ i)                     
                    (isProp→PathP
                      (λ i → snd (mutex⊎
                         (_ , isProp< {fst (ml= i)} {n})
                         (_ , isSetℕ (fst (ml= i)) _)
                         (uncurry <→≢)))
                       p
                       (≤-split {fst mlₛₙ} {n} x) i)
                    (~ k)
        ;(j = i1) → _▷_ {A = λ i' → Path (Lim→ S)
                (push (a , bₙ≡ i) i')
                (push (a , bₙ) i')}
                {a₁' = λ i' → inl {n = suc n}
                  (a , snd (B a (suc n))
                    (<B (<-weaken {m = n} (≤-refl n))
          (snd (B a n) bₙ (<B x (fst (snd mlₛₙ))) i))
          (<B (<-weaken {m = n} (≤-refl n)) bₙ) i')}
            (λ i' k → push {n = n} (a , bₙ≡ (i ∧ ~ k)) i' )
             (congP {B = λ i' z → Path (Lim→ S) _ _}
               (λ i → cong (inl ∘ (a ,_)))
              (isProp→isSet (snd (B a (suc n))) _ _ _ _ )) i k
          })
       (push (a , bₙ≡ i) (i ∧ j))
 
 retLim→→ΣLeast : retract lim→→ΣLeast ΣLeast→lim→
 retLim→→ΣLeast (inl {n} (a , b)) =
   wInl a (ml a n b) n b (ml< n a b) 

 retLim→→ΣLeast (push {n = n} (a , b) i) j =
   let bₛₙ = (<B ((<-weaken {n} (≤-refl n))) b)
   in wSq a n b bₛₙ
     (ml a n b) (ml a (suc n) bₛₙ) (ml< n a b) (ml< (suc n) a bₛₙ) i j 

 IsoLim→ΣLeast : Iso (Lim→ S) (Σ A λ a → Σ ℕ Least)
 Iso.fun IsoLim→ΣLeast = lim→→ΣLeast
 Iso.inv IsoLim→ΣLeast = ΣLeast→lim→
 Iso.rightInv IsoLim→ΣLeast = secLim→→ΣLeast
 Iso.leftInv IsoLim→ΣLeast = retLim→→ΣLeast

 isoIsoLim→∃P : (Lim→ S) ≡ (Σ A λ _ → ∃ ℕ (fst ∘ (B _)))
 isoIsoLim→∃P = isoToPath IsoLim→ΣLeast ∙
   cong (Σ A) (funExt λ a → ΣLeast≡∃P (snd ∘ B a) B?)
