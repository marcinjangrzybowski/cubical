{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.Recursive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence

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

  ΣLeast≡∃P : (∀ m → isProp (P m)) → (∀ m → Dec (P m)) →
                Σ _ (Least P) ≡ ∃ _ P 
  ΣLeast≡∃P pP dec =
   hPropExt (isPropΣLeast pP) squash₁
    (∣_∣₁ ∘ Least→)
    (rec₁ (isPropΣLeast pP) (→Least dec))
  
module MinimalPred {ℓ ℓ'} (A : Type ℓ)
 (B : A → ℕ → hProp ℓ')
 (<B : ∀ {a m n} → m ≤ n → ⟨ B a m ⟩ → ⟨ B a n ⟩)
 (B? : ∀ {a} n → Dec ⟨ B a n ⟩) where
 
 ⟨B⟩ : A → ℕ → Type ℓ'
 ⟨B⟩ = λ a n → fst (B a n)
 
 open Sequence
 
 S : Sequence (ℓ-max ℓ ℓ')
 space S n = Σ _ λ a → ⟨B⟩ a n
 Sequence.map S {n} = map-snd (<B (<-weaken {n} (≤-refl n)))


 lim→→ΣLeast : (Lim→ S) → (Σ A λ a → Σ ℕ (Minimal.Least (⟨B⟩ a)))
 fst (lim→→ΣLeast (inl (a , _))) = a
 snd (lim→→ΣLeast (inl (_ , b))) = Minimal.→Least B? (_ , b)
 fst (lim→→ΣLeast (push (a , _) _)) = a
 snd (lim→→ΣLeast (push {n = n} (a , b) i)) = 
   Minimal.isPropΣLeast (snd ∘ B a)
     (Minimal.→Least B? (_ , b))
     (Minimal.→Least B? (suc n , <B ((<-weaken {n} (≤-refl n))) b)) i

 ΣLeast→lim→ : (Σ A λ a → Σ ℕ (Minimal.Least (⟨B⟩ a))) → (Lim→ S)
 ΣLeast→lim→ (a , (_ , b , _)) = inl (a , b)

 secLim→→ΣLeast : section lim→→ΣLeast ΣLeast→lim→
 secLim→→ΣLeast (a , b) =
   cong (a ,_) (Minimal.isPropΣLeast (snd ∘ B a) _ _)

 w : ∀ m n n-m (m+n≡ : n ≡ (n-m) + m) a bₘ b → (m < n) ⊎ (m ≡ n) →
       Path (Lim→ S)
        (inl {n = m} (a , bₘ)) (inl {n = n} (a , b)) 
 w m (suc n) zero m+n≡ a bₘ b (inl x) = Empty.rec (<→≢ x (sym m+n≡))
 w m (suc n) (suc n-m) m+n≡ a bₘ b (inl x) =
   let bₙ = <B x bₘ
   in w m
       n n-m (injSuc m+n≡)
        a bₘ bₙ
             (≤-split x) ∙∙
        push {n = n} (a , bₙ)
        ∙∙ cong {B = λ _ → Lim→ S}
           (λ b → inl (a , b))
          (snd (B a (suc n)) (<B (<-weaken {m = n} {n = suc n} (≤-refl n)) bₙ)
                             b)           
 w m n _ _ a bₘ b (inr x) i =
  inl (a , isProp→PathP (λ i → snd (B a (x i))) bₘ b i)


 -- wSq : ∀ m n n-m (m+n≡ : n ≡ (n-m) + m) sn-m sn-m≡ a bₘ  b b' m≤n m≤sn →
 --       Square
 --          (w m n n-m m+n≡ a bₘ b  m≤n)
 --          {!!}
 --          {!!}
 --          (push {n = n} (a , b))
        
 -- wSq m n n-m m+n≡ sn-m sn-m≡ a bₘ b m≤n m≤sn i j = {!!}

 wInl : ∀ n a b → ΣLeast→lim→ (lim→→ΣLeast (inl {n = n} (a , b))) ≡ inl (a , b) 
 wInl n a b =
  let n₀ = fst (Minimal.→Least B? (n , b))
      q = ( (¬<-≥ n n₀
           λ p → snd (snd (Minimal.→Least B? (n , b)))
             n p b))
  in w n₀ n (n ∸ n₀)
      (sym (≤-∸+ {n₀} {n} q)) a _ _
        (≤-split q)

 wSq' : ∀ n a (b : ⟨B⟩ a n) (b' : ⟨ B a (suc n) ⟩) → ∀ nn p p' →
         Square
            (wInl n a b)
            (w _ (suc n)
                nn
                p _ _ _ p')
            
            (λ i → ΣLeast→lim→ (lim→→ΣLeast (push (a , b) i)))
            (push {n = n} (a , b))
 wSq' n a b b' zero p (inl x) = Empty.rec (<→≢ x (sym p))
 wSq' n a b b' (suc nn) p (inl x) i j =
  let bs = <B {a = a} (<-weaken {n} {suc n} (≤-refl n)) b
      b'' = <B x (fst (snd (Minimal.→Least B? (suc n , bs))))
      bP = snd (B a n) b b''
      mlu = Minimal.Least-unique ((fst (Minimal.→Least B? (n , b)))) (fst (Minimal.→Least B? (suc n , bs)))
              (((snd (Minimal.→Least B? (n , b)))))
              ((snd (Minimal.→Least B? (suc n , bs))))
      nnP : _ ≡ _
      nnP = λ i → +-cancel-∸ n nn (mlu i)
             (injSuc p ∙ λ j → nn + mlu (i ∨ (~ j))) i
      split<P : PathP (λ i → mlu i ≤ n)
                   (((¬<-≥ n (fst (Minimal.→Least B? (n , b)))
          (λ p₁ → snd (snd (Minimal.→Least B? (n , b))) n p₁ b))))
                   x       
      split<P = isProp→PathP (λ i → isProp≤ {mlu i} {n = n}) _ _

  in hcomp
      (λ k → λ {
        (i = i0) → wInl n a b (j ∨ ~ k)
       ;(j = i0) → 
           -- hcomp
           --   (λ k' → λ {
           --     (k = i0) → inl (a , bP i)
           --    ;(k = i1) → inl {n = mlu i} (a , {!!})
           --    ;(i = i0) → wInl n a b (~ k)
           --    ;(i = i1) → (w (fst (Minimal.→Least B? (suc n , _))) n
           --      nn
           --      (injSuc p) a
           --      ((fst
           -- (snd
           --  (Minimal.→Least B?
           --   (suc n , bs)))))
           --       ((<B {a = a} {n = n} x
           -- (fst
           --  (snd
           --   (Minimal.→Least B? (suc n , bs)))))) (≤-split x) (~ k))
           --    })
             (w
              (mlu i) n (nnP i)
                {!!}
               -- (isProp→PathP
               --     (λ i → isSetℕ n (nnP i + mlu i))
               --     (sym (≤-∸+ {{!!}}
               --      (¬<-≥ n (fst (Minimal.→Least B? (n , b)))
               --       (λ p₁ → snd (snd (Minimal.→Least B? (n , b))) n p₁ b))))
               --     (injSuc p)
               --  i)
-- Goal: n ≡
--       +-cancel-∸ n nn
--       (Minimal.Least-unique (fst (Minimal.→Least B? (n , b)))
--        (fst (Minimal.→Least B? (suc n , bs)))
--        (snd (Minimal.→Least B? (n , b)))
--        (snd (Minimal.→Least B? (suc n , bs))) i)
--       (injSuc p ∙
--        (λ j₁ →
--           nn +
--           Minimal.Least-unique (fst (Minimal.→Least B? (n , b)))
--           (fst (Minimal.→Least B? (suc n , bs)))
--           (snd (Minimal.→Least B? (n , b)))
--           (snd (Minimal.→Least B? (suc n , bs))) (i ∨ ~ j₁)))
--       i
--       +
--       Minimal.Least-unique (fst (Minimal.→Least B? (n , b)))
--       (fst (Minimal.→Least B? (suc n , bs)))
--       (snd (Minimal.→Least B? (n , b)))
--       (snd (Minimal.→Least B? (suc n , bs))) i
-- ———— Boundary (wanted) —————————————————————————————————————
-- i = i0 ⊢ (λ i₁ →
--             ≤-∸+
--             (¬<-≥ n (fst (Minimal.→Least B? (n , b)))
--              (λ p₁ → snd (snd (Minimal.→Least B? (n , b))) n p₁ b))
--             (~ i₁))
-- i = i1 ⊢ (injSuc p)

               a {!!} (bP i)
                (≤-split (split<P i)) (~ k) ) 
       ;(j = i1) →  
           hcomp
             (λ k' → λ {
               (k = i0) → push (a , bP (i ∧ k')) i
              ;(k = i1) → push (a , b) i
              ;(i = i0) → inl {n = n} (a , b)
              ;(i = i1) → inl {n = suc n} (a , 
                    
                 isSet→SquareP
                   (λ _ _ → isProp→isSet (snd (B a (suc n))))
                   (λ i  → <B {a = a} (<-weaken {n} {suc n} (≤-refl n)) (bP i))
                   (λ _ → bs)
                   (λ _ → bs)
                   ((snd (B a (suc n)) (<B (<-weaken {m = n} {n = suc n} (≤-refl n)) _))
                      bs ) k k'
                   )
              })
             (push (a , b) i) 
       }) ((push {n = n}
          (a , bP i)
          (i ∧ j)))

 wSq' n a b b' nn p (inr x) =
  let (n₀ , n₀L) = Minimal.→Least B? (n , b)
      (n₀' , n₀L') = Minimal.→Least B? (suc n , snd (S .Sequence.map (a , b)))
      q = ( (¬<-≥ n n₀
           λ p → snd (snd (Minimal.→Least B? (n , b)))
             n p b))
  in Empty.rec (<→≢ {n₀} {suc n} q
        (Minimal.Least-unique _ _ n₀L n₀L' ∙ x))

 retLim→→ΣLeast : retract lim→→ΣLeast ΣLeast→lim→
 retLim→→ΣLeast (inl {n} (a , b)) = wInl n a b

 retLim→→ΣLeast (push {n = n} (a , b) i) j =
   wSq' n a b (<B ((<-weaken {n} (≤-refl n))) b)
    ((suc n ∸ fst (Minimal.→Least (B? {a = a}) (suc n ,
      snd (S .Sequence.map (a , b)))) ))
    ((λ i₁ →
            ≤-∸+
            {fst
             (Minimal.→Least {ℓ'}
              {λ z →
                 ⟨_⟩ {ℓ'} {ℓ'} {isOfHLevel {ℓ'} 1}
                 (B (fst (S .Sequence.map {n} (a , b))) z)}
              (B? {fst (S .Sequence.map {n} (a , b))})
              (suc n , snd (S .Sequence.map {n} (a , b))))}
            {suc n}
            (¬<-≥ (suc n)
             (fst
              (Minimal.→Least {ℓ'}
               {λ z →
                  ⟨_⟩ {ℓ'} {ℓ'} {isOfHLevel {ℓ'} 1}
                  (B (fst (S .Sequence.map {n} (a , b))) z)}
               (B? {fst (S .Sequence.map {n} (a , b))})
               (suc n , snd (S .Sequence.map {n} (a , b)))))
             (λ p →
                snd
                (snd
                 (Minimal.→Least {ℓ'}
                  {λ z →
                     ⟨_⟩ {ℓ'} {ℓ'} {isOfHLevel {ℓ'} 1}
                     (B (fst (S .Sequence.map {n} (a , b))) z)}
                  (B? {fst (S .Sequence.map {n} (a , b))})
                  (suc n , snd (S .Sequence.map {n} (a , b)))))
                (suc n) p (snd (S .Sequence.map {n} (a , b)))))
            (~ i₁)))
    ((≤-split
          {fst
           (Minimal.→Least {ℓ'}
            {λ z →
               ⟨_⟩ {ℓ'} {ℓ'} {isOfHLevel {ℓ'} 1}
               (B (fst (S .Sequence.map {n} (a , b))) z)}
            (B? {fst (S .Sequence.map {n} (a , b))})
            (suc n , snd (S .Sequence.map {n} (a , b))))}
          {suc n}
          (¬<-≥ (suc n)
           (fst
            (Minimal.→Least {ℓ'}
             {λ z →
                ⟨_⟩ {ℓ'} {ℓ'} {isOfHLevel {ℓ'} 1}
                (B (fst (S .Sequence.map {n} (a , b))) z)}
             (B? {fst (S .Sequence.map {n} (a , b))})
             (suc n , snd (S .Sequence.map {n} (a , b)))))
           (λ p →
              snd
              (snd
               (Minimal.→Least {ℓ'}
                {λ z →
                   ⟨_⟩ {ℓ'} {ℓ'} {isOfHLevel {ℓ'} 1}
                   (B (fst (S .Sequence.map {n} (a , b))) z)}
                (B? {fst (S .Sequence.map {n} (a , b))})
                (suc n , snd (S .Sequence.map {n} (a , b)))))
              (suc n) p (snd (S .Sequence.map {n} (a , b))))))) i j


--  XX : Iso (Lim→ S) (Σ A λ a → Σ ℕ (Minimal.Least (⟨B⟩ a)))
--  Iso.fun XX = lim→→ΣLeast
--  Iso.inv XX = ΣLeast→lim→
--  Iso.rightInv XX = secLim→→ΣLeast
--  Iso.leftInv XX = retLim→→ΣLeast

-- open Minimal using (Decidable→Collapsible) public
