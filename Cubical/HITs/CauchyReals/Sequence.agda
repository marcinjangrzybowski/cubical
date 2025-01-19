{-# OPTIONS --lossy-unification #-}

module Cubical.HITs.CauchyReals.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv hiding (_■)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

import Cubical.Functions.Logic as L

open import Cubical.Algebra.CommRing.Instances.Int

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Bool.Base using () renaming (Bool to 𝟚 ; true to 1̂ ; false to 0̂)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
open import Cubical.Data.Nat.Order.Recursive as OR
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Sigma hiding (Path)
open import Cubical.Data.List as L
open import Cubical.Data.List using () renaming (List to ⟦_⟧)
open import Cubical.Foundations.Interpolate
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Data.Rationals using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Data.NatPlusOne
open import Cubical.Foundations.Path
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Rationals using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.Properties as ℚ using (invℚ₊;/2₊;x/2<x;/4₊;invℚ)

open import Cubical.Data.NatPlusOne
open import Cubical.Foundations.Path
open import Cubical.Foundations.CartesianKanOps


import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base


import Cubical.Algebra.CommRing as CR

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse

import Cubical.Algebra.CommRing as CR
import Cubical.Algebra.Ring as RP


Seq : Type
Seq = ℕ → ℝ




≤ᵣ-·ᵣo : ∀ m n (o : ℝ₊) →  m ≤ᵣ n → (m ·ᵣ (fst o) ) ≤ᵣ (n ·ᵣ (fst o))
≤ᵣ-·ᵣo m n o p =
  ≡ContinuousWithPred _ _
     (openPred< 0) (openPred< 0)
     (λ o _ → maxᵣ (m ·ᵣ o) (n ·ᵣ o) )
     (λ o _ → n ·ᵣ o)
     (contDiagNE₂WP maxR _
        _ _
       (cont₂·ᵣWP _ _ _ ((AsContinuousWithPred _ _ (IsContinuousConst _)))
          (AsContinuousWithPred _ _ (IsContinuousId)))
       ((cont₂·ᵣWP _ _ _ (AsContinuousWithPred _ _ (IsContinuousConst _))
         (AsContinuousWithPred _ _ (IsContinuousId)))))
     ((cont₂·ᵣWP _ _ _ (AsContinuousWithPred _ _ (IsContinuousConst _))
       (AsContinuousWithPred _ _ (IsContinuousId))))
     (λ r 0<r _ → ≤ᵣ-·o m n (r , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<r)) p)
       (fst o) (snd o) (snd o)


≤ᵣ-o·ᵣ : ∀ m n (o : ℝ₊) →  m ≤ᵣ n → ((fst o) ·ᵣ m   ) ≤ᵣ ((fst o) ·ᵣ n)
≤ᵣ-o·ᵣ m n o p = subst2 _≤ᵣ_
  (·ᵣComm _ _)
  (·ᵣComm _ _)
  (≤ᵣ-·ᵣo m n o p)

≤ᵣ₊Monotone·ᵣ : ∀ m (n : ℝ₊) (o : ℝ₊) s
       → m ≤ᵣ (fst n) → fst o ≤ᵣ s
       → (m ·ᵣ fst o) ≤ᵣ (fst n ·ᵣ s)
≤ᵣ₊Monotone·ᵣ m (n , 0<n) (o , 0<o) s m≤n o≤s =
  isTrans≤ᵣ _ _ _ (≤ᵣ-·ᵣo m n (o , 0<o) m≤n)
    (≤ᵣ-o·ᵣ o s (n , 0<n) o≤s)




ℝ₊· : (m : ℝ₊) (n : ℝ₊) → 0 <ᵣ (fst m) ·ᵣ (fst n)
ℝ₊· (m , 0<m) (n , 0<n) = PT.map2
  (λ ((q , q') , 0≤q , q<q' , q'≤m) →
   λ ((r , r') , 0≤r , r<r' , r'≤n) →
    let 0<r' = ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ 0 r 0≤r) r<r'
        qr₊ = (q' , ℚ.<→0< _ (ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ 0 q 0≤q) q<q'))
               ℚ₊· (r' , ℚ.<→0< _ 0<r')
    in (fst (/2₊ qr₊) , fst qr₊) ,
         ≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ (/2₊ qr₊)) ,
           x/2<x qr₊ ,
           subst (_≤ᵣ (m ·ᵣ n))
             (sym (rat·ᵣrat q' r'))
              (≤ᵣ₊Monotone·ᵣ (rat q')
                (m , 0<m) (rat r' , <ℚ→<ᵣ _ _ 0<r') n
                             q'≤m r'≤n) ) 0<m 0<n

_₊·ᵣ_ : ℝ₊ → ℝ₊  → ℝ₊
(m , 0<m) ₊·ᵣ (n , 0<n) = _ , ℝ₊· (m , 0<m) (n , 0<n)

_₊／ᵣ₊_ : ℝ₊ → ℝ₊  → ℝ₊
(q , 0<q) ₊／ᵣ₊ (r , 0<r) = (q ／ᵣ[ r , inl (0<r) ] ,
  ℝ₊· (q , 0<q) (_ , invℝ-pos r 0<r) )




0<1/x : ∀ x 0＃x → 0 <ᵣ x → 0 <ᵣ invℝ x 0＃x
0<1/x x 0＃x 0<x = ℝ₊·
  (_ , 0<signᵣ x 0＃x 0<x)
  (_ , invℝ'-pos (absᵣ x) (0＃→0<abs x 0＃x))

<ᵣ-·ᵣo : ∀ m n (o : ℝ₊) →  m <ᵣ n → (m ·ᵣ (fst o)) <ᵣ (n ·ᵣ (fst o))
<ᵣ-·ᵣo m n (o , 0<o) p =
  let z = subst (0 <ᵣ_) (·DistR+ n (-ᵣ m) o ∙
                   cong ((n ·ᵣ o) +ᵣ_) (-ᵣ· m o))
           (ℝ₊· (_ , x<y→0<y-x _ _ p) (o , 0<o))
  in 0<y-x→x<y _ _ z

<ᵣ-o·ᵣ : ∀ m n (o : ℝ₊) →  m <ᵣ n → ((fst o) ·ᵣ m) <ᵣ ((fst o) ·ᵣ n )
<ᵣ-o·ᵣ m n (o , 0<o) p =
  subst2 (_<ᵣ_)
    (·ᵣComm _ _) (·ᵣComm _ _) (<ᵣ-·ᵣo m n (o , 0<o) p)



/nᵣ : ℕ₊₁ → ℝ → ℝ
/nᵣ n = fst (fromLipschitz ([ 1 / n ] , _)
  (_ , Lipschitz-rat∘ ([ 1 / n ] , _) (ℚ._· [ 1 / n ])
   λ q r ε x →
     subst (ℚ._< ([ 1 / n ]) ℚ.· (fst ε))
      (sym (ℚ.pos·abs [ 1 / n ] (q ℚ.- r)
       (ℚ.<Weaken≤ 0 [ 1 / n ]
           ( (ℚ.0<→< [ 1 / n ] _))))
       ∙ cong ℚ.abs (ℚ.·Comm _ _ ∙ ℚ.·DistR+ q (ℚ.- r) [ 1 / n ]
        ∙ cong ((q ℚ.· [ 1 / n ]) ℚ.+_)
            (sym (ℚ.·Assoc -1 r [ 1 / n ]))))
      (ℚ.<-o· (ℚ.abs (q ℚ.- r)) (fst ε) [ 1 / n ]
       ((ℚ.0<→< [ 1 / n ] _))
       x)))


seqSumUpTo : (ℕ → ℝ) → ℕ →  ℝ
seqSumUpTo s zero = 0
seqSumUpTo s (suc n) = s zero +ᵣ seqSumUpTo (s ∘ suc) n

seqSumUpTo· : ∀ s r n → seqSumUpTo s n ·ᵣ r ≡ seqSumUpTo ((_·ᵣ r) ∘ s) n
seqSumUpTo· s r zero = 𝐑'.0LeftAnnihilates r
seqSumUpTo· s r (suc n) =
  ·DistR+ (s zero) (seqSumUpTo (s ∘ suc) n) r ∙
   cong ((s zero ·ᵣ r) +ᵣ_) (seqSumUpTo· (s ∘ suc) r n)



seqSumUpTo' : (ℕ → ℝ) → ℕ →  ℝ
seqSumUpTo' s zero = 0
seqSumUpTo' s (suc n) = seqSumUpTo' s n +ᵣ s n

seqΣ : Seq → Seq
seqΣ = seqSumUpTo'

seqΣ' : Seq → Seq
seqΣ' = seqSumUpTo


seqSumUpTo-suc : ∀ f n → seqSumUpTo f n +ᵣ f n ≡
      f zero +ᵣ seqSumUpTo (λ x → f (suc x)) n
seqSumUpTo-suc f zero = +ᵣComm _ _
seqSumUpTo-suc f (suc n) =
  sym (+ᵣAssoc _ _ _) ∙
    cong ((f zero) +ᵣ_ ) (seqSumUpTo-suc _ _)

seqSumUpTo≡seqSumUpTo' : ∀ f n → seqSumUpTo' f n ≡ seqSumUpTo f n
seqSumUpTo≡seqSumUpTo' f zero = refl
seqSumUpTo≡seqSumUpTo' f (suc n) =
 cong (_+ᵣ (f n)) (seqSumUpTo≡seqSumUpTo' (f) n) ∙
   seqSumUpTo-suc f n

<-·sk-cancel : ∀ {m n k} → m ℕ.· suc k ℕ.< n ℕ.· suc k → m ℕ.< n
<-·sk-cancel {n = zero} x = ⊥.rec (ℕ.¬-<-zero x)
<-·sk-cancel {zero} {n = suc n} x = ℕ.suc-≤-suc (ℕ.zero-≤ {n})
<-·sk-cancel {suc m} {n = suc n} {k} x =
  ℕ.suc-≤-suc {suc m} {n}
    (<-·sk-cancel {m} {n} {k}
     (ℕ.≤-k+-cancel (subst (ℕ._≤ (k ℕ.+ n ℕ.· suc k))
       (sym (ℕ.+-suc _ _)) (ℕ.pred-≤-pred x))))

2≤x→1<quotient[x/2] : ∀ n → 0 ℕ.< (ℕ.quotient (2 ℕ.+ n) / 2)
2≤x→1<quotient[x/2] n =
 let z : 0 ℕ.<
             ((ℕ.quotient (2 ℕ.+ n) / 2) ℕ.· 2)
     z = subst (0 ℕ.<_) (ℕ.·-comm _ _)
          (ℕ.≤<-trans ℕ.zero-≤ (ℕ.<-k+-cancel (subst (ℕ._< 2 ℕ.+
             (2 ℕ.· (ℕ.quotient (2 ℕ.+ n) / 2)))
           (ℕ.≡remainder+quotient 2 (2 ℕ.+ n))
             (ℕ.<-+k {k = 2 ℕ.· (ℕ.quotient (2 ℕ.+ n) / 2)}
              (ℕ.mod< 1 (2 ℕ.+ n))))))
 in <-·sk-cancel {0} {ℕ.quotient (2 ℕ.+ n) / 2 } {k = 1}
     z


open ℕ.Minimal

log2ℕ : ∀ n → Σ _ (Least (λ k → n ℕ.< 2 ^ k))
log2ℕ n = w n n ℕ.≤-refl
 where

  w : ∀ N n → n ℕ.≤ N
          → Σ _ (Least (λ k → n ℕ.< 2 ^ k))
  w N zero x = 0 , (ℕ.≤-refl , λ k' q → ⊥.rec (ℕ.¬-<-zero q))
  w N (suc zero) x = 1 , (ℕ.≤-refl ,
     λ { zero q → ℕ.<-asym (ℕ.suc-≤-suc ℕ.≤-refl)
      ; (suc k') q → ⊥.rec (ℕ.¬-<-zero (ℕ.pred-≤-pred q))})
  w zero (suc (suc n)) x = ⊥.rec (ℕ.¬-<-zero x)
  w (suc N) (suc (suc n)) x =
   let (k , (X , Lst)) = w N
          (ℕ.quotient 2 ℕ.+ n / 2)
          (ℕ.≤-trans (ℕ.pred-≤-pred (ℕ.2≤x→quotient[x/2]<x n))
             (ℕ.pred-≤-pred x))
       z = ℕ.≡remainder+quotient 2 (2 ℕ.+ n)
       zz = ℕ.<-+-≤ X X
       zzz : suc (suc n) ℕ.< (2 ^ suc k)
       zzz = subst2 (ℕ._<_)
           (ℕ.+-comm _ _
              ∙ sym (ℕ.+-assoc ((ℕ.remainder 2 ℕ.+ n / 2)) _ _)
               ∙ cong ((ℕ.remainder 2 ℕ.+ n / 2) ℕ.+_)
             ((cong ((ℕ.quotient 2 ℕ.+ n / 2) ℕ.+_)
              (sym (ℕ.+-zero (ℕ.quotient 2 ℕ.+ n / 2)))))
             ∙ z)
           (cong ((2 ^ k) ℕ.+_) (sym (ℕ.+-zero (2 ^ k))))
           (ℕ.≤<-trans
             (ℕ.≤-k+ (ℕ.≤-+k (ℕ.pred-≤-pred (ℕ.mod< 1 (2 ℕ.+ n))))) zz)
   in (suc k)
       , zzz
        , λ { zero 0'<sk 2+n<2^0' →
                ⊥.rec (ℕ.¬-<-zero (ℕ.pred-≤-pred 2+n<2^0'))
            ; (suc k') k'<sk 2+n<2^k' →
               Lst k' (ℕ.pred-≤-pred k'<sk)
                (<-·sk-cancel {k = 1}
                    (subst2 ℕ._<_ (ℕ.·-comm _ _) (ℕ.·-comm _ _)
                      (ℕ.≤<-trans (_ , z)
                         2+n<2^k' )))}





0<x^ⁿ : ∀ x n → 0 <ᵣ x → 0 <ᵣ (x ^ⁿ n)
0<x^ⁿ x zero x₁ = <ℚ→<ᵣ _ _ (𝟚.toWitness {Q = ℚ.<Dec 0 1} tt)
0<x^ⁿ x (suc n) x₁ = ℝ₊· (_ , 0<x^ⁿ x n x₁) (_ , x₁)


geometricProgression : ℝ → ℝ → ℕ → ℝ
geometricProgression a r zero = a
geometricProgression a r (suc n) =
  (geometricProgression a r n) ·ᵣ r

geometricProgressionClosed : ∀ a r n →
 geometricProgression a r n ≡ a ·ᵣ (r ^ⁿ n)
geometricProgressionClosed a r zero = sym (·IdR a)
geometricProgressionClosed a r (suc n) =
  cong (_·ᵣ r) (geometricProgressionClosed a r n) ∙
   sym (·ᵣAssoc _ _ _)

geometricProgression-suc : ∀ a r n →
   geometricProgression a r (suc n) ≡
    geometricProgression (a ·ᵣ r) r n
geometricProgression-suc a r zero = refl
geometricProgression-suc a r (suc n) =
  cong (_·ᵣ r) (geometricProgression-suc a r n)


geometricProgression-suc' : ∀ a r n →
   geometricProgression a r (suc n) ≡
    geometricProgression (a) r n  ·ᵣ r
geometricProgression-suc' a r _ = refl

Sₙ : ℝ → ℝ → ℕ → ℝ
Sₙ a r = seqSumUpTo (geometricProgression a r)


Sₙ-suc : ∀ a r n → Sₙ a r (suc n) ≡ (a +ᵣ (Sₙ a r n ·ᵣ r ))
Sₙ-suc a r n = cong (a +ᵣ_) (sym (seqSumUpTo· (geometricProgression a r) r n) )


SₙLem' : ∀ a n r → (Sₙ a r n) ·ᵣ (1 +ᵣ (-ᵣ r))  ≡
                   a ·ᵣ (1 +ᵣ (-ᵣ (r ^ⁿ n)))
SₙLem' a n r =
 let z : Sₙ a r n +ᵣ geometricProgression a r n
            ≡ (a +ᵣ (Sₙ a r n ·ᵣ r))
     z = cong (_+ᵣ (geometricProgression a r n))
           (sym (seqSumUpTo≡seqSumUpTo' (geometricProgression a r) n))
            ∙∙ seqSumUpTo≡seqSumUpTo' (geometricProgression a r) _
          ∙∙ Sₙ-suc a r n
     z' = ((sym (+IdR _) ∙ cong ((Sₙ a r n +ᵣ (-ᵣ (Sₙ a r n ·ᵣ r))) +ᵣ_)
             (sym (+-ᵣ (geometricProgression a r n))))
           ∙ 𝐑'.+ShufflePairs _ _ _ _ )
         ∙∙ cong₂ _+ᵣ_ z (
           (+ᵣComm (-ᵣ (Sₙ a r n ·ᵣ r))
              (-ᵣ (geometricProgression a r n)))) ∙∙
            (𝐑'.+ShufflePairs _ _ _ _ ∙
              cong ((a +ᵣ (-ᵣ (geometricProgression a r n))) +ᵣ_)
             ( (+-ᵣ (Sₙ a r n ·ᵣ r))) ∙ +IdR _)
 in (·DistL+ (Sₙ a r n) 1 (-ᵣ r)
      ∙ cong₂ _+ᵣ_ (·IdR (Sₙ a r n)) (𝐑'.-DistR· (Sₙ a r n) r))
      ∙∙ z' ∙∙ (cong₂ _+ᵣ_ (sym (·IdR a))
       (cong (-ᵣ_) (geometricProgressionClosed a r n) ∙
        sym (𝐑'.-DistR· _ _))
     ∙ sym (·DistL+ a 1 (-ᵣ ((r ^ⁿ (n))))))

SₙLem : ∀ a r (0＃1-r : 0 ＃ (1 +ᵣ (-ᵣ r))) n →
              (Sₙ a r n)   ≡
                   a ·ᵣ ((1 +ᵣ (-ᵣ (r ^ⁿ n)))
                     ／ᵣ[ (1 +ᵣ (-ᵣ r)) , 0＃1-r ])
SₙLem a r 0＃1-r n =
     x·y≡z→x≡z/y (Sₙ a r n)
       (a ·ᵣ (1 +ᵣ (-ᵣ (r ^ⁿ n))))
        _ 0＃1-r (SₙLem' a n r)
      ∙ sym (·ᵣAssoc _ _ _)

Sₙ-sup : ∀ a r n → (0 <ᵣ a) → (0 <ᵣ r) → (r<1 : r <ᵣ 1) →
                (Sₙ a r n)
                <ᵣ (a ·ᵣ (invℝ (1 +ᵣ (-ᵣ r)) (inl (x<y→0<y-x _ _ r<1))))
Sₙ-sup a r n a<0 0<r r<1  =
   isTrans≤<ᵣ _ _ _ (≡ᵣWeaken≤ᵣ _ _ (SₙLem a r _ n))
     (<ᵣ-o·ᵣ _ _ (a , a<0)
      (isTrans<≤ᵣ _ _ _
          (<ᵣ-·ᵣo (1 +ᵣ (-ᵣ (r ^ⁿ n))) 1
            (invℝ (1 +ᵣ (-ᵣ r)) (inl (x<y→0<y-x _ _ r<1)) ,
              0<1/x _ _ (( (x<y→0<y-x _ _ r<1))))
            (isTrans<≤ᵣ _ _ _
               (<ᵣ-o+ _ _ 1 (-ᵣ<ᵣ 0 (r ^ⁿ n) (0<x^ⁿ r n 0<r)))
               (≡ᵣWeaken≤ᵣ _ _ (+IdR _)) ))
          (≡ᵣWeaken≤ᵣ _ _ (·IdL _ ) )))

Seq<→Σ< : (s s' : Seq) →
  (∀ n → s n <ᵣ s' n) →
   ∀ n → seqSumUpTo s (suc n) <ᵣ seqSumUpTo s' (suc n)
Seq<→Σ< s s' x zero = subst2 _<ᵣ_
  (sym (+IdR _)) (sym (+IdR _)) (x 0)
Seq<→Σ< s s' x (suc n) = <ᵣMonotone+ᵣ _ _ _ _
 (x 0) (Seq<→Σ< (s ∘ suc) (s' ∘ suc) (x ∘ suc) n)

Seq≤→Σ≤ : (s s' : Seq) →
  (∀ n → s n ≤ᵣ s' n) →
   ∀ n → seqSumUpTo s n ≤ᵣ seqSumUpTo s' n
Seq≤→Σ≤ s s' x zero = ≤ᵣ-refl _
Seq≤→Σ≤ s s' x (suc n) = ≤ᵣMonotone+ᵣ _ _ _ _
 (x 0) (Seq≤→Σ≤ (s ∘ suc) (s' ∘ suc) (x ∘ suc) n)

Seq'≤→Σ≤ : (s s' : Seq) →
  (∀ n → s n ≤ᵣ s' n) →
   ∀ n → seqSumUpTo' s n ≤ᵣ seqSumUpTo' s' n
Seq'≤→Σ≤ s s' x zero = ≤ᵣ-refl _
Seq'≤→Σ≤ s s' x (suc n) =
 ≤ᵣMonotone+ᵣ _ _ _ _
 (Seq'≤→Σ≤ s s' x n)  (x n)

0≤seqΣ : ∀ s → (∀ n → 0 ≤ᵣ s n)
            → ∀ n → 0 ≤ᵣ seqΣ s n
0≤seqΣ s x zero = ≤ᵣ-refl _
0≤seqΣ s x (suc n) =
  ≤ᵣMonotone+ᵣ _ _ _ _ (0≤seqΣ s x n) (x n)

seriesDiff : (s : Seq)  →
  ∀ N n → (seqΣ s (n ℕ.+ N) +ᵣ (-ᵣ seqΣ s N)) ≡
     seqΣ (s ∘ (ℕ._+ N)) n
seriesDiff s N zero = +-ᵣ (seqΣ s N)
seriesDiff s N (suc n) =
  cong (_+ᵣ _) (+ᵣComm _ _) ∙∙
  sym (+ᵣAssoc _ _ _) ∙∙
   cong (s (n ℕ.+ N) +ᵣ_) (seriesDiff s N n)
    ∙ +ᵣComm (s (n ℕ.+ N)) (seqΣ (s ∘ (ℕ._+ N)) n)


IsCauchySequence : Seq → Type
IsCauchySequence s =
  ∀ (ε : ℝ₊) → Σ[ N ∈ ℕ ] (∀ m n → N ℕ.< n → N ℕ.< m →
    absᵣ ((s n) +ᵣ (-ᵣ (s m))) <ᵣ fst ε   )


IsConvSeries : Seq → Type
IsConvSeries s =
    ∀ (ε : ℝ₊) →
     Σ[ N ∈ ℕ ] ∀ n m →
       absᵣ (seqΣ (s ∘ (ℕ._+ (n ℕ.+ (suc N)))) m) <ᵣ fst ε


IsoIsConvSeriesIsCauchySequenceSum : (s : Seq) →
  Iso (IsConvSeries s) (IsCauchySequence (seqΣ s))
IsoIsConvSeriesIsCauchySequenceSum s =
   codomainIsoDep λ ε →
     Σ-cong-iso-snd λ N →
        isProp→Iso (isPropΠ2 λ _ _ → squash₁)
         (isPropΠ4 λ _ _ _ _ → squash₁ )
         (λ f → ℕ.elimBy≤
           (λ n n' X <n <n' → subst (_<ᵣ fst ε)
             (minusComm-absᵣ _ _) (X <n' <n))
           λ n n' n≤n' N<n' N<n →
              subst ((_<ᵣ fst ε) ∘ absᵣ)
                 (cong (λ x → seqΣ (s ∘ (ℕ._+ x)) (n' ∸ n))
                    (ℕ.[n-m]+m (suc N) n N<n)
                   ∙∙ sym (seriesDiff s n (n' ∸ n)) ∙∙
                   cong (_+ᵣ (-ᵣ seqΣ s n))
                     (cong (seqΣ s)
                       (ℕ.[n-m]+m n n' n≤n')))
                 (f (n ∸ (suc N)) (n' ∸ n)))
         λ f n m →
           subst ((_<ᵣ fst ε) ∘ absᵣ)
             (seriesDiff s (n ℕ.+ suc N) m)
               (f (n ℕ.+ (suc N)) (m ℕ.+ (n ℕ.+ suc N))
               (subst (N ℕ.<_) (sym (ℕ.+-assoc _ _ _))
                 (ℕ.≤SumRight {suc N} {m ℕ.+ n}))
               (ℕ.≤SumRight {suc N} {n}))


IsConvSeries≃IsCauchySequenceSum : (s : Seq) →
  IsConvSeries s ≃ IsCauchySequence (seqΣ s)
IsConvSeries≃IsCauchySequenceSum s =
  isoToEquiv (IsoIsConvSeriesIsCauchySequenceSum s)



isCauchyAprox : (ℚ₊ → ℝ) → Type
isCauchyAprox f = (δ ε : ℚ₊) →
  (absᵣ (f δ +ᵣ (-ᵣ  f ε)) <ᵣ rat (fst (δ ℚ₊+ ε)))

lim' : ∀ x → isCauchyAprox x → ℝ
lim' x y = lim x λ δ ε  → (invEq (∼≃abs<ε _ _ _)) (y δ ε)


fromCauchySequence : ∀ s → IsCauchySequence s → ℝ
fromCauchySequence s ics =
  lim x y

 where
 x : ℚ₊ → ℝ
 x q = s (suc (fst (ics (ℚ₊→ℝ₊ q))))

 y : (δ ε : ℚ₊) → x δ ∼[ δ ℚ₊+ ε ] x ε
 y δ ε = invEq (∼≃abs<ε _ _ _)
    (ww (ℕ.Dichotomyℕ δₙ εₙ) )
  where
  δₙ = fst (ics (ℚ₊→ℝ₊ δ))
  εₙ = fst (ics (ℚ₊→ℝ₊ ε))

  ww : _ ⊎ _ → absᵣ (x δ +ᵣ (-ᵣ x ε)) <ᵣ rat (fst (δ ℚ₊+ ε))
  ww (inl δₙ≤εₙ) =
   let z = snd (ics (ℚ₊→ℝ₊ δ)) (suc εₙ) (suc δₙ)
              ℕ.≤-refl  (ℕ.suc-≤-suc δₙ≤εₙ )
   in isTrans<ᵣ (absᵣ (x δ +ᵣ (-ᵣ x ε)))
           (rat (fst (δ))) (rat (fst (δ ℚ₊+ ε)))
           z (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' (fst δ) (fst δ) ε (ℚ.isRefl≤ (fst δ))))
  ww (inr εₙ<δₙ) =
    let z = snd (ics (ℚ₊→ℝ₊ ε)) (suc εₙ) (suc δₙ)
               (ℕ.≤-suc εₙ<δₙ) ℕ.≤-refl
    in isTrans<ᵣ (absᵣ (x δ +ᵣ (-ᵣ x ε)))
           (rat (fst (ε))) (rat (fst (δ ℚ₊+ ε)))
           z ((<ℚ→<ᵣ _ _
               (subst ((fst ε) ℚ.<_) (ℚ.+Comm _ _)
               (ℚ.<+ℚ₊' (fst ε) (fst ε) δ (ℚ.isRefl≤ (fst ε))))))

limₙ→∞_is_ : Seq → ℝ → Type
limₙ→∞ s is x =
  ∀ (ε : ℝ₊) → Σ[ N ∈ ℕ ]
    (∀ n → N ℕ.< n →
      absᵣ ((s n) +ᵣ (-ᵣ x)) <ᵣ (fst ε))



Limₙ→∞ : Seq → Type
Limₙ→∞ s = Σ _ (limₙ→∞ s is_)
