module Cubical.HITs.CauchyReals.Integration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Fin

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals.Fast as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Fast.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡ ; [_/_]₊)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Summation

open import Cubical.Tactics.CommRingSolverFast.RationalsReflection
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection
open import Cubical.Tactics.CommRingSolverFast.IntReflection
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.Tactics.CommRingSolverFast.RealsReflection


record Partition[_,_] (a b : ℝ) : Type₀ where
 field
  len : ℕ
  pts : Fin (1 ℕ.+ len) → ℝ
  a≤pts : ∀ k → a ≤ᵣ pts k
  pts≤b : ∀ k → pts k ≤ᵣ b
  pts≤pts : (k : Fin len) → pts (finj k) ≤ᵣ pts (fsuc k)

 diffs : Fin len → Σ ℝ (0 ≤ᵣ_)
 diffs k = _ , x≤y→0≤y-x (pts (finj k)) _ (pts≤pts k)

 mesh : ℝ
 mesh = foldlFin maxᵣ 0 (fst ∘ diffs)

 a≤b : a ≤ᵣ b
 a≤b = isTrans≤ᵣ a _ _ (a≤pts fzero) (pts≤b fzero)

 pts'Σ-R : ElimFinSS (Σ _ (_∈ intervalℙ a b))  (suc len)
 pts'Σ-R .ElimFinSS.a₀ = a , ≤ᵣ-refl a , a≤b
 pts'Σ-R .ElimFinSS.f k = pts k , a≤pts _ , pts≤b _
 pts'Σ-R .ElimFinSS.aₙ = b , a≤b , ≤ᵣ-refl b

 pts'Σ : Fin (3 ℕ.+ len) → (Σ _ (_∈ intervalℙ a b))
 pts'Σ = ElimFinSS.go pts'Σ-R

 pts' : Fin (3 ℕ.+ len) → ℝ
 pts' = fst ∘ pts'Σ

 a≤pts' : ∀ k → a ≤ᵣ pts' k
 a≤pts' = fst ∘ snd ∘ pts'Σ

 pts'≤b : ∀ k → pts' k ≤ᵣ b
 pts'≤b = snd ∘ snd ∘ pts'Σ

 pts'≤pts' : ∀ k → pts' (finj k) ≤ᵣ pts' (fsuc k)
 pts'≤pts' (zero , l , p) = a≤pts' (1 , l , +-suc _ _ ∙ cong suc p)
 pts'≤pts' k'@(suc k , zero , p) =
  let z = pts'≤b (suc k , 1 , cong suc p)
  in isTrans≡≤ᵣ (pts' (finj k'))
        (pts' (suc k , 1 , (λ i → suc (p i))))
        _ (cong {x = finj k'}
                {(suc k , 1 , cong suc p)} pts'
                 (toℕ-injective refl)) z
 pts'≤pts' (suc k , suc l , p) =
   let k' = k , l , cong (predℕ ∘ predℕ)
               (sym (ℕ.+-suc (suc l) (suc k)) ∙ p)
   in subst2 _≤ᵣ_
         (cong (λ u → pts (k , l ℕ.+ (suc zero) , u))
           (isSetℕ _ _ _ _))
         (cong (λ u → pts (suc k , l , u))
           (isSetℕ _ _ _ _))
         (pts≤pts k')

 isStrictPartition : Type
 isStrictPartition = ∀ k → pts' (finj k) <ᵣ pts' (fsuc k)

 mesh≤ᵣ : ℝ → Type
 mesh≤ᵣ δ = ∀ k →  pts' (fsuc k) -ᵣ pts' (finj k)  ≤ᵣ δ

 record Sample : Type₀ where
  field
   samples : Fin (2 ℕ.+ len) → ℝ
   pts'≤samples : (k : Fin _) → pts' (finj k) ≤ᵣ samples k
   samples≤pts' : (k : Fin _) → samples k ≤ᵣ pts' (fsuc k)


  a≤samples : ∀ k → a  ≤ᵣ samples k
  a≤samples k = isTrans≤ᵣ a _ _ (a≤pts' (finj k)) (pts'≤samples k)

  samples≤b : ∀ k → samples k ≤ᵣ b
  samples≤b k = isTrans≤ᵣ (samples k) _ b (samples≤pts' k) (pts'≤b (fsuc k))

  samplesΣ : Fin (2 ℕ.+ len) → Σ[ t ∈ ℝ ] (a ≤ᵣ t ) × (t ≤ᵣ b)
  samplesΣ k = samples k , a≤samples k , samples≤b k

  riemannSum : (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ
  riemannSum f = foldlFin
    (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t a≤t t≤b) ) 0
     (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))

  riemannSum' : (ℝ → ℝ) → ℝ
  riemannSum' f = foldlFin {n = 2 ℕ.+ len}
    (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t) ) 0
     (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))

  riemannSum'≡ : (f g : ℝ → ℝ) → (∀ x → x ∈ intervalℙ a b → f x ≡ g x) →
                     riemannSum' f ≡ riemannSum' g
  riemannSum'≡ f g f≡g =
    cong (λ g → foldlFin {n = 2 ℕ.+ len}
        g 0)
        (funExt₂ (λ S ((t , a≤t , t≤b) , b-a) →
           cong ((S +ᵣ_) ∘ (b-a ·ᵣ_))
               (f≡g t (a≤t , t≤b))))
         ≡$ (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))

  riemannSum-clamp : (f : ∀ r → r ∈ intervalℙ a b → ℝ)
    → riemannSum (curry ∘ f) ≡
      riemannSum'
      (λ x₁ →  f (clampᵣ a b x₁) (clampᵣ∈ℚintervalℙ a b a≤b x₁))
  riemannSum-clamp f =
    cong (λ g → foldlFin {n = 2 ℕ.+ len}
        g 0)
        (funExt₂ (λ S ((t , a≤t , t≤b) , b-a) →
           cong ((S +ᵣ_) ∘ (b-a ·ᵣ_))
             (cong (uncurry f)
               (Σ≡Prop (∈-isProp (intervalℙ a b))
                (∈ℚintervalℙ→clampᵣ≡ a b t (a≤t , t≤b))))))
         ≡$ (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))

  riemannSum'+ : (f g : ℝ → ℝ) →
    riemannSum' f +ᵣ riemannSum' g
      ≡ riemannSum' (λ x → f x +ᵣ g x)
  riemannSum'+ f g = zip-foldFin+ᵣ' (2 ℕ.+ len)
    (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))
    _ _ 0 0
   ∙ (cong₂ foldlFin (funExt₂
    λ S y → cong (S +ᵣ_) (sym (·DistL+ _ _ _)))
   (+ᵣ-rat 0 0)
    ≡$ (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k)))


  riemannSum+ : ∀ f g →
    riemannSum f +ᵣ riemannSum g
      ≡ riemannSum (λ x ≤x x≤  → f x ≤x x≤ +ᵣ g x ≤x x≤)
  riemannSum+ f g = zip-foldFin+ᵣ' (2 ℕ.+ len)
    (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))
    _ _ 0 0
   ∙ (cong₂ foldlFin (funExt₂
    λ S y → cong (S +ᵣ_) (sym (·DistL+ _ _ _)))
   (+ᵣ-rat 0 0)
    ≡$ (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k)))

  riemannSum'≤ : (f g : ℝ → ℝ) →
    (∀ r → a ≤ᵣ r → r ≤ᵣ b → f r ≤ᵣ g r) →
    riemannSum' f ≤ᵣ riemannSum' g

  riemannSum'≤ f g f≤g =
     foldFin+≤ (2 ℕ.+ len) _ _ _  _
       (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))
       (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))
       (≤ᵣ-refl 0) λ x → ≤ᵣ-o·ᵣ _ _ _ (x≤y→0≤y-x _ _ (pts'≤pts' x))
         (f≤g _ (a≤samples x) (samples≤b x))



  riemannSum'C· : ∀ C (f : ℝ → ℝ) →
    riemannSum' (λ x → C ·ᵣ f x)
     ≡ C ·ᵣ riemannSum' f
  riemannSum'C· C f =
    (cong foldlFin (funExt₂
    λ S y → cong (S +ᵣ_)
      (·ᵣAssoc _ _ _ ∙∙ cong (_·ᵣ f (y .fst .fst)) (·ᵣComm _ _)
       ∙∙ sym (·ᵣAssoc _ _ _)))
    ≡$ 0
    ≡$ (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k)))
    ∙ foldFin·DistL' (2 ℕ.+ len) _ _
    (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))

  riemannSumC· : ∀ C f →
    riemannSum (λ x ≤x x≤ → C ·ᵣ f x ≤x x≤)
     ≡ C ·ᵣ riemannSum f
  riemannSumC· C f =
    (cong foldlFin (funExt₂
    λ S y → cong (S +ᵣ_)
      (·ᵣAssoc _ _ _ ∙∙ cong (_·ᵣ f (y .fst .fst) _ _) (·ᵣComm _ _)
       ∙∙ sym (·ᵣAssoc _ _ _)))
    ≡$ 0
    ≡$ (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k)))
    ∙ foldFin·DistL' (2 ℕ.+ len) _ _
    (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))


  riemannSum'- : (f g : ℝ → ℝ) →
    riemannSum' f -ᵣ riemannSum' g
      ≡ riemannSum' (λ x → f x -ᵣ g x)
  riemannSum'- f g =
      cong₂ _+ᵣ_ refl
        (-ᵣ≡[-1·ᵣ] _
         ∙ sym (riemannSum'C· -1 _)
         ∙ cong riemannSum' (funExt λ _ → sym (-ᵣ≡[-1·ᵣ] _)))
    ∙ riemannSum'+ _ _


  riemannSum- : ∀ f g →
    riemannSum f -ᵣ riemannSum g
      ≡ riemannSum (λ x ≤x x≤ → f x ≤x x≤ -ᵣ g x ≤x x≤)
  riemannSum- f g =
      cong₂ _+ᵣ_ refl
        (-ᵣ≡[-1·ᵣ] _
         ∙ sym (riemannSumC· -1 _)
         ∙ cong riemannSum (funExt₃ λ _ _ _ → sym (-ᵣ≡[-1·ᵣ] _)))
    ∙ riemannSum+ _ _



  riemannSum'-alt : (ℝ → ℝ) → ℝ
  riemannSum'-alt f = foldlFin {n = 2 ℕ.+ len}
    (λ S k →
     S +ᵣ (pts' (fsuc k) -ᵣ pts' (finj k)) ·ᵣ (f (fst (samplesΣ k))) ) 0
     (idfun _)

  riemannSum'-alt-lem : ∀ f → riemannSum' f ≡ riemannSum'-alt f
  riemannSum'-alt-lem f =
   foldFin+map (2 ℕ.+ len) 0 _
    (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))
    (idfun _)


  riemannSum-empty : (f : ∀ r → r ∈ intervalℙ a b → ℝ)
    → a ≡ b
    → 0 ≡ riemannSum (curry ∘ f)

  riemannSum-empty f a≡b =
      sym (𝐑'.0RightAnnihilates _)
    ∙ sym (foldFin+Const (2 ℕ.+ len) 0 (idfun _))
    ∙ (cong (foldlFin {n = 2 ℕ.+ len}) (funExt₂
      (λ S y → cong (S +ᵣ_) ((sym (𝐑'.0LeftAnnihilates' _ _
        (𝐑'.+InvR' _ _ (
         cong fst (isContr→isProp (pointIntervalℙ a b a≡b)
          (pts'Σ (fsuc y)) (pts'Σ (finj y))))))))))
       ≡$ 0 ≡$ idfun _)
    ∙ sym (riemannSum'-alt-lem _)
    ∙ sym (riemannSum-clamp f)


  riemannSum'-absᵣ≤ : (f : ℝ → ℝ) →
    absᵣ (riemannSum' f) ≤ᵣ riemannSum' (absᵣ ∘ f)
  riemannSum'-absᵣ≤ f =
    subst2 _≤ᵣ_
      (cong absᵣ (sym (riemannSum'-alt-lem f)))
      (sym (riemannSum'-alt-lem (absᵣ ∘ f)))
      (foldFin+≤-abs (2 ℕ.+ len) 0 0 _ _
        (idfun _) (idfun _)
        (isTrans≡≤ᵣ _ _ _ absᵣ0 (≤ᵣ-refl 0))
        λ k →
          ≡ᵣWeaken≤ᵣ _ _
            (·absᵣ _ _
           ∙ cong₂ _·ᵣ_
             (absᵣNonNeg _ (x≤y→0≤y-x _ _ (pts'≤pts' k)))
             refl))



  riemannSum'Const : ∀ C → riemannSum' (const C) ≡ C ·ᵣ (b -ᵣ a)
  riemannSum'Const C = riemannSum'-alt-lem (const C)
   ∙ (λ i → foldlFin {n = 2 ℕ.+ len}
    (λ S k →
     S +ᵣ ·ᵣComm (pts' (fsuc k) -ᵣ pts' (finj k)) C i ) 0
     (idfun _))
   ∙ foldFin·DistL' (2 ℕ.+ len) _ C (idfun _)
   ∙ cong (C ·ᵣ_) (deltas-sum (2 ℕ.+ len) pts')


 open Sample public

 leftSample : Sample
 leftSample .samples = pts' ∘ finj
 leftSample .pts'≤samples = ≤ᵣ-refl ∘ pts' ∘ finj
 leftSample .samples≤pts' = pts'≤pts'

 rightSample : Sample
 rightSample .samples = pts' ∘ fsuc
 rightSample .pts'≤samples = pts'≤pts'
 rightSample .samples≤pts' = ≤ᵣ-refl ∘ pts' ∘ fsuc


-- clampDeltaᵣ : ∀ L L' x → clampᵣ L L' x ≡
--                (x +ᵣ clampᵣ (L -ᵣ x) (L' -ᵣ x) 0)
-- clampDeltaᵣ L L' x = {!!}


-- clampDeltaSplitℚ : ∀ L L' x y → L ℚ.≤ L' → x ℚ.≤ y
--             → (y ℚ.- x) ≡
--               (ℚ.min L y ℚ.- ℚ.min L x)
--                ℚ.+ (ℚ.clamp L L' y ℚ.- ℚ.clamp L L' x)
--                ℚ.+ (ℚ.max L' y ℚ.- ℚ.max L' x)
-- clampDeltaSplitℚ = {!!}

open Partition[_,_] public hiding (a≤b)

TaggedPartition[_,_] : ℝ → ℝ → Type
TaggedPartition[ a , b ] = Σ (Partition[ a , b ]) Sample




on[_,_]IntegralOf_is_ : ∀ a b → (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ → Type

on[ a , b ]IntegralOf f is s =
   ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
     ∀ ((p , t) : TaggedPartition[ a , b ]) →
     (mesh≤ᵣ p (rat (fst δ)) →
       absᵣ (riemannSum t f -ᵣ s) <ᵣ rat (fst ε))


on[_,_]IntegralOf_is'_ : ∀ a b → (ℝ → ℝ) → ℝ → Type
on[ a , b ]IntegralOf f is' s =
   ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
     ∀ ((p , t) : TaggedPartition[ a , b ]) →
     (mesh≤ᵣ p (rat (fst δ)) →
       absᵣ (riemannSum' t f -ᵣ s) <ᵣ rat (fst ε))


0≤pos/ : ∀ {p q} → 0 ℚ.≤ [ pos p / q ]
0≤pos/ {p} {q} =
  subst (0 ℤ.≤_) (sym (ℤ.·IdR _))
    (ℤ.ℕ≤→pos-≤-pos 0 p ℕ.zero-≤)


module Integration a b (a≤b : a ≤ᵣ b) where

 Δ : ℝ
 Δ = b -ᵣ a

 0≤Δ : 0 ≤ᵣ Δ
 0≤Δ = x≤y→0≤y-x a _ a≤b


 -- uContMesh : ∀ f → IsUContinuous f →
 --        ∀ (ε₊ : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
 --                  (∀ ((p , t) : TaggedPartition[ a , b ]) →
 --                     (mesh p <ᵣ rat (fst δ) →
 --                       absᵣ (riemannSum' t f -ᵣ
 --                             riemannSum' (leftSample p) f)
 --                          <ᵣ Δ ·ᵣ rat (fst ε₊)))
 -- uContMesh d iucf ε₊ = {!!}

 module _ (n : ℕ) where

  t : ℕ → ℚ
  t k = [ pos (suc k) / 2+ n  ]

  0≤t : ∀ k → 0 ≤ᵣ rat (t k)
  0≤t k = ≤ℚ→≤ᵣ 0 (t k) (0≤pos/ {suc k} {2+ n})

  t≤1 : ∀ (k : Fin (1 ℕ.+ n)) → rat (t (fst k)) ≤ᵣ 1
  t≤1 k = ≤ℚ→≤ᵣ (t (fst k)) 1 w
   where
   w : pos (suc (k .fst)) ℤ.· ℚ.ℕ₊₁→ℤ 1 ℤ.≤ pos 1 ℤ.· ℚ.ℕ₊₁→ℤ (2+ n)
   w = subst2 ℤ._≤_ (sym (ℤ.·IdR _)) (sym (ℤ.·IdL _))
          (ℤ.ℕ≤→pos-≤-pos (suc (fst k))
           _ (ℕ.suc-≤-suc $ ℕ.≤-suc $ ℕ.predℕ-≤-predℕ (snd k)))

  tIncr : ∀ k → t k ℚ.≤ t (suc k)
  tIncr k = ℤ.≤-·o {m = pos (suc k)} {n = pos (suc (suc k))} {k = suc (suc n)}
            (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.≤-sucℕ)

  equalPartition : Partition[ a , b ]
  equalPartition .len = n
  equalPartition .pts k = a +ᵣ Δ ·ᵣ (rat (t (fst k)))
  equalPartition .a≤pts k =
    isTrans≡≤ᵣ a (a +ᵣ Δ ·ᵣ 0) _
      (sym (𝐑'.+IdR' _ _ (𝐑'.0RightAnnihilates _)))
       (≤ᵣ-o+ (Δ ·ᵣ 0) (Δ ·ᵣ (rat (t (fst k)))) a
         (≤ᵣ-o·ᵣ 0 (rat (t (fst k))) Δ  0≤Δ (0≤t (fst k))))
  equalPartition .pts≤b k =
    isTrans≤≡ᵣ (a +ᵣ Δ ·ᵣ rat (t (fst k))) (a +ᵣ Δ) b
    (≤ᵣ-o+ _ _ a
     (isTrans≤≡ᵣ (Δ ·ᵣ rat (t (fst k))) (Δ ·ᵣ 1) Δ
      (≤ᵣ-o·ᵣ (rat (t (fst k))) 1 Δ  0≤Δ (t≤1 k)) (·IdR Δ)))
      (L𝐑.lem--05 {a} {b})
  equalPartition .pts≤pts k =
     ≤ᵣ-o+ _ _ a (≤ᵣ-o·ᵣ (rat (t ( (fst k)))) (rat (t (suc (fst k)))) Δ  0≤Δ
      (≤ℚ→≤ᵣ (t (fst k)) _ (tIncr (fst k))))


  equalPartitionPts' : ∀ k → pts' equalPartition k ≡
        a +ᵣ Δ ·ᵣ rat [ pos (fst k) / 2+ n  ]
  equalPartitionPts' (zero , zero , p) = ⊥.rec (ℕ.znots (cong predℕ p))
  equalPartitionPts' (zero , suc l , p) =
   sym (𝐑'.+IdR' _ _ (𝐑'.0RightAnnihilates' _ _ (cong rat (ℚ.[0/n]≡[0/m] _ _))))
  equalPartitionPts' (suc k , zero , p) =
    sym (L𝐑.lem--05 {a} {b}) ∙
      cong (a +ᵣ_) (sym (𝐑'.·IdR' _ _ (cong (rat ∘ [_/ 2+ n ])
       (cong (pos ∘ predℕ) p)
       ∙ (cong rat $ ℚ.[n/n]≡[m/m] (suc n) 0))))
  equalPartitionPts' (suc k , suc l , p) = refl

  equalPartitionΔ : ∀ k →
    pts' equalPartition (fsuc k) -ᵣ pts' equalPartition (finj k)
    ≡ Δ ·ᵣ rat [ 1 / 2+ n ]
  equalPartitionΔ (zero , zero , snd₁) = ⊥.rec (ℕ.znots (cong predℕ snd₁))
  equalPartitionΔ (zero , suc fst₂ , snd₁) =
   L𝐑.lem--063 {a}
  equalPartitionΔ (suc fst₁ , zero , snd₁) =
    L𝐑.lem--089 {b} {a} {Δ ·ᵣ rat [ pos (suc fst₁) / 2+ n ]}
     ∙ cong₂ (_-ᵣ_)
       (sym (·IdR Δ)) (cong (Δ ·ᵣ_) (cong (rat ∘ [_/ 2+ n ])
         (cong (pos ∘ predℕ) snd₁)))
       ∙ sym (𝐑'.·DistR- _ _ _) ∙
        cong (Δ ·ᵣ_)
         (cong₂ {x = 1}
          {rat [ pos (suc (suc n)) / 2+ n ]}
          _-ᵣ_ (cong rat (ℚ.[n/n]≡[m/m] 0 (suc n)))
          {rat [ pos (suc n) / 2+ n ]}
          {rat [ pos (suc n) / 2+ n ]}
          refl
          ∙ -ᵣ-rat₂ [ (pos (suc (suc n))) / 2+ n ] [ pos (suc n) / 2+ n ]
           ∙ cong rat
               (ℚ.n/k-m/k (pos (suc (suc n))) (pos (suc n)) (2+ n) ∙
                  cong [_/ 2+ n ] (cong (ℤ._- pos (suc n))
                      (ℤ.pos+ 1 (suc n)) ∙ ℤ.plusMinus (pos (suc n)) 1)))

  equalPartitionΔ (suc k , suc l , p) =
   L𝐑.lem--088 {a} ∙
       sym (𝐑'.·DistR- _ _ _) ∙
         cong (Δ ·ᵣ_) zz
    where
    zz : rat (t (suc k)) -ᵣ rat (t k) ≡ rat [ 1 / 2+ n ]
    zz = cong₂ {x = rat (t (suc k))}
          {rat [ pos (suc (suc k)) / 2+ n ]}
          _-ᵣ_ refl {rat (t k)} {rat [ pos (suc k) / (2+ n) ]}
           refl  ∙ -ᵣ-rat₂
          ([ pos (suc (suc k)) / 2+ n ]) ([ pos (suc k) / 2+ n ]) ∙
           cong
             {x = [ pos (suc (suc k)) / 2+ n ] ℚ.- [ pos (suc k) / 2+ n ]}
             {y = [ 1 / 2+ n ]}
             rat (ℚ.n/k-m/k (pos (suc (suc k))) (pos (suc k)) (2+ n)  ∙
                cong [_/ 2+ n ] (cong (ℤ._- pos (suc k)) (ℤ.pos+ 1 (suc k))

                 ∙ ℤ.plusMinus (pos (suc k)) 1))

 isStrictEqualPartition : a <ᵣ b → ∀ n → isStrictPartition (equalPartition n)
 isStrictEqualPartition a<b n k =
   subst2 _<ᵣ_
     (sym (equalPartitionPts' n (finj k)))
     (sym (equalPartitionPts' n (fsuc k)))
     (<ᵣ-o+ _ _ a
       (<ᵣ-o·ᵣ _ _
         (Δ , x<y→0<y-x _ _ a<b)
         (<ℚ→<ᵣ _ _ ((ℚ.[k/n]<[k'/n]
          (pos (fst k)) (pos (suc (fst k))) (2+ n)
            ℤ.isRefl≤)))))

 equalPartition-2ⁿ : ℕ → Partition[ a , b ]
 equalPartition-2ⁿ n = equalPartition (predℕ (predℕ (2^ (suc n))))

 equalPartition-mesh : ∀ n →
  mesh≤ᵣ (equalPartition n)
   ((b -ᵣ a) ·ᵣ (rat [ 1 / 2+ n  ]) )
 equalPartition-mesh n k = ≡ᵣWeaken≤ᵣ _ _
  (equalPartitionΔ n k)

∃Partition< : ∀ a b → a ≤ᵣ b → ∀ (ε : ℚ₊) →
  ∃[ (p , tg) ∈ TaggedPartition[ a , b ] ] mesh≤ᵣ p (rat (fst ε))
∃Partition< a b a≤b ε =
  PT.map
    (λ (x' , b-a<x' , _) →
      let x'₊ = (x' , ℚ.<→0< x'
                (<ᵣ→<ℚ 0 x' (isTrans≤<ᵣ 0 (b -ᵣ a) (rat x')
                  (x≤y→0≤y-x a b a≤b) b-a<x')))
          (N , _) , (p , (u , _)) = ℚ.ceil-[1-frac]ℚ₊ (invℚ₊ ε ℚ₊· x'₊)
          ww : fst (x'₊ ℚ₊· invℚ₊ ε) ℚ.≤ fromNat (suc (suc N))
          ww = ℚ.isTrans≤ (fst (x'₊ ℚ₊· invℚ₊ ε)) (fromNat N)
                (fromNat (suc (suc N)))
              (subst2 (ℚ._≤_) (ℚ.+IdR (fst (invℚ₊ ε ℚ₊· x'₊))
             ∙ ℚ.·Comm (fst (invℚ₊ ε)) x') p
               (ℚ.≤-o+ _ _ (fst (invℚ₊ ε ℚ₊· x'₊)) u))
                ((ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos N (suc (suc N))
                 (ℕ.≤-trans ℕ.≤-sucℕ ℕ.≤-sucℕ))))

      in (_ , leftSample (∫ab.equalPartition N)) ,
          λ k → isTrans≤ᵣ _ _ _ (∫ab.equalPartition-mesh N k)
            (isTrans≤ᵣ _ _ _
              (isTrans≤≡ᵣ _ _ _ (≤ᵣ-·ᵣo _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.0≤pos 1 (2+ N)))
                (<ᵣWeaken≤ᵣ _ _ b-a<x'))
                (sym (rat·ᵣrat x' _)))
              (≤ℚ→≤ᵣ _ _ (ℚ.x≤y·z→x·invℚ₊y≤z x' (fst ε) (fromNat (suc (suc N)))
               (subst (x' ℚ.≤_) (ℚ.·Comm (fst ε) _)
              (ℚ.x·invℚ₊y≤z→x≤y·z x' (fromNat (suc (suc N))) ε
              ww)))))
      )
    (denseℚinℝ (b -ᵣ a) ((b -ᵣ a) +ᵣ 1)
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR _)) (<ᵣ-o+ 0 1 (b -ᵣ a) decℚ<ᵣ?)))
 where
 module ∫ab = Integration a b a≤b

Integral'Uniq : ∀ a b → (a ≤ᵣ b) → ∀ f s s'
  → on[ a , b ]IntegralOf f is' s
  → on[ a , b ]IntegralOf f is' s'
  → s ≡ s'
Integral'Uniq a b a≤b f s s' S S' =
   eqℝ _ _
    λ ε →
      PT.rec2 (isProp∼ _ _ _ )
       (λ (δ , X) (δ' , X') →
         let δ⊔δ' = ℚ.min₊ δ δ'
         in PT.rec (isProp∼ _ _ _)
             (λ (TP , TP<) → subst∼ (ℚ.ε/2+ε/2≡ε (fst ε))
              (triangle∼ {ε = /2₊ ε} {/2₊ ε}
                (sym∼ _ _ _ (invEq (∼≃abs<ε _ _ _)
                 (X TP λ k → isTrans≤ᵣ _ _ _ (TP< k)
                  (≤ℚ→≤ᵣ _ _ (ℚ.min≤ (fst δ) (fst δ'))))))
                (invEq (∼≃abs<ε _ _ _)
                  (X' TP λ k → isTrans≤ᵣ _ _ _ (TP< k)
                   (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) (fst δ')))))))
                (∃Partition< a b a≤b δ⊔δ'))
       (S (/2₊ ε)) (S' (/2₊ ε))



IntegralUniq : ∀ a b → (a ≤ᵣ b) → ∀ f s s'
  → on[ a , b ]IntegralOf f is s
  → on[ a , b ]IntegralOf f is s'
  → s ≡ s'
IntegralUniq a b a≤b f s s' S S' =
  eqℝ _ _
    λ ε →
      PT.rec2 (isProp∼ _ _ _ )
       (λ (δ , X) (δ' , X') →
         let δ⊔δ' = ℚ.min₊ δ δ'
         in PT.rec (isProp∼ _ _ _)
             (λ (TP , TP<) → subst∼ (ℚ.ε/2+ε/2≡ε (fst ε))
              (triangle∼ {ε = /2₊ ε} {/2₊ ε}
                (sym∼ _ _ _ (invEq (∼≃abs<ε _ _ _)
                 (X TP λ k → isTrans≤ᵣ _ _ _ (TP< k)
                  (≤ℚ→≤ᵣ _ _ (ℚ.min≤ (fst δ) (fst δ'))))))
                (invEq (∼≃abs<ε _ _ _)
                  (X' TP λ k → isTrans≤ᵣ _ _ _ (TP< k)
                   (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) (fst δ')))))))
                (∃Partition< a b a≤b δ⊔δ'))
       (S (/2₊ ε)) (S' (/2₊ ε))


IntegratedProp : ∀ a b → a ≤ᵣ b → ∀ f → isProp (Σ _ on[ a , b ]IntegralOf f is'_)
IntegratedProp a b a≤b f (s , S) (s' , S')  =
  Σ≡Prop (λ _ → isPropΠ λ _ → squash₁ )
   (Integral'Uniq a b a≤b f s s' S S')

IntegratedℙPropℙ : ∀ a b → a ≤ᵣ b → ∀ f → isProp (Σ _ on[ a , b ]IntegralOf f is_)
IntegratedℙPropℙ a b a≤b f (s , S) (s' , S')  =
  Σ≡Prop (λ _ → isPropΠ λ _ → squash₁ )
   (IntegralUniq a b a≤b f s s' S S')



module Partition-pre+ (a b : ℝ) (α : ℝ) where
 partition-pre+ :
    ( (TaggedPartition[ a , b ]))
    → ((TaggedPartition[ a +ᵣ α , b +ᵣ α ]))
 partition-pre+  x .fst .len = x .fst .len
 partition-pre+  x .fst .pts = (_+ᵣ α) ∘ x .fst .pts
 partition-pre+  x .fst .a≤pts =
   ≤ᵣ-+o _ _ _ ∘ x .fst .a≤pts
 partition-pre+  x  .fst .pts≤b =
    ≤ᵣ-+o _ _ _ ∘ x .fst .pts≤b
 partition-pre+  x  .fst .pts≤pts =
     ≤ᵣ-+o _ _ _ ∘ x .fst .pts≤pts
 partition-pre+  x  .snd .samples =
  (_+ᵣ α) ∘  x  .snd .samples
 partition-pre+  x .snd .pts'≤samples =
   λ { k@(0 , _ , _) → ≤ᵣ-+o _ _ _ (x .snd .pts'≤samples k)
     ; k@(suc _ , 0 , _) → ≤ᵣ-+o _ _ _ (x  .snd .pts'≤samples k)
     ; k@(suc _ , suc _ , _) → ≤ᵣ-+o _ _ _ (x .snd .pts'≤samples k)
      }


 partition-pre+  x .snd .samples≤pts' =
   λ { k@(0 , 0 , _) → ≤ᵣ-+o _ _ _ (x .snd .samples≤pts' k)
     ; k@(0 , suc _ , _) → ≤ᵣ-+o _ _ _ (x .snd .samples≤pts' k)
     ; k@(suc _ , 0 , _) → ≤ᵣ-+o _ _ _ (x .snd .samples≤pts' k)
     ; k@(suc _ , suc _ , _) → ≤ᵣ-+o _ _ _ (x .snd .samples≤pts' k)
      }

 partition-pre+-lem : ∀ tp k →
      pts' (fst (partition-pre+ tp)) (fsuc k) -ᵣ
      pts' (fst (partition-pre+ tp)) (finj k)
      ≡
      (pts' (fst tp) (fsuc k)) -ᵣ (pts' (fst tp) (finj k))
 partition-pre+-lem tp (0 , 0 , _) = L𝐑.lem--075
 partition-pre+-lem tp (0 , suc _ , _) = L𝐑.lem--075
 partition-pre+-lem tp (suc _ , 0 , _) = L𝐑.lem--075
 partition-pre+-lem tp (suc _ , suc _ , _) = L𝐑.lem--075

 mesh-pre+ : ∀ δ → (tp : TaggedPartition[ a , b ]) →
             mesh≤ᵣ (fst tp) δ
            → mesh≤ᵣ (fst (partition-pre+ tp)) δ
 mesh-pre+ δ tp x k =
   isTrans≡≤ᵣ _ _ _ (partition-pre+-lem tp k) (x k)


pts'-tranp : ∀ {a a' b b'} → (p : a ≡ a') (p' : b ≡ b') →
 ((pa , tg) : TaggedPartition[ a , b ]) →
 ∀ k k' → fst k ≡ fst k' →
 pts' pa k ≡ pts' (fst (subst2 TaggedPartition[_,_] p p' (pa , tg))) k'
pts'-tranp {a} {a'} {b} {b'} p p' =
 J2 (λ a' p b' p' →
              ((pa , tg) : TaggedPartition[ a , b ]) →
            ∀ k k' → fst k ≡ fst k' →
            pts' pa k ≡
            pts' (fst (subst2 TaggedPartition[_,_] p p' (pa , tg))) k' )
         (λ (pa , tg) k k' pp i →
           fst (pts'Σ (transportRefl pa (~ i))
             (toℕ-injective {suc (suc (suc (len pa)))}
               {k} {k'} pp i)))
           {a'} p {b'} p'

integral'-transl : ∀ a b Δ f s
         → (on[ a  , b ]IntegralOf (f ∘S (Δ +ᵣ_)) is' s)
         → (on[ a +ᵣ Δ  , b +ᵣ Δ  ]IntegralOf f is' s)
integral'-transl a b Δ f s X ε =
  PT.map
    (map-snd (λ {δ} Y (p , tp) m≤ →
      isTrans≡<ᵣ _ _ _
       (cong (λ rs → absᵣ (rs -ᵣ s))
        (riemannSum'-alt-lem tp f ∙∙
          cong (λ (gg : Fin (suc (suc (len p))) → ℝ) → foldlFin
              (λ S k →
               S +ᵣ gg k ) 0
               (idfun _))
            (funExt
             (λ x → cong₂ _·ᵣ_
                (sym (Partition-pre+.partition-pre+-lem
                  (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ) (p , tp) x) ∙
                   cong₂ _-ᵣ_
                    (pts'-tranp ((𝐑'.plusMinus a Δ)) ((𝐑'.plusMinus b Δ))
                      (Partition-pre+.partition-pre+
                     (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ) (p , tp))
                     (fsuc x) (fsuc x) refl)
                    ((pts'-tranp ((𝐑'.plusMinus a Δ)) ((𝐑'.plusMinus b Δ))
                      (Partition-pre+.partition-pre+
                     (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ) (p , tp))
                     (finj x) (finj x) refl)) )
               (cong f ((sym (𝐑'.minusPlus _ Δ)
                 ∙ cong ((_+ᵣ Δ) ∘ (_+ᵣ (-ᵣ Δ)))
                  (cong (samples tp) (toℕ-injective refl))) ∙ +ᵣComm _ _ ))))
         ∙∙ sym (riemannSum'-alt-lem
           (fst
             (subst2
              (λ a' b' →
                 Σ TaggedPartition[ a' , b' ]
                 (λ pp → mesh≤ᵣ (fst pp) (rat (fst δ))))
              (𝐑'.plusMinus a Δ) (𝐑'.plusMinus b Δ)
              (Partition-pre+.partition-pre+ (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ)
               _
               ,
               Partition-pre+.mesh-pre+ (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ) (rat (fst δ))
               (p , tp) m≤))
             .snd) (f ∘S _+ᵣ_ Δ))))
        (uncurry Y
         (subst2 (λ a' b' →
          Σ (TaggedPartition[ a' , b' ]) (λ (xx , _) →
            mesh≤ᵣ xx (rat (fst δ)) ) )
            (𝐑'.plusMinus a Δ) (𝐑'.plusMinus b Δ)
         (Partition-pre+.partition-pre+
          (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ) (p , tp) ,
           Partition-pre+.mesh-pre+
          (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ) (rat (fst δ)) (p , tp) m≤)))))
    (X ε)



module Partition-pre· (a b : ℝ) (α : ℝ) (0≤α : 0 ≤ᵣ α) where
 partition-pre· :
    ( (TaggedPartition[ a , b ]))
    → ((TaggedPartition[ a ·ᵣ α , b ·ᵣ α ]))
 partition-pre·  x .fst .len = x .fst .len
 partition-pre·  x .fst .pts = (_·ᵣ α) ∘ x .fst .pts
 partition-pre·  x .fst .a≤pts =
   ≤ᵣ-·ᵣo _ _ _ 0≤α ∘ x .fst .a≤pts
 partition-pre·  x  .fst .pts≤b =
    ≤ᵣ-·ᵣo _ _ _ 0≤α ∘ x .fst .pts≤b
 partition-pre·  x  .fst .pts≤pts =
     ≤ᵣ-·ᵣo _ _ _ 0≤α ∘ x .fst .pts≤pts
 partition-pre·  x  .snd .samples =
  (_·ᵣ α) ∘  x  .snd .samples
 partition-pre·  x .snd .pts'≤samples =
   λ { k@(0 , _ , _) → ≤ᵣ-·ᵣo _ _ _ z (x .snd .pts'≤samples k)
     ; k@(suc _ , 0 , _) → ≤ᵣ-·ᵣo _ _ _ z (x  .snd .pts'≤samples k)
     ; k@(suc _ , suc _ , _) → ≤ᵣ-·ᵣo _ _ _ z (x .snd .pts'≤samples k)
      }
   where
    z = 0≤α

 partition-pre·  x .snd .samples≤pts' =
   λ { k@(0 , 0 , _) → ≤ᵣ-·ᵣo _ _ _ z (x .snd .samples≤pts' k)
     ; k@(0 , suc _ , _) → ≤ᵣ-·ᵣo _ _ _ z (x .snd .samples≤pts' k)
     ; k@(suc _ , 0 , _) → ≤ᵣ-·ᵣo _ _ _ z (x .snd .samples≤pts' k)
     ; k@(suc _ , suc _ , _) → ≤ᵣ-·ᵣo _ _ _ z (x .snd .samples≤pts' k)
      }
   where
    z = 0≤α

 partition-pre·-lem : ∀ tp k →
      pts' (fst (partition-pre· tp)) (fsuc k) -ᵣ
      pts' (fst (partition-pre· tp)) (finj k)
      ≡
      pts' (fst tp) (fsuc k) ·ᵣ α -ᵣ pts' (fst tp) (finj k) ·ᵣ α
 partition-pre·-lem tp (0 , 0 , _) = refl
 partition-pre·-lem tp (0 , suc _ , _) = refl
 partition-pre·-lem tp (suc _ , 0 , _) = refl
 partition-pre·-lem tp (suc _ , suc _ , _) = refl

 mesh-pre· : ∀ δ → (tp : TaggedPartition[ a , b ]) →
             mesh≤ᵣ (fst tp) δ
            → mesh≤ᵣ (fst (partition-pre· tp)) (δ ·ᵣ α)
 mesh-pre· δ tp x k =
   isTrans≡≤ᵣ _ _ _
     (partition-pre·-lem tp k ∙ sym (𝐑'.·DistL- _ _ _))
     (≤ᵣ-·ᵣo _ _ _ 0≤α
      (x k))

 -- mesh-pre·-sample : ((p , tg) : TaggedPartition[ a , b ]) → ∀ k →
 --     fst (samplesΣ tg k) ≡ {!!}
 -- mesh-pre·-sample = {!!}

-- module _ (a b : ℝ) (α : ℝ) (0≤α : 0 ≤ᵣ α) where

--  integral'-pre· : ∀ f s
--           → (on[ a  , b ]IntegralOf (f ∘S (_·ᵣ (α))) is' s)
--           → (on[ a ·ᵣ α  , b ·ᵣ α  ]IntegralOf f is' (s ·ᵣ α))
--  integral'-pre· f s X ε =
--    PT.rec squash₁
--       (λ (x' , (α<x' , _)) →
--        let x'₊ : ℚ₊
--            x'₊ = (x' , ℚ.<→0< x'
--                   (<ᵣ→<ℚ [ pos 0 / 1+ 0 ] x'
--                    (isTrans≤<ᵣ (rat [ pos 0 / 1+ 0 ]) α (rat x') 0≤α α<x')))
--        in PT.map
--          (map-snd λ {δ}
--            (XX : ((p , tg) : TaggedPartition[ a , b ]) →
--                                mesh≤ᵣ p (rat (fst δ)) →
--                                absᵣ (riemannSum' tg (f ∘S (_·ᵣ α)) -ᵣ s) <ᵣ
--                                rat (fst (ε ℚ₊· invℚ₊ x'₊)))
--           (p , tg) (m≤ : mesh≤ᵣ p (rat (fst δ)))  →
--            {! !})
--           (X (ε ℚ₊· invℚ₊ x'₊)))
--      ((denseℚinℝ α (α +ᵣ 1)
--        (isTrans≡<ᵣ _ _ _
--          (sym (+IdR _)) (<ᵣ-o+ 0 1 α decℚ<ᵣ?))))

module _ (a b : ℝ) (α : ℝ) (0<α : 0 <ᵣ α) where

 module PP = Partition-pre· (a ·ᵣ α) (b ·ᵣ α)
  (fst (invℝ₊ (α , 0<α))) (<ᵣWeaken≤ᵣ _ _ (snd (invℝ₊ (α , 0<α))))

 integral'-pre·< : ∀ f s
          → (on[ a  , b ]IntegralOf (f ∘S (_·ᵣ (α))) is' s)
          → (on[ a ·ᵣ α  , b ·ᵣ α  ]IntegralOf f is' (s ·ᵣ α))
 integral'-pre·< f s X ε =
   PT.rec2 squash₁
      (λ (x'' , (0<x'' , x''<α)) (x' , (α<x' , _)) →
       let x'₊ : ℚ₊
           x'₊ = (x' , ℚ.<→0< x'
                  (<ᵣ→<ℚ [ pos 0 / 1+ 0 ] x'
                   (isTrans<ᵣ (rat [ pos 0 / 1+ 0 ]) α (rat x') 0<α α<x')))
       in PT.map
         (λ ((δ , XX) : Σ _ λ δ' → (((p , tg) : TaggedPartition[ a , b ]) →
                               mesh≤ᵣ p (rat (fst δ')) →
                               absᵣ (riemannSum' tg (f ∘S (_·ᵣ α)) -ᵣ s) <ᵣ
                               rat (fst (ε ℚ₊· invℚ₊ x'₊)))) →
          let x''₊ : ℚ₊
              x''₊ = x'' , ℚ.<→0< x'' (<ᵣ→<ℚ 0 x'' 0<x'')
              δ' : ℚ₊
              δ' = δ ℚ₊· x''₊
          in δ' ,
               λ (p , tg) (m≤ : mesh≤ᵣ p (rat (fst δ')))  →
               let (p' , tg') = PP.partition-pre· (p , tg)
                   ZZ = subst2 (λ u v → Σ TaggedPartition[ u , v ]
                              λ (p , _) → mesh≤ᵣ p (rat (fst δ)))
                         ([x·yᵣ]/₊y a (α , 0<α)) ([x·yᵣ]/₊y b (α , 0<α))
                        ((p' , tg') ,

                          λ k →
                            isTrans≤ᵣ _ _ _
                              (PP.mesh-pre· (rat (fst δ')) (p , tg) m≤ k)
                               (isTrans≤≡ᵣ _ _ _
                                 (≤ᵣ-o·ᵣ _ (fst (invℝ₊ (ℚ₊→ℝ₊ x''₊))) _ (
                                  <ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ δ')))
                                  (invEq (invℝ₊-≤-invℝ₊ _ _)
                                    (<ᵣWeaken≤ᵣ _ _ x''<α)))
                                 (cong (_·ᵣ fst (invℝ₊ (ℚ₊→ℝ₊ x''₊)))
                                   (rat·ᵣrat (fst δ) x'')
                                  ∙ [x·yᵣ]/₊y (rat (fst δ)) (ℚ₊→ℝ₊ x''₊)))
                                 )
                   zzz = isTrans<≡ᵣ _ _ _ (uncurry XX ZZ)
                           (rat·ᵣrat (fst ε) _ ∙
                             cong (rat (fst ε) ·ᵣ_) (sym (invℝ₊-rat x'₊)))
                   zzz' = fst (z<x/y₊≃y₊·z<x _ _ (ℚ₊→ℝ₊ x'₊)) zzz
               in isTrans≡<ᵣ _ _ _
                    (cong absᵣ
                      (cong (_-ᵣ s ·ᵣ α)
                        ( riemannSum'-alt-lem tg f
                         ∙∙ (cong (λ (f : Fin _ → ℝ) → foldlFin
                            {n = (2 ℕ.+ len (fst (fst ZZ)))}
                              (λ S k → S +ᵣ f k) 0 (idfun _))
                              (funExt
                                λ (k : Fin _) →
                                 cong₂ _·ᵣ_
                                   (x/₊y≡z→x≡z·y _ _ (α , 0<α)
                                     (𝐑'.·DistL- _ _ _
                                       ∙
                                        sym (PP.partition-pre·-lem (p , tg) k)
                                         ∙
                                         cong₂ _-ᵣ_
                                          (pts'-tranp
                                            ([x·yᵣ]/₊y a (α , 0<α))
                                            ([x·yᵣ]/₊y b (α , 0<α))
                                            (p' , tg') (fsuc k) (fsuc k) refl)
                                          ((pts'-tranp
                                            ([x·yᵣ]/₊y a (α , 0<α))
                                            ([x·yᵣ]/₊y b (α , 0<α))
                                            (p' , tg') (finj k) (finj k) refl)))
                                    ∙ ·ᵣComm _ _)
                                   (cong f
                                    (x/₊y≡z→x≡z·y _ _ (α , 0<α)
                                      (cong
                                        (λ k
                                         → (fst (samplesΣ tg k) ／ᵣ₊ (α , 0<α)))
                                        (toℕ-injective refl)))) ∙
                                  sym (·ᵣAssoc _ _ _))
                          ∙ foldFin·DistL' (2 ℕ.+ len (fst (fst ZZ)))
                             _
                              α (idfun _))
                           ∙ ·ᵣComm _ _ ∙∙
                         cong (_·ᵣ α)
                           (sym (riemannSum'-alt-lem
                            (fst ZZ .snd) (λ x → f (x ·ᵣ α)))))
                        ∙∙
                       sym (𝐑'.·DistL- _ _ α) ∙∙ ·ᵣComm _ _)
                      ∙∙ ·absᵣ _ _ ∙∙
                      cong (_·ᵣ absᵣ (riemannSum' (fst ZZ .snd) (f ∘S (_·ᵣ α)) -ᵣ s))
                          (absᵣPos _ 0<α))
                    (isTrans≤<ᵣ _ _ _
                       (≤ᵣ-·ᵣo _ _ _ (0≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ α<x'))
                      zzz'))
          (X (ε ℚ₊· invℚ₊ x'₊)))
     (denseℚinℝ 0 α 0<α)
     (denseℚinℝ α (α +ᵣ 1)
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR _)) (<ᵣ-o+ 0 1 α decℚ<ᵣ?)))




-- integral'-pre· : ∀ a b f s (α : ℝ₊)
--                  → (on[ a , b ]IntegralOf f is' s)
--          → (on[ a ·ᵣ (fst α) , b ·ᵣ (fst α)
--            ]IntegralOf (f ∘S (_·ᵣ fst (invℝ₊ α))) is' (s ·ᵣ (fst α)))
-- integral'-pre· a b f s α X ε =
--   PT.rec squash₁
--     (λ (δ , (0<δ , δ<)) →
--       PT.map (map-snd
--          λ {δ'} →
--            λ Y p p≤ →
--             let pp = partition-pre·
--                        (a ·ᵣ (fst α)) (b ·ᵣ (fst α)) (invℝ₊ α)
--                      (p)
--             in isTrans<ᵣ _ _ _
--                (isTrans≡<ᵣ _ _ _ (({!!} ∙ ·absᵣ {!!} (fst α))
--                     ∙ cong (absᵣ _ ·ᵣ_) (absᵣPos _ (snd α)) ∙ ·ᵣComm _ _ )
--                     {!!}
--                  -- (<ᵣ-o·ᵣ _ _  α (Y (subst2 TaggedPartition[_,_]
--                  --  ([x·yᵣ]/₊y _ α) (([x·yᵣ]/₊y _ α)) pp)
--                  --   {!p≤!}))
--                    )
--                 (fst (z<x/y₊≃y₊·z<x _ _ _) δ<)
--               )
--         (X (δ , {!!})))
--     (denseℚinℝ 0 (rat (fst ε) ·ᵣ (fst (invℝ₊ α))) {!cfc!})



opaque
 unfolding _+ᵣ_ maxᵣ

 clamp-Δ-·f : ∀ a b → a ≤ᵣ b → ∀ f
       → IsContinuous f
       → ∀ (δ : ℚ₊)
       → ∀ u v → u ≤ᵣ v
       → v -ᵣ u ≤ᵣ rat (fst δ)
       → ∀ x → x ∈ intervalℙ u v
       → (clampᵣ a b v -ᵣ clampᵣ a b u) ·ᵣ f x
         ≡ (clampᵣ a b v -ᵣ clampᵣ a b u)
           ·ᵣ f (clampᵣ (a -ᵣ rat (fst δ)) (b +ᵣ rat (fst δ)) x)
 clamp-Δ-·f a b a≤b f cf δ u v u≤v v∼u x x∈ =
   sym (λ i → (clampᵣ a (b* i) (v* i) -ᵣ clampᵣ a (b* i) u) ·ᵣ f (x* i))
   ∙∙
   hhh'' a b u v x
   ∙∙
   λ i → (clampᵣ a (b* i) (v* i) -ᵣ clampᵣ a (b* i) u) ·ᵣ
      f (clampᵣ (a -ᵣ δ* i) ((b* i) +ᵣ δ* i) (x* i))


   where
   b* v* x* δ* : I → ℝ
   b* i = ≤→maxᵣ a b a≤b i
   v* i = ≤→maxᵣ u v u≤v i
   x* i = ((cong (clampᵣ u) (λ i → v* i) ≡$ x) ∙ sym (∈ℚintervalℙ→clampᵣ≡ u v x x∈)
               ) i
   δ* i = ((λ i → maxᵣ (v* i -ᵣ u) (rat (fst δ)))
        ∙ ≤→maxᵣ  (v -ᵣ u) (rat (fst δ)) v∼u) i

   fL : ℝ → ℝ → ℝ → ℝ → ℝ
   fL a b u v = clampᵣ a (maxᵣ a b) (maxᵣ u v) -ᵣ clampᵣ a (maxᵣ a b) u

   fLC : ∀ a b → IsContinuous₂ (fL a b)
   fLC a b = IsContinuous-₂∘
     (cont∘₂ (IsContinuousClamp a (maxᵣ a b)) (contNE₂ maxR))
    (cont∘₂ (IsContinuousClamp a (maxᵣ a b)) cont₂-fst)

   fLC' : ∀ u v → IsContinuous₂ (λ a b → fL a b u v)
   fLC' u v = IsContinuous-₂∘
     (IsContinuousClamp₂∘ (maxᵣ u v) cont₂-fst (contNE₂ maxR))
    (IsContinuousClamp₂∘ u cont₂-fst (contNE₂ maxR))

   f₀ f₁ : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
   f₀ a b u v x = fL a b u v ·ᵣ f (clampᵣ u (maxᵣ u v) x)
   f₁ a b u v x = fL a b u v ·ᵣ
      f (clampᵣ (a -ᵣ (maxᵣ (maxᵣ u v -ᵣ u) (rat (fst δ))))
       ((maxᵣ a b) +ᵣ (maxᵣ (maxᵣ u v -ᵣ u) (rat (fst δ))))
       ((clampᵣ u (maxᵣ u v) x)))

   f₀C : ∀ a b x → IsContinuous₂ (λ u v → f₀ a b u v x)
   f₀C a b x = cont₂·₂ᵣ (fLC a b)
     (cont∘₂ cf (IsContinuousClamp₂∘ x
       cont₂-fst (contNE₂ maxR)))
   f₁C : ∀ a b x → IsContinuous₂ (λ u v → f₁ a b u v x)
   f₁C a b x = cont₂·₂ᵣ (fLC a b) (cont∘₂ cf
      (IsContinuousClamp₂∘'
        (IsContinuous-₂∘ (cont₂-id a)
          (contNE₂∘ maxR
            (IsContinuous-₂∘ (contNE₂ maxR) cont₂-fst) (cont₂-id _)))
        ((contNE₂∘ sumR (cont₂-id (maxᵣ a b))
          (contNE₂∘ maxR
            (IsContinuous-₂∘ (contNE₂ maxR) cont₂-fst) (cont₂-id _))))
        (IsContinuousClamp₂∘ x cont₂-fst (contNE₂ maxR))))

   f₀C' : ∀ u v x → IsContinuous₂ (λ a b → f₀ a b u v x)
   f₀C' u v x = cont∘₂ (IsContinuous·ᵣR _) (fLC' u v)
   f₁C' : ∀ u v x → IsContinuous₂ (λ a b → f₁ a b u v x)
   f₁C' u v x = cont₂·₂ᵣ (fLC' u v)
      (cont∘₂ cf (IsContinuousClamp₂∘ (clampᵣ u (maxᵣ u v) x)
        (cont∘₂ (IsContinuous+ᵣR (-ᵣ (maxᵣ (maxᵣ u v -ᵣ u) (rat (fst δ)))))
          cont₂-fst)
        ((cont∘₂ (IsContinuous+ᵣR (maxᵣ (maxᵣ u v -ᵣ u) (rat (fst δ))))
          (contNE₂ maxR)))))

   f₀C'' : ∀ a b u v → IsContinuous (f₀ a b u v)
   f₀C'' a b u v = IsContinuous∘ _ _ (IsContinuous·ᵣL _)
     (IsContinuous∘ _ _ cf (IsContinuousClamp u (maxᵣ u v)))
   f₁C'' : ∀ a b u v → IsContinuous (f₁ a b u v)
   f₁C'' a b u v = IsContinuous∘ _ _ (IsContinuous·ᵣL _)
     (IsContinuous∘ _ _ cf
       (IsContinuous∘ _ _
        (IsContinuousClamp
          (a -ᵣ (maxᵣ (maxᵣ u v -ᵣ u) (rat (fst δ))))
          ((maxᵣ a b) +ᵣ (maxᵣ (maxᵣ u v -ᵣ u) (rat (fst δ)))))
        (IsContinuousClamp u (maxᵣ u v))))


   hhh : ∀ a b → a ℚ.≤ b
       → ∀ u v → u ℚ.≤ v
       → ∀ δ
       → rat v -ᵣ rat u ≤ᵣ rat δ
       → ∀ x → x ∈ ℚintervalℙ u v

       → (clampᵣ (rat a) (rat b) (rat v) -ᵣ clampᵣ (rat a) (rat b) (rat u)) ·ᵣ f (rat x)
         ≡ (clampᵣ (rat a) (rat b) (rat v) -ᵣ clampᵣ (rat a) (rat b) (rat u))
           ·ᵣ f (clampᵣ (rat a -ᵣ rat δ) (rat b +ᵣ rat δ) (rat x))
   hhh a b a≤b u v u≤v δ v-u≤δ x (≤x , x≤) = ⊎.rec
        (λ p →
         let q : clampᵣ (rat a) (rat b) (rat v)
                 -ᵣ clampᵣ (rat a) (rat b) (rat u) ≡ 0
             q = cong₂ _-ᵣ_ (clampᵣ-rat a b v) (clampᵣ-rat a b u)
                   ∙ -ᵣ-rat₂ (ℚ.clamp a b v) (ℚ.clamp a b u)  ∙ cong rat p
         in (𝐑'.0LeftAnnihilates'
               (clampᵣ (rat a) (rat b) (rat v)
                 -ᵣ clampᵣ (rat a) (rat b) (rat u)) (f (rat x)) q)
          ∙ sym (𝐑'.0LeftAnnihilates'
              (clampᵣ (rat a) (rat b) (rat v)
                 -ᵣ clampᵣ (rat a) (rat b) (rat u))
                  (f (clampᵣ (rat a -ᵣ rat (δ)) (rat b +ᵣ rat δ) (rat x))) q))
                  (λ (a≤v , u≤b) →
                     cong ( (clampᵣ (rat a) (rat b) (rat v) -ᵣ clampᵣ (rat a) (rat b) (rat u)) ·ᵣ_)
                        (cong f
                          (∈ℚintervalℙ→clampᵣ≡ (rat a -ᵣ rat δ) (rat b +ᵣ rat δ) (rat x)
                           (isTrans≤ᵣ _ _ _
                              (isTrans≤≡ᵣ _ _ _
                                (≤ᵣMonotone+ᵣ _ _ _ _
                                  (≤ℚ→≤ᵣ a _ a≤v) (-ᵣ≤ᵣ _ _ v-u≤δ) )
                                (L𝐑.lem--079 {rat v} ))
                              (≤ℚ→≤ᵣ u _ ≤x)
                           , isTrans≤ᵣ _ _ _
                                (≤ℚ→≤ᵣ _ v x≤)
                                (isTrans≡≤ᵣ _ _ _
                                  (sym (L𝐑.lem--05 {rat u}))
                                  (≤ᵣMonotone+ᵣ _ _ _ _
                                   (≤ℚ→≤ᵣ u _ u≤b) v-u≤δ))))))
                  (clampCases a b a≤b u v u≤v)

   hhh' : ∀ (a b u v x : ℚ) → f₀ (rat a) (rat b) (rat u) (rat v) (rat x)
                 ≡
               f₁ (rat a) (rat b) (rat u) (rat v) (rat x)
   hhh' a b u v x = hhh a (ℚ.max a b) (ℚ.≤max a b) u (ℚ.max u v) (ℚ.≤max u v)
      (ℚ.max ((ℚ.max u v) ℚ.- u) (fst δ))
        (isTrans≡≤ᵣ _ _ _
          ((-ᵣ-rat₂ (ℚ.max u v) u))
          (≤ℚ→≤ᵣ ((ℚ.max u v) ℚ.- u) _
            (ℚ.≤max ((ℚ.max u v) ℚ.- u) (fst δ))))

          (ℚ.clamp u (ℚ.max u v) x)
            (clam∈ℚintervalℙ u (ℚ.max u v) (ℚ.≤max u v) x)
     ∙ cong₂ _·ᵣ_
          refl
          (cong f
            (cong₃ clampᵣ (cong (_-ᵣ_ (rat a))
              (cong (flip maxᵣ (rat (fst δ))) (sym (-ᵣ-rat₂ (ℚ.max u v) u))))
              (cong (rat (ℚ.max a b) +ᵣ_)
               (cong (flip maxᵣ (rat (fst δ))) (sym (-ᵣ-rat₂ (ℚ.max u v) u))))
              refl))

   hhh'' : ∀ (a b u v x : ℝ) → f₀ a b u v x ≡ f₁ a b u v x
   hhh'' a b u v x =
     ≡Cont₂ (f₀C a b x) (f₁C a b x)
       (λ uℚ vℚ → let u = rat uℚ ; v = rat vℚ in
         ≡Cont₂ (f₀C' u v x) (f₁C' u v x)
          (λ aℚ bℚ → let a = rat aℚ ; b = rat bℚ in
           ≡Continuous (f₀ a b u v) (f₁ a b u v)
            (f₀C'' a b u v) (f₁C'' a b u v)
             (hhh' aℚ bℚ uℚ vℚ) x)
          a b)
       u v


 -- clamp-Δ-·f' : ∀ a b → a ≤ᵣ b → ∀ f
 --      → IsContinuous f
 --      → ∀ (δ : ℚ₊)
 --      → ∀ u v → u ≤ᵣ v
 --      → v -ᵣ u ≤ᵣ rat (fst δ)
 --      → ∀ x → rat x ∈ intervalℙ u v
 --      → (clampᵣ a b v -ᵣ clampᵣ a b u) ·ᵣ f (rat x)
 --        ≡ (clampᵣ a b v -ᵣ clampᵣ a b u)
 --          ·ᵣ f (clampᵣ (a -ᵣ rat (fst δ)) (b) (rat x))
 -- clamp-Δ-·f' a b a≤b f cf δ u v u≤v v∼u x (≤x , x≤) =
 --   subst {x = rat x} {clampᵣ u v (rat x)}
 --      (λ x →
 --      (clampᵣ a b v -ᵣ clampᵣ a b u) ·ᵣ f x
 --        ≡ (clampᵣ a b v -ᵣ clampᵣ a b u)
 --          ·ᵣ f (clampᵣ (a -ᵣ rat (fst δ)) (b) x))
 --          ?
 --       (subst2 (λ b u →
 --      (clampᵣ a b v -ᵣ clampᵣ a b u) ·ᵣ f (rat x)
 --        ≡ (clampᵣ a b v -ᵣ clampᵣ a b u)
 --          ·ᵣ f (clampᵣ (a -ᵣ rat (fst δ)) (b) (rat x)))
 --     (≤→maxᵣ _ _ a≤b)

 --     (sym (∈ℚintervalℙ→clampᵣ≡
 --       (v -ᵣ rat (fst δ)) v
 --       u (≤u , u≤v)))
 --       (≡Cont₂
 --         {f₀ = λ a b → f₀ a b u v}
 --         {f₁ = λ a b → f₁ a b u v}
 --        (cont∘₂ (IsContinuous·ᵣR (f (u' ?))) ch)
 --         (cont₂·₂ᵣ
 --           ch
 --           (cont∘₂ cf
 --             (IsContinuousClamp₂∘ (clampᵣ (v -ᵣ rat (fst δ)) v ?)
 --               ((λ _ → IsContinuousConst _) ,
 --                (λ _ → IsContinuous+ᵣR (-ᵣ rat (fst δ)))
 --                ) ((contNE₂ maxR)))))
 --        (λ aℚ bℚ →
 --          ≡Cont₂ {f₀ = f₀ (rat aℚ) (rat bℚ)}
 --                 {f₁ = f₁ (rat aℚ) (rat bℚ)}
 --             (cont₂·₂ᵣ (ch' aℚ bℚ)
 --               (cont∘₂ cf ch''))
 --             (cont₂·₂ᵣ (ch' aℚ bℚ)
 --               (cont∘₂ cf
 --                 (cont∘₂ (IsContinuousClamp (rat aℚ -ᵣ rat (fst δ))
 --                       ((maxᵣ (rat aℚ) (rat bℚ)))) ch'')))
 --             (λ uℚ vℚ →
 --              let qqq = (cong (λ xx →
 --                       clampᵣ xx (rat vℚ) (rat uℚ))
 --                        (sym (-ᵣ-rat₂ vℚ  (fst δ))))
 --                  ppp =
 --                     cong (λ uu →
 --                        clampᵣ (rat aℚ) (maxᵣ (rat aℚ) (rat bℚ)) (rat vℚ) -ᵣ
 --                       clampᵣ (rat aℚ) (maxᵣ (rat aℚ) (rat bℚ))
 --                       uu)
 --                        qqq
 --              in cong₂ _·ᵣ_
 --                 (sym ppp)
 --                 (cong f (sym qqq))
 --                 ∙∙ hh aℚ ((ℚ.max aℚ bℚ))
 --                       (ℚ.≤max aℚ bℚ)
 --                    ((ℚ.clamp (vℚ ℚ.- (fst δ)) (vℚ) ( uℚ)))
 --                       (vℚ) (ℚ.clamp≤ (vℚ ℚ.- fst δ) vℚ uℚ)
 --                        (isTrans≤≡ᵣ _ _ _ (≤ᵣ-o+ (-ᵣ (rat (ℚ.clamp (vℚ ℚ.- fst δ) vℚ uℚ)))
 --                         (-ᵣ rat (vℚ ℚ.- fst δ))
 --                         (rat vℚ)
 --                          (-ᵣ≤ᵣ _ _  (≤ℚ→≤ᵣ _ _ (ℚ.≤clamp (vℚ ℚ.- fst δ) vℚ uℚ
 --                           (ℚ.≤-ℚ₊ vℚ vℚ δ (ℚ.isRefl≤ vℚ))))))
 --                          (cong (_-ᵣ_ (rat vℚ)) (sym (-ᵣ-rat₂ vℚ (fst δ)))
 --                           ∙ L𝐑.lem--079 {rat vℚ} {rat (fst δ)})
 --                          ) ∙∙
 --                 cong₂ _·ᵣ_
 --                  ppp
 --                  (cong f
 --                    (cong (clampᵣ (rat aℚ -ᵣ rat (fst δ)) _)

 --                      qqq)))
 --             u v)
 --         a b))


 --   where
 --    -- x'
 --    ≤u : v -ᵣ rat (fst δ) ≤ᵣ u
 --    ≤u = a-b≤c⇒a-c≤b v _ _ v∼u


 --    u' : ℝ → ℝ
 --    u' = clampᵣ (v -ᵣ rat (fst δ)) v

 --    f₀ : ℝ → ℝ → ℝ → ℝ → ℝ
 --    f₀ a b u v = ((clampᵣ a (maxᵣ a b)) v -ᵣ clampᵣ a (maxᵣ a b)
 --      (clampᵣ (v -ᵣ rat (fst δ)) v u))
 --       ·ᵣ f (clampᵣ (v -ᵣ rat (fst δ)) v (rat x))


 --    f₁ : ℝ → ℝ → ℝ → ℝ → ℝ
 --    f₁ a b u v = ((clampᵣ a (maxᵣ a b)) v -ᵣ clampᵣ a (maxᵣ a b)
 --         (clampᵣ (v -ᵣ rat (fst δ)) v u))
 --          ·ᵣ f (clampᵣ (a -ᵣ rat (fst δ)) ((maxᵣ a b))
 --           (clampᵣ (v -ᵣ rat (fst δ)) v (rat x)))




 --    b' : ℝ
 --    b' = maxᵣ a b

 --    ch : IsContinuous₂ λ z z₁ →
 --                            NonExpanding₂-Lemmas.NE.go ℚ._+_ sumR
 --                             (clampᵣ z (maxᵣ z z₁) v)
 --                            (-ᵣ clampᵣ z (maxᵣ z z₁) (u' u))
 --    ch = (IsContinuous-₂∘
 --             (IsContinuousClamp₂∘ v
 --                ((λ _ → IsContinuousConst _) , (λ _ → IsContinuousId))
 --                (contNE₂ maxR))
 --             (IsContinuousClamp₂∘ (clampᵣ (v -ᵣ rat (fst δ)) v u)
 --                 ((λ _ → IsContinuousConst _) , (λ _ → IsContinuousId))
 --                 (contNE₂ maxR)))

 --    ch'' : IsContinuous₂ (λ z z₁ → (clampᵣ (z₁ -ᵣ rat (fst δ)) z₁ (rat x)))
 --    ch'' = ?
 --    -- contNE₂∘ minR
 --    --      {λ z z₁ → maxᵣ ((z₁ -ᵣ rat (fst δ))) z}
 --    --      {λ z z₁ → z₁}
 --    --    (contNE₂∘ maxR
 --    --      ((λ _ → IsContinuous+ᵣR (-ᵣ rat (fst δ))) , (λ _ → IsContinuousConst _))
 --    --      ( (λ _ → IsContinuousConst _) ,  (λ _ → IsContinuousId)))
 --    --   ((λ _ → IsContinuousId) , (λ _ → IsContinuousConst _))

 --    ch' : ∀ aℚ bℚ → IsContinuous₂
 --      (λ z z₁ →
 --         clampᵣ (rat aℚ) (maxᵣ (rat aℚ) (rat bℚ)) z₁ -ᵣ
 --         clampᵣ (rat aℚ) (maxᵣ (rat aℚ) (rat bℚ))
 --         (clampᵣ (z₁ -ᵣ rat (fst δ)) z₁ _))
 --    ch' aℚ bℚ = ?
 --    -- IsContinuous-₂∘
 --    --   ((λ _ → IsContinuousClamp (rat aℚ) (maxᵣ (rat aℚ) (rat bℚ)))
 --    --    , λ _ → IsContinuousConst _ )
 --    --   (cont∘₂ (IsContinuousClamp (rat aℚ) (maxᵣ (rat aℚ) (rat bℚ)))
 --    --    ch'')

 --    hh : ∀ a b → a ℚ.≤ b
 --      → ∀ u v → u ℚ.≤ v
 --      → rat v -ᵣ rat u ≤ᵣ rat (fst δ)

 --      → (clampᵣ (rat a) (rat b) (rat v) -ᵣ clampᵣ (rat a) (rat b) (rat u))
 --         ·ᵣ f (rat x)
 --        ≡ (clampᵣ (rat a) (rat b) (rat v) -ᵣ clampᵣ (rat a) (rat b) (rat u))
 --          ·ᵣ f (clampᵣ (rat a -ᵣ rat (fst δ)) (rat b) (rat x))
 --    hh a b a≤b u v u≤v v-u≤δ = ?
 --      -- ⊎.rec
 --      --   (λ p →
 --      --    let q : clampᵣ (rat a) (rat b) (rat v)
 --      --            -ᵣ clampᵣ (rat a) (rat b) (rat u) ≡ 0
 --      --        q = cong₂ _-ᵣ_ (clampᵣ-rat a b v) (clampᵣ-rat a b u)
 --      --              ∙ -ᵣ-rat₂ (ℚ.clamp a b v) (ℚ.clamp a b u)  ∙ cong rat p
 --      --    in (𝐑'.0LeftAnnihilates'
 --      --          (clampᵣ (rat a) (rat b) (rat v)
 --      --            -ᵣ clampᵣ (rat a) (rat b) (rat u)) (f (rat u)) q)
 --      --     ∙ sym (𝐑'.0LeftAnnihilates'
 --      --         (clampᵣ (rat a) (rat b) (rat v)
 --      --            -ᵣ clampᵣ (rat a) (rat b) (rat u))
 --      --             (f (clampᵣ (rat a -ᵣ rat (fst δ)) (rat b) (rat u))) q))
 --      --   (λ (a≤v , u≤b) →
 --      --      cong ( (clampᵣ (rat a) (rat b) (rat v) -ᵣ clampᵣ (rat a) (rat b) (rat u)) ·ᵣ_)
 --      --     (cong f ((∈ℚintervalℙ→clampᵣ≡ (rat a -ᵣ rat (fst δ)) (rat b) (rat u)
 --      --        ((isTrans≤ᵣ _ _ _
 --      --          (≤ᵣ-+o _ _ (-ᵣ (rat (fst δ))) (≤ℚ→≤ᵣ a v a≤v)) (a-b≤c⇒a-c≤b (rat v) _ _ v-u≤δ))
 --      --          , (≤ℚ→≤ᵣ u b u≤b)))
 --      --           )))
 --      --  (clampCases a b a≤b u v u≤v)



opaque
 unfolding maxᵣ
 clamp-interval-Δ-swap : ∀ a b a' b'
            → a  ≤ᵣ b
            → a' ≤ᵣ b'
                 → clampᵣ a  b  b' -ᵣ clampᵣ a  b  a'
                 ≡ clampᵣ a' b' b  -ᵣ clampᵣ a' b' a
 clamp-interval-Δ-swap a b a' b' a≤b a'≤b' =
   subst2 (λ b' b → clampᵣ a  b  b' -ᵣ clampᵣ a  b  a'
                 ≡ clampᵣ a' b' b  -ᵣ clampᵣ a' b' a)
       (≤→maxᵣ _ _ a'≤b') (≤→maxᵣ _ _ a≤b)
       (≡Cont₂ {f₀ = λ a b → f a b a' b'}
               {f₁ = λ a b → f a' b' a b}
          (fC' a' b')
          (fC a' b')
          (λ aℚ bℚ → let a = (rat aℚ) ; b = (rat bℚ) in
             ≡Cont₂ {f₀ = λ a' b' → f a b a' b'}
                    {f₁ = λ a' b' → f a' b' a b}
              (fC (rat aℚ) (rat bℚ))
              (fC' (rat aℚ) (rat bℚ))
              (λ aℚ' bℚ' →
                 -ᵣ-rat₂ _ _ ∙∙ cong rat
                    (ℚclampInterval-delta aℚ _ aℚ' _ (ℚ.≤max aℚ bℚ) (ℚ.≤max aℚ' bℚ'))
                  ∙∙ sym (-ᵣ-rat₂ _ _))
              a' b')
          a b)



  where

  f : ℝ → ℝ → ℝ → ℝ → ℝ
  f a b a' b' = clampᵣ a (maxᵣ a b) (maxᵣ a' b') -ᵣ clampᵣ a (maxᵣ a b) a'

  fC : ∀ a b → IsContinuous₂ (f a b)
  fC a b = IsContinuous-₂∘
     (cont∘₂ (IsContinuousClamp a (maxᵣ a b)) (contNE₂ maxR))
     (cont∘₂ (IsContinuousClamp a (maxᵣ a b))
      ((λ _ → IsContinuousConst _) ,  (λ _ → IsContinuousId)))

  fC' : ∀ a b → IsContinuous₂ (λ a' b' → f a' b' a b)
  fC' a' b' = IsContinuous-₂∘
     (IsContinuousClamp₂∘ (maxᵣ a' b')
      (((λ _ → IsContinuousConst _) ,  (λ _ → IsContinuousId)))
      (contNE₂ maxR))
     (IsContinuousClamp₂∘ a'
      ((λ _ → IsContinuousConst _) ,  (λ _ → IsContinuousId)) (contNE₂ maxR))


llll : absᵣ (rat [ pos 0 / 1+ 0 ] -ᵣ rat [ pos 0 / 1+ 0 ]) ≤ᵣ
      rat [ pos 0 / 1+ 0 ]
llll = ≡ᵣWeaken≤ᵣ _ _
   (cong absᵣ (-ᵣ-rat₂ _ _) ∙ absᵣ0
     ∙ cong {x = zero} (λ z → rat [ pos z / 1+ z ]) refl )

0<2^-ℚ : ∀ n → ℚ.0< [ pos (2^ n) / 1+ 0 ]
0<2^-ℚ n = ℚ.<→0< [ pos (2^ n) / 1+ 0 ] (ℚ.<ℤ→<ℚ 0 (pos (2^ n))
 (invEq (ℤ.pos-<-pos≃ℕ< 0 _) (0<2^ n) ))

2^-mon : ∀ n → 2^ n ℕ.< 2^ (suc n)
2^-mon zero = ℕ.≤-solver 2 2
2^-mon (suc n) = ℕ.<-+-< (2^-mon n) (2^-mon n)

lemXX : ∀ n → 2 ℕ.+ predℕ (predℕ (2^ (suc n))) ≡ 2^ (suc n)
lemXX n = ℕ.k+predℕₖ {2} {2^ (suc n)} (ℕ.≤-+-≤ {1} {2^ n} {1} {2^ n}
 (0<2^ n) (0<2^ n))

invℚ₊-inj : ∀ a b → fst (invℚ₊ a) ≡ fst (invℚ₊ b) → fst a ≡ fst b
invℚ₊-inj a b x =
  sym (ℚ.invℚ₊-invol _)
  ∙∙ cong (fst ∘ invℚ₊) (ℚ₊≡ x) ∙∙
  ℚ.invℚ₊-invol _

module Resample where


 -- resampledRiemannSum : ∀ a b → a ≤ᵣ b →  (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ)
 --   → (pa pa' : Partition[ a , b ])
 --    (s : Sample pa) → ℝ
 -- resampledRiemannSum a b a≤b f pa pa' sa =
 --   foldlFin {n = 2 ℕ.+ P'.len}
 --      (λ s  k →
 --        let  a' = P'.pts' (finj k)
 --             b' = P'.pts' (fsuc k)
 --        in s +ᵣ
 --            foldlFin {n = 2 ℕ.+ P.len}
 --            (λ s ((t , a≤t , t≤b) , b-a) → s +ᵣ
 --              b-a ·ᵣ (f (clampᵣ a' b' t)
 --                (isTrans≤ᵣ _ _ _ (P'.a≤pts' (finj k))
 --                  (≤clampᵣ a' b' t (P'.pts'≤pts' k)))
 --                (isTrans≤ᵣ _ _ _ (clamp≤ᵣ a' b' t) (P'.pts'≤b (fsuc k)))) ) 0
 --                (λ k →  S.samplesΣ k , P.pts' (fsuc k) -ᵣ P.pts' (finj k))
 --        )
 --      0
 --      (idfun _)

 --      -- (λ k →  k (P'.pts' (fsuc k) , P'.pts' (finj k)))
 --  -- foldlFin {n = 2 ℕ.+ P.len}
 --  --    (λ s ((t , a≤t , t≤b) , b-a) → s +ᵣ
 --  --      b-a ·ᵣ (f t a≤t t≤b) ) 0
 --  --        (λ k →  S.samplesΣ k , P.pts' (fsuc k) -ᵣ P.pts' (finj k))
 --  where
 --  module P = Partition[_,_] pa
 --  module P' = Partition[_,_] pa'
 --  module S = Sample sa


 resampledRiemannSum' : ∀ a b →  (ℝ → ℝ)
   → (pa pa' : Partition[ a , b ])
    (s : Sample pa) → ℝ
 resampledRiemannSum' a b f pa pa' sa =
   foldlFin {n = 2 ℕ.+ P'.len}
      (λ s  k →
        let  a' = P'.pts' (finj k)
             b' = P'.pts' (fsuc k)
        in s +ᵣ
            foldlFin {n = 2 ℕ.+ P.len}
            (λ s ((t , a≤t , t≤b) , b-a) → s +ᵣ
              b-a ·ᵣ (f t) ) 0
                (λ k →  S.samplesΣ k ,
                 clampᵣ a' b' (P.pts' (fsuc k))
                  -ᵣ clampᵣ a' b' (P.pts' (finj k)))
        ) 0 (idfun _)

  where
  module P = Partition[_,_] pa
  module P' = Partition[_,_] pa'
  module S = Sample sa


 partitionClamp : ∀ a b  → ∀ a' b' → a' ≤ᵣ b'
   → a ≤ᵣ a' →  b' ≤ᵣ b →
   (pa : Partition[ a , b ]) →
    b' -ᵣ a' ≡
         foldlFin {n = 2 ℕ.+ len pa}
      (λ s  k →
        let  a* = pts' pa (finj k)
             b* = pts' pa (fsuc k)
        in s +ᵣ
            ((clampᵣ a' b' b* -ᵣ clampᵣ a' b' a*))
        )
      0
      (idfun _)
 partitionClamp a b a' b' a'≤b' a≤a' b'≤b pa =
   cong₂ _-ᵣ_
     (sym (≤x→clampᵣ≡ a' b' (pts' pa flast) a'≤b' b'≤b))
     (sym (x≤→clampᵣ≡ a' b' (pts' pa fzero)
       a'≤b' a≤a'))
    ∙ sym (deltas-sum (2 ℕ.+ len pa)
      (clampᵣ a' b' ∘ pts' pa ))



 resample : ∀ a b → a ≤ᵣ b → (pa pa' : Partition[ a , b ])
    (sa : Sample pa)  → ∀ f
    → resampledRiemannSum' a b f pa pa' sa
       ≡ riemannSum' sa f
 resample a b a≤b pa pa' sa f =
    ((cong (foldlFin {n = 2 ℕ.+ P'.len})
     (funExt₂ (λ s k' →
       cong (s +ᵣ_)
        (foldFin+map (2 ℕ.+ P.len) 0 _
         (λ k →  S.samplesΣ k ,
                 clampᵣ (P'.pts' (finj k')) (P'.pts' (fsuc k'))
                  (P.pts' (fsuc k))
                  -ᵣ clampᵣ (P'.pts' (finj k')) (P'.pts' (fsuc k'))
                   (P.pts' (finj k))) (idfun _) )))
     ≡$ 0) ≡$ (idfun _))
     ∙ foldFin+transpose (2 ℕ.+ P'.len) (2 ℕ.+ P.len) _ 0
     ∙ ((cong (foldlFin {n = 2 ℕ.+ P.len})
          (funExt₂ (λ s k →
            cong (s +ᵣ_)
             (  (cong (foldlFin {n = 2 ℕ.+ P'.len})
               (funExt₂ (λ s k' → cong (s +ᵣ_)
                 (·ᵣComm _ _)))
               ≡$ 0 ≡$ (idfun _))
              ∙ foldFin·DistL' (2 ℕ.+ P'.len) _ (f (fst (S.samplesΣ k))) (idfun _)
              ∙ cong (f (fst (S.samplesΣ k)) ·ᵣ_)
                  (((cong (foldlFin {n = 2 ℕ.+ P'.len})
                     (funExt₂ (λ s k' → cong (s +ᵣ_)
                         ((clamp-interval-Δ-swap
                          (P'.pts' (finj k')) (P'.pts' (fsuc k'))
                          (P.pts' (finj k)) (P.pts' (fsuc k))
                          (P'.pts'≤pts' k') (P.pts'≤pts' k)))
                         )) ≡$ 0)
                      ≡$ (idfun _))
                   ∙ sym
                     (partitionClamp a b (P.pts' (finj k)) (P.pts' (fsuc k))
                      (P.pts'≤pts' k) (P.a≤pts' (finj k)) (P.pts'≤b (fsuc k)) pa'))
              ∙ ·ᵣComm _ _
             )
                        ))
          ≡$ 0) ≡$ (idfun _))
     ∙ sym (foldFin+map (2 ℕ.+ P.len) 0 _
       (λ k →  S.samplesΣ k , P.pts' (fsuc k) -ᵣ P.pts' (finj k)) (idfun _))


  where
  module P = Partition[_,_] pa
  module P' = Partition[_,_] pa'
  module S = Sample sa

--
 resampleΔ-UC : ∀ a b → (a<b : a ≤ᵣ b)   → ∀ f → IsUContinuous f → (ε : ℚ₊)
    → (δ : ℚ₊ ) →  (∀ (u v : ℝ) →
                   u ∼[ δ ] v →
                   absᵣ (f u -ᵣ f v) <ᵣ
                   fst (ℚ₊→ℝ₊ ε ₊·ᵣ
                       invℝ₊ (maxᵣ 1 (b -ᵣ a) ,
                         isTrans<≤ᵣ _ _ _ (decℚ<ᵣ? {0} {1}) (≤maxᵣ 1 (b -ᵣ a)))))
    → (tpa tpa' : TaggedPartition[ a , b ])
       → mesh≤ᵣ (fst tpa) (rat (fst (/4₊ δ)))
       → mesh≤ᵣ (fst tpa') (rat (fst (/4₊ δ))) →
      absᵣ (riemannSum' (snd tpa) f -ᵣ riemannSum' (snd tpa') f) ≤ᵣ
     rat (fst ε)
 resampleΔ-UC a b a≤b f fcu ε δ X (pa , sa) (pa' , sa') = zzzz
   -- PT.map {A = Σ ℚ₊
   --              (λ δ →
   --                 (u v : ℝ) →
   --                 u ∼[ δ ] v →
   --                 absᵣ (f u -ᵣ f v) <ᵣ
   --                 fst (ℚ₊→ℝ₊ ε ₊·ᵣ invℝ₊ (b +ᵣ -ᵣ a , x<y→0<y-x a b a<b)))}
     -- (λ (δ , X) →  , λ )
    -- (IsUContinuous-εᵣ f fcu
    --  (ℚ₊→ℝ₊ ε ₊·ᵣ invℝ₊ (_ , x<y→0<y-x _ _ a<b)))

  where
    σ : ℝ₊
    σ = maxᵣ 1 (b -ᵣ a) ,
        isTrans<≤ᵣ _ _ _ (decℚ<ᵣ? {0} {1}) (≤maxᵣ 1 (b -ᵣ a))
    η : ℝ₊
    η = ℚ₊→ℝ₊ ε ₊·ᵣ invℝ₊ σ

    cf : IsContinuous f
    cf = IsUContinuous→IsContinuous f fcu


    module P = Partition[_,_] pa
    module P' = Partition[_,_] pa'
    module S = Sample sa
    module S' = Sample sa'

    ruc'Δ : Fin (suc (suc P.len)) → Fin (suc (suc P'.len)) → ℝ
    ruc'Δ k k' = (clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (fsuc k'))
         -ᵣ
        clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (finj k')))


    opaque
     unfolding maxᵣ minᵣ
     zzzz :
       P.mesh≤ᵣ (rat (fst (/4₊ δ))) →
       P'.mesh≤ᵣ (rat (fst (/4₊ δ))) →
       absᵣ (S.riemannSum' f -ᵣ S'.riemannSum' f) ≤ᵣ
       rat (fst ε)
     zzzz m-pa< m-pa'< =
        isTrans≡≤ᵣ _ _ _
         (cong absᵣ
          (cong (_-ᵣ_ (S.riemannSum' f))
            (sym (resample a b a≤b pa' pa sa' f))
            ∙ zip-foldFin-ᵣ (2 ℕ.+ len pa)

              (λ k →  S.samplesΣ k , P.pts' (fsuc k) -ᵣ P.pts' (finj k))
              (idfun _)
              _ _ _ _))
         (isTrans≤ᵣ _ _ _ (isTrans≤≡ᵣ _ _ _

           (foldFin+≤-abs (2 ℕ.+ len pa) _ 0
             _ (λ k → (fst η ·ᵣ pts' pa (fsuc k) -ᵣ fst η ·ᵣ pts' pa (finj k))
                          )
                           (λ k →
                             (S.samplesΣ k ,
                              P.pts' (fsuc k) -ᵣ P.pts' (finj k)) , k)
                           (idfun _)
            llll
            ruc
            )
           (deltas-sum (2 ℕ.+ len pa) ((fst η ·ᵣ_) ∘ pts' pa)
            ∙ sym (𝐑'.·DistR- _ _ _)))
             (isTrans≤≡ᵣ _ _ _
               (≤ᵣ-o·ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ (snd η))
                (isTrans≤≡ᵣ _ _ _ (≤maxᵣ (b -ᵣ a) 1) (maxᵣComm (b -ᵣ a) 1)) )
               ([x/₊y]·yᵣ _ σ)))

      where

 -- ruc

       ruc' : ∀ k k' →
              absᵣ
          (f (S.samplesΣ k .fst) ·ᵣ ruc'Δ k k' -ᵣ
            ruc'Δ k k' ·ᵣ f (S'.samplesΣ k' .fst))
          ≤ᵣ fst η ·ᵣ ruc'Δ k k'
       ruc' k k' =
        isTrans≡≤ᵣ _ _ _

         (cong absᵣ (cong₂ _-ᵣ_
          (·ᵣComm _ _)
          ((clamp-Δ-·f _ _ (P.pts'≤pts' k)
            f cf (/2₊ (/2₊ δ)) _ _ (P'.pts'≤pts' k')
              (isTrans≤≡ᵣ _ _ _ (m-pa'< k')
                (cong rat (ℚ./4₊≡/2₊/2₊ δ))) _
                 (S'.pts'≤samples k' ,
                  S'.samples≤pts' k' )))

                  ∙
               sym (𝐑'.·DistR- (ruc'Δ k k') _ f') ) ∙
                ·absᵣ _ _ ∙
                 cong (_·ᵣ (absᵣ (f (S.samplesΣ k .fst) -ᵣ
                      f'))) (absᵣNonNeg _ hh
                        ) ∙ ·ᵣComm _ _)
         (≤ᵣ-·ᵣo _ _ _ hh (<ᵣWeaken≤ᵣ _ _ (X _ _ smpl-δ)))
         where
          δ/4<δ/2 : rat (fst δ ℚ.· ([ 1 / 2 ] ℚ.· [ 1 / 2 ])) <ᵣ
             rat (fst (/2₊ δ))
          δ/4<δ/2 = (isTrans≡<ᵣ _ _ _
                            (cong rat (ℚ.·Assoc (fst δ) _ _))
                            (<ℚ→<ᵣ (fst (/2₊ (/2₊ δ))) (fst (/2₊ δ)) (ℚ.x/2<x (/2₊ δ))))

          f' : ℝ
          f' = _
          hh : 0 ≤ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (fsuc k'))
                -ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (finj k'))
          hh = (x≤y→0≤y-x _ _
                         (clamp-monotone-≤ᵣ
                          (P.pts' (finj k))
                          (P.pts' (fsuc k))
                          _ _ (P'.pts'≤pts' k')))

          xzxd : absᵣ
              (P.pts' (fsuc k) +ᵣ rat (fst (/2₊ (/2₊ δ))) +ᵣ -ᵣ P.pts' (finj k))
              +ᵣ absᵣ (-ᵣ (-ᵣ rat (fst (/2₊ (/2₊ δ)))))
              <ᵣ rat (fst δ)
          xzxd =
            a<b-c⇒a+c<b _ _ _
            (subst2 _<ᵣ_
             (sym (absᵣPos _
                (isTrans≡<ᵣ _ _ _
                 (sym (+ᵣ-rat 0 0))
                 (<≤ᵣMonotone+ᵣ _ _ _ _
                  (snd (ℚ₊→ℝ₊ (/2₊ (/2₊ δ))))
                  (x≤y→0≤y-x _ _ (P.pts'≤pts' k)))))
               ∙ cong absᵣ
               (+ᵣAssoc _ _ _ ∙ cong (_+ᵣ (-ᵣ P.pts' (finj k))) (+ᵣComm _ _ )))
               (cong rat (𝐐'.·DistR- (fst δ) 1 _) ∙ sym (-ᵣ-rat₂ (fst δ ℚ.· 1) _) ∙
                 cong₂ (_-ᵣ_)
                    (cong rat (ℚ.·IdR _))
                    ((cong rat (ℚ./4₊≡/2₊/2₊ δ)) ∙ sym (absᵣPos _ (snd (ℚ₊→ℝ₊ (/2₊ (/2₊ δ)))))
                      ∙ cong absᵣ (sym (-ᵣInvol _))))
             (isTrans≤<ᵣ _ _ _
               (≤ᵣMonotone+ᵣ _ _ _ _
                (≡ᵣWeaken≤ᵣ _ _ (cong rat (sym (ℚ./4₊≡/2₊/2₊ δ)))) (m-pa< k))
               (isTrans≡<ᵣ _ _ _
                 (+ᵣ-rat _ _ ∙ cong rat (sym ((ℚ.·DistL+ (fst δ) _ _))))
                 (<ℚ→<ᵣ _ _
                   ((ℚ.<-o· ([ 1 / 4 ] ℚ.+ [ 1 / 4 ])
                     (1 ℚ.- [ 1 / 4 ]) (fst δ) (ℚ.0<ℚ₊ δ)
                      (ℚ.decℚ<? {[ 1 / 4 ] ℚ.+ [ 1 / 4 ]}
                         {1 ℚ.- [ 1 / 4 ]})))))))

          smpl-δ : S.samplesΣ k .fst ∼[ δ ]
               clampᵣ (P.pts' (finj k) -ᵣ rat (fst (/2₊ (/2₊ δ))))
                      (P.pts' (fsuc k) +ᵣ rat (fst (/2₊ (/2₊ δ))))
               (fst (S'.samplesΣ k'))
          smpl-δ =
            invEq (∼≃abs<ε _ _ _)
            ((isTrans≤<ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _
                (cong absᵣ
                 ((cong₂ _-ᵣ_
                   (∈ℚintervalℙ→clampᵣ≡ (P.pts' (finj k) -ᵣ rat (fst (/2₊ (/2₊ δ))))
                    (P.pts' (fsuc k) +ᵣ rat (fst (/2₊ (/2₊ δ))))
                     (fst (S.samplesΣ k))

                      ((isTrans≤ᵣ _ _ _
                        (isTrans≤≡ᵣ _ _ _
                          (≤ᵣ-o+ _ _ (P.pts' (finj k))
                           (-ᵣ≤ᵣ _ _ (≤ℚ→≤ᵣ 0 _ (ℚ.0≤ℚ₊ (/2₊ (/2₊ δ))))))
                          (𝐑'.+IdR' _ _ (-ᵣ-rat 0)))
                        (S.pts'≤samples k)) ,
                         isTrans≤ᵣ _ _ _
                         (S.samples≤pts' k)
                         (isTrans≡≤ᵣ _ _ _ (sym (𝐑'.+IdR' _ _ refl))
                           (≤ᵣ-o+ _ _ (P.pts' (fsuc k))
                           (≤ℚ→≤ᵣ 0 _ (ℚ.0≤ℚ₊ (/2₊ (/2₊ δ))))))
                        )
                        )
                   refl)))
                  (clampᵣ-dist (P.pts' (finj k) -ᵣ rat (fst (/2₊ (/2₊ δ))))
                   (P.pts' (fsuc k) +ᵣ rat (fst (/2₊ (/2₊ δ))))
                     _ _))
                  (isTrans≤<ᵣ _ _ _
                   (isTrans≡≤ᵣ _ _ _ (cong absᵣ
                    (cong ((P.pts' (fsuc k) +ᵣ rat (fst (/2₊ (/2₊ δ)))) +ᵣ_) ( -ᵣDistr _ _) ∙ +ᵣAssoc _ _ _))
                     (absᵣ-triangle _ _))
                      xzxd)))
       ruc : ∀ k →
           absᵣ
         ((P.pts' (fsuc k) -ᵣ P.pts' (finj k)) ·ᵣ f (S.samplesΣ k .fst) -ᵣ
          foldlFin
          (λ s ((t , a≤t , t≤b) , b-a) → s +ᵣ b-a ·ᵣ f t) 0
          (λ k₁ →
             P'.samplesΣ sa' k₁ ,
             clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (fsuc k₁))
             -ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (finj k₁))))
         ≤ᵣ
         (fst η ·ᵣ P.pts' (fsuc k) -ᵣ fst η ·ᵣ P.pts' (finj k))

       ruc k =
         isTrans≡≤ᵣ _ _ _
           (cong (absᵣ ∘ (_-ᵣ (foldlFin
          (λ s ((t , a≤t , t≤b) , b-a) → s +ᵣ b-a ·ᵣ f t) 0
          (λ k₁ →
             P'.samplesΣ sa' k₁ ,
             clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (fsuc k₁))
             -ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (finj k₁))
             ))))
              (cong (_·ᵣ f (S.samplesΣ k .fst))
                (partitionClamp a b
                  (P.pts' (finj k))
                  (P.pts' (fsuc k))
                   (P.pts'≤pts' k)
                  (P.a≤pts' (finj k)) (P.pts'≤b (fsuc k)) pa'
                  ) ∙ ·ᵣComm _ _ ∙
                   sym (foldFin·DistL (2 ℕ.+ len pa') _ _ _
                    (idfun _))) ∙
                   cong absᵣ
                    (zip-foldFin-ᵣ (2 ℕ.+ len pa')
                    (idfun _)
                     (λ k₁ →
                       (samplesΣ sa' k₁ ,
                           clampᵣ (P.pts' (finj k))
                            (P.pts' (fsuc k)) (P'.pts' (fsuc k₁))
                        -ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k))
                            (P'.pts' (finj k₁))))
                       _ _ _
                     0))
              (isTrans≤≡ᵣ _ _ _
               (foldFin+≤-abs (2 ℕ.+ len pa')
                  _ 0 _
                   (λ kk →  fst η ·ᵣ
                    (clampᵣ (P.pts' (finj k)) ((P.pts' (fsuc k)))
                     (P'.pts' (fsuc kk)) -ᵣ
                      clampᵣ (P.pts' (finj k)) ((P.pts' (fsuc k)))
                       (P'.pts' (finj kk)))
                            )
                   ((λ k₁ → k₁ ,
                       (samplesΣ sa' k₁ ,
                          clampᵣ (P.pts' (finj k))
                           (P.pts' (fsuc k)) (P'.pts' (fsuc k₁))
                             -ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k))
                             (P'.pts' (finj k₁)))))
                   (idfun _)
                   (isTrans≡≤ᵣ _ _ _
                      (cong absᵣ (cong (_-ᵣ 0) (𝐑'.0RightAnnihilates _)))
                      llll)
                 (ruc' k))
               ((foldFin·DistL' (2 ℕ.+ len pa') _ _ (idfun _) ∙
                cong (fst η ·ᵣ_) (deltas-sum (2 ℕ.+ P'.len )
                 (clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) ∘ (P'.pts'))
                  ∙ cong₂ _-ᵣ_
                    (≤x→clampᵣ≡ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' flast)
                      (P.pts'≤pts' k) (P.pts'≤b (fsuc k)) )
                    (x≤→clampᵣ≡ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' fzero)
                     (P.pts'≤pts' k) (P.a≤pts' (finj k))))
                ) ∙ 𝐑'.·DistR- _ _ _) )

∃enclosingℚInterval : ∀ a b →
                      ∃[ (A , B) ∈ (ℚ × ℚ) ]
                        (rat A ≤ᵣ a) × (b ≤ᵣ rat B)
∃enclosingℚInterval a b =
  PT.map2 (λ (A , _ , A<a) (B , b<B , _)
       → (A , B) , <ᵣWeaken≤ᵣ _ _ A<a , <ᵣWeaken≤ᵣ _ _ b<B)
   (denseℚinℝ (a -ᵣ 1) a (isTrans<≡ᵣ _ _ _ (<ᵣ-o+ _ _ a (-ᵣ<ᵣ _ _ (decℚ<ᵣ? {0} {1})))
       (𝐑'.+IdR' _ _ (-ᵣ-rat 0)) ))
   (denseℚinℝ b (b +ᵣ 1)
    (isTrans≡<ᵣ _ _ _ (sym (+IdR b)) (<ᵣ-o+ _ _ b (decℚ<ᵣ? {0} {1}))))


record RefinableTaggedPartition[_,_] (a b : ℝ) : Type where
 field
  tpSeq : ℕ → TaggedPartition[ a , b ]
  tpRef : ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ n → N ℕ.< n →
   mesh≤ᵣ (fst (tpSeq n)) (rat (fst ε)))

 tpTP : ∀ (ε : ℚ₊) →
   Σ[ tp ∈ TaggedPartition[ a , b ] ]
    (mesh≤ᵣ (fst tp) (rat (fst ε)))
 tpTP ε = tpSeq (suc (fst (tpRef ε))) , (snd (tpRef ε) _ ℕ.≤-refl)


clamp-TaggedPartition : ∀ A B → A ≤ᵣ B → ∀ a b → a ≤ᵣ b →
   TaggedPartition[ A , B ] →
   TaggedPartition[ a , b ]
clamp-TaggedPartition A B A≤B a b a≤b tp = w

 where
 w : TaggedPartition[ a , b ]
 w .fst .len = fst (tp) .len
 w .fst .pts = clampᵣ a b ∘ (fst (tp) .pts)
 w .fst .a≤pts k = ≤clampᵣ a b _ a≤b
 w .fst .pts≤b k = clamp≤ᵣ a b _
 w .fst .pts≤pts k = clamp-monotone-≤ᵣ a b _ _
   (tp  .fst .pts≤pts k)
 w .snd .samples = clampᵣ a b ∘ (tp .snd .samples)
 w .snd .pts'≤samples j@(zero , l , _) =
   ≤clampᵣ a b  _ a≤b
 w .snd .pts'≤samples j@(suc k , zero , _) =
  clamp-monotone-≤ᵣ a b _ _
   (tp .snd .pts'≤samples j)
 w .snd .pts'≤samples j@(suc k , suc l , _) =
  clamp-monotone-≤ᵣ a b _ _
   (tp .snd .pts'≤samples j)
 w .snd .samples≤pts' j@(zero , zero , p) =
  ⊥.rec (ℕ.znots (cong predℕ p))
 w .snd .samples≤pts' j@(zero , suc l , _) =
  clamp-monotone-≤ᵣ a b _ _
   (tp .snd .samples≤pts' j)
 w .snd .samples≤pts' j@(suc k , zero , _) =
  clamp≤ᵣ a b  _
 w .snd .samples≤pts' j@(suc k , suc l , _) =
  clamp-monotone-≤ᵣ a b _ _
   (tp .snd .samples≤pts' j)

clamp-TaggedPartition-mesh : ∀ A B A≤B a b a≤b
  → a ∈ intervalℙ A B
  → b ∈ intervalℙ A B
  → ∀ tp δ
  → mesh≤ᵣ (fst tp) δ
  → mesh≤ᵣ (fst (clamp-TaggedPartition A B A≤B a b a≤b tp)) δ

clamp-TaggedPartition-mesh A B A≤B a b a≤b (≤a , a≤) (≤b , b≤) tp δ mesh-tp k =
   isTrans≤ᵣ _ _ _
    (isTrans≡≤ᵣ _ _ _
     (cong₂ _-ᵣ_  (w-pts (fsuc k)) (w-pts (finj k)))
     ((subst2 _≤ᵣ_
        (absᵣNonNeg _ ((x≤y→0≤y-x _ _
          (clamp-monotone-≤ᵣ (pts' (fst tp) (finj k)) (pts' (fst tp) (fsuc k))
            a b a≤b)))
         ∙ sym (clamp-interval-Δ-swap
              a b
              (pts' (fst (tp)) (finj k))
              (pts' (fst (tp)) (fsuc k))

               a≤b ((pts'≤pts' (fst (tp)) k))))
        (absᵣNonNeg _ (x≤y→0≤y-x _ _ (pts'≤pts' (fst (tp)) k)))
        (clampᵣ-dist _ _ _ _))))
    (mesh-tp k)
 where


 w-pts : ∀ k → pts' (fst (clamp-TaggedPartition A B A≤B a b a≤b tp)) k ≡
  clampᵣ a b (pts' (fst tp) k)
 w-pts j@(suc k , zero , _) = sym (≤x→clampᵣ≡ a b B a≤b b≤)
 w-pts j@(zero , _ , _) = sym (x≤→clampᵣ≡ a b A a≤b ≤a)
 w-pts j@(suc k , suc l , _) = refl

clamp-RefinableTaggedPartition : ∀ A B → ∀ a b → a ≤ᵣ b
   → a ∈ intervalℙ A B
   → b ∈ intervalℙ A B →
   RefinableTaggedPartition[ A , B ] →
   RefinableTaggedPartition[ a , b ]
clamp-RefinableTaggedPartition A B a b a≤b (≤a , a≤) (≤b , b≤) rfp = ww
 where
 open RefinableTaggedPartition[_,_]



 w : ℕ → TaggedPartition[ a , b ]
 w = clamp-TaggedPartition A B
   (isTrans≤ᵣ _ _ _ (isTrans≤ᵣ _ _ _ ≤a a≤b) b≤)
    a b a≤b ∘ rfp .tpSeq

 w-pts : ∀ n k → pts' (fst (w n)) k ≡
  clampᵣ a b (pts' (fst (rfp .tpSeq n)) k)
 w-pts n j@(suc k , zero , _) = sym (≤x→clampᵣ≡ a b B a≤b b≤)
 w-pts n j@(zero , _ , _) = sym (x≤→clampᵣ≡ a b A a≤b ≤a)
 w-pts n j@(suc k , suc l , _) = refl

 ww : RefinableTaggedPartition[ a , b ]
 ww .tpSeq = w
 ww .tpRef = map-snd (λ X n n< k →
   isTrans≤ᵣ _ _ _
     ((subst2 _≤ᵣ_
        (cong absᵣ
           (sym (cong₂ _-ᵣ_ (w-pts n (fsuc k)) (w-pts n (finj k))
             ∙ (clamp-interval-Δ-swap
              a b
              (pts' (fst (rfp .tpSeq n)) (finj k))
              (pts' (fst (rfp .tpSeq n)) (fsuc k))

               a≤b ((pts'≤pts' (fst (rfp .tpSeq n)) k))))) ∙
          absᵣNonNeg _ (x≤y→0≤y-x _ _ (pts'≤pts' (fst (w n)) k)))
        (absᵣNonNeg _ (x≤y→0≤y-x _ _ (pts'≤pts' (fst (rfp .tpSeq n)) k)))
        (clampᵣ-dist _ _ _ _))
      ) (X n n< k) ) ∘ (tpRef rfp)




module PreIntegration a b (a≤b : a ≤ᵣ b) (A B : ℚ)
  (A≤a : rat A ≤ᵣ a)
  (b≤B : b ≤ᵣ rat B) (rtp : RefinableTaggedPartition[ a , b ])
  f (ucf : IsUContinuous f) where

 open RefinableTaggedPartition[_,_] rtp

 ∫-seq : Seq
 ∫-seq = (flip Sample.riemannSum' f ∘ snd) ∘S tpSeq

 module HLP (ε : ℚ₊) where
  σ' : ℚ₊
  σ' = ℚ.max 1 (B ℚ.- A) ,
      ℚ.<→0< (ℚ.max 1 (B ℚ.- A))
       (ℚ.isTrans<≤ 0 1 (ℚ.max 1 (B ℚ.- A))
        (ℚ.decℚ<? {0} {1}) ((ℚ.≤max 1 (B ℚ.- A))))


  η' : ℚ₊
  η' = (/2₊ ε) ℚ₊· invℚ₊ σ'

  σ : ℝ₊
  σ = maxᵣ 1 (b -ᵣ a) ,
      isTrans<≤ᵣ _ _ _ (decℚ<ᵣ? {0} {1}) (≤maxᵣ 1 (b -ᵣ a))

  η : ℝ₊
  η = ℚ₊→ℝ₊ (/2₊ ε) ₊·ᵣ invℝ₊ σ


  opaque
   unfolding maxᵣ
   η'≤η : rat (fst η') ≤ᵣ fst η
   η'≤η = isTrans≡≤ᵣ _ _ _ (rat·ᵣrat _ _)
              (≤ᵣ-o·ᵣ _ _ _
               (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ (/2₊ ε))))
               (isTrans≡≤ᵣ _ _ _
                (sym (invℝ₊-rat σ'))
                (invEq (invℝ₊-≤-invℝ₊ _ _)
                  ((max-monotone-≤ᵣ 1 (b -ᵣ a) (rat (B ℚ.- A))
                    (isTrans≤≡ᵣ _ _ _
                     (a+d≤c+b⇒a-b≤c-d b a (rat B) (rat A)
                     (≤ᵣMonotone+ᵣ _ _ _ _
                      b≤B A≤a)) (-ᵣ-rat₂ _ _))))  )))


 IsCauchySequence'-∫-seq : IsCauchySequence' ∫-seq
 IsCauchySequence'-∫-seq ε =
  let (δ , Y) = ucf η'
      (N , X) = tpRef (/4₊ δ)
  in N , λ m n N<n N<m →
    let qqzq = Resample.resampleΔ-UC a b a≤b f ucf (/2₊ ε) δ
          (λ u v x →
           isTrans<≤ᵣ
            _ _ _ (fst (∼≃abs<ε _ _ _) (Y u v x))
            η'≤η)
           (tpSeq n) (tpSeq m) (X n N<n) (X m N<m)
     in isTrans≤<ᵣ _ _ _
          qqzq (<ℚ→<ᵣ _ _ (x/2<x ε))
  where
  open HLP ε

 IntegralOfUContinuous : ℝ
 IntegralOfUContinuous =
   fromCauchySequence' ∫-seq IsCauchySequence'-∫-seq

 isIntegralOfUContinuous : on[ a , b ]IntegralOf f is' IntegralOfUContinuous
 isIntegralOfUContinuous ε =
  let (δ , Y) = ucf η'
      (N , X) = tpRef (/4₊ δ)
      zuio = fst (∼≃abs<ε _ _ _) (𝕣-lim-self _ (fromCauchySequence'-isCA
               ∫-seq IsCauchySequence'-∫-seq)
                (/2₊ (/2₊ ε)) ((/2₊ (/2₊ ε))))
      zzLem : riemannSum' (snd (tpSeq (suc N))) f
         ≡ ∫-seq (suc (fst (IsCauchySequence'-∫-seq (/2₊ (/2₊ ε)))))
      zzLem = refl
  in ∣ /4₊ δ ,
     (λ (pa , tp) pa≤δ →
       let qqzq = Resample.resampleΔ-UC a b a≤b f ucf (/2₊ (/2₊ (/2₊ ε))) δ
              (λ u v x →
                isTrans<≤ᵣ
                 _ _ _ (fst (∼≃abs<ε _ _ _) (Y u v x))
                 η'≤η)
                (pa , tp) (tpSeq (suc N))
                pa≤δ (X _ ℕ.≤-refl)
           zuii = isTrans≤<ᵣ _ _ _ (absᵣ-triangle _ _)
               (≤<ᵣMonotone+ᵣ _ _ _ _
                 qqzq zuio)
        in (isTrans<≤ᵣ _ _ _ (subst2 _<ᵣ_
            (cong absᵣ L𝐑.lem--060)
              (+ᵣ-rat _ _ ∙
                cong rat (cong (fst (/2₊ (/2₊ (/2₊ ε))) ℚ.+_)
               (ℚ.ε/2+ε/2≡ε (fst (/2₊ ε)))))

            zuii )) (isTrans≤≡ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _
                ((ℚ.<-+o (fst (/2₊ (/2₊ (/2₊ ε))))
                   ((fst (/2₊ ε))) ((fst (/2₊ ε)))
                  (ℚ.isTrans<
                    (fst (/2₊ (/2₊ (/2₊ ε))))
                    (fst (/2₊ (/2₊ ε)))
                    (fst (/2₊ ε))
                    (x/2<x (/2₊ (/2₊ ε))) (x/2<x (/2₊ ε)))))))
                  (cong rat (ℚ.ε/2+ε/2≡ε (fst ε))))) ∣₁
  where
  open HLP (/2₊ (/2₊ ε))


rtp-1/n : ∀ (A B : ℚ) → A ℚ.≤ B → RefinableTaggedPartition[ rat A , rat B ]
rtp-1/n A B A≤B .RefinableTaggedPartition[_,_].tpSeq n =
  Integration.equalPartition (rat A) (rat B) (≤ℚ→≤ᵣ _ _ A≤B) n
   , leftSample _
rtp-1/n A B A≤B .RefinableTaggedPartition[_,_].tpRef ε =
  let Δ₊ = ℚ.max (B ℚ.- A) 1 , ℚ.<→0< (ℚ.max (B ℚ.- A) 1)
              (ℚ.isTrans<≤ 0 1 (ℚ.max (B ℚ.- A) 1)
              (ℚ.decℚ<? {0} {1})
              ((ℚ.≤max' (B ℚ.- A) 1)))
      (1+ N , p)  = ℚ.ceilℚ₊ (Δ₊ ℚ₊· invℚ₊ ε)
      in N , λ n N<n k →
       let z = subst (ℚ.max (B ℚ.- A) [ pos 1 / 1+ 0 ] ℚ.≤_)
             (ℚ.·Comm (fst ε) [ pos (suc (suc n)) / 1+ 0 ])
              ((ℚ.x·invℚ₊y≤z→x≤y·z (ℚ.max (B ℚ.- A) [ pos 1 / 1+ 0 ])
                   _ ε
                (ℚ.<Weaken≤ (fst (Δ₊ ℚ₊· invℚ₊ ε)) (fromNat (suc (suc n)))
                (ℚ.isTrans< (fst (Δ₊ ℚ₊· invℚ₊ ε)) _ (fromNat (suc (suc n))) p
                 (ℚ.<ℤ→<ℚ
                   (ℤ.pos (suc N)) (ℤ.pos (suc (suc n)))
                     (invEq (ℤ.pos-<-pos≃ℕ< (suc N) (suc (suc n)))
                        (ℕ.suc-≤-suc (ℕ.≤-suc N<n))))))))
       in isTrans≡≤ᵣ _ _ _
          (Integration.equalPartitionΔ (rat A) (rat B) (≤ℚ→≤ᵣ A B A≤B) n k ∙
            cong (_·ᵣ rat [ pos 1 / 2+ n ]) (-ᵣ-rat₂ _ _) ∙
             sym (rat·ᵣrat _ _))
              (≤ℚ→≤ᵣ _ _
                (ℚ.isTrans≤ ((B ℚ.- A) ℚ.· [ pos 1 / 2+ n ])
                   _ (fst ε)
                  ((ℚ.≤-·o (B ℚ.- A) (ℚ.max (B ℚ.- A) 1) ([ pos 1 / 2+ n ])
                  (ℚ.0≤pos 1 (2+ n))
                  (ℚ.≤max (B ℚ.- A) 1)))
                  ( ℚ.x≤y·z→x·invℚ₊y≤z (ℚ.max (B ℚ.- A) 1)
                   (fst ε) (fromNat (suc (suc n))) z)))

∃RefinableTaggedPartition : (∀ (A B : ℚ) → A ℚ.≤ B → RefinableTaggedPartition[ rat A , rat B ])
  → ∀ a b → a ≤ᵣ b → ∥ RefinableTaggedPartition[ a , b ] ∥₁
∃RefinableTaggedPartition rtpℚ a b a≤b =
  PT.map (λ ((A , B) , A≤a , b≤B) →
    (clamp-RefinableTaggedPartition
            _ _ a b a≤b
             (A≤a , (isTrans≤ᵣ _ _ _ a≤b b≤B))
             (isTrans≤ᵣ _ _ _ A≤a a≤b , b≤B)
            (rtpℚ A B
              (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _
                (isTrans≤ᵣ _ _ _ A≤a a≤b)
                  b≤B)))))
   (∃enclosingℚInterval a b)
