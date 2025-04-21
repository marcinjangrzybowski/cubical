{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.BisectApprox2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
import Cubical.Functions.Logic as L
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Bisect
open import Cubical.HITs.CauchyReals.Exponentiation



≤Weaken<+ᵣ : ∀ x y (z : ℝ₊) →
       x ≤ᵣ y → x <ᵣ y +ᵣ fst z 
≤Weaken<+ᵣ x y z x≤y =
  isTrans≡<ᵣ _ _ _ (sym (+IdR _))
   (≤<ᵣMonotone+ᵣ x y 0 (fst z) x≤y (snd z))

Dichotomyℝ : ∀ (ε : ℚ₊) x y →
    ⟨ ((x  <ᵣ y +ᵣ rat (fst ε)) , squash₁)
       L.⊔ ((y <ᵣ x +ᵣ rat (fst ε)) , squash₁) ⟩
Dichotomyℝ ε x x' =
     (PT.map2 
         (λ (r , x<r , r<x+ε/2) (r' , x'-ε/2<r' , r'<x') →
           ⊎.map

              (λ r≤r' → isTrans<ᵣ _ _ _
                 x<r (isTrans≤<ᵣ _ _ _
                   (≤ℚ→≤ᵣ r r' r≤r') r'<x'))
              (λ r'<r → 
                 isTrans<ᵣ _ _ _
                  (isTrans<ᵣ _ _ _ x'-ε/2<r' (<ℚ→<ᵣ r' r r'<r))
                  r<x+ε/2 )
             (ℚ.Dichotomyℚ r r'))
        (denseℚinℝ x (x +ᵣ rat (fst (ε)))
          (≤Weaken<+ᵣ _ _ (ℚ₊→ℝ₊ (ε)) (≤ᵣ-refl _)))
        (denseℚinℝ x' (x' +ᵣ rat (fst (ε)))
         ((≤Weaken<+ᵣ _ _ (ℚ₊→ℝ₊ (ε)) (≤ᵣ-refl _)))))


-- isIncrasing→injectiveℝ : ∀ f → IsContinuous f  →
--      isIncrasing f →
--       ∀ x x' → f x ≡ f x' → x ≡ x' 
      
-- isIncrasing→injectiveℝ f fC incrF x x' p = {!!}
 -- eqℝ _ _ λ ε → invEq (∼≃abs<ε _ _ _)
 --     (PT.rec2 squash₁
 --         (λ (r , x<r , r<x+ε/2) (r' , x'<r' , r'<x'+ε/2) →
 --           ⊎.rec

 --              (λ r≤r' → {!!}
 --                 -- let fx<fx' = incrF x x' $ isTrans<ᵣ _ _ _
 --                 --         x<r
 --                 --         (isTrans≤<ᵣ _ _ _
 --                 --           (≤ℚ→≤ᵣ r r' r≤r')
 --                 --           r'<x')
 --                 -- in ⊥.rec (isIrrefl<ᵣ (f x) (subst (f x <ᵣ_) (sym p)
 --                 --          fx<fx'))
 --                          )
 --              (λ r'<r → {!!}
 --                -- let z = isTrans<ᵣ _ _ _
 --                --       x'-ε/2<r'
 --                --         (isTrans<ᵣ _ _ _
 --                --            (<ℚ→<ᵣ r' r r'<r)
 --                --             r<x+ε/2)
 --                --     z' = {!!}
 --                -- in {!!}
 --                )
 --             (ℚ.Dichotomyℚ r r'))
 --        (denseℚinℝ x (x +ᵣ rat (fst (/2₊ ε))) {!!})
 --        (denseℚinℝ x' (x' +ᵣ rat (fst (/2₊ ε))) {!!}))


isIncrasingℙᵣ : (P : ℙ ℝ) → (∀ (x : ℝ) → x ∈ P → ℝ) → Type
isIncrasingℙᵣ P f =
 ∀ (x : ℝ) (x∈ : x ∈ P) (y : ℝ) (y∈ : y ∈ P) → x <ᵣ y → f x x∈ <ᵣ f y y∈

isNondecrasingℙᵣ : (P : ℙ ℝ) → (∀ (x : ℝ) → x ∈ P → ℝ) → Type
isNondecrasingℙᵣ P f =
 ∀ (x : ℝ) (x∈ : x ∈ P) (y : ℝ) (y∈ : y ∈ P) → x ≤ᵣ y → f x x∈ ≤ᵣ f y y∈



opaque
 _<ᵣ'_ : ℝ → ℝ → Type
 _<ᵣ'_ = _<ᵣ_

 <ᵣ'≃<ᵣ : ∀ x y → (x <ᵣ' y) ≃ (x <ᵣ y) 
 <ᵣ'≃<ᵣ _ _ = idEquiv _

 _≤ᵣ'_ : ℝ → ℝ → Type
 _≤ᵣ'_ = _≤ᵣ_

 ≤ᵣ'≃≤ᵣ : ∀ x y → (x ≤ᵣ' y) ≃ (x ≤ᵣ y) 
 ≤ᵣ'≃≤ᵣ _ _ = idEquiv _

 isProp≤ᵣ' : ∀ x y → isProp (x ≤ᵣ' y)
 isProp≤ᵣ' = isProp≤ᵣ
 
 intervalℙ' : ℝ → ℝ → ℙ ℝ 
 intervalℙ' a b x = ((a ≤ᵣ' x) × (x ≤ᵣ' b)) ,
   isProp× (isSetℝ _ _)  (isSetℝ _ _)


 intervalℙ'⊆intervalℙ : ∀ a b → intervalℙ' a b ⊆ intervalℙ a b
 intervalℙ'⊆intervalℙ a b _ (<x , x<) =
   fst (≤ᵣ'≃≤ᵣ _ _) <x  , fst (≤ᵣ'≃≤ᵣ _ _) x<


 intervalℙ⊆intervalℙ' : ∀ a b → intervalℙ a b ⊆ intervalℙ' a b
 intervalℙ⊆intervalℙ' a b _ (<x , x<) =
   invEq (≤ᵣ'≃≤ᵣ _ _) <x  , invEq (≤ᵣ'≃≤ᵣ _ _) x<



<^n' : ∀ N n (q : ℚ₊) → fst q ℚ.< 1 → N ℕ.< n →
        (fst q ℚ^ⁿ n) ℚ.< (fst q ℚ^ⁿ N)
<^n' N n q q<1 N<n =
  let z' = (^ℚ-StrictMonotoneR
           {ℚ₊→ℝ₊ (invℚ₊ q)}
             (<ℚ→<ᵣ _ _
               (fst (ℚ.invℚ₊-<-invℚ₊ q 1) q<1))
             (fromNat N) (fromNat n)
               (ℚ.<ℤ→<ℚ _ _ (ℤ.ℕ≤→pos-≤-pos  _ _ N<n)))
      z = <ᵣ→<ℚ _ _ $ subst2 _<ᵣ_
          (^ⁿ-ℚ^ⁿ _ _ ∙ cong rat (sym (ℚ.invℚ₊-ℚ^ⁿ _ _)))
          (^ⁿ-ℚ^ⁿ _ _ ∙ cong rat (sym (ℚ.invℚ₊-ℚ^ⁿ _ _)))
           z'
  in invEq (ℚ.invℚ₊-<-invℚ₊ _ _) z 


isIncrasingℙ→isNondecrasingℙᵣ : ∀ P f
               → isIncrasingℙᵣ P f
               → isNondecrasingℙᵣ P f 
isIncrasingℙ→isNondecrasingℙᵣ P f incF x x∈ y y∈ =
  {!!}


-- apartFrom-Lipschitz-ℝ→ℝℙ : ∀ L P f →
--     Lipschitz-ℝ→ℝℙ L P f →
--      (∀ u u∈ v v∈ → (ε : ℚ₊) →
--          rat (fst (L ℚ₊· ε)) ≤ᵣ absᵣ (f u u∈ -ᵣ f v v∈)   →
--            rat (fst ε) ≤ᵣ absᵣ (u -ᵣ v))
-- apartFrom-Lipschitz-ℝ→ℝℙ = {!!}



-- apartFrom-Invlipschitz-ℝ→ℝℙ** : ∀ K P f →
--     Invlipschitz-ℝ→ℝℙ K P f →
--     isIncrasingℙᵣ P f → 
--      (∀ u u∈ v v∈ → v <ᵣ u → (ε : ℚ₊) →
--          rat (fst (K ℚ₊· ε)) +ᵣ v ≤ᵣ u   →
--            rat (fst ε) +ᵣ f v v∈ ≤ᵣ f u u∈ )
-- apartFrom-Invlipschitz-ℝ→ℝℙ** K P f X incr u u∈ v v∈ v<u ρ Y =
--     x<y+δ→x≤y _ _ λ ε →
--      let Δ = f u u∈ -ᵣ f v v∈ 
--          ε* = {!!}
--          Y' = {!Y!}
--      in PT.rec {!!}
--          (λ (r , Δ<r , _) →
--            let zz = X u u∈ v v∈ (r , {!!})
--                      (invEq (∼≃abs<ε _ _ _)
--                         (isTrans≡<ᵣ _ _ _ (absᵣPos _
--                           (x<y→0<y-x _ _
--                             (incr _ _ _ _ v<u))) Δ<r))
--            in {!fst (∼≃abs<ε _ _ _) zz!})
--          (denseℚinℝ Δ (Δ +ᵣ rat (fst (ε*)))
--           (≤Weaken<+ᵣ _ _ (ℚ₊→ℝ₊ (ε*)) (≤ᵣ-refl _)))
--      -- let ε* = {!!}
--      --     zz = X u u∈ v v∈ {!!}
--      --           (invEq (∼≃abs<ε _ _ _)
--      --             {!!})
--      --           -- x<y+δ→x≤y _ _ λ ε →
--      -- in {!zz!}  


apartFrom-Invlipschitz-ℝ→ℝℙ : ∀ K P f →
    Invlipschitz-ℝ→ℝℙ K P f →
     (∀ u u∈ v v∈ → (ε : ℚ₊) →
         rat (fst (K ℚ₊· ε)) ≤ᵣ absᵣ (u -ᵣ v)   →
           rat (fst ε) ≤ᵣ absᵣ (f u u∈ -ᵣ f v v∈))
apartFrom-Invlipschitz-ℝ→ℝℙ K P f X u u∈ v v∈ ρ Y =
 let Δ = absᵣ (f u u∈ -ᵣ f v v∈)
 in x<y+δ→x≤y _ _ λ ε → 
      PT.rec squash₁ -- u ∼[ K ℚ₊· (q , ?3) ] v
        (λ (q , Δ<q , q<Δ+ε) →
          let 0<q = ℚ.<→0< _ (<ᵣ→<ℚ 0 q
                     (isTrans≤<ᵣ _ _ _
                       (0≤absᵣ _) Δ<q))
              zzz : (fst (K ℚ₊· ρ)) ℚ.< (fst (K ℚ₊· (q , 0<q)))
              zzz = <ᵣ→<ℚ _ _ $ isTrans≤<ᵣ _ _ _
                       Y
                       (fst (∼≃abs<ε _ _ _)
                      $ X u u∈ v v∈ (q , 0<q)
                       (invEq (∼≃abs<ε _ _ _)
                         Δ<q))
              zzz' = ℚ.<-·o-cancel _ _ _ 
                         (ℚ.0<ℚ₊ K)
                      (subst2 ℚ._<_ (ℚ.·Comm _ _) (ℚ.·Comm _ _)
                          zzz)
              zz : rat (fst ρ) <ᵣ Δ +ᵣ rat (fst ε)
              zz = isTrans<ᵣ _ _ _
                      (<ℚ→<ᵣ _ _ zzz')
                       q<Δ+ε
          in zz
          )
        ((denseℚinℝ Δ (Δ +ᵣ rat (fst (ε)))
             (≤Weaken<+ᵣ _ _ (ℚ₊→ℝ₊ (ε)) (≤ᵣ-refl _))))

a≤b-c⇒a+c≤b : ∀ a b c → a ≤ᵣ b -ᵣ c → a +ᵣ c ≤ᵣ b
a≤b-c⇒a+c≤b a b c p =
   subst ((a +ᵣ c) ≤ᵣ_)
        (L𝐑.lem--00 {b} {c})
     (≤ᵣ-+o _ _ c p)

a-b≤c⇒a≤c+b : ∀ a b c → a -ᵣ b ≤ᵣ c  → a ≤ᵣ c +ᵣ b
a-b≤c⇒a≤c+b a b c p =
  subst (_≤ᵣ (c +ᵣ b))
    (L𝐑.lem--00 {a} {b})
     (≤ᵣ-+o _ _ b p)

open ℕ.Minimal


logₘℕ : ∀ n m → Σ _ (Least (λ k → n ℕ.< m ^ k))
logₘℕ n = {!!}

-- w n n ℕ.≤-refl
--  where

--   w : ∀ N n → n ℕ.≤ N
--           → Σ _ (Least (λ k → n ℕ.< 2 ^ k))
--   w N zero x = 0 , (ℕ.≤-refl , λ k' q → ⊥.rec (ℕ.¬-<-zero q))
--   w N (suc zero) x = 1 , (ℕ.≤-refl ,
--      λ { zero q → ℕ.<-asym (ℕ.suc-≤-suc ℕ.≤-refl)
--       ; (suc k') q → ⊥.rec (ℕ.¬-<-zero (ℕ.pred-≤-pred q))})
--   w zero (suc (suc n)) x = ⊥.rec (ℕ.¬-<-zero x)
--   w (suc N) (suc (suc n)) x =
--    let (k , (X , Lst)) = w N
--           (ℕ.quotient 2 ℕ.+ n / 2)
--           (ℕ.≤-trans (ℕ.pred-≤-pred (ℕ.2≤x→quotient[x/2]<x n))
--              (ℕ.pred-≤-pred x))
--        z = ℕ.≡remainder+quotient 2 (2 ℕ.+ n)
--        zz = ℕ.<-+-≤ X X
--        zzz : suc (suc n) ℕ.< (2 ^ suc k)
--        zzz = subst2 (ℕ._<_)
--            (ℕ.+-comm _ _
--               ∙ sym (ℕ.+-assoc ((ℕ.remainder 2 ℕ.+ n / 2)) _ _)
--                ∙ cong ((ℕ.remainder 2 ℕ.+ n / 2) ℕ.+_)
--              ((cong ((ℕ.quotient 2 ℕ.+ n / 2) ℕ.+_)
--               (sym (ℕ.+-zero (ℕ.quotient 2 ℕ.+ n / 2)))))
--              ∙ z)
--            (cong ((2 ^ k) ℕ.+_) (sym (ℕ.+-zero (2 ^ k))))
--            (ℕ.≤<-trans
--              (ℕ.≤-k+ (ℕ.≤-+k (ℕ.pred-≤-pred (ℕ.mod< 1 (2 ℕ.+ n))))) zz)
--    in (suc k)
--        , zzz
--         , λ { zero 0'<sk 2+n<2^0' →
--                 ⊥.rec (ℕ.¬-<-zero (ℕ.pred-≤-pred 2+n<2^0'))
--             ; (suc k') k'<sk 2+n<2^k' →
--                Lst k' (ℕ.pred-≤-pred k'<sk)
--                 (<-·sk-cancel {k = 1}
--                     (subst2 ℕ._<_ (ℕ.·-comm _ _) (ℕ.·-comm _ _)
--                       (ℕ.≤<-trans (_ , z)
--                          2+n<2^k' )))}


ℕε<kⁿ : ∀ p q r s → 0 ℕ.< q →  s ℕ.< r → Σ[ n ∈ ℕ ]
           p ℕ.· s ℕ.^ n ℕ.< q ℕ.· r ℕ.^ n
ℕε<kⁿ = {!!}

ε<kⁿ : (ε q : ℚ₊) → 1 ℚ.< fst q  → Σ[ n ∈ ℕ ] fst ε ℚ.< (fst q) ℚ^ⁿ n
ε<kⁿ ε q q<1 = {!!}
   -- let n = fst (logₘℕ (fst (ℚ.ceilℚ₊ ε))) in n ,
   --       subst (fst ε ℚ.<_) (sym (ℚ.fromNat-^ _ _))
   --        (ℚ.isTrans< _ _ (fromNat (2 ^ n))
   --                ((snd (ℚ.ceilℚ₊ ε)))
   --                 (ℚ.<ℤ→<ℚ (ℤ.pos ((fst (ℚ.ceilℚ₊ ε))))
   --                   _ (ℤ.ℕ≤→pos-≤-pos  _ _
   --                  (fst (snd (log2ℕ (fst (ℚ.ceilℚ₊ ε))))))))


1/mⁿ<ε : ∀ m (ε : ℚ₊) → Σ[ n ∈ ℕ ] [ pos (suc m) / 2+ m ] ℚ^ⁿ n ℚ.< fst ε
1/mⁿ<ε m ε = 
 let (n , 1/ε<n) = ε<kⁿ (invℚ₊ ε) ([ pos (suc (suc m)) / 1+ m ] , _)
                     {!!}

 in n , invEq (ℚ.invℚ₊-<-invℚ₊ (([ pos (suc m) / 2+ m ] , _) ℚ₊^ⁿ n) ε)
         (subst (fst (invℚ₊ ε) ℚ.<_)
           (sym (ℚ.invℚ₊-ℚ^ⁿ ([ pos (suc m) / 2+ m ] , _) n)) 1/ε<n)


module IsBilipschitz' (a b : ℚ)  (a<b : a ℚ.< b)
         (f : ∀ (x : ℝ) → x ∈ (intervalℙ (rat a) (rat b)) → ℝ) 
          (incrF : isIncrasingℙᵣ (intervalℙ (rat a) (rat b)) f)
          (y : ℚ)

          where

 nondF = isIncrasingℙ→isNondecrasingℙᵣ (intervalℙ (rat a) (rat b)) f incrF

 a∈ : rat a ∈ (intervalℙ (rat a) (rat b))
 
 a∈ = (≤ᵣ-refl (rat a) , <ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ a<b))
 b∈ : rat b ∈ (intervalℙ (rat a) (rat b)) 
 b∈ = (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ a<b) , ≤ᵣ-refl (rat b))
 
 fa = f (rat a) a∈
 fb = f (rat b) b∈

 f∈ : ∀ x x∈ → f x x∈ ∈ (intervalℙ fa fb)
 f∈ x x∈ = 
   nondF (rat a) _ x x∈ (fst x∈) ,
    nondF x x∈  (rat b) _ (snd x∈)

 f' : ∀ x x∈ → Σ ℝ (_∈ intervalℙ fa fb) 
 f' x x∈ = _ , f∈ x x∈


 fa<fb : fa <ᵣ fb
 fa<fb = incrF
   (rat a) a∈
   (rat b) b∈
   (<ℚ→<ᵣ _ _ a<b)

 a≤b = ℚ.<Weaken≤ _ _ a<b

 Δ₀ = b ℚ.- a
 Δ₀₊ = ℚ.<→ℚ₊ _ _ a<b 



 module _
    (approxF : ℚApproxℙ' (intervalℙ (rat a) (rat b)) (intervalℙ fa fb) f')
    (L K : ℚ₊)
    (1/K≤L : fst (invℚ₊ K) ℚ.≤ fst L)
    (lipF : Lipschitz-ℝ→ℝℙ L (intervalℙ (rat a) (rat b)) f)
    (lip⁻¹F : Invlipschitz-ℝ→ℝℙ K (intervalℙ (rat a) (rat b)) f)

   where

  module _ (y : ℚ) (y∈ : rat y ∈ (intervalℙ fa fb))  where

   record Step (Δ : ℚ) : Type where
    field
     a' b' : ℚ
     a'<b' : a' ℚ.< b'
     b'-a'≤Δ : b' ℚ.- a' ℚ.≤ Δ 
     a'∈ : a' ∈ ℚintervalℙ a b
     b'∈ : b' ∈ ℚintervalℙ a b
     a'≤ : f (rat a') (∈ℚintervalℙ→∈intervalℙ _ _ _ a'∈) ≤ᵣ' rat y
     ≤b' : rat y ≤ᵣ' f (rat b') (∈ℚintervalℙ→∈intervalℙ _ _ _ b'∈)

    a'≤b' : a' ℚ.≤ b'
    a'≤b' = ℚ.<Weaken≤ _ _ a'<b'
    mid : ℚ
    mid = b' ℚ.· [ 1 / 2 ] ℚ.+ a' ℚ.· [ 1 / 2 ]

    Δ₊ : ℚ₊
    Δ₊ = Δ , ℚ.<→0< _ (ℚ.isTrans<≤ 0 _ _ (ℚ.-< a' b' a'<b') b'-a'≤Δ)



    p = ℚ.<-·o _ _ [ 1 / 2 ] (ℚ.decℚ<? {0} {[ 1 / 2 ]}) a'<b'

    a'<mid : a' ℚ.< mid
    a'<mid = ℚ.isTrans≤< _ _ _
      (ℚ.≡Weaken≤ _ _ (sym (ℚ.·IdR a') ∙ cong (a' ℚ.·_) ℚ.decℚ? ∙
        ℚ.·DistL+ a' _ _))
      (ℚ.<-+o _ _ (a' ℚ.· [ 1 / 2 ]) p) 

    mid<b' : mid ℚ.< b' 
    mid<b' = ℚ.isTrans<≤ _ _ _    
      (ℚ.<-o+ _ _ (b' ℚ.· [ 1 / 2 ]) p) 
      ((ℚ.≡Weaken≤ _ _ ((sym (ℚ.·DistL+ b' _ _) ∙ cong (b' ℚ.·_) ℚ.decℚ? ∙
        ℚ.·IdR b'))))

    mid∈ : mid ∈ ℚintervalℙ a b
    mid∈ = ℚ.isTrans≤ _ _ _ (fst (a'∈)) (ℚ.<Weaken≤ _ _ a'<mid) ,
            ℚ.isTrans≤ _ _ _ (ℚ.<Weaken≤ _ _ mid<b') (snd b'∈)

    mid∈' = (∈ℚintervalℙ→∈intervalℙ _ _ _ mid∈)

    fMidᵣ = f (rat mid) mid∈'



   record Step⊃Step {Δ ΔS : _} (s : Step Δ) (sS : Step ΔS) : Type where

    field
     a'≤a'S : Step.a' s ℚ.≤ Step.a' sS 
     bS≤b' : Step.b' sS ℚ.≤ Step.b' s
     -- distA' : (Step.a' sS) ℚ.≤ Δ ℚ.· [ 1 / 2 ] ℚ.+ (Step.a' s)

   step0 : Step Δ₀
   step0 .Step.a' = a
   step0 .Step.b' = b
   step0 .Step.a'<b' = a<b
   step0 .Step.b'-a'≤Δ = ℚ.isRefl≤ _
   step0 .Step.a'∈ = ℚ.isRefl≤ _  , a≤b
   step0 .Step.b'∈ = a≤b , (ℚ.isRefl≤ _)
   step0 .Step.a'≤ = 
         subst (_≤ᵣ' _)
           (cong (f (rat a)) (snd (intervalℙ _ _ _) _ _)) (invEq (≤ᵣ'≃≤ᵣ _ _) (fst y∈)) 
   step0 .Step.≤b' =
         subst (_ ≤ᵣ'_)
           (cong (f (rat b)) (snd (intervalℙ _ _ _) _ _)) (invEq (≤ᵣ'≃≤ᵣ _ _) (snd y∈)) 

   stepS' : ∀ Δ → (s : Step Δ) → Σ (Step (Δ ℚ.· [ 3 / 4 ])) (Step⊃Step s)
   stepS' Δ s = w (ℚ.Dichotomyℚ y fMid)
    where
    open Step s


    Δ₊* : ℚ₊
    Δ₊* = ℚ.<→ℚ₊ _ _ a'<b'

    Δ* : ℚ
    Δ* = fst Δ₊*


    Δ*≤Δ : Δ* ℚ.≤ Δ  
    Δ*≤Δ = b'-a'≤Δ

    Φ : ℚ₊
    Φ = /2₊ (invℚ₊ K ℚ₊· /4₊ Δ₊*)

    fMid = fst (approxF mid mid∈') Φ

    fMidDist : rat fMid ∼[ (invℚ₊ K ℚ₊· /4₊ Δ₊*) ] f (rat mid) mid∈'
    fMidDist =
      subst∼ (ℚ.ε/2+ε/2≡ε _) (subst (rat fMid ∼[ Φ ℚ₊+ Φ ]_)
                (snd (snd (snd (approxF mid mid∈'))))
                 (𝕣-lim-self _ _ Φ Φ))


    a'-mid≡Δ/2 : (mid ℚ.- a') ≡ Δ* ℚ.· [ 1 / 2 ]
    a'-mid≡Δ/2 = 
       ((sym (ℚ.+Assoc _ _ _) ∙
          cong (b' ℚ.· [ 1 / 2 ] ℚ.+_)
           (cong (a' ℚ.· [ 1 / 2 ] ℚ.+_) (ℚ.·Comm -1 a')
            ∙ sym (ℚ.·DistL+ a' _ _) ∙
             ℚ.·Comm _ _ ∙
              sym (ℚ.·Assoc [ 1 / 2 ] -1 a') ∙  ℚ.·Comm [ 1 / 2 ] _)
           ∙ sym (ℚ.·DistR+ _ _ _)))

    w : (y ℚ.≤ fMid) ⊎ (fMid ℚ.< y) → Σ (Step (Δ ℚ.· [ 3 / 4 ]))
              (Step⊃Step s)
    w (inl x) = ww
     where

     ab-dist = ℚ.isTrans≤
      ((mid ℚ.+ (Δ* ℚ.· [ 1 / 4 ])) ℚ.- a') _ _
       (ℚ.≡Weaken≤ _ _
         (cong (ℚ._- a') (ℚ.+Comm _ _) ∙ sym (ℚ.+Assoc _ _ _)))
        ((ℚ.isTrans≤ _ _ _
          (ℚ.≤-o+ _ _ _ (ℚ.≡Weaken≤ _ _ a'-mid≡Δ/2))
            (ℚ.≡Weaken≤ _ _ (sym (ℚ.·DistL+ Δ* _ _) ∙
              cong (Δ* ℚ.·_) ℚ.decℚ?))))

     newb' = mid ℚ.+ (Δ* ℚ.· [ 1 / 4 ])


     newb'+Δ/4≡b' : newb' ℚ.+ (Δ* ℚ.· [ 1 / 4 ]) ≡ b'  
     newb'+Δ/4≡b' = sym (ℚ.+Assoc _ _ _) ∙
       {!!}

     y≤fnewb' : rat y ≤ᵣ f (rat newb') _  
     y≤fnewb' = 
      (isTrans≤ᵣ _ _ _
        (≤ℚ→≤ᵣ _ _ x) (isTrans≤ᵣ _ _ _
           (a-b≤c⇒a≤c+b _ _ _
             (isTrans≤ᵣ _ _ _ (≤absᵣ _ )
               (<ᵣWeaken≤ᵣ _ _ (fst (∼≃abs<ε _ _ _) fMidDist)))) mid-dist))
        where
         mid-dist : rat (fst (invℚ₊ K ℚ₊· /4₊ Δ₊*))
                      +ᵣ f (rat mid) mid∈' ≤ᵣ
                      f _ _ 
         mid-dist = a≤b-c⇒a+c≤b _ _ _ $ isTrans≤≡ᵣ _ _ _
          (apartFrom-Invlipschitz-ℝ→ℝℙ
           K _ f lip⁻¹F _ _ (rat mid) mid∈'
             (invℚ₊ K ℚ₊· (/4₊ Δ₊*))
                (≤ℚ→≤ᵣ _ _
                  (subst2 ℚ._≤_ (sym (ℚ.y·[x/y] K (fst (/4₊ Δ₊*))))
                    (cong ℚ.abs' (sym lem--063))
                  (ℚ.≤abs' _)))
                  )
              (absᵣPos _ (x<y→0<y-x _ _
                (incrF _ mid∈' _ _
                    (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' mid mid ((Δ₊* ℚ₊· ([ 1 / 4 ] , _))) (ℚ.isRefl≤ mid) )))))

     a'<newb' : a' ℚ.< newb'
     a'<newb' =  ℚ.isTrans≤< _ _ _
         (ℚ.≡Weaken≤ _ _ (sym (ℚ.+IdR _))) (ℚ.<Monotone+ _ _ 0 (Δ* ℚ.· [ 1 / 4 ]) 
              a'<mid (ℚ.0<ℚ₊ (Δ₊* ℚ₊· ([ 1 / 4 ] , _))))

     newb'≤b' : newb' ℚ.≤ b'
     newb'≤b' = 
      subst (newb' ℚ.≤_) newb'+Δ/4≡b'
       (ℚ.≤+ℚ₊ _ _ (Δ₊* ℚ₊· _) (ℚ.isRefl≤ _))



     newb'∈ : newb' ∈ ℚintervalℙ a b
     newb'∈ = ℚ.isTrans≤ _ _ _
              (fst a'∈) (ℚ.<Weaken≤ _ _ a'<newb')
       , ℚ.isTrans≤ _ _ _ newb'≤b' (snd b'∈)


     ww : Σ (Step (Δ ℚ.· [ 3 / 4 ])) (Step⊃Step s)
     ww .fst .Step.a' = a'
     ww .fst .Step.b' = newb'
     ww .fst .Step.a'<b' = a'<newb' 
     ww .fst .Step.b'-a'≤Δ = ℚ.isTrans≤
           _ _ _ ab-dist (ℚ.≤-·o Δ* Δ [ 3 / 4 ]
             (ℚ.<Weaken≤ 0 [ 3 / 4 ] (ℚ.0<pos 2 4)) Δ*≤Δ)
     ww .fst .Step.a'∈ = a'∈
     ww .fst .Step.b'∈ = newb'∈
     ww .fst .Step.a'≤ = a'≤
     ww .fst .Step.≤b' = invEq (≤ᵣ'≃≤ᵣ _ _) y≤fnewb'
     ww .snd .Step⊃Step.a'≤a'S = ℚ.isRefl≤ a'
     ww .snd .Step⊃Step.bS≤b' = newb'≤b'
    w (inr x) = {!!}

   
   stepS : ∀ Δ → Step Δ → Step (Δ ℚ.· [ 3 / 4 ])
   stepS Δ s = fst (stepS' Δ s)

   ww : ∀ n → Step (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n))
   ww zero = subst (Step) (sym (ℚ.·IdR Δ₀)) step0
   ww (suc n) = subst (Step) (sym (ℚ.·Assoc _ _ _)) (stepS _ (ww n))

   s : ℕ → ℚ
   s = Step.a' ∘ ww

   s' : ℕ → ℚ
   s' = Step.b' ∘ ww

   ss≤-suc : ∀ n (z : Step (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n))) → Step.a' z ℚ.≤
       Step.a' (subst (Step) (sym (ℚ.·Assoc _ _ _)) (stepS
        (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n)) z))
   ss≤-suc n z = ℚ.isTrans≤ _ _ _ (Step⊃Step.a'≤a'S (snd (stepS'
        (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n)) z)))
          (ℚ.≡Weaken≤ _ _ (sym (transportRefl _)))

   ≤ss'-suc : ∀ n (z : Step (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n))) →  
        Step.b' (subst (Step) (sym (ℚ.·Assoc _ _ _)) (stepS
        (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n)) z))
       ℚ.≤
        Step.b' z
   ≤ss'-suc n z =  ℚ.isTrans≤ _ _ _ 
          (ℚ.≡Weaken≤ _ _  (transportRefl _))
            ((Step⊃Step.bS≤b' (snd (stepS'
        (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n)) z))))
   ss≤ : ∀ n m → s n ℚ.≤ s (m ℕ.+ n) 
   ss≤ n zero = ℚ.isRefl≤ _ 
   ss≤ n (suc m) = ℚ.isTrans≤ _ _ _ (ss≤ n m) (ss≤-suc (m ℕ.+ n) (ww (m ℕ.+ n)))

   ≤ss' : ∀ n m →  s' (m ℕ.+ n) ℚ.≤ s' n 
   ≤ss' n zero = ℚ.isRefl≤ _ 
   ≤ss' n (suc m) = ℚ.isTrans≤ _ _ _
     (≤ss'-suc (m ℕ.+ n) (ww (m ℕ.+ n))) (≤ss' n m)



   ww⊂ : ∀ n m → (s (m ℕ.+ n) ℚ.- s n) ℚ.≤ Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n)
   ww⊂ n m = ℚ.isTrans≤
     (s (m ℕ.+ n) ℚ.- s n) (s' n ℚ.- s n) _
       (ℚ.≤-+o (s (m ℕ.+ n)) (s' n) (ℚ.- (s n))
        (ℚ.isTrans≤ _ _ _ (Step.a'≤b' (ww (m ℕ.+ n))) (≤ss' n m)))
    (Step.b'-a'≤Δ (ww n))

   www : {ε : ℚ₊} → (Σ[ n ∈ ℕ ] [ 3 / 4 ] ℚ^ⁿ n ℚ.<
             fst (ε ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)))
          → Σ[ N ∈ ℕ ] (∀ m n → N ℕ.< n → N ℕ.< m →
               absᵣ (rat (s n) -ᵣ rat (s m)) <ᵣ rat (fst ε)   )
   www (N , P) .fst = N
   www {ε} (N , P) .snd = ℕ.elimBy≤+
     (λ n m X m< n< → subst (_<ᵣ (rat (fst ε)))
       (minusComm-absᵣ (rat (s m)) (rat (s n))) (X n< m<))
     λ n m p N<n →
       let P' : Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ N) ℚ.< fst ε
           P' = ℚ.isTrans<≤ _ _ (fst ε) (ℚ.<-o· _ _ _ (ℚ.-< a b a<b) P)
                  (ℚ.≡Weaken≤ _ _
                     ((cong (fst (ℚ.<→ℚ₊ a b a<b) ℚ.·_) (ℚ.·Comm _ _))
                      ∙ ℚ.y·[x/y] (ℚ.<→ℚ₊ _ _ a<b) (fst ε)))
           zz = ℚ.isTrans≤< _ _ _
                   (ℚ.isTrans≤ _ ((s (m ℕ.+ n)) ℚ.- (s n)) _
                     (ℚ.≡Weaken≤ _ _ (ℚ.absNonNeg (s (m ℕ.+ n) ℚ.- s n)
                       (ℚ.-≤ (s n) (s (m ℕ.+ n)) (ss≤ n m))))
                       (ww⊂ n m))
                   (ℚ.isTrans< _ (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ (N))) _
                     (ℚ.<-o· _ _ Δ₀ (ℚ.-< a b a<b)
                      (<^n' N n _ ℚ.decℚ<? N<n)) P')
       in isTrans≡<ᵣ _ _ _ (cong rat (sym (ℚ.abs'≡abs _)))
            (<ℚ→<ᵣ _ _ zz) 


   f⁻¹ : ℝ
   f⁻¹ = fromCauchySequence' (rat ∘ s)
         λ ε → www {ε} (1/mⁿ<ε 2 (ε ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)))




   f⁻¹∈ : f⁻¹ ∈ intervalℙ (rat a) (rat b)
   f⁻¹∈ = ((≤lim _ _ _
            λ δ → ≤ℚ→≤ᵣ _ _ $ fst (Step.a'∈
             (ww (suc (1/mⁿ<ε 2 (δ ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)) .fst))))))
      , (lim≤ _ _ _
            λ δ → ≤ℚ→≤ᵣ _ _ $ snd (Step.a'∈
             (ww (suc (1/mⁿ<ε 2 (δ ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)) .fst)))))


   s∈ : ∀ n → rat (s n) ∈ intervalℙ (rat a) (rat b)
   s∈ n = ((≤ℚ→≤ᵣ _ _ $ fst (Step.a'∈
             (ww n))))
      , (≤ℚ→≤ᵣ _ _ $ snd (Step.a'∈
             (ww n)))


   s~y : (ε : ℚ₊) →
           ∃-syntax ℕ
           (λ N →
              (n : ℕ) →
              N ℕ.< n →
              absᵣ (f (rat (s n)) (s∈ n) -ᵣ rat y) <ᵣ rat (fst ε))
   s~y ε = 
     let (N , X) = (1/mⁿ<ε 2 (invℚ₊ (L ℚ₊· Δ₀₊) ℚ₊· ε))

     in ∣ suc N ,
        (λ { zero x → ⊥.rec (ℕ.¬-<-zero x)
           ; (suc n) x →
              let 𝒔 = ww (suc n)
                  XX : ([ 3 / 4 ] ℚ^ⁿ N) ℚ.< fst (invℚ₊ (L ℚ₊· Δ₀₊) ℚ₊· ε)
                  XX = {!X!}
                 
              in {!X!}
           }) ∣₁


   f∘f⁻¹ : f f⁻¹ f⁻¹∈
       ≡ rat y
   f∘f⁻¹ = 
      snd (map-fromCauchySequence'
          L (rat ∘ s)
            (λ ε → www {ε} (1/mⁿ<ε 2  (ε ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b))))
             {!f'!}
              {!!}) ∙
               fromCauchySequence'≡ _ _ _
          s~y



  f⁻¹-L : Lipschitz-ℚ→ℝℙ K (intervalℙ fa fb) f⁻¹
  f⁻¹-L y y∈ r r∈ ε x =
    let zz = lip⁻¹F _ _ _ _ ε
             (subst2 _∼[ ε ]_
               (sym (f∘f⁻¹ y y∈))
               (sym (f∘f⁻¹ r r∈)) (invEq (∼≃abs<ε _ _ _)
                  (<ℚ→<ᵣ (ℚ.abs' (y ℚ.- r)) (fst ε)
                    (subst (ℚ._< fst ε) (ℚ.abs'≡abs (y ℚ.- r)) x))))
        
    in fst (∼≃abs<ε (f⁻¹ y y∈) (f⁻¹ r r∈) _) zz





  -- -- -- ext-f⁻¹ : ?
  -- -- -- ext-f⁻¹ = extend-Lipshitzℚ→ℝ K fa fb (ℚ.<Weaken≤ _ _ fa<fb) f⁻¹ f⁻¹-L
  


  -- --  -- s~y : (ε : ℚ₊) →
  -- --  --         ∃-syntax ℕ
  -- --  --         (λ N →
  -- --  --            (n : ℕ) →
  -- --  --            N ℕ.< n →
  -- --  --            absᵣ {!!} <ᵣ rat (fst ε))
  -- --  -- s~y ε = {!!}
   
  -- --  -- f⁻¹∈ : f⁻¹ ∈ intervalℙ (rat a) (rat b)
  -- --  -- f⁻¹∈ = ((≤lim _ _ _
  -- --  --          λ δ → ≤ℚ→≤ᵣ _ _ $ fst (Step.a'∈
  -- --  --           (ww (suc (1/2ⁿ<ε (δ ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)) .fst))))))
  -- --  --    , (lim≤ _ _ _
  -- --  --          λ δ → ≤ℚ→≤ᵣ _ _ $ snd (Step.a'∈
  -- --  --           (ww (suc (1/2ⁿ<ε (δ ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)) .fst)))))


  -- --  -- f∘f⁻¹ : ? --fst fl-ebl f⁻¹
  -- --  --     ≡ rat y
  -- --  -- f∘f⁻¹ = snd (map-fromCauchySequence'
  -- --  --     L (rat ∘ s)
  -- --  --       (λ ε → www {ε} (1/2ⁿ<ε (ε ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b))))
  -- --  --        ( fst fl-ebl) (snd fl-ebl)) ∙
  -- --  --          fromCauchySequence'≡ _ _ _
  -- --  --     s~y
