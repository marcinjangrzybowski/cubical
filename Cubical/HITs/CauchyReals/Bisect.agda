{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.Bisect where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

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


<^n : ∀ N n → N ℕ.< n →
        ([ 1 / 2 ] ℚ^ⁿ n) ℚ.< ([ 1 / 2 ] ℚ^ⁿ N)
<^n N zero x = ⊥.rec (ℕ.¬-<-zero x)
<^n zero (suc zero) x = ℚ.decℚ<? {[ 1 / 2 ] ℚ.· 1} {1}
<^n zero (suc (suc n)) x = ℚ.isTrans<
  (([ 1 / 2 ] ℚ^ⁿ (suc n)) ℚ.· [ 1 / 2 ] )
  (([ 1 / 2 ] ℚ^ⁿ n) ℚ.· [ 1 / 2 ])
  _
  (ℚ.<-·o _ _ [ 1 / 2 ] (ℚ.decℚ<? {0} {[ 1 / 2 ]})
    (<^n n (suc n) ℕ.≤-refl))
  (<^n zero (suc n) (ℕ.suc-≤-suc ℕ.zero-≤))
<^n (suc N) (suc n) x =
 ℚ.<-·o _ _ [ 1 / 2 ] (ℚ.decℚ<? {0} {[ 1 / 2 ]})
   (<^n N n (ℕ.predℕ-≤-predℕ x))




Lipschitz-ℚ→ℝℙ : ℚ₊ → (P : ℙ ℝ) → (∀ x → rat x ∈ P  → ℝ) → Type
Lipschitz-ℚ→ℝℙ L P f =
  (∀ q q∈ r r∈ → (ε : ℚ₊) →
    ℚ.abs (q ℚ.- r) ℚ.< (fst ε) → absᵣ (f q q∈ -ᵣ f r r∈)
     <ᵣ rat (fst (L ℚ₊· ε  )))

Lipschitz-ℚ→ℝℙ< : ℚ₊ → (P : ℙ ℝ) → (∀ x → rat x ∈ P  → ℝ) → Type
Lipschitz-ℚ→ℝℙ< L P f = ∀ q q∈ r r∈ → r ℚ.< q →
     absᵣ (f q q∈ -ᵣ f r r∈)
     ≤ᵣ rat (fst L ℚ.·  (q ℚ.- r) )

Lipschitz-ℚ→ℝℙ<→Lipschitz-ℚ→ℝℙ : ∀ L P f →
 Lipschitz-ℚ→ℝℙ< L P f → Lipschitz-ℚ→ℝℙ L P f
Lipschitz-ℚ→ℝℙ<→Lipschitz-ℚ→ℝℙ L P f X = (flip ∘
  flip (ℚ.elimBy≡⊎<
    (λ x y X →
       λ x∈ y∈ ε u → isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _)
         (X y∈ x∈ ε (subst (ℚ._< (fst ε)) (ℚ.absComm- _ _) u)) )
    (λ _ _ _ ε _ → isTrans≡<ᵣ _ _ _
      (cong absᵣ (𝐑'.+InvR' _ _
        (cong (f _) (∈-isProp P _ _ _))))
     (<ℚ→<ᵣ 0 _ $ ℚ.0<ℚ₊ (L ℚ₊· ε)))
    λ x y x₁ y₁ r∈ ε u → isTrans≤<ᵣ _ _ _
     (X y y₁ x r∈ x₁)
        (<ℚ→<ᵣ _ _  (ℚ.<-o· _ _ (fst L) (ℚ.0<ℚ₊ L)
          (subst (ℚ._< fst ε) (ℚ.absPos _ ((ℚ.-< _ _ x₁))) u)) )))

Lipschitz-ℝ→ℝℙ : ℚ₊ → (P : ℙ ℝ) → (∀ x → x ∈ P  → ℝ) → Type
Lipschitz-ℝ→ℝℙ L P f =
    (∀ u u∈ v v∈ → (ε : ℚ₊) →
        u ∼[ ε  ] v → f u u∈ ∼[ L ℚ₊· ε  ] f v v∈)



Invlipschitz-ℚ→ℚℙ : ℚ₊ → (P : ℙ ℚ) → (∀ x → x ∈ P  → ℚ) → Type
Invlipschitz-ℚ→ℚℙ K P f =
  (∀ q q∈ r r∈ → (ε : ℚ₊) →
        ℚ.abs' (f q q∈ ℚ.- f r r∈) ℚ.< (fst ε)
     → ℚ.abs' (q ℚ.- r) ℚ.< fst (K ℚ₊· ε ) )

Invlipschitz-ℝ→ℝ : ℚ₊ → (∀ x → ℝ) → Type
Invlipschitz-ℝ→ℝ K f =
    (∀ u v → (ε : ℚ₊) →
        f u  ∼[ ε ] f v → u ∼[ K ℚ₊· ε  ] v)

Invlipschitz-ℝ→ℝ→injective : ∀ K f → Invlipschitz-ℝ→ℝ K f
    → ∀ x y → f x ≡ f y → x ≡ y
Invlipschitz-ℝ→ℝ→injective K f il x y =
 fst (∼≃≡ _ _) ∘
   (λ p ε → subst∼ (ℚ.y·[x/y] K (fst ε))
     (il x y ((invℚ₊ K) ℚ₊· ε) (p (invℚ₊ K ℚ₊· ε))))
   ∘S invEq (∼≃≡ _ _)

Invlipschitz-ℚ→ℚ : ℚ₊ → (∀ x → ℚ) → Type
Invlipschitz-ℚ→ℚ K f =
  (∀ q r → (ε : ℚ₊) →
        ℚ.abs' (f q ℚ.- f r) ℚ.< (fst ε)
     → ℚ.abs' (q ℚ.- r) ℚ.< fst (K ℚ₊· ε) )


Invlipschitz-ℚ→ℚ' : ℚ₊ → (ℚ → ℚ) → Type
Invlipschitz-ℚ→ℚ' K f =
  (∀ q r → 
     ℚ.abs' (q ℚ.- r) ℚ.≤ fst K ℚ.· ℚ.abs' (f q ℚ.- f r))

Invlipschitz-ℝ→ℝ' : ℚ₊ → (ℝ → ℝ) → Type
Invlipschitz-ℝ→ℝ' K f =
    (∀ u v → 
        absᵣ (u -ᵣ v) ≤ᵣ rat (fst K) ·ᵣ absᵣ (f u -ᵣ f v))


Invlipschitz-ℚ→ℚ→Invlipschitz-ℚ→ℚ' : ∀ K f →
  Invlipschitz-ℚ→ℚ K f → Invlipschitz-ℚ→ℚ' K f
Invlipschitz-ℚ→ℚ→Invlipschitz-ℚ→ℚ' K f X q r =
 ℚ.≮→≥ _ _ λ x →
   
   let x* : ℚ.abs' (f q ℚ.- f r) ℚ.<
            fst (invℚ₊ K) ℚ.·  ℚ.abs' (q ℚ.- r)
       x* = subst (ℚ._< fst (invℚ₊ K) ℚ.· ℚ.abs' (q ℚ.- r))
              (ℚ.[y·x]/y K _) (ℚ.<-o· _ _ (fst (invℚ₊ K))
               (ℚ.0<ℚ₊ ((invℚ₊ K))) x)
       z = X q r ((invℚ₊ K) ℚ₊·
                     (_ , ℚ.<→0< _ (ℚ.isTrans≤< 0 _ _
                        (
                         (subst2 (ℚ._≤_)
                           (ℚ.·AnnihilR _)
                         (cong (fst K ℚ.·_) (ℚ.abs'≡abs _)) -- (ℚ.abs'≡abs _)
                          (ℚ.≤-o· _ _ (fst K) (ℚ.0≤ℚ₊ K) (ℚ.0≤abs _)))) x))) x*
   in ⊥.rec (ℚ.isIrrefl< (ℚ.abs' (q ℚ.- r))
         (subst (ℚ.abs' (q ℚ.- r) ℚ.<_) (ℚ.y·[x/y] K _) z))

Invlipschitz-ℚ→ℚ'→Invlipschitz-ℚ→ℚ : ∀ K f →
  Invlipschitz-ℚ→ℚ' K f → Invlipschitz-ℚ→ℚ K f
Invlipschitz-ℚ→ℚ'→Invlipschitz-ℚ→ℚ K f X q r ε fq-fr<ε =
  ℚ.isTrans≤< _ _ _ (X q r) (ℚ.<-o· _ _ (fst K) (ℚ.0<ℚ₊ K)
             fq-fr<ε) 


Invlipschitz-ℚ→ℚℙ'< : ℚ₊ → (P : ℙ ℚ) → (∀ x → x ∈ P  → ℚ) → Type
Invlipschitz-ℚ→ℚℙ'< K P f =
  (∀ q q∈ r r∈  → r ℚ.< q → 
      (q ℚ.- r) ℚ.≤ fst K ℚ.· ℚ.abs' (f q q∈ ℚ.- f r r∈))


Invlipschitz-ℚ→ℚℙ'<→Invlipschitz-ℚ→ℚℙ : ∀ K P f →
  Invlipschitz-ℚ→ℚℙ'< K P f → Invlipschitz-ℚ→ℚℙ K P f
Invlipschitz-ℚ→ℚℙ'<→Invlipschitz-ℚ→ℚℙ K P f X = flip ∘
  flip (ℚ.elimBy≡⊎<
    ((λ x y X →
       λ x∈ y∈ ε u → ℚ.isTrans≤< _ _ _
        (ℚ.≡Weaken≤ _ _ (ℚ.abs'Comm- x y))
         ((X y∈ x∈ ε ((subst (ℚ._< (fst ε))
          (ℚ.abs'Comm- (f x x∈) (f y y∈)) u)))) ))
    (λ x _ _ ε _ → subst (ℚ._< fst (K ℚ₊· ε))
      (cong ℚ.abs' (sym (ℚ.+InvR x))) (ℚ.0<ℚ₊ (K ℚ₊· ε)))
    λ x y x<y y∈  x∈ ε u →
      ℚ.isTrans≤< _ _ _
        (ℚ.≡Weaken≤ _ _ (sym (ℚ.abs'≡abs _) ∙ ℚ.absPos _ (ℚ.-< _ _ x<y) ))
       (ℚ.isTrans≤< _ _ _
        (X y y∈ x x∈  x<y) (ℚ.<-o· _ _ (fst K) (ℚ.0<ℚ₊ K) u)))


Invlipschitz-ℝ→ℝ'→Invlipschitz-ℝ→ℝ : ∀ K f →
  Invlipschitz-ℝ→ℝ' K f → Invlipschitz-ℝ→ℝ K f
Invlipschitz-ℝ→ℝ'→Invlipschitz-ℝ→ℝ K f X u v ε fu∼fv =
 let y = fst (∼≃abs<ε _ _ _) fu∼fv
     y'' = isTrans≤<ᵣ _ _ _ (X u v) (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ K) y )
 in invEq (∼≃abs<ε _ _ _)
       (isTrans<≡ᵣ _ _ _ y'' (sym (rat·ᵣrat _ _)))

Invlipschitz-ℝ→ℝℙ : ℚ₊ → (P : ℙ ℝ) → (∀ x → x ∈ P  → ℝ) → Type
Invlipschitz-ℝ→ℝℙ K P f =
    (∀ u u∈ v v∈ → (ε : ℚ₊) →
        f u u∈ ∼[ ε ] f v v∈ → u ∼[ K ℚ₊· ε  ] v)




ℚintervalℙ : ℚ → ℚ → ℙ ℚ 
ℚintervalℙ a b x = ((a ℚ.≤ x) × (x ℚ.≤ b)) ,
  isProp× (ℚ.isProp≤ _ _)  (ℚ.isProp≤ _ _)


intervalℙ : ℝ → ℝ → ℙ ℝ 
intervalℙ a b x = ((a ≤ᵣ x) × (x ≤ᵣ b)) ,
  isProp× (isSetℝ _ _)  (isSetℝ _ _)

clam∈ℚintervalℙ : ∀ a b → (a ℚ.≤ b) → ∀ x →
  ℚ.clamp a b x ∈ ℚintervalℙ a b 
clam∈ℚintervalℙ a b a≤b x = ℚ.≤clamp _ _ _ a≤b , (ℚ.clamp≤ _ _ _)

∈ℚintervalℙ→clam≡ : ∀ a b → ∀ x →
    x ∈ ℚintervalℙ a b → x ≡ ℚ.clamp a b x
∈ℚintervalℙ→clam≡ a b x = sym ∘ uncurry (ℚ.inClamps a b x)
 
∈ℚintervalℙ→clampᵣ≡ : ∀ a b → ∀ x →
    x ∈ intervalℙ a b → x ≡ clampᵣ a b x
∈ℚintervalℙ→clampᵣ≡ a b x (a≤x , x≤b) =
 sym (≤→minᵣ _ _ x≤b)  ∙ cong (λ y → minᵣ y b) (sym a≤x)


clamp-contained-agree : ∀ (a b a' b' x : ℚ)
  → a ℚ.≤ a'
  → b' ℚ.≤ b
  → x ∈ ℚintervalℙ a' b'
  → ℚ.clamp a b x ≡ ℚ.clamp a' b' x
clamp-contained-agree a b a' b' x a≤a' b'≤b x∈ =
  sym (∈ℚintervalℙ→clam≡ a b x
   ((ℚ.isTrans≤ _ _ _ a≤a' (fst x∈)) ,
    (ℚ.isTrans≤ _ _ _ (snd x∈) b'≤b))) ∙ ∈ℚintervalℙ→clam≡ a' b' x x∈

≤clampᵣ : ∀ L L' x → L ≤ᵣ L' →  L ≤ᵣ clampᵣ L L' x
≤clampᵣ L L' x y =
  isTrans≤≡ᵣ _ _ _ (≤maxᵣ L (minᵣ x L'))
    (cong₂ maxᵣ (sym (≤→minᵣ _ _ y) ∙ minᵣComm _ _) (minᵣComm _ _)
     ∙∙ sym (maxDistMin L' L x) ∙∙
     minᵣComm _ _ )
     
clampᵣ∈ℚintervalℙ : ∀ a b → (a ≤ᵣ b) → ∀ x →
  clampᵣ a b x ∈ intervalℙ a b 
clampᵣ∈ℚintervalℙ a b a≤b x =
        ≤clampᵣ _ _ _ a≤b , min≤ᵣ' (maxᵣ a x) b

≡clampᵣ→∈intervalℙ : ∀ a b → (a ≤ᵣ b) → ∀ x →
  x ≡ clampᵣ a b x → x ∈ intervalℙ a b 
≡clampᵣ→∈intervalℙ a b a≤b x p =
        subst-∈ (intervalℙ a b ) (sym p) (clampᵣ∈ℚintervalℙ a b a≤b x)


∈ℚintervalℙ→∈intervalℙ : ∀ a b x → x ∈ ℚintervalℙ a b
                                 → rat x ∈ intervalℙ (rat a) (rat b)
∈ℚintervalℙ→∈intervalℙ a b x (a≤x , x≤b) = ≤ℚ→≤ᵣ _ _ a≤x , ≤ℚ→≤ᵣ _ _ x≤b

∈intervalℙ→∈ℚintervalℙ : ∀ a b x → rat x ∈ intervalℙ (rat a) (rat b)
                                 → x ∈ ℚintervalℙ a b
∈intervalℙ→∈ℚintervalℙ a b x (a≤x , x≤b) = ≤ᵣ→≤ℚ _ _ a≤x , ≤ᵣ→≤ℚ _ _ x≤b


isIncrasingℙ : (P : ℙ ℚ) → (∀ x → x ∈ P → ℚ) → Type₀
isIncrasingℙ P f = ∀ x x∈ y y∈ → x ℚ.< y → f x x∈ ℚ.< f y y∈

isNondecrasingℙ : (P : ℙ ℚ) → (∀ x → x ∈ P → ℚ) → Type₀
isNondecrasingℙ P f = ∀ x x∈ y y∈ → x ℚ.≤ y → f x x∈ ℚ.≤ f y y∈

isIncrasingℙ→injective : (P : ℙ ℚ) → (f : ∀ x → x ∈ P → ℚ) →
                          isIncrasingℙ P f →
                          ∀ x x∈ x' x'∈
                            → f x x∈ ≡ f x' x'∈ → x ≡ x' 
isIncrasingℙ→injective P f incrF x x∈ x' x'∈ =
  ⊎.rec const (⊎.rec (w x x∈ x' x'∈) ((sym ∘_) ∘ (_∘ sym) ∘ w x' x'∈ x x∈))
    (ℚ.≡⊎# x x')

 where
 w : ∀ x x∈ x' x'∈  → x ℚ.< x' → f x x∈ ≡ f x' x'∈ → x ≡ x'
 w x x∈ x' x'∈ x<x' p =
  ⊥.rec (ℚ.isIrrefl# _
    (inl (subst (ℚ._< f x' x'∈) p (incrF x x∈ x' x'∈ x<x'))))

ℚisIncrasing→injective : (f : ℚ → ℚ) →
                            (∀ x x' → x ℚ.< x' → f x ℚ.< f x')

                            → ∀ x x' → f x ≡ f x' → x ≡ x' 
ℚisIncrasing→injective f incrF x x' =
    ⊎.rec const (⊎.rec (w x x') ((sym ∘_) ∘ (_∘ sym) ∘ w x' x))
    (ℚ.≡⊎# x x')

 where
 w : ∀ x x' → x ℚ.< x' → f x ≡ f x' → x ≡ x'
 w x x' x<x' p =
  ⊥.rec (ℚ.isIrrefl# _
    (inl (subst (ℚ._< f x') p (incrF x x' x<x'))))


-- isIncrasing→injectiveℝ : ∀ f → IsContinuous f  →
--      isIncrasing f →
--       ∀ x x' → f x ≡ f x' → x ≡ x' 
      
-- isIncrasing→injectiveℝ f fC incrF x x' p =
--  eqℝ _ _ λ ε → invEq (∼≃abs<ε _ _ _) {!!}

isIncrasingℙ→isNondecrasingℙ : ∀ P f
               → isIncrasingℙ P f
               → isNondecrasingℙ P f 
isIncrasingℙ→isNondecrasingℙ P f incF x x∈ y y∈ =
  ⊎.rec (ℚ.≡Weaken≤ _ _ ∘ cong (uncurry f) ∘ Σ≡Prop (∈-isProp _))
   (ℚ.<Weaken≤ _ _ ∘ incF _ _ _ _) ∘ ℚ.≤→≡⊎< _ _

ℚisIncrasing : (ℚ → ℚ) → Type₀
ℚisIncrasing f = ∀ x y →  x ℚ.< y → f x ℚ.< f y


elimInClamps : ∀ {ℓ} {P : ℚ → Type ℓ} → ∀ L L' → L ℚ.≤ L' →
     (∀ x → x ∈ ℚintervalℙ L L' → P x) → 
     ∀ x → P (ℚ.clamp L L' x)
elimInClamps L L' L≤L' X x = X _ (clam∈ℚintervalℙ L L' L≤L' x)

elimInClampsᵣ : ∀ {ℓ} {P : ℝ → Type ℓ} → ∀ L L' →
     (∀ x → P (clampᵣ L L' x)) → 
     (∀ x → x ∈ intervalℙ L L' → P x) 
     
elimInClampsᵣ {P = P} L L' X x x∈ =
  subst P (sym (∈ℚintervalℙ→clampᵣ≡ _ _ _ x∈)) (X x) 

elimFromClampsᵣ : ∀ {ℓ} {P : ℝ → Type ℓ} → ∀ L L' → L ≤ᵣ L' → 
     (∀ x → x ∈ intervalℙ L L' → P x) → 
     (∀ x → P (clampᵣ L L' x)) 
      
elimFromClampsᵣ {P = P} L L' L≤L' X x =
  X (clampᵣ L L' x) (clampᵣ∈ℚintervalℙ _ _ L≤L' x)


elimInClamps2 : ∀ {ℓ} {P : ℚ → ℚ → Type ℓ} → ∀ L L' → L ℚ.≤ L' →
     (∀ x y → x ∈ ℚintervalℙ L L' → y ∈ ℚintervalℙ L L' → P x y) → 
     ∀ x y → P (ℚ.clamp L L' x) (ℚ.clamp L L' y)
elimInClamps2 L L' L≤L' X x y =
  X _ _ (clam∈ℚintervalℙ L L' L≤L' x) (clam∈ℚintervalℙ L L' L≤L' y)


cont-f∈ : ∀ (f : ℝ → ℝ) → IsContinuous f
          → ∀ a b → (a ℚ.≤ b) → ∀ a' b' → a' ≤ᵣ b'    
          → (∀ x → rat x ∈ intervalℙ (rat a) (rat b)
                 → f (rat x) ∈ intervalℙ a' b')
          → ∀ x → x ∈ intervalℙ (rat a) (rat b) → f x ∈ intervalℙ a' b'
cont-f∈ f fc a b a≤b a' b' a'≤b' X = elimInClampsᵣ (rat a) (rat b)
  λ x → ≡clampᵣ→∈intervalℙ a' b' a'≤b'
    (f (clampᵣ (rat a)  (rat b) x))
      ((≡Continuous _ _
          (IsContinuous∘ _ _ fc (IsContinuousClamp (rat a)  (rat b)))
        (IsContinuous∘ _ _ (IsContinuousClamp a' b')
          (IsContinuous∘ _ _ fc (IsContinuousClamp (rat a)  (rat b))))
         (elimInClamps {P = λ (r : ℚ) →
                   f (rat r) ≡ (clampᵣ a' b' (f (rat r)))}
           a b a≤b λ r → ∈ℚintervalℙ→clampᵣ≡ a' b' (f (rat r))
                 ∘S X r
                 ∘S ∈ℚintervalℙ→∈intervalℙ a b r  )
         ) _)
  
extend-Lipshitzℚ→ℝ : ∀ L →  ∀ a b → (a ℚ.≤ b) → ∀ f →  
        Lipschitz-ℚ→ℝℙ L (intervalℙ (rat a) (rat b)) f →
        Σ[ f' ∈ (ℚ → ℝ) ]
          (Lipschitz-ℚ→ℝ L f' × (∀ x x∈ → f' x ≡ f x x∈ ))
        
extend-Lipshitzℚ→ℝ L a b a≤b f li =
 (λ x → f (ℚ.clamp a b x) (∈ℚintervalℙ→∈intervalℙ _ _ _
  (clam∈ℚintervalℙ a b a≤b x))) ,
   w , (λ x x∈ → cong (uncurry f)
    (Σ≡Prop (∈-isProp (intervalℙ (rat a) (rat b) ∘ rat))
    (ℚ.inClamps a b x (≤ᵣ→≤ℚ _ _ (fst x∈)) (≤ᵣ→≤ℚ _ _ (snd x∈)) )))

 where
 w : Lipschitz-ℚ→ℝ L
       (λ x →
          f (ℚ.clamp a b x)
          (∈ℚintervalℙ→∈intervalℙ a b (ℚ.clamp a b x)
           (clam∈ℚintervalℙ a b a≤b x)))
 w q r ε u v = invEq (∼≃abs<ε _ _ _)
  (li _ _
   _ _ ε (ℚ.isTrans≤< _ _ _
    (ℚ.clampDist _ _ _ _) (ℚ.absFrom<×< (fst ε) (q ℚ.- r) u v))) 

IsContinuous₂ : (ℝ → ℝ → ℝ) → Type
IsContinuous₂ f =
 (∀ x → IsContinuous (f x)) × (∀ x → IsContinuous (flip f x))


≡Cont₂ : {f₀ f₁ : ℝ → ℝ → ℝ}
         → IsContinuous₂ f₀
         → IsContinuous₂ f₁
         → (∀ u u' → f₀ (rat u) (rat u') ≡ f₁ (rat u) (rat u'))
             → ∀ x x' → f₀ x x' ≡ f₁ x x'
≡Cont₂ {f₀} {f₁} (f₀C , f₀C') (f₁C , f₁C') p x =
  ≡Continuous _ _ (f₀C x) (f₁C x)
    (λ q → ≡Continuous _ _ (f₀C' (rat q)) (f₁C' (rat q))
       (λ r → p r q) x)


contNE₂∘ : ∀ {h} → (ne : NonExpanding₂ h)
  {f₀ f₁ : ℝ → ℝ → ℝ}
   → IsContinuous₂ f₀
   → IsContinuous₂ f₁
  → IsContinuous₂ (λ x x' → NonExpanding₂.go ne (f₀ x x') (f₁ x x'))
contNE₂∘ ne x x₁ =
  (λ x₂ → contDiagNE₂ ne _ _ (x .fst x₂) (x₁ .fst x₂)) ,
   λ x₂ → contDiagNE₂ ne _ _ (x .snd x₂) (x₁ .snd x₂)

cont∘₂ : ∀ {g} 
  {f : ℝ → ℝ → ℝ}
   → IsContinuous g
   → IsContinuous₂ f
  → IsContinuous₂ (λ x x' → g (f x x'))
cont∘₂ cG (cF , _) .fst x = IsContinuous∘ _ _ cG (cF x)
cont∘₂ cG (_ , cF) .snd x = IsContinuous∘ _ _ cG (cF x)

cont₂∘ :  
  {g : ℝ → ℝ → ℝ}
  → ∀ {f f'}
   → IsContinuous₂ g
   → IsContinuous f
   → IsContinuous f'
  → IsContinuous₂ (λ x x' → g (f x) (f' x'))
cont₂∘ (cG , _) _ cF .fst x = IsContinuous∘ _ _ (cG _) cF
cont₂∘ (_ , cG) cF _ .snd x = IsContinuous∘ _ _ (cG _) cF


contNE₂ : ∀ {h} → (ne : NonExpanding₂ h)
  → IsContinuous₂ (NonExpanding₂.go ne)
contNE₂ ne =
  contNE₂∘ ne
   ((λ _ → IsContinuousConst _) , (λ _ → IsContinuousId))
   ((λ _ → IsContinuousId) , (λ _ → IsContinuousConst _))



≤Cont₂ : {f₀ f₁ : ℝ → ℝ → ℝ}
         → IsContinuous₂ f₀
         → IsContinuous₂ f₁
         → (∀ u u' → f₀ (rat u) (rat u') ≤ᵣ f₁ (rat u) (rat u'))
             → ∀ x x' → f₀ x x' ≤ᵣ f₁ x x'
≤Cont₂ f₀C f₁C =
  ≡Cont₂ (contNE₂∘ maxR f₀C f₁C) f₁C

fromLipInvLip' : ∀ K L (f : ℚ → ℚ)
                 → (fl : Lipschitz-ℚ→ℝ L (rat ∘ f))
                 → Invlipschitz-ℚ→ℚ' K f
                 → Invlipschitz-ℝ→ℝ' K
                      (fst (fromLipschitz L ((rat ∘ f) , fl)))
fromLipInvLip' K L f fl il =
       ≤Cont₂ (cont∘₂ IsContinuousAbsᵣ
                (cont₂∘ (contNE₂ sumR)
                 IsContinuousId IsContinuous-ᵣ ))
                (cont∘₂ (IsContinuous∘ _ _ (IsContinuous·ᵣL _)
                   IsContinuousAbsᵣ)
                 (cont₂∘ ((cont₂∘ (contNE₂ sumR)
                 IsContinuousId IsContinuous-ᵣ ))
                  cf cf))
                λ u u' →
         isTrans≤≡ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ (il u u'))
          (rat·ᵣrat _ _)
 where
 cf = Lipschitz→IsContinuous L _
        (snd (fromLipschitz L ((rat ∘ f) , fl)))



fromLipInvLip : ∀ K L (f : ℚ → ℚ)
                 → (fl : Lipschitz-ℚ→ℝ L (rat ∘ f))
                 → Invlipschitz-ℚ→ℚ K f
                 → Invlipschitz-ℝ→ℝ K
                      (fst (fromLipschitz L ((rat ∘ f) , fl)))
fromLipInvLip K L f fl =
    Invlipschitz-ℝ→ℝ'→Invlipschitz-ℝ→ℝ K _
  ∘S fromLipInvLip' K L f fl
  ∘S Invlipschitz-ℚ→ℚ→Invlipschitz-ℚ→ℚ' K f

extend-Bilipshitz : ∀ L K → fst (invℚ₊ K) ℚ.≤ fst L → ∀ a b → (a ℚ.≤ b) →
            (f : ∀ q → q ∈ ℚintervalℙ a b → ℚ) →
             isIncrasingℙ _ f → 
        Lipschitz-ℚ→ℝℙ L (intervalℙ (rat a) (rat b))
          ((λ x x₁ → rat (f x (∈intervalℙ→∈ℚintervalℙ a b x x₁)))) →
        Invlipschitz-ℚ→ℚℙ K (ℚintervalℙ a b) f → 
        Σ[ f' ∈ (ℚ → ℚ) ]
          Lipschitz-ℚ→ℝ L (rat ∘ f')
           × Invlipschitz-ℚ→ℚ K f' × (∀ x x∈ → f' x ≡ f x x∈ )
extend-Bilipshitz L K 1/K≤L a b a≤b f monF li il =
  fst ∘ f' , li' , (ili' ,
    snd ∘ f')
 where

 α : ℚ₊
 α = /2₊ (ℚ.invℚ₊ K ℚ₊+ L)

 α≤L : fst α ℚ.≤ fst L
 α≤L = ℚ.isTrans≤ _ _ _ (ℚ.≤-·o _ _ [ 1 / 2 ]
         (ℚ.decℚ≤? {0} {[ 1 / 2 ]})
          (ℚ.≤-+o (fst (invℚ₊ K)) (fst L) (fst L) 1/K≤L))
          (ℚ.≡Weaken≤ _ _ (
            cong (ℚ._· [ 1 / 2 ])
              (cong₂ ℚ._+_ (sym (ℚ.·IdL _)) (sym (ℚ.·IdL _))
              ∙ sym (ℚ.·DistR+ 1 1 (fst L)))
              ∙∙ ℚ.·Comm _ _ ∙∙ ℚ.[y·x]/y 2 (fst L)))

 1/K≤α : fst (ℚ.invℚ₊ K) ℚ.≤  fst α 
 1/K≤α = ℚ.isTrans≤ _ _ _
   (ℚ.≡Weaken≤ _ _ ((sym (ℚ.[y·x]/y 2 (fst (invℚ₊ K))) ∙ ℚ.·Comm _ _)
     ∙ cong (ℚ._· [ 1 / 2 ]) ((ℚ.·DistR+ 1 1 (fst (invℚ₊ K))) ∙
      cong₂ ℚ._+_ (ℚ.·IdL _) (ℚ.·IdL _) )))
    (ℚ.≤-·o _ _ [ 1 / 2 ] (ℚ.decℚ≤? {0} {[ 1 / 2 ]})
     ((ℚ.≤-o+ (fst (invℚ₊ K)) (fst L) (fst (invℚ₊ K)) 1/K≤L)))
 
 g : ℚ → ℚ → ℚ
 g Δ x = fst α ℚ.· (x ℚ.- Δ)


 f≡ : ∀ {x x' x∈ x'∈} → x ≡ x' → f x x∈ ≡ f x' x'∈ 
 f≡ p = (cong (uncurry f) (Σ≡Prop (∈-isProp (ℚintervalℙ a b))
              (p)))


 f' : ∀ x → Σ ℚ λ f'x → ∀ x∈ →  f'x ≡ f x x∈
 f' x = (g a x ℚ.- g a x') ℚ.+ (f x' x'∈)
   , f'=f
  where
   x' = ℚ.clamp a b x
   x'∈ = clam∈ℚintervalℙ a b a≤b x

   f'=f : (x∈ : x ∈ ℚintervalℙ a b) →
            (g a x ℚ.- g a x') ℚ.+ f x' x'∈ ≡ f x x∈
   f'=f x∈ =
    let p = ∈ℚintervalℙ→clam≡ a b x x∈
    in cong₂ ℚ._+_ (cong ((ℚ._- (g a x')) ∘S g a) p ∙
            ℚ.+InvR _)
         (f≡ (sym p))
         ∙ ℚ.+IdL _
 

 monF' : ℚisIncrasing (fst ∘ f')
 monF' = ℚ.elim≤By+ h  
  where
  h : (x : ℚ) (ε : ℚ₊) (x< : x ℚ.< x ℚ.+ fst ε) → _
  h x ε x< = ℚ.<minus→< _ _ (subst (0 ℚ.<_)
                  (sym (lem--069 {fst α} {δ = a}))
                    (h' (ℚ.≤→≡⊎< x' x+Δ' x'≤x+Δ')))

 

   where

   x<x+Δ = (ℚ.<+ℚ₊' x x ε (ℚ.isRefl≤ x))
   x' = ℚ.clamp a b x
   x'∈ = clam∈ℚintervalℙ a b a≤b x

   x+Δ' = ℚ.clamp a b (x ℚ.+ fst ε)
   x+Δ'∈ = clam∈ℚintervalℙ a b a≤b (x ℚ.+ fst ε)

   x'≤x+Δ' : x' ℚ.≤ x+Δ'
   x'≤x+Δ' = ℚ.≤MonotoneClamp a b _ _ (ℚ.<Weaken≤ _ _ x<x+Δ)

   h' : (x' ≡ x+Δ') ⊎ (x' ℚ.< x+Δ') →
           0 ℚ.< fst α ℚ.· (fst ε ℚ.- (x+Δ' ℚ.- x')) ℚ.+
            (f x+Δ' x+Δ'∈  ℚ.- f x' x'∈)
   h' (inl x) = subst (0 ℚ.<_)
                    (cong (fst α ℚ.·_) (sym (𝐐'.+IdR' _ _
                     (cong (ℚ.-_) (𝐐'.+InvR' _ _ (sym x))))) ∙
                      sym (𝐐'.+IdR' _ _
                        (𝐐'.+InvR' _ _ (f≡ (sym x)))))
                 (ℚ.0<ℚ₊ (α ℚ₊· ε))
   h' (inr xx) = ℚ.≤<Monotone+ 0 _ 0
     (f x+Δ' x+Δ'∈  ℚ.- f x' x'∈)
     (subst (ℚ._≤ fst α ℚ.· (fst ε ℚ.- (x+Δ' ℚ.- x')))
          (ℚ.·AnnihilR (fst α))
           
           (ℚ.≤-o· _ _ _ (ℚ.0≤ℚ₊ α)
               (ℚ.-≤ _ _
                 (subst ((x+Δ' ℚ.- x') ℚ.≤_)
                    lem--063 (ℚ.clampDiff a b x (x ℚ.+ fst ε)
                     (ℚ.<Weaken≤ _ _ x<x+Δ ))))))
      ((ℚ.<→<minus (f x' x'∈) (f x+Δ' x+Δ'∈)
          (monF x' x'∈ x+Δ' x+Δ'∈ xx)))


 li<' : ∀ q Δ ε (u : ℚ.- fst ε ℚ.< (q ℚ.- (q ℚ.+ fst Δ)))
          (v : (q ℚ.- (q ℚ.+ fst Δ)) ℚ.< fst ε) →
        absᵣ
        ((rat ∘ (λ x → fst (f' x))) (q ℚ.+ fst Δ) +ᵣ
         -ᵣ (rat ∘ (λ x → fst (f' x))) q)
        <ᵣ rat (fst (L ℚ₊· ε))
 li<' q Δ ε u v = isTrans≡<ᵣ _ _ _
   (absᵣPos _ (x<y→0<y-x _ _ (
     (<ℚ→<ᵣ _ _ (monF' _ _ q<q+Δ))))
      ∙ cong rat (lem--069 {fst α}))
   (isTrans≤<ᵣ (rat ((fst α ℚ.· (fst Δ ℚ.- (q+Δ' ℚ.- q'))) ℚ.+
             (((f q+Δ' q+Δ'∈) ℚ.- (f q' q'∈)))))
             (rat ((ℚ.abs' ((f q+Δ' _) ℚ.- (f q' _)))
               ℚ.+ (fst L ℚ.· (fst Δ ℚ.- (q+Δ' ℚ.- q'))))) _
              (≤ℚ→≤ᵣ _ _ zz )
               h')
  where
    Δ<ε : fst Δ ℚ.< fst ε
    Δ<ε = ℚ.minus-<' (fst ε) (fst Δ)
            (subst ((ℚ.- (fst ε)) ℚ.<_) lem--072 u)
    
    q<q+Δ = (ℚ.<+ℚ₊' q q Δ (ℚ.isRefl≤ q))
    q' = ℚ.clamp a b q
    q'∈ = clam∈ℚintervalℙ a b a≤b q

    q+Δ' = ℚ.clamp a b (q ℚ.+ fst Δ)
    q+Δ'∈ = clam∈ℚintervalℙ a b a≤b (q ℚ.+ fst Δ)

    q'≤q+Δ' : q' ℚ.≤ q+Δ'
    q'≤q+Δ' = ℚ.≤MonotoneClamp a b _ _ (ℚ.<Weaken≤ _ _ q<q+Δ)

    zz : ((fst α ℚ.· (fst Δ ℚ.- (q+Δ' ℚ.- q'))) ℚ.+
             (((f q+Δ' q+Δ'∈) ℚ.- (f q' q'∈))))
             ℚ.≤ 
             ((ℚ.abs' ((f q+Δ' _) ℚ.- (f q' _)))
               ℚ.+ (fst L ℚ.· (fst Δ ℚ.- (q+Δ' ℚ.- q'))))
    zz = subst2 ℚ._≤_ (ℚ.+Comm _ _)
          (cong (ℚ._+ (fst L ℚ.· (fst Δ ℚ.- (q+Δ' ℚ.- q')))) 
             (sym (ℚ.absNonNeg _ (ℚ.≤→<minus _ _
                  (((isIncrasingℙ→isNondecrasingℙ _ f monF)
                      _ q'∈ _ q+Δ'∈ q'≤q+Δ' ))
                  )) ∙
                   cong ℚ.abs (cong₂ ℚ._-_ (f≡ refl) (f≡ refl))
                     ∙ (ℚ.abs'≡abs _)))
            (ℚ.≤-o+ _ _ _ (ℚ.≤-·o _ _ ((fst Δ ℚ.- (q+Δ' ℚ.- q')))
              (ℚ.≤→<minus _ _
                (ℚ.isTrans≤ _ _ _ (ℚ.clampDiff a b q (q ℚ.+ fst Δ)
                  (ℚ.<Weaken≤ _ _ q<q+Δ))
                 (ℚ.≡Weaken≤ _ _ lem--063))) α≤L))


    h' = a<b-c⇒a+c<b _ (rat (fst L ℚ.· fst ε))
             (rat (fst L ℚ.· ((fst Δ ℚ.- (q+Δ' ℚ.- q'))))) (isTrans<≡ᵣ _ _ _
          (li q+Δ' (∈ℚintervalℙ→∈intervalℙ _ _ _ q+Δ'∈)
            q' (∈ℚintervalℙ→∈intervalℙ _ _ _ q'∈)
            (fst ε ℚ.- (fst Δ ℚ.- (q+Δ' ℚ.- q')) ,
               ℚ.<→0< _ (ℚ.-< _ _
                 (ℚ.isTrans≤< _ _ _
                   (subst ((fst Δ ℚ.- (q+Δ' ℚ.- q')) ℚ.≤_)
                     (ℚ.+IdR _ ∙ sym lem--063)
                      (ℚ.≤-o+ _ 0 (fst Δ)
                       (ℚ.minus-≤ 0 _ (ℚ.≤→<minus _ _ q'≤q+Δ'))))
                    ((ℚ.minus-<' _ _ (subst ((ℚ.- (fst ε)) ℚ.<_)
                     (sym (ℚ.-[x-y]≡y-x _ _)) u))))))
                      (subst2 ℚ._<_ (ℚ.+IdL _ ∙
                        sym (ℚ.absNonNeg _ (ℚ.≤→<minus _ _
                         q'≤q+Δ')))
                        (sym (ℚ.+Assoc _ _ _) ∙
                         cong (fst ε ℚ.+_) (sym (ℚ.-Distr' _ _)))
                       (ℚ.<-+o 0 (fst ε ℚ.- fst Δ) (q+Δ' ℚ.- q')
                        (ℚ.<→<minus _ _ Δ<ε)))
                   )
               (cong rat (ℚ.·DistL+ (fst L) (fst ε)
                  (ℚ.- (fst Δ ℚ.- (q+Δ' ℚ.- q')))) ∙
                 cong (rat (fst L ℚ.· fst ε) +ᵣ_)
                  (cong rat (sym lem--070))))

 li' : Lipschitz-ℚ→ℝ L (rat ∘ (λ x → fst (f' x)))
 li' = ℚ.elimBy≡⊎<'
  (λ q r X ε u v → sym∼ _ _ _
    (X ε (subst (ℚ.- fst ε ℚ.<_) (ℚ.-[x-y]≡y-x _ _) (ℚ.minus-< _ _ v))
          (subst2 ℚ._<_ (ℚ.-[x-y]≡y-x _ _)
            (ℚ.-Invol _) (ℚ.minus-< _ _ u))))
  (λ q ε _ _ → refl∼ _ _)
  λ q Δ ε u v → sym∼ _ _ _ (invEq (∼≃abs<ε _ _ _)
    (li<' q Δ ε u v))

 ili'< : ∀ x (Δ : ℚ₊) → 
                  fst Δ ℚ.≤
                  fst K  ℚ.· ℚ.abs' (fst (f' x) ℚ.- fst (f' (x ℚ.+ fst Δ)))
 ili'< x Δ = 
   ℚ.isTrans≤ _ _ _
   (ℚ.isTrans≤ _ _ _ (ℚ.isTrans≤ _ _ _
     (ℚ.isTrans≤ _ _ _ (ℚ.≡Weaken≤ _ _ (sym (ℚ.+IdR (fst Δ))))
       (ℚ.≤-o+ _ _ _ (ℚ.≤→<minus _ ((fst K) ℚ.· (f x+Δ' x+Δ'∈ ℚ.- f x' x'∈))
        ((⊎.rec h≡ h< (ℚ.≤→≡⊎< x' x+Δ' x'≤x+Δ'))))))
      (ℚ.≡Weaken≤ _ _
          (cong (fst Δ ℚ.+_) (ℚ.+Comm _ _) ∙ (ℚ.+Assoc _ _ _) ∙ (cong (ℚ._+
             ((fst K) ℚ.· (f x+Δ' x+Δ'∈ ℚ.- f x' x'∈))) (sym (ℚ.y·[x/y] K _)))
           ∙  sym (ℚ.·DistL+ (fst K) _ _)))
       )
      (ℚ.≤-o· _ _ (fst K) (ℚ.0≤ℚ₊ K)
         (ℚ.isTrans≤ _ _ _ (ℚ.≤-+o _ _
          (f x+Δ' x+Δ'∈ ℚ.- f x' x'∈) (ℚ.≤-·o _ _ (fst Δ ℚ.- (x+Δ' ℚ.- x'))
          (ℚ.≤→<minus _ _
           (ℚ.isTrans≤ _ _ _
             (ℚ.clampDiff a b x (x ℚ.+ (fst Δ)) (ℚ.<Weaken≤ _ _ x<x+Δ))
              (ℚ.≡Weaken≤ _ _ lem--063)))
            1/K≤α)) (ℚ.≤abs _))))
   
   (ℚ.≡Weaken≤ _ _ (cong (fst K  ℚ.·_) (cong (ℚ.abs) (sym lem-f') ∙
       ℚ.absComm- _ _ ∙ ℚ.abs'≡abs _)))
  where

  x<x+Δ = (ℚ.<+ℚ₊' x x Δ (ℚ.isRefl≤ x))
  x' = ℚ.clamp a b x
  x'∈ = clam∈ℚintervalℙ a b a≤b x

  x+Δ' = ℚ.clamp a b (x ℚ.+ fst Δ)
  x+Δ'∈ = clam∈ℚintervalℙ a b a≤b (x ℚ.+ fst Δ)

  x'≤x+Δ' : x' ℚ.≤ x+Δ'
  x'≤x+Δ' = ℚ.≤MonotoneClamp a b _ _ (ℚ.<Weaken≤ _ _ x<x+Δ)


  lem-f' : (fst (f' (x ℚ.+ fst Δ)) ℚ.- fst (f' x))
        ≡ (fst α) ℚ.· (fst Δ ℚ.- (x+Δ' ℚ.- x'))
            ℚ.+ (f x+Δ' x+Δ'∈ ℚ.- f x' x'∈)
  lem-f' = lem--069 {fst α}

  from-il = il x+Δ' x+Δ'∈ x' x'∈ 

  h< : x' ℚ.< x+Δ' → (x+Δ' ℚ.- x') ℚ.≤ fst K ℚ.· (f x+Δ' x+Δ'∈ ℚ.- f x' x'∈)
  h< p = ℚ.≮→≥ _ _
    λ p' →
     let pp = from-il (invℚ₊ K ℚ₊· (ℚ.<→ℚ₊ _ _ p))
           (ℚ.isTrans≤< _ _ _
              (ℚ.≡Weaken≤ _ _ ((sym (ℚ.abs'≡abs _) ∙ (ℚ.absPos _
               (ℚ.<→<minus _ _  (monF _ x'∈ _ x+Δ'∈ p ))))
               ∙ sym (ℚ.[y·x]/y K _)))
               (ℚ.<-o· _ _ (fst (invℚ₊ K)) ((ℚ.0<ℚ₊ (invℚ₊ K))) p'))
     in ℚ.isIrrefl<  _ (ℚ.isTrans<≤ _ _ _ pp
         (ℚ.≡Weaken≤ _ _
           ((ℚ.y·[x/y] K _) ∙
            (sym (ℚ.absPos _ (ℚ.<→<minus _ _ p)) ∙ ℚ.abs'≡abs _))))
    
  h≡ : x' ≡ x+Δ' → (x+Δ' ℚ.- x') ℚ.≤ fst K ℚ.· (f x+Δ' x+Δ'∈ ℚ.- f x' x'∈)

  h≡ p = ℚ.≡Weaken≤ _ _ (𝐐'.+InvR' _ _ (sym p) ∙
           sym (ℚ.·AnnihilR (fst K)) ∙
            cong (fst K ℚ.·_) (sym (𝐐'.+InvR' _ _ (f≡ (sym p)))))

 ili' : Invlipschitz-ℚ→ℚ K (λ x → fst (f' x))
 ili' = ℚ.elimBy≡⊎<'
   (λ x y X ε u → ℚ.isTrans≤< _ _ _
       (ℚ.≡Weaken≤ _ _ (ℚ.abs'Comm- _ _))
        (X ε (ℚ.isTrans≤< _ _ _
       (ℚ.≡Weaken≤ _ _ (ℚ.abs'Comm- _ _)) u)) )
   (λ x ε _ → 
       ℚ.isTrans≤< (ℚ.abs' (x ℚ.- x)) 0 _
       (ℚ.≡Weaken≤ _ _ (cong ℚ.abs' (ℚ.+InvR x))) (ℚ.0<ℚ₊ (K ℚ₊· ε))
       )
   λ x Δ ε f'x-f'[x+Δ]<ε → 
     let z = ili'< x Δ
     in ℚ.isTrans≤< (ℚ.abs' (x ℚ.- (x ℚ.+ fst Δ)))
           ((fst K) ℚ.· ℚ.abs' (fst (f' x) ℚ.- fst (f' (x ℚ.+ fst Δ))))
             _ (ℚ.isTrans≤ _ _ _
               (ℚ.≡Weaken≤ _ _ (sym (ℚ.abs'≡abs _)  ∙
                     ℚ.absComm- _ _  
                  ∙∙ cong ℚ.abs lem--063 ∙∙ -- (cong ℚ.abs' lem--072)
                    ℚ.absPos _ (ℚ.0<ℚ₊ Δ) ) )
               z )
            (ℚ.<-o· _ _ (fst K) (ℚ.0<ℚ₊ K) (f'x-f'[x+Δ]<ε)) --ili'<

<ᵣ-o+-cancel : ∀ m n o →  o +ᵣ m <ᵣ o +ᵣ n → m <ᵣ n
<ᵣ-o+-cancel m n o p =
     subst2 (_<ᵣ_) L𝐑.lem--04 L𝐑.lem--04
     (<ᵣ-o+ _ _ (-ᵣ o) p)

absᵣ-triangle-minus : (x y : ℝ) → absᵣ x -ᵣ absᵣ y ≤ᵣ absᵣ (x -ᵣ y)
absᵣ-triangle-minus x y =
  isTrans≡≤ᵣ _ _ _ (cong (_-ᵣ _) (cong absᵣ (sym (L𝐑.lem--05))))
   (a≤c+b⇒a-c≤b _ _ _ (absᵣ-triangle y (x -ᵣ y)))

absᵣ-triangle' : (x y : ℝ) → absᵣ x  ≤ᵣ absᵣ (x -ᵣ y) +ᵣ absᵣ y
absᵣ-triangle' x y =
   isTrans≡≤ᵣ _ _ _ (cong absᵣ (sym (L𝐑.lem--00))) (absᵣ-triangle (x -ᵣ y) y)
  

fromLip-Invlipschitz-ℚ→ℚ' : ∀ L K f
           → (l : Lipschitz-ℚ→ℝ L (rat ∘ f))
           → Invlipschitz-ℚ→ℚ K f
           → Invlipschitz-ℝ→ℝ K 
             (fst (fromLipschitz L ((rat ∘ f) , l)))
fromLip-Invlipschitz-ℚ→ℚ' L K f l il u v ε <ε =
  PT.rec (isProp∼ _ _ _)
    (λ (ε' , fu-fv<ε' , ε'<ε) →
     let ε-ε' = (ℚ.<→ℚ₊ ε' (fst ε) (<ᵣ→<ℚ _ _ ε'<ε))
         δ = /4₊ ε-ε'
         ε'₊ : ℚ₊
         ε'₊ = (ε' , ℚ.<→0< ε' (<ᵣ→<ℚ _ _
                  (isTrans≤<ᵣ 0 _ (rat ε') (0≤absᵣ _) fu-fv<ε')) )
         δ/L⊔K = (ℚ.min₊ K (invℚ₊ L)) ℚ.ℚ₊· δ  
         
         
     in PT.rec2 (isProp∼ _ _ _)
          (λ (u' , u<u' , u'<u+δ/L⊔K)
             (v' , v<v' , v'<v+δ/L⊔K) →
               let L·δ/L⊔K≤δ : rat (fst (L ℚ₊· δ/L⊔K)) ≤ᵣ rat (fst δ)
                   L·δ/L⊔K≤δ =  
                     isTrans≤≡ᵣ _ _ _
                        ((≤ℚ→≤ᵣ _ _
                            ((ℚ.≤-o· _ _ _
                             (ℚ.0≤ℚ₊ L)
                               (ℚ.≤-·o _ _ _ ((ℚ.0≤ℚ₊ δ))
                                 (ℚ.min≤' _ _))))))
                      (cong rat (ℚ.y·[x/y] L (fst δ)))
                   δ/L⊔K≤K·δ : rat (fst δ/L⊔K) ≤ᵣ rat (fst K ℚ.· fst δ)
                   δ/L⊔K≤K·δ = ≤ℚ→≤ᵣ _ _ 
                                  (ℚ.≤-·o (fst (ℚ.min₊ K (invℚ₊ L)))
                                    _ _ ((ℚ.0≤ℚ₊ δ)) (ℚ.min≤ _ _))
                   ∣'u-u∣<δ/L⊔K = (isTrans≡<ᵣ _ _ _
                               (absᵣPos _ (x<y→0<y-x _ _ u<u'))
                               (a<c+b⇒a-c<b _ _ _ u'<u+δ/L⊔K))
                   ∣'v-v∣<δ/L⊔K = (isTrans≡<ᵣ _ _ _
                               (absᵣPos _ (x<y→0<y-x _ _ v<v'))
                               (a<c+b⇒a-c<b _ _ _ v'<v+δ/L⊔K))
                   lU : absᵣ (rat (f u') -ᵣ f𝕣 u)
                           <ᵣ rat (fst δ)
                   lU = isTrans<≤ᵣ _ _ _
                          (fst (∼≃abs<ε _ _ _) $ lf (rat u') u δ/L⊔K
                         (invEq (∼≃abs<ε _ _ _)
                            ∣'u-u∣<δ/L⊔K))
                                L·δ/L⊔K≤δ
                   lV : absᵣ (f𝕣 v -ᵣ rat (f v'))
                           <ᵣ rat (fst δ)
                   lV = isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _) (isTrans<≤ᵣ _ _ _
                          (fst (∼≃abs<ε _ _ _) $ lf (rat v') v δ/L⊔K
                         (invEq (∼≃abs<ε _ _ _)
                            ∣'v-v∣<δ/L⊔K))
                                L·δ/L⊔K≤δ)
                   z< : absᵣ (rat (f u') -ᵣ rat (f v'))
                            
                         <ᵣ (rat (fst δ) +ᵣ rat (fst δ)) +ᵣ rat ε'
                   z< = isTrans<ᵣ _ _ _ (a-b<c⇒a<c+b _ _ _
                          (isTrans≤<ᵣ _ _ _
                            (absᵣ-triangle-minus (rat (f u') -ᵣ rat (f v')) _)
                           (isTrans≤<ᵣ _ _ _
                           (isTrans≡≤ᵣ _ _ _
                             (cong absᵣ (L𝐑.lem--067
                                {rat (f u')} {rat (f v')}))
                               (absᵣ-triangle _ _))
                             (<ᵣMonotone+ᵣ _ _ _ _ lU lV))))
                               (<ᵣ-o+ _ _ _ fu-fv<ε')
                   
                  
                   z : ℚ.abs' (u' ℚ.- v') ℚ.<
                         fst K ℚ.· ((fst δ ℚ.+ fst δ) ℚ.+ ε')
                   z = il u' v' ((δ ℚ.ℚ₊+ δ) ℚ.ℚ₊+ ε'₊) (<ᵣ→<ℚ _ _ z<)
                   zz : absᵣ (u +ᵣ -ᵣ v -ᵣ (rat u' -ᵣ rat v'))
                          ≤ᵣ (rat ((fst K ℚ.· fst δ)
                               ℚ.+ (fst K ℚ.· fst δ)))
                   zz = isTrans≤ᵣ _ _ _
                          (isTrans≡≤ᵣ _ _ _
                            (cong absᵣ (L𝐑.lem--067 {u} {v} {rat u'} {rat v'} ))
                             (absᵣ-triangle _ _))
                          (≤ᵣMonotone+ᵣ _ _ _ _
                            (isTrans≤ᵣ _ _ _
                              (isTrans≡≤ᵣ _ _ _ (minusComm-absᵣ _ _)
                                 (<ᵣWeaken≤ᵣ _ _ ∣'u-u∣<δ/L⊔K)) δ/L⊔K≤K·δ)
                            (isTrans≤ᵣ _ _ _
                              (<ᵣWeaken≤ᵣ _ _ ∣'v-v∣<δ/L⊔K) δ/L⊔K≤K·δ)) 
               in invEq (∼≃abs<ε _ _ _)
                    (isTrans<≡ᵣ _ (rat ((((fst K ℚ.· fst δ)
                               ℚ.+ (fst K ℚ.· fst δ)))
                                      ℚ.+ (fst K ℚ.· ((fst δ ℚ.+ fst δ) ℚ.+ ε')))) _
                      (isTrans≤<ᵣ _ _ _
                        ((absᵣ-triangle' (u +ᵣ -ᵣ v) ((rat u' -ᵣ (rat v')))))
                        (≤<ᵣMonotone+ᵣ _ (rat ((fst K ℚ.· fst δ)
                               ℚ.+ (fst K ℚ.· fst δ)))
                             _ _ zz (<ℚ→<ᵣ _ _ z) ))
                      (cong rat
                        (cong (ℚ._+ (fst K ℚ.· ((fst δ ℚ.+ fst δ) ℚ.+ ε')))
                            (sym (ℚ.·DistL+ _ _ _)) ∙
                           (sym (ℚ.·DistL+ _ _ _)) ∙
                            cong (fst K ℚ.·_)
                             (ℚ.+Assoc _ _ _ ∙
                              cong (ℚ._+ ε')
                               (cong₂ ℚ._+_ (cong fst (ℚ./4₊+/4₊≡/2₊ ε-ε'))
                                 ((cong fst (ℚ./4₊+/4₊≡/2₊ ε-ε'))) ∙
                                  ℚ.ε/2+ε/2≡ε _) ∙ lem--00))))) 
          (denseℚinℝ u (u +ᵣ rat (fst (δ/L⊔K)))
            ( isTrans≡<ᵣ _ _ _ (sym (+IdR u))
               (<ᵣ-o+ _ _ u (<ℚ→<ᵣ 0 _ (ℚ.0<ℚ₊ δ/L⊔K)) )))
          (denseℚinℝ v (v +ᵣ rat (fst (δ/L⊔K)))
             (( isTrans≡<ᵣ _ _ _ (sym (+IdR v))
               (<ᵣ-o+ _ _ v (<ℚ→<ᵣ 0 _ (ℚ.0<ℚ₊ δ/L⊔K)) )))))
    (denseℚinℝ _ _ (fst (∼≃abs<ε _ _ _) <ε))


 where
  lf = snd (fromLipschitz L ((rat ∘ f) , l))

  f𝕣 = fst (fromLipschitz L ((rat ∘ f) , l))
  



fromBilpschitz-ℚ→ℚℙ : ∀ L K → fst (invℚ₊ K) ℚ.≤ fst L →  ∀ a b → (a<b : a ℚ.< b) → ∀ f
           → isIncrasingℙ _ f
           → (l : Lipschitz-ℚ→ℝℙ L (intervalℙ (rat a) (rat b))
              (λ x x₁ → rat (f x (∈intervalℙ→∈ℚintervalℙ a b x x₁))))
           → Invlipschitz-ℚ→ℚℙ K (ℚintervalℙ a b) f
           →  Σ[ g ∈ (∀ x → x ∈ _  → ℝ ) ]
                 ((Lipschitz-ℝ→ℝℙ L (intervalℙ (rat a) (rat b))) g
                  × Invlipschitz-ℝ→ℝℙ K (intervalℙ (rat a) (rat b)) g
                   × (∀ x x∈ ratx∈ → g (rat x) ratx∈ ≡ rat (f x x∈))) 
             
fromBilpschitz-ℚ→ℚℙ L K 1/K≤L a b a<b f incrF l il =
  let (f' , f'-l , f'-il , f≡f') =
         extend-Bilipshitz L K 1/K≤L a b (ℚ.<Weaken≤ _ _ a<b)
            f incrF l il

      (f'' , f''-l) = fromLipschitz L ((rat ∘ f') , f'-l)
      f''-il = fromLip-Invlipschitz-ℚ→ℚ' L K f' f'-l f'-il
  in (λ x _ → f'' x) ,
       (λ u u∈ v v∈ ε x → f''-l u v ε x) ,
       (λ u u∈ v v∈ ε x → f''-il u v ε x) ,
       λ x x∈ ratx∈ → cong rat (f≡f' _ _)

open ℚ.HLP


map-fromCauchySequence' : ∀ L s ics f → (Lipschitz-ℝ→ℝ L f) → 
    Σ _ λ icsf →
      f (fromCauchySequence' s ics) ≡ fromCauchySequence' (f ∘ s) icsf
map-fromCauchySequence' L s ics f lf =
  icsf , sym (fromCauchySequence'≡ _ _ _ h)

 where

 icsf : IsCauchySequence' (f ∘ s)
 icsf ε = map-snd
   (λ X m n <m <n →
      let z = X m n <m <n
          z' = lf (s n) (s m) (invℚ₊ L ℚ₊· ε)
                (invEq (∼≃abs<ε _ _ _) z)
       in fst (∼≃abs<ε _ _ ε) (subst∼ (ℚ.y·[x/y] L (fst ε)) z'))
   (ics (invℚ₊ L ℚ₊· ε))  

 h : (ε : ℚ₊) →
       ∃-syntax ℕ
       (λ N →
          (n : ℕ) →
          N ℕ.< n →
          absᵣ ((f ∘ s) n -ᵣ f (fromCauchySequence' s ics)) <ᵣ rat (fst ε))
 h ε =
   let (N , X) = ics ((invℚ₊ L ℚ₊· (/4₊ ε)))
       (N' , X') = icsf (/4₊ ε)
       midN = suc (ℕ.max N N')
       midV = f (s midN)
       
   in ∣ midN , (λ n midN<n →
        let 3ε/4<ε = subst (ℚ._< (fst ε))
                 (cong (fst (/4₊ ε) ℚ.+_)
                   (sym (ℚ.y·[x/y] L _)
                    ∙ cong (fst L ℚ.·_) (ℚ.·DistL+ _ _ _) ))
                    distℚ<! ε [ ((ge[ ℚ.[ 1 / 4 ] ]) +ge
                        (ge[ ℚ.[ 1 / 4 ] ] +ge ge[ ℚ.[ 1 / 4 ] ]))
                        < ge1 ]
            z' = invEq (∼≃abs<ε _ _ (/4₊ ε)) (X' ((suc N')) n
                 (ℕ.<-trans (ℕ.suc-≤-suc ℕ.right-≤-max) midN<n)
                  ℕ.≤-refl )
            
            zzzz' = 
                (𝕣-lim-self _ (fromCauchySequence'-isCA s ics)
                      ((invℚ₊ L ℚ₊· (/4₊ ε))) ( (invℚ₊ L ℚ₊· (/4₊ ε))))
            
        in fst (∼≃abs<ε _ _ ε)
             (∼-monotone< 3ε/4<ε
                (triangle∼ z' (lf _ _ _ zzzz')))) ∣₁


record IsBilipschitz a b  (a<b : a ℚ.< b) f : Type where
 field
  incrF : isIncrasingℙ (ℚintervalℙ a b) f
  L K : ℚ₊
  1/K≤L : fst (invℚ₊ K) ℚ.≤ fst L
  
  lipF : Lipschitz-ℚ→ℝℙ L (intervalℙ (rat a) (rat b))
              (λ x x₁ → rat (f x (∈intervalℙ→∈ℚintervalℙ a b x x₁)))
  lip⁻¹F : Invlipschitz-ℚ→ℚℙ K (ℚintervalℙ a b) f

 fa = f a (ℚ.isRefl≤ a , ℚ.<Weaken≤ a b a<b)
 fb = f b (ℚ.<Weaken≤ a b a<b , ℚ.isRefl≤ b)

 fa<fb : fa ℚ.< fb
 fa<fb = incrF
   a (ℚ.isRefl≤ a , ℚ.<Weaken≤ a b a<b)
   b (ℚ.<Weaken≤ a b a<b , ℚ.isRefl≤ b)
   a<b
 
 a≤b = ℚ.<Weaken≤ _ _ a<b
 Δ₀ = b ℚ.- a
 Δ₀₊ = ℚ.<→ℚ₊ _ _ a<b 


 ebl = extend-Bilipshitz
   L K  1/K≤L a b (ℚ.<Weaken≤ a b a<b) f incrF lipF lip⁻¹F

 fl-ebl = fromLipschitz L ((rat ∘ (fst ebl)) , fst (snd ebl))

 fl-ebl∈ : ∀ y →
             y ∈ ℚintervalℙ a b →
              fst fl-ebl ((rat y)) ∈ intervalℙ (rat fa) (rat fb) 
 fl-ebl∈ y y∈ = isTrans≤≡ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ z)
       (sym p) , isTrans≡≤ᵣ _ _ _ p  (≤ℚ→≤ᵣ _ _ z')
  where
   p = (cong rat (ebl .snd .snd .snd y y∈))
   z = (isIncrasingℙ→isNondecrasingℙ _ _ incrF)
          a ((ℚ.isRefl≤ _) , a≤b) y y∈ (fst y∈)


   z' = (isIncrasingℙ→isNondecrasingℙ _ _ incrF)
          y y∈ b (a≤b , (ℚ.isRefl≤ _)) (snd y∈)

 record Step (y Δ : ℚ) : Type where
  field
   a' b' : ℚ
   a'<b' : a' ℚ.< b'
   b'-a'≤Δ : b' ℚ.- a' ℚ.≤ Δ 
   a'∈ : a' ∈ ℚintervalℙ a b
   b'∈ : b' ∈ ℚintervalℙ a b
   a'≤ : f a' a'∈ ℚ.≤ y
   ≤b' : y ℚ.≤ f b' b'∈

  a'≤b' : a' ℚ.≤ b'
  a'≤b' = ℚ.<Weaken≤ _ _ a'<b'


  mid : ℚ
  mid = b' ℚ.· [ 1 / 2 ] ℚ.+ a' ℚ.· [ 1 / 2 ]

  p = ℚ.<-·o _ _ [ 1 / 2 ] (ℚ.decℚ<? {0} {[ 1 / 2 ]}) a'<b'

  a'<mid : a' ℚ.< mid
  a'<mid = ℚ.isTrans≤< _ _ _
    (ℚ.≡Weaken≤ _ _ (sym (ℚ.·IdR a') ∙ cong (a' ℚ.·_) ℚ.decℚ? ∙
      ℚ.·DistL+ a' _ _))
    (ℚ.<-+o _ _ (a' ℚ.· [ 1 / 2 ]) p) 

  mid<b' : mid ℚ.< b' 
  mid<b' = ℚ.isTrans<≤ _ _ _    
    (ℚ.<-o+ _ _ (b' ℚ.· [ 1 / 2 ]) p) 
    (ℚ.≡Weaken≤ _ _ (sym (ℚ.·DistL+ b' _ _) ∙ cong (b' ℚ.·_) ℚ.decℚ? ∙
      ℚ.·IdR b'))
  mid∈ : mid ∈ ℚintervalℙ a b
  mid∈ = ℚ.isTrans≤ _ _ _ (fst (a'∈)) (ℚ.<Weaken≤ _ _ a'<mid) ,
          ℚ.isTrans≤ _ _ _ (ℚ.<Weaken≤ _ _ mid<b') (snd b'∈)

  fMid = f mid mid∈


 record Step⊃Step {y Δ ΔS : _} (s : Step y Δ) (sS : Step y ΔS) : Type where
  
  field
   a'≤a'S : Step.a' s ℚ.≤ Step.a' sS 
   bS≤b' : Step.b' sS ℚ.≤ Step.b' s
   -- distA' : (Step.a' sS) ℚ.≤ Δ ℚ.· [ 1 / 2 ] ℚ.+ (Step.a' s)
 
 module _ (y : ℚ) (y∈ : rat y ∈ (intervalℙ (rat fa) (rat fb))) where
   
  step0 : Step y Δ₀
  step0 .Step.a' = a
  step0 .Step.b' = b
  step0 .Step.a'<b' = a<b
  step0 .Step.b'-a'≤Δ = ℚ.isRefl≤ _
  step0 .Step.a'∈ = ℚ.isRefl≤ _  , a≤b
  step0 .Step.b'∈ = a≤b , (ℚ.isRefl≤ _)
  step0 .Step.a'≤ = ≤ᵣ→≤ℚ _ _ (fst y∈) 
  step0 .Step.≤b' = ≤ᵣ→≤ℚ _ _ (snd y∈)

  stepS' : ∀ Δ → (s : Step y Δ) → Σ (Step y (Δ ℚ.· [ 1 / 2 ])) (Step⊃Step s)
  stepS' Δ s = w (ℚ.Dichotomyℚ y fMid)
   where
   open Step s

   a'-mid≤Δ/2 : (mid ℚ.- a') ℚ.≤ Δ ℚ.· [ 1 / 2 ]
   a'-mid≤Δ/2 = 
     ℚ.isTrans≤ _ _ _
      (ℚ.≡Weaken≤ (mid ℚ.- a') ((b' ℚ.- a') ℚ.· [ 1 / 2 ])
        (sym (ℚ.+Assoc _ _ _) ∙
         cong (b' ℚ.· [ 1 / 2 ] ℚ.+_)
          (cong (a' ℚ.· [ 1 / 2 ] ℚ.+_) (ℚ.·Comm -1 a')
           ∙ sym (ℚ.·DistL+ a' _ _) ∙
            ℚ.·Comm _ _ ∙
             sym (ℚ.·Assoc [ 1 / 2 ] -1 a') ∙  ℚ.·Comm [ 1 / 2 ] _)
          ∙ sym (ℚ.·DistR+ _ _ _)))
      (ℚ.≤-·o _ _ _ (ℚ.decℚ≤? {0} {[ 1 / 2 ]}) b'-a'≤Δ)

   w : (y ℚ.≤ fMid) ⊎ (fMid ℚ.< y) → Σ (Step y (Δ ℚ.· [ 1 / 2 ]))
             (Step⊃Step s) 
   w (inl x) .fst .Step.a' = a'
   w (inl x) .fst .Step.b' = mid
   w (inl x) .fst .Step.a'<b' = a'<mid
   w (inl x) .fst .Step.b'-a'≤Δ = a'-mid≤Δ/2
   w (inl x) .fst .Step.a'∈ = a'∈
   w (inl x) .fst .Step.b'∈ = mid∈ 
   w (inl x) .fst .Step.a'≤ = a'≤
   w (inl x) .fst .Step.≤b' = x
   w (inl x) .snd .Step⊃Step.a'≤a'S = ℚ.isRefl≤ a'
   w (inl x) .snd .Step⊃Step.bS≤b' = ℚ.<Weaken≤ _ _ mid<b'
   w (inr x) .fst .Step.a' = mid
   w (inr x) .fst .Step.b' = b'
   w (inr x) .fst .Step.a'<b' = mid<b'
   w (inr x) .fst .Step.b'-a'≤Δ =
     ℚ.isTrans≤ _ _ _
        (ℚ.≡Weaken≤ (b' ℚ.- mid)
                    ((b' ℚ.- a') ℚ.· [ 1 / 2 ])
                      ((cong (b' ℚ.+_) (ℚ.-Distr _ _ ) ∙
                       ℚ.+Assoc _ _ _ ∙
                        cong₂ ℚ._+_
                        (cong₂ ℚ._+_ (sym (ℚ.·IdR b'))
                         (ℚ.·Comm -1 _ ∙ sym (ℚ.·Assoc _ _ _))
                         ∙ sym (ℚ.·DistL+ b' 1 [ -1 / 2 ]))
                         (ℚ.·Assoc -1 _ _))
                       ∙ sym (ℚ.·DistR+ _ _ _)))
          (ℚ.≤-·o _ _ _ (ℚ.decℚ≤? {0} {[ 1 / 2 ]}) b'-a'≤Δ)

   w (inr x) .fst .Step.a'∈ = mid∈
   w (inr x) .fst .Step.b'∈ = b'∈
   w (inr x) .fst .Step.a'≤ = ℚ.<Weaken≤ _ _ x
   w (inr x) .fst .Step.≤b' = ≤b'
   w (inr x) .snd .Step⊃Step.a'≤a'S = ℚ.<Weaken≤ _ _  a'<mid
   w (inr x) .snd .Step⊃Step.bS≤b' = ℚ.isRefl≤ b'
   
  stepS : ∀ Δ → Step y Δ → Step y (Δ ℚ.· [ 1 / 2 ])
  stepS Δ s = fst (stepS' Δ s)
  
  ww : ∀ n → Step y (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n))
  ww zero = subst (Step y) (sym (ℚ.·IdR Δ₀)) step0
  ww (suc n) = subst (Step y) (sym (ℚ.·Assoc _ _ _)) (stepS _ (ww n))

  s : ℕ → ℚ
  s = Step.a' ∘ ww

  s' : ℕ → ℚ
  s' = Step.b' ∘ ww


  ss≤-suc : ∀ n (z : Step y (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n))) → Step.a' z ℚ.≤
      Step.a' (subst (Step y) (sym (ℚ.·Assoc _ _ _)) (stepS
       (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n)) z))
  ss≤-suc n z = ℚ.isTrans≤ _ _ _ (Step⊃Step.a'≤a'S (snd (stepS'
       (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n)) z)))
         (ℚ.≡Weaken≤ _ _ (sym (transportRefl _)))

  ≤ss'-suc : ∀ n (z : Step y (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n))) →  
       Step.b' (subst (Step y) (sym (ℚ.·Assoc _ _ _)) (stepS
       (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n)) z))
      ℚ.≤
       Step.b' z
  ≤ss'-suc n z =  ℚ.isTrans≤ _ _ _ 
         (ℚ.≡Weaken≤ _ _  (transportRefl _))
           ((Step⊃Step.bS≤b' (snd (stepS'
       (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n)) z))))
  ss≤ : ∀ n m → s n ℚ.≤ s (m ℕ.+ n) 
  ss≤ n zero = ℚ.isRefl≤ _ 
  ss≤ n (suc m) = ℚ.isTrans≤ _ _ _ (ss≤ n m) (ss≤-suc (m ℕ.+ n) (ww (m ℕ.+ n)))

  ≤ss' : ∀ n m →  s' (m ℕ.+ n) ℚ.≤ s' n 
  ≤ss' n zero = ℚ.isRefl≤ _ 
  ≤ss' n (suc m) = ℚ.isTrans≤ _ _ _
    (≤ss'-suc (m ℕ.+ n) (ww (m ℕ.+ n))) (≤ss' n m)


  ww⊂ : ∀ n m → (s (m ℕ.+ n) ℚ.- s n) ℚ.≤ Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ n)
  ww⊂ n m = ℚ.isTrans≤
    (s (m ℕ.+ n) ℚ.- s n) (s' n ℚ.- s n) _
      (ℚ.≤-+o (s (m ℕ.+ n)) (s' n) (ℚ.- (s n))
       (ℚ.isTrans≤ _ _ _ (Step.a'≤b' (ww (m ℕ.+ n))) (≤ss' n m)))
   (Step.b'-a'≤Δ (ww n))
    
  www : {ε : ℚ₊} → (Σ[ n ∈ ℕ ] [ 1 / 2 ] ℚ^ⁿ n ℚ.<
            fst (ε ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)))
         → Σ[ N ∈ ℕ ] (∀ m n → N ℕ.< n → N ℕ.< m →
              absᵣ (rat (s n) -ᵣ rat (s m)) <ᵣ rat (fst ε)   )
  www (N , P) .fst = N
  www {ε} (N , P) .snd = ℕ.elimBy≤+
    (λ n m X m< n< → subst (_<ᵣ (rat (fst ε)))
      (minusComm-absᵣ (rat (s m)) (rat (s n))) (X n< m<))
    λ n m p N<n →
      let P' : Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ N) ℚ.< fst ε
          P' = ℚ.isTrans<≤ _ _ (fst ε) (ℚ.<-o· _ _ _ (ℚ.-< a b a<b) P)
                 (ℚ.≡Weaken≤ _ _
                    ((cong (fst (ℚ.<→ℚ₊ a b a<b) ℚ.·_) (ℚ.·Comm _ _))
                     ∙ ℚ.y·[x/y] (ℚ.<→ℚ₊ _ _ a<b) (fst ε)))
          zz = ℚ.isTrans≤< _ _ _
                  (ℚ.isTrans≤ _ ((s (m ℕ.+ n)) ℚ.- (s n)) _
                    (ℚ.≡Weaken≤ _ _ (ℚ.absNonNeg (s (m ℕ.+ n) ℚ.- s n)
                      (ℚ.-≤ (s n) (s (m ℕ.+ n)) (ss≤ n m))))
                      (ww⊂ n m))
                  (ℚ.isTrans< _ (Δ₀ ℚ.· ([ 1 / 2 ] ℚ^ⁿ (N))) _
                    (ℚ.<-o· _ _ Δ₀ (ℚ.-< a b a<b) (<^n N n N<n)) P')
      in isTrans≡<ᵣ _ _ _ (cong rat (sym (ℚ.abs'≡abs _)))
           (<ℚ→<ᵣ _ _ zz) 

  f⁻¹ : ℝ
  f⁻¹ = fromCauchySequence' (rat ∘ s)
        λ ε → www {ε} (1/2ⁿ<ε (ε ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)))



  s~y : (ε : ℚ₊) →
          ∃-syntax ℕ
          (λ N →
             (n : ℕ) →
             N ℕ.< n →
             absᵣ ((fst fl-ebl ∘ (λ x → rat (s x))) n -ᵣ rat y) <ᵣ rat (fst ε))
  s~y ε = 
    let (N , X) = (1/2ⁿ<ε (invℚ₊ (L ℚ₊· Δ₀₊) ℚ₊· ε))
        
    in ∣ suc N ,
       (λ { zero x → ⊥.rec (ℕ.¬-<-zero x)
          ; (suc n) x →
             let 𝒔 = ww (suc n)
                 q = fst ((∼≃abs<ε _ _ _)) $
                     snd fl-ebl (rat (Step.b' 𝒔)) (rat (Step.a' 𝒔))
                       ((Δ₀₊ ℚ₊· (([ 1 / 2 ] , _) ℚ₊^ⁿ n)))
                        (invEq (∼≃abs<ε _ _ _)
                         (isTrans≡<ᵣ _ _ _
                           (absᵣPos _ (<ℚ→<ᵣ _ _
                             (ℚ.<→<minus _ _ (Step.a'<b' 𝒔)))
                            ) (<ℚ→<ᵣ _ _
                           (ℚ.isTrans≤< _ _ _
                              (Step.b'-a'≤Δ 𝒔)
                                 (ℚ.<-o· _ _ Δ₀ (ℚ.0<ℚ₊ Δ₀₊) (<^n _ _ ℕ.≤-refl )))  )))
             in isTrans<ᵣ _ _ _ (isTrans≤<ᵣ _ _ _
                   (isTrans≡≤ᵣ _ _ _
                     (minusComm-absᵣ
                      ((fst fl-ebl ∘ (λ x → rat (s x))) (suc n))
                        (rat y) ∙
                          absᵣNonNeg _
                           (≤ℚ→≤ᵣ _ _ (ℚ.≤→<minus _ _ (
                               (ℚ.isTrans≤ _ _ _ 
                                   (ℚ.≡Weaken≤ _ _
                                    ((snd (snd (snd ebl)) _ _)) )
                                    (Step.a'≤ 𝒔))))))
                      (isTrans≤≡ᵣ _ _ _
                        (≤ᵣ-+o _ _ (-ᵣ fst fl-ebl (rat (s (suc n))))
                          (isTrans≤≡ᵣ _ _ _
                            (≤ℚ→≤ᵣ _ _ (Step.≤b' (ww (suc n))))
                            (cong rat (sym (snd (snd (snd ebl)) _ _)))))
                       (sym (absᵣPos _
                         (<ℚ→<ᵣ _ _
                          (ℚ.<→<minus _ _
                            (subst2 ℚ._<_ (sym (snd (snd (snd ebl)) _ _))
                              (sym ((snd (snd (snd ebl)) _ _)))
                              (incrF _ (Step.a'∈ 𝒔) _
                               (Step.b'∈ 𝒔)
                               (Step.a'<b' 𝒔)))))))))
                   q)
       
                 (isTrans<ᵣ _ _ _
                    
                    (isTrans≡<ᵣ _ _ _ (cong rat (ℚ.·Assoc _ _ _)) (<ℚ→<ᵣ _ _
                       ( ℚ.<-o· _ _ (fst (L ℚ₊· Δ₀₊))
                           ((ℚ.0<ℚ₊ (L ℚ₊· Δ₀₊)))
                            (<^n _ _ (ℕ.pred-≤-pred x)))))
                    (isTrans<≡ᵣ _ _ _
                      (<ℚ→<ᵣ _ _ (ℚ.<-o· _ _ (fst (L ℚ₊· Δ₀₊))
                       (ℚ.0<ℚ₊ (L ℚ₊· Δ₀₊) ) X))
                        (cong rat (ℚ.y·[x/y] (L ℚ₊· Δ₀₊) (fst ε))))
                     )}) ∣₁

  f⁻¹∈ : f⁻¹ ∈ intervalℙ (rat a) (rat b)
  f⁻¹∈ = ((≤lim _ _ _
           λ δ → ≤ℚ→≤ᵣ _ _ $ fst (Step.a'∈
            (ww (suc (1/2ⁿ<ε (δ ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)) .fst))))))
     , (lim≤ _ _ _
           λ δ → ≤ℚ→≤ᵣ _ _ $ snd (Step.a'∈
            (ww (suc (1/2ⁿ<ε (δ ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)) .fst)))))


  f∘f⁻¹ : fst fl-ebl f⁻¹
      ≡ rat y
  f∘f⁻¹ = snd (map-fromCauchySequence'
      L (rat ∘ s)
        (λ ε → www {ε} (1/2ⁿ<ε (ε ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b))))
         ( fst fl-ebl) (snd fl-ebl)) ∙
           fromCauchySequence'≡ _ _ _
      s~y

 

 f⁻¹-L : Lipschitz-ℚ→ℝℙ K (intervalℙ
                 (rat (f a (ℚ.isRefl≤ _  , ℚ.<Weaken≤ a b a<b)))
                 (rat (f b (ℚ.<Weaken≤ _ _ a<b , (ℚ.isRefl≤ _))))) f⁻¹
 f⁻¹-L y y∈ r r∈ ε x = 
   let ilℝ = fst (snd (snd
        ((fromBilpschitz-ℚ→ℚℙ L K  1/K≤L a b a<b f incrF lipF lip⁻¹F)))) 
       z = ilℝ (f⁻¹ y y∈) (f⁻¹∈ y y∈) (f⁻¹ r r∈) (f⁻¹∈ r r∈) ε
           (invEq (∼≃abs<ε _ _ _)
             (isTrans≡<ᵣ _ _ _ (cong absᵣ
               (cong₂ _-ᵣ_  (f∘f⁻¹ y y∈) (f∘f⁻¹ r r∈))
                    ∙ cong rat (sym (ℚ.abs'≡abs (y ℚ.- r))))
               (<ℚ→<ᵣ (ℚ.abs (y ℚ.- r)) (fst ε) x)))
   in fst (∼≃abs<ε _ _ _) z

 ext-f⁻¹ = extend-Lipshitzℚ→ℝ K fa fb (ℚ.<Weaken≤ _ _ fa<fb) f⁻¹ f⁻¹-L

 f⁻¹R-L : Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ K)
 f⁻¹R-L = fromLipschitz K (map-snd fst ext-f⁻¹)

 𝒇⁻¹ = fst f⁻¹R-L
 𝒇 = fst fl-ebl

 𝒇∘𝒇⁻¹' : ∀ y 
            → fst fl-ebl (fst f⁻¹R-L (clampᵣ (rat fa) (rat fb) y)) ≡
               (clampᵣ (rat fa) (rat fb) y)
 𝒇∘𝒇⁻¹' = ≡Continuous _ _ (IsContinuous∘ _ _
        (IsContinuous∘ _ _
          (Lipschitz→IsContinuous L (fst fl-ebl) (snd fl-ebl))
          (Lipschitz→IsContinuous K (fst f⁻¹R-L) (snd f⁻¹R-L)))
       (IsContinuousClamp (rat fa) (rat fb)))
  (IsContinuousClamp (rat fa) (rat fb))
    λ r → (cong (fst fl-ebl) (snd (snd ext-f⁻¹) _
          ((∈ℚintervalℙ→∈intervalℙ _ _ _ (clam∈ℚintervalℙ fa fb
             (ℚ.<Weaken≤ _ _ fa<fb) r)))))
         ∙ f∘f⁻¹ _ _


 𝒇∘𝒇⁻¹ : ∀ y → y ∈ intervalℙ (rat fa) (rat fb)
            → fst fl-ebl (fst f⁻¹R-L y) ≡ y
 𝒇∘𝒇⁻¹ = elimInClampsᵣ (rat fa) (rat fb) 𝒇∘𝒇⁻¹'

 invl𝒇 : Invlipschitz-ℝ→ℝ K (fst fl-ebl)
 invl𝒇 = fromLipInvLip K L (fst ebl) (fst (snd ebl))
       (fst (snd (snd ebl))) 

 inj𝒇 : (x y : ℝ) → fst fl-ebl x ≡ fst fl-ebl y → x ≡ y
 inj𝒇 = Invlipschitz-ℝ→ℝ→injective K (fst fl-ebl) invl𝒇


 𝒇∈ : ∀ x → x ∈ intervalℙ (rat a) (rat b)
          →  fl-ebl .fst x ∈ intervalℙ (rat fa) (rat fb)
 𝒇∈ = cont-f∈ (fl-ebl .fst) (Lipschitz→IsContinuous L _ (snd fl-ebl))
         a b a≤b (rat fa) (rat fb)
          (≤ℚ→≤ᵣ fa fb (ℚ.<Weaken≤ fa fb fa<fb))
         λ x → fl-ebl∈ x ∘S ∈intervalℙ→∈ℚintervalℙ _ _ x

 𝒇⁻¹∘𝒇' : ∀ y 
            → fst f⁻¹R-L (fst fl-ebl  (clampᵣ (rat a) (rat b) y)) ≡
               (clampᵣ (rat a) (rat b) y)
 𝒇⁻¹∘𝒇' y = inj𝒇 _ _
    (𝒇∘𝒇⁻¹ (fst fl-ebl  (clampᵣ (rat a) (rat b) y))
       (𝒇∈ (clampᵣ (rat a) (rat b) y)
          (clampᵣ∈ℚintervalℙ _ _ (≤ℚ→≤ᵣ _ _ a≤b) y)))


 𝒇⁻¹∘𝒇 : ∀ y →  y ∈ intervalℙ (rat a) (rat b)
            → fst f⁻¹R-L (fst fl-ebl  y) ≡ y
 𝒇⁻¹∘𝒇 = elimInClampsᵣ (rat a) (rat b) 𝒇⁻¹∘𝒇'



 𝒇⁻¹∈ : ∀ x → x ∈ intervalℙ (rat fa) (rat fb)
          →  f⁻¹R-L .fst x ∈ intervalℙ (rat a) (rat b)
 𝒇⁻¹∈ =
    cont-f∈ (f⁻¹R-L .fst) (Lipschitz→IsContinuous K _ (snd f⁻¹R-L))
         fa fb (ℚ.<Weaken≤ fa fb fa<fb) (rat a) (rat b)
          (≤ℚ→≤ᵣ a b a≤b)
         λ r → subst-∈ (intervalℙ (rat a) (rat b))
           (sym (snd (snd ext-f⁻¹) _ _))
                 ∘ f⁻¹∈ r 

 
 isoF : Iso (Σ _ (_∈ intervalℙ (rat a) (rat b)))
            (Σ _ (_∈ intervalℙ (rat fa) (rat fb)))
 isoF .Iso.fun (x , x∈) = 𝒇 x , 𝒇∈ x x∈ 
 isoF .Iso.inv (x , x∈) = 𝒇⁻¹ x , 𝒇⁻¹∈ x x∈ 
 isoF .Iso.rightInv (x , x∈) =
   Σ≡Prop (∈-isProp (intervalℙ (rat fa) (rat fb)))
     (𝒇∘𝒇⁻¹ x x∈) 
 isoF .Iso.leftInv (x , x∈) =
   Σ≡Prop (∈-isProp (intervalℙ (rat a) (rat b)))
     (𝒇⁻¹∘𝒇 x x∈)
