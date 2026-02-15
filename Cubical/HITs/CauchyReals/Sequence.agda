module Cubical.HITs.CauchyReals.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

import Cubical.Functions.Logic as L


open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
import Cubical.Data.Fin as F
open import Cubical.Data.Fast.Int as ℤ using (pos)
import Cubical.Data.Fast.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals.Fast as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Fast.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡  ; [_/_]₊)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base

open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.CommRing.Instances.Fast.Int
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
import Cubical.Algebra.Ring.BigOps
import Cubical.Data.FinData as FD


open import Cubical.Tactics.CommRingSolverFast.RationalsReflection
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection
open import Cubical.Tactics.CommRingSolverFast.IntReflection
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.Tactics.CommRingSolverFast.RealsReflection



Dichotomyℝ' : ∀ x y z → x <ᵣ z →
              ∥ (y <ᵣ z) ⊎ (x <ᵣ y) ∥₁
Dichotomyℝ' x y z x<z =
  PT.map2
   (λ (q  , x<q  , q<x+Δ)
      (q' , y-Δ<q' , q'<y)
     → ⊎.map
         (λ q'≤q →
           isTrans<ᵣ _ _ _
             (a-b<c⇒a<c+b _ _ _ y-Δ<q')
             (isTrans<≡ᵣ _ _ _
               (<ᵣ-+o _ _ _
                 ((isTrans≤<ᵣ _ _ _ (≤ℚ→≤ᵣ q' _ q'≤q)
                  q<x+Δ ))) ℝ!))
         (λ q<q' →
           isTrans<ᵣ _ _ _ (isTrans<ᵣ _ _ _
               x<q
               (<ℚ→<ᵣ q _ q<q'))
             q'<y)
         (ℚ.Dichotomyℚ q' q))
    (denseℚinℝ x (x +ᵣ (fst Δ₊))
      (isTrans≡<ᵣ _ _ _
        (sym (+IdR x)) (<ᵣ-o+ _ _ _ (snd Δ₊))))
    (denseℚinℝ (y -ᵣ (fst Δ₊)) y
      (isTrans<≡ᵣ _ _ _
         (<ᵣ-o+ _ _ _
           (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ (snd Δ₊)) (-ᵣ-rat 0)))
         (+IdR y)))

 where
 Δ₊ : ℝ₊
 Δ₊ = (z -ᵣ x , x<y→0<y-x _ _ x<z) ₊·ᵣ ℚ₊→ℝ₊ ([ 1 / 2 ]₊)


fromPositive·ᵣ : ∀ {a b} → 0 ≤ᵣ a → 0 ≤ᵣ b → 0 <ᵣ a ·ᵣ b  → 0 <ᵣ b  
fromPositive·ᵣ {a} {b} 0≤a 0≤b 0<a·b =
 PT.rec (isProp<ᵣ _ _) (⊎.rec
   (λ a<1 → isTrans<≤ᵣ _ _ _
       0<a·b
       (isTrans≤≡ᵣ _ _ _
         (≤ᵣ-·ᵣo a 1 b 0≤b (<ᵣWeaken≤ᵣ _ _ a<1))
         (·IdL b)))
   (flip (invEq ∘ curry (0<x≃0<y₊·x b) a) 0<a·b))
   (Dichotomyℝ' 0 a 1 decℚ<ᵣ?)


-- opaque
--  unfolding _<ᵣ_
x<δ→x≤0 : ∀ x → ((ε : ℚ₊) → x <ᵣ (rat (fst ε))) → x ≤ᵣ 0
x<δ→x≤0 x p = ≡→≤ᵣ (eqℝ _ _
  λ ε → invEq (∼≃abs<ε _ _ _)
    (isTrans≡<ᵣ _ _ _
      
        (cong absᵣ (ℝ! ∙ maxᵣComm _ _)
          ∙ (absᵣNonNeg _ (≤maxᵣ 0 x)) ∙ maxᵣComm _ _)
          (p' ε)))
  where
  p' : (ε : ℚ₊) → maxᵣ x 0 <ᵣ (rat (fst ε))
  p' ε = max<-lem _ _ _  (p ε) (snd (ℚ₊→ℝ₊ ε))


x<y+δ→x≤y : ∀ x y → ((ε : ℚ₊) → x <ᵣ y +ᵣ (rat (fst ε))) → x ≤ᵣ y
x<y+δ→x≤y x y p = invEq (x≤y≃0≤y-x _ _)
 ( isTrans≤≡ᵣ _ _ _
   (isTrans≡≤ᵣ _ _ _ ℝ! (-ᵣ≤ᵣ _ 0 (x<δ→x≤0 _ (a<c+b⇒a-c<b _ _ _ ∘ p)))) -- 
   (-[x-y]≡y-x _ _))


absᵣ-triangle-midpt
       : (x z y : ℝ) →  absᵣ (x -ᵣ y) ≤ᵣ absᵣ (x -ᵣ z) +ᵣ absᵣ (z -ᵣ y)
absᵣ-triangle-midpt x z y =
  isTrans≡≤ᵣ _ _ _
    (cong absᵣ ℝ!)
    (absᵣ-triangle (x -ᵣ z) (z -ᵣ y))


≤ᵣ→≯ᵣ : ∀ x y →  x ≤ᵣ y → (y <ᵣ x) → ⊥
≤ᵣ→≯ᵣ x y x≤y y<x =
 let x=y = isAntisym≤ᵣ x y x≤y (<ᵣWeaken≤ᵣ _ _ y<x)
 in isAsym<ᵣ y x y<x (subst2 _<ᵣ_ (sym x=y) x=y y<x)



≯ᵣ→≤ᵣ : ∀ x y →  ((y <ᵣ x) → ⊥) → x ≤ᵣ y
≯ᵣ→≤ᵣ x y f = x<y+δ→x≤y _ _
  λ ε → PT.rec (isProp<ᵣ _ _)
      (⊎.rec (idfun _) (⊥.rec ∘ f ))
       (Dichotomyℝ' y x (y +ᵣ (rat (fst ε)))
        (isTrans≡<ᵣ _ _ _ (sym (+IdR _)) (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ ε)))))

≤ᵣ≃≯ᵣ : ∀ x y →  (x ≤ᵣ y) ≃ ((y <ᵣ x) → ⊥)
≤ᵣ≃≯ᵣ _ _ = propBiimpl→Equiv (isProp≤ᵣ _ _)
  (isPropΠ λ _ → isProp⊥)
  (≤ᵣ→≯ᵣ _ _) (≯ᵣ→≤ᵣ _ _)



≡-byContracdition : ∀ x y → ((ε : ℚ₊) → rat (fst ε) <ᵣ absᵣ (x -ᵣ y) → ⊥ )
                      → x ≡ y
≡-byContracdition x y X =
  eqℝ _ _ λ ε →
    PT.rec (isProp∼ _ _ _)
        (⊎.rec (invEq (∼≃abs<ε _ _ ε))
         (⊥.rec ∘ X (/2₊ ε)) )
      (Dichotomyℝ' (fst (ℚ₊→ℝ₊ (/2₊ ε))) (absᵣ (x -ᵣ y)) (fst (ℚ₊→ℝ₊ ε))
       (<ℚ→<ᵣ _ _ (x/2<x ε)))

continous-＃ : ∀ P f → IsContinuousWithPred P f
                → ∀ x y x∈ y∈ → (f x x∈) ＃ (f y y∈) → x ＃ y 
continous-＃ P f fic x y x∈ y∈ fx＃fy =
 let z = fst (＃≃0<dist _ _) fx＃fy
 in PT.rec (isProp＃ _ _)
     (λ (q , (0<q , q<fx-fy)) →
       PT.rec (isProp＃ _ _)
         (λ (δ , Δ) → 
           PT.rec (isProp＃ _ _)
            (⊎.rec (λ u → ⊥.rec (isAsym<ᵣ _ _
              (fst (∼≃abs<ε _ _ _) (Δ y y∈ (invEq (∼≃abs<ε _ _ _) u)))
               q<fx-fy) ) (invEq (＃≃0<dist _ _)))
             (Dichotomyℝ' 0 (absᵣ (x -ᵣ y)) (rat (fst δ)) (<ℚ→<ᵣ _ _ (snd δ))))
         (fic x (q , <ᵣ→<ℚ _ _ 0<q) x∈))
     (denseℚinℝ _ _ z)

record 3-⊎-prop-elim {ℓa ℓb ℓ} (A : Type ℓa) (B : Type ℓb)
           (X : A ⊎ B → A ⊎ B → A ⊎ B → Type ℓ)  : Type (ℓ-max (ℓ-max ℓa ℓb) ℓ) where
 field
  isPropA : isProp A
  isPropB : isProp B
  aaa : ∀ a → X (inl a) (inl a) (inl a)
  aab : ∀ a b → X (inl a) (inl a) (inr b)
  aba : ∀ a b → X (inl a) (inr b) (inl a)
  baa : ∀ a b → X (inr b) (inl a) (inl a)
  abb : ∀ a b → X (inl a) (inr b) (inr b)
  bab : ∀ a b → X (inr b) (inl a) (inr b)
  bba : ∀ a b → X (inr b) (inr b) (inl a)
  bbb : ∀ b → X (inr b) (inr b) (inr b)


 go : ∀ x₀ x₁ x₂ → X x₀ x₁ x₂ 
 go (inl _) (inl _) (inl _) =
  subst2 (X (inl _)) (cong inl (isPropA _ _)) (cong inl (isPropA _ _)) (aaa _) 
 go (inl _) (inl _) (inr _) =
   subst (λ u → X (inl _) (inl u) (inr _)) (isPropA _ _) (aab _ _)
 go (inl _) (inr _) (inl _) =
   subst (λ u → X (inl _) (inr _) (inl u)) (isPropA _ _) (aba _ _)
 go (inl _) (inr _) (inr _) =
   subst (λ u → X (inl _) (inr u) (inr _)) (isPropB _ _) (abb _ _)
 go (inr _) (inl _) (inl _) =
   subst (λ u → X (inr _) (inl u) (inl _)) (isPropA _ _) (baa _ _)
 go (inr _) (inl _) (inr _) =
   subst (λ u → X (inr _) (inl _) (inr u)) (isPropB _ _) (bab _ _)
 go (inr _) (inr _) (inl _) =
   subst (λ u → X (inr _) (inr u) (inl _)) (isPropB _ _) (bba _ _)
 go (inr _) (inr _) (inr _) =
  subst2 (X (inr _)) (cong inr (isPropB _ _)) (cong inr (isPropB _ _)) (bbb _)
 
module Stiching {ℓ} (A : Type ℓ) (a b : ℝ) (a<b : a <ᵣ b)
           (f : ∀ x → x <ᵣ b → A)
           (g : ∀ x → a <ᵣ x → A)
           (f=g : ∀ x x< <x → f x x< ≡ g x <x)
            where


 w₂ : ∀ x → 2-Constant (⊎.rec (f x) (g x))
 w₂ x (inl u) (inl v)  = cong (f x) (isProp<ᵣ _ _ u v)
 w₂ x (inl u) (inr v) = f=g x u v
 w₂ x (inr u) (inl v) = sym (f=g x v u)
 w₂ x (inr u) (inr v) = cong (g x) (isProp<ᵣ _ _ u v)


 w₃ :  ∀ x → 3-Constant (⊎.rec (f x) (g x))
 w₃ x .3-Constant.link = w₂ x
 w₃ x .3-Constant.coh₁ = 3-⊎-prop-elim.go ww
  where
  open 3-⊎-prop-elim 
  ww : 3-⊎-prop-elim (x <ᵣ b) (a <ᵣ x) _
  ww .isPropA = isProp<ᵣ _ _
  ww .isPropB = isProp<ᵣ _ _
  ww .aaa _ = congP (λ _ → cong (f x)) (isSet→isSet' (isProp→isSet (isProp<ᵣ _ _)) _ _  _ _) 
  ww .aab p q = cong {y = refl} (cong (f x)) (isSet→isSet' (isProp→isSet (isProp<ᵣ _ _)) _ _ _ _)
    ◁ λ i i₁ → f=g x p q (i ∧ i₁)
  ww .aba p q = (λ i i₁ → f=g x p q (~ i ∧ i₁)) ▷
    cong {x = refl} (cong (f x)) (isSet→isSet' (isProp→isSet (isProp<ᵣ _ _)) _ _ _ _)
  ww .baa p q = flipSquare ((λ _ → refl) ▷
    cong {x = refl} (cong (f x)) (isSet→isSet' (isProp→isSet (isProp<ᵣ _ _)) _ _ _ _))
  ww .abb p q = flipSquare ((λ _ → refl) ▷
    cong {x = refl} (cong (g x)) (isSet→isSet' (isProp→isSet (isProp<ᵣ _ _)) _ _ _ _))
  ww .bab p q = (λ i i₁ → f=g x p q (~ i₁ ∨ i))
    ▷ cong {x = refl} (cong (g x)) (isSet→isSet' (isProp→isSet (isProp<ᵣ _ _)) _ _ _ _)
  ww .bba p q = cong {y = refl} (cong (g x)) (isSet→isSet' (isProp→isSet (isProp<ᵣ _ _)) _ _ _ _)
    ◁ λ i i₁ → f=g x p q (~ (i₁ ∧ i)) 
  ww .bbb _ = congP (λ _ → cong (g x)) (isSet→isSet' (isProp→isSet (isProp<ᵣ _ _)) _ _  _ _) 
  
 module hLev2 (isSetA : isSet A) where
   
    preStichSetFns : ∀ x → ∥ (x <ᵣ b) ⊎ (a <ᵣ x) ∥₁  → A
    preStichSetFns x = PT.rec→Set isSetA
        (⊎.rec (f x) (g x))
        (w₂ x)


    stichSetFns : ℝ → A
    stichSetFns x = preStichSetFns x (Dichotomyℝ' a x b a<b)

    stichSetFns-x< : ∀ x x<b → stichSetFns x ≡ f x x<b
    stichSetFns-x< x x<b =
       cong (preStichSetFns x) (squash₁ (Dichotomyℝ' a x b a<b)
         ∣ inl x<b ∣₁)

    stichSetFns-<x : ∀ x a<x → stichSetFns x ≡ g x a<x
    stichSetFns-<x x a<x =
       cong (preStichSetFns x) (squash₁ (Dichotomyℝ' a x b a<b)
         ∣ inr a<x ∣₁)


 module hLev3 (isGrpdA : isGroupoid A) where
   
    preStichGrpdFns : ∀ x → ∥ (x <ᵣ b) ⊎ (a <ᵣ x) ∥₁  → A
    preStichGrpdFns x = PT.rec→Gpd
        isGrpdA (⊎.rec (f x) (g x))
         (w₃ x)

    stichGrpdFns : ℝ → A
    stichGrpdFns x = preStichGrpdFns x (Dichotomyℝ' a x b a<b)

    stichGrpdFns-x< : ∀ x x<b → stichGrpdFns x ≡ f x x<b
    stichGrpdFns-x< x x<b =
       cong (preStichGrpdFns x) (squash₁ (Dichotomyℝ' a x b a<b)
         ∣ inl x<b ∣₁)

    stichGrpdFns-<x : ∀ x a<x → stichGrpdFns x ≡ g x a<x
    stichGrpdFns-<x x a<x =
       cong (preStichGrpdFns x) (squash₁ (Dichotomyℝ' a x b a<b)
         ∣ inr a<x ∣₁)


-- open Stiching public using (hLev2.stichSetFns)


private
  variable
    ℓ : Level
    A A' B B' : Type ℓ


foldlFin : ∀ {n} → (B → A → B) → B → (F.Fin n → A) → B
foldlFin {n = zero} f b v = b
foldlFin {n = suc n} f b v = foldlFin {n = n} f (f b (v F.fzero)) (v ∘ F.fsuc)

-- k·mᵏ<[m+sn]ᵏ : ∀ k m n → k ℕ.· (m ℕ.^ k) ℕ.< (m ℕ.+ suc n) ℕ.^ (suc k)
-- k·mᵏ<[m+sn]ᵏ zero m n = subst2 ℕ._<_ refl
--   (sym (ℕ.·-identityʳ _)) (ℕ.≤-+-< (ℕ.zero-≤ {m}) (ℕ.zero-<-suc {n}))
-- k·mᵏ<[m+sn]ᵏ (suc k) zero n =
--  subst2 ℕ._<_
--   (ℕ.0≡m·0 k)
--     refl (ℕ.monotone-^ 0 (suc n) (suc k) (ℕ.zero-<-suc {n}))
-- k·mᵏ<[m+sn]ᵏ (suc k) m@(suc m') n =
--   subst2 ℕ._<_
--     (ℕ.·-identityʳ _)
--     ( cong₂ ℕ._+_
--        (cong₂ ℕ._+_ (sym (ℕ.+-zero _) )
--          refl)
--        (cong₂ ℕ._·_ refl (cong suc (sym (ℕ.·-identityʳ _)))
--      ∙ (sym (ℕ.·-assoc (suc (suc k))
--         (suc m' ^ (suc k)) (suc n ^ 1))
--            ∙∙ cong₂ ℕ._·_ (sym (choose1 (suc (suc k)))) (ℕ.·-comm (suc m' ^ suc k) (suc n ^ 1))
--            ∙∙ ℕ.·-assoc _ _ _)) ∙ (sym (ℕ.+-assoc _ _ _)
--        ∙ cong₂ ℕ._+_ refl (ℕ.+-comm
--          _
--          ((suc (suc k) choose 1) ℕ.· (suc n ^ 1) ℕ.· (suc m' ^ suc k))))
--       ∙ sym (binomialℕ (suc (suc k)) (suc n) m)
--       ∙ cong (ℕ._^ (suc (suc k))) (ℕ.+-comm (suc n) m))
--     (ℕ.<-+-≤ {zero} {_}
--       (ℕ.<-+-≤ (ℕ.monotone-^ 0 (suc m') (suc k) (ℕ.zero-<-suc {m'})) ℕ.zero-≤)
--       (ℕ.≤monotone· (ℕ.≤-·k (ℕ.≤-sucℕ {suc k}))
--        (ℕ.suc-≤-suc (ℕ.zero-≤ {n})))
--       )


--  where
--  open Cubical.Algebra.CommRing.BinomialThm.BinomialThm ℤCommRing
--   renaming (_choose_ to _ℤchoose_)
--  open Exponentiation ℤCommRing renaming (_^_ to _^ℤ_)
--  open Cubical.Algebra.Ring.BigOps.Sum (CommRing→Ring ℤCommRing)

--  choose1 : ∀ n → n choose 1 ≡  n
--  choose1 zero = refl
--  choose1 (suc n) = ℕ.+-comm (n choose 1) (n choose 0) ∙ cong suc (choose1 n)


--  binVecℕ : ∀ k n m → FD.Fin (suc k) → ℕ
--  binVecℕ k n m i = (k choose (FD.toℕ i)) ℕ.· n ℕ.^
--   (FD.toℕ i) ℕ.· m ℕ.^ (k ∸ (FD.toℕ i))

--  choose≡ℤchoose : ∀ k l → pos (k choose l) ≡ (k ℤchoose l)
--  choose≡ℤchoose k zero = refl
--  choose≡ℤchoose zero (suc l) = refl
--  choose≡ℤchoose (suc k) (suc l) = ℤ.pos+ _ _ ∙
--   cong₂ ℤ._+_ (choose≡ℤchoose k (suc l))
--    (choose≡ℤchoose k l)


--  ^-lemma : ∀ a b → pos (a ℕ.^ b) ≡ (pos a) ^ℤ b
--  ^-lemma a zero = refl
--  ^-lemma a (suc b) = ℤ.pos·pos a (a ^ b)
--   ∙ cong₂ ℤ._·_ refl (^-lemma a b)


--  binVecℕ≡bvℤ : ∀ k n m f  →
--    pos (binVecℕ k n m f) ≡ BinomialVec k (pos n) (pos m) f
--  binVecℕ≡bvℤ k n m f =
--    ℤ.pos·pos _ _ ∙
--     cong₂ ℤ._·_
--      (ℤ.pos·pos _ _ ∙ cong₂ ℤ._·_
--        (choose≡ℤchoose _ _) (^-lemma _ _))
--      (^-lemma m (k ∸ FD.toℕ f))


--  bnmℕ : ∀ k f → pos (FD.foldrFin {n = k} ℕ._+_ zero f)
--      ≡ (FD.foldrFin ℤ._+_ (pos zero) (pos ∘ f))

--  bnmℕ zero f = refl
--  bnmℕ (suc k) f = ℤ.pos+ _ _ ∙
--    cong₂ ℤ._+_
--     refl (bnmℕ k _)


--  binomialℕ : ∀ k n m →
--      (n ℕ.+ m) ℕ.^ k ≡ FD.foldrFin ℕ._+_ zero (binVecℕ k n m)
--  binomialℕ k n m =
--     ℤ.injPos
--      ((^-lemma _ _  ∙
--       cong (_^ℤ k) (ℤ.pos+ n m))
--    ∙∙ BinomialThm k (pos n) (pos m)
--    ∙∙ (cong (FD.foldrFin ℤ._+_ (pos zero))
--      (funExt (sym ∘ binVecℕ≡bvℤ k n m))
--      ∙ sym (bnmℕ (suc k) (binVecℕ k n m))))



-- ℕkⁿ<ε : ∀ p q r s → 0 ℕ.< q →  s ℕ.< r → Σ[ n ∈ ℕ ]
--              p ℕ.· s ℕ.^ n ℕ.< q ℕ.· r ℕ.^ n
-- ℕkⁿ<ε p q zero s 0<q s<r = ⊥.rec (ℕ.¬-<-zero s<r)
-- ℕkⁿ<ε p zero _ s 0<q s<r = ⊥.rec (ℕ.¬-<-zero 0<q)
-- ℕkⁿ<ε p (suc q) (suc r) s 0<q (u , u+ss=sr) =


--  let n = p ℕ.· s
--  in suc n ,
--       subst (ℕ._< suc q ℕ.· (suc r ℕ.^ suc n))
--        (sym (ℕ.·-assoc p s (s ℕ.^ n))) (ℕ.<≤-trans {n ℕ.· (s ^ n)}
--           {(s ℕ.+ suc u) ℕ.^ suc n}
--           {suc q ℕ.· (suc r ℕ.^ suc n)}
--           (k·mᵏ<[m+sn]ᵏ n s u)
--           (subst2 (ℕ._≤_)
--              (+-zero _)
--              (cong (λ r → suc q ℕ.· (r ^ suc n))
--                ((+-suc s u ∙ +-comm (suc s) u) ∙ u+ss=sr))
--              (ℕ.≤-·k {1} {suc q} {k = (s ℕ.+ suc u) ^ suc n}
--                (ℕ.zero-<-suc {q}))))



Lipschitz-ℚ→ℝℙ : ℚ₊ → (P : ℙ ℝ) → (∀ x → rat x ∈ P  → ℝ) → Type
Lipschitz-ℚ→ℝℙ L P f =
  (∀ q q∈ r r∈ → (ε : ℚ₊) →
    ℚ.abs (q ℚ.- r) ℚ.< (fst ε) → absᵣ (f q q∈ -ᵣ f r r∈)
     <ᵣ rat (fst (L ℚ₊· ε  )))


extend-Lipshitzℚ→ℝ : ∀ L →  ∀ a b → (a ℚ.≤ b) → ∀ f →
        Lipschitz-ℚ→ℝℙ L (intervalℙ (rat a) (rat b)) f →
        Σ[ f' ∈ (ℚ → ℝ) ]
          (Lipschitz-ℚ→ℝ L f' × (∀ x x∈ → f' x ≡ f x x∈ ))

extend-Lipshitzℚ→ℝ L a b a≤b f li =
 (λ x → f (ℚ.clamp a b x) (∈ℚintervalℙ→∈intervalℙ _ _ _
  (ℚ.clam∈ℚintervalℙ a b a≤b x))) ,
   w , (λ x x∈ → cong (uncurry f)
    (Σ≡Prop (∈-isProp (intervalℙ (rat a) (rat b) ∘ rat))
    (ℚ.inClamps a b x (≤ᵣ→≤ℚ _ _ (fst x∈)) (≤ᵣ→≤ℚ _ _ (snd x∈)) )))

 where
 w : Lipschitz-ℚ→ℝ L
       (λ x →
          f (ℚ.clamp a b x)
          (∈ℚintervalℙ→∈intervalℙ a b (ℚ.clamp a b x)
           (ℚ.clam∈ℚintervalℙ a b a≤b x)))
 w q r ε u v = invEq (∼≃abs<ε _ _ _)
  (li _ _
   _ _ ε (ℚ.isTrans≤<
    (ℚ.abs (ℚ.clamp a b q ℚ.- ℚ.clamp a b r)) (ℚ.abs (q ℚ.- r)) (fst ε)
    (ℚ.clampDist a b r q) (ℚ.absFrom<×< (fst ε) (q ℚ.- r) u v)))


LLipschitz-ℚ→ℝ : (ℚ → ℝ) → Type
LLipschitz-ℚ→ℝ f =
  (∀ x → ∃[ (L , ε) ∈ (ℚ₊ × ℚ₊) ]
    ∀ q r → absᵣ (rat q -ᵣ x) <ᵣ rat (fst ε)
          → absᵣ (rat r -ᵣ x) <ᵣ rat (fst ε)
            → f q ∼[ L ℚ₊· ε  ] f r)


Dichotomyℝ : ∀ (ε : ℚ₊) x y →
    ⟨ ((x  <ᵣ y +ᵣ rat (fst ε)) , isProp<ᵣ _ _)
       L.⊔ ((y <ᵣ x +ᵣ rat (fst ε)) , isProp<ᵣ _ _) ⟩
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

Seq : Type
Seq = ℕ → ℝ

/nᵣ-L : (n : ℕ₊₁) → Σ _ (Lipschitz-ℝ→ℝ ([ 1 / n ]₊))
/nᵣ-L n = (fromLipschitz [ 1 / n ]₊
  (_ , Lipschitz-rat∘ [ 1 / n ]₊ (ℚ._· [ 1 / n ])
   λ q r ε x →
     subst (ℚ._< ([ 1 / n ]) ℚ.· (fst ε))
      (sym (ℚ.pos·abs [ 1 / n ] (q ℚ.- r)
       (ℚ.<Weaken≤ 0 [ 1 / n ]
           ( (ℚ.0<→< [ 1 / n ] (ℚ.0<pos _ _)))))
       ∙ cong ℚ.abs (ℚ.·Comm [ 1 / n ] (q ℚ.+ ℚ.- r) ∙ ℚ.·DistR+ q (ℚ.- r) [ 1 / n ]
        ∙ cong ((q ℚ.· [ 1 / n ]) ℚ.+_)
            (sym (ℚ.·Assoc -1 r [ 1 / n ]))))
      (ℚ.<-o· (ℚ.abs (q ℚ.- r)) (fst ε) [ 1 / n ]
       ((ℚ.0<→< [ 1 / n ] (ℚ.0<pos _ _)))
       x)))

/nᵣ : ℕ₊₁ → ℝ → ℝ
/nᵣ = fst ∘ /nᵣ-L

/nᵣ-／ᵣ : ∀ n x (p : 0 ＃ fromNat (ℕ₊₁→ℕ n))
            → /nᵣ n x ≡ (x ／ᵣ[ fromNat (ℕ₊₁→ℕ n) , p ] )
/nᵣ-／ᵣ n x p = ≡Continuous _ _
  (Lipschitz→IsContinuous [ 1 / n ]₊ (fst (/nᵣ-L n)) (snd (/nᵣ-L n)))
   (IsContinuous·ᵣR _)
  (λ r → fromLipschitz-rat ∙ cong rat (cong (r ℚ.·_) (cong [ 1 /_] (sym (·₊₁-identityˡ _))))
    ∙ rat·ᵣrat _ _ ∙
      cong (rat r ·ᵣ_) (sym (invℝ-rat _ _ (fst (rat＃ _ _) p)) )) x

-- /nᵣ-／ᵣ₊ : ∀ n x
--             → /nᵣ n x ≡ (x ／ᵣ₊ (fromNat (ℕ₊₁→ℕ n)) )
-- /nᵣ-／ᵣ₊ n x = {!!}
--  -- ≡Continuous _ _
--  --   (Lipschitz→IsContinuous _ (fst (/nᵣ-L n)) (snd (/nᵣ-L n)))
--  --    (IsContinuous·ᵣR _)
--  --   (λ r → cong rat (cong (r ℚ.·_) (cong [ 1 /_] (sym (·₊₁-identityˡ _))))
--  --     ∙ rat·ᵣrat _ _ ∙
--  --       cong (rat r ·ᵣ_) (cong rat
--  --         (cong (λ n → [ pos 1 / 1+ n ])
--  --           (ℕ.+-zero _))
--  --        ∙ sym (invℝ'-rat _ _ _))) x


/nᵣ-pos : ∀ n x → 0 <ᵣ x → 0 <ᵣ /nᵣ n x
/nᵣ-pos n x 0<x = subst (0 <ᵣ_) (sym (/nᵣ-／ᵣ _ _ _))
                     (ℝ₊· (_ , 0<x) (_ , invℝ-pos _
                         (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _))))

seqSumUpTo : (ℕ → ℝ) → ℕ →  ℝ
seqSumUpTo s zero = 0
seqSumUpTo s (suc n) = s zero +ᵣ seqSumUpTo (s ∘ suc) n

seqSumUpToConst : ∀ x n → seqSumUpTo (const x) n ≡ x ·ᵣ fromNat n
seqSumUpToConst x zero = sym (𝐑'.0RightAnnihilates x)
seqSumUpToConst x (suc n) =
 cong₂ (_+ᵣ_) (sym (·IdR x)) (seqSumUpToConst x n) ∙
   sym (·DistL+ x 1 (fromNat n))
    ∙ cong ((x ·ᵣ_))
     (+ᵣ-rat _ _ ∙ cong rat (ℚ.ℕ+→ℚ+ 1 n))

seqSumUpTo· : ∀ s r n → seqSumUpTo s n ·ᵣ r ≡ seqSumUpTo ((_·ᵣ r) ∘ s) n
seqSumUpTo· s r zero = 𝐑'.0LeftAnnihilates r
seqSumUpTo· s r (suc n) =
  ·DistR+ (s zero) (seqSumUpTo (s ∘ suc) n) r ∙
   cong ((s zero ·ᵣ r) +ᵣ_) (seqSumUpTo· (s ∘ suc) r n)

seqSumUpTo≤ : ∀ s s' → (∀ n → s n ≤ᵣ s' n) →
  ∀ n → seqSumUpTo s n ≤ᵣ seqSumUpTo s' n
seqSumUpTo≤ s s' X zero = ≤ᵣ-refl _
seqSumUpTo≤ s s' X (suc n) =
  ≤ᵣMonotone+ᵣ _ _ _ _ (X 0) (seqSumUpTo≤ _ _ (X ∘ suc) n)


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
    cong ((f zero) +ᵣ_ ) (seqSumUpTo-suc (f ∘ suc) n)

seqSumUpTo≡seqSumUpTo' : ∀ f n → seqSumUpTo' f n ≡ seqSumUpTo f n
seqSumUpTo≡seqSumUpTo' f zero = refl
seqSumUpTo≡seqSumUpTo' f (suc n) =
 cong (_+ᵣ (f n)) (seqSumUpTo≡seqSumUpTo' f n) ∙
   seqSumUpTo-suc f n

-- seqΣ0≡0 : ∀ f n → (∀ n → f n ≡ 0) → seqSumUpTo' f n ≡ 0
-- seqΣ0≡0 f n p = ((cong seqSumUpTo' (funExt p)) ≡$ n)
--   ∙ seqSumUpTo≡seqSumUpTo' _ _
--   ∙ seqSumUpToConst _ n
--   ∙ 𝐑'.0LeftAnnihilates _


seqΣ'0≡0 : ∀ f n → (∀ n → f n ≡ 0) → seqSumUpTo f n ≡ 0
seqΣ'0≡0 f n p = ((cong seqSumUpTo (funExt p)) ≡$ n)
  ∙ seqSumUpToConst _ n
  ∙ 𝐑'.0LeftAnnihilates _


-- -seqΣ' : ∀ s n → -ᵣ (seqΣ s n) ≡ seqΣ (-ᵣ_ ∘ s) n
-- -seqΣ' s n =
--   cong (-ᵣ_) (seqSumUpTo≡seqSumUpTo' _ _)
--    ∙∙ -ᵣ≡[-1·ᵣ] _
--    ∙∙ ·ᵣComm _ _ ∙ seqSumUpTo· _ -1 n
--    ∙∙ (cong seqΣ' (funExt λ _ → ·ᵣComm _ _ ∙ sym (-ᵣ≡[-1·ᵣ] _)) ≡$ n)
--    ∙∙ sym (seqSumUpTo≡seqSumUpTo' _ _)

<-·sk-cancel : ∀ {m n k} → m ℕ.· suc k ℕ.< n ℕ.· suc k → m ℕ.< n
<-·sk-cancel {n = zero} x = ⊥.rec (ℕ.¬-<-zero x)
<-·sk-cancel {zero} {n = suc n} x = ℕ.suc-≤-suc (ℕ.zero-≤ {n})
<-·sk-cancel {suc m} {n = suc n} {k} x =
  ℕ.suc-≤-suc {suc m} {n}
    (<-·sk-cancel {m} {n} {k}
     (ℕ.≤-k+-cancel (subst (ℕ._≤ (k ℕ.+ n ℕ.· suc k))
       (sym (ℕ.+-suc _ _)) (ℕ.pred-≤-pred x))))

-- 2≤x→1<quotient[x/2] : ∀ n → 0 ℕ.< (ℕ.quotient (2 ℕ.+ n) / 2)
-- 2≤x→1<quotient[x/2] n =
--  let z : 0 ℕ.<
--              ((ℕ.quotient (2 ℕ.+ n) / 2) ℕ.· 2)
--      z = subst (0 ℕ.<_) (ℕ.·-comm _ _)
--           (ℕ.≤<-trans ℕ.zero-≤ (ℕ.<-k+-cancel (subst (ℕ._< 2 ℕ.+
--              (2 ℕ.· (ℕ.quotient (2 ℕ.+ n) / 2)))
--            (ℕ.≡remainder+quotient 2 (2 ℕ.+ n))
--              (ℕ.<-+k {k = 2 ℕ.· (ℕ.quotient (2 ℕ.+ n) / 2)}
--               (ℕ.mod< 1 (2 ℕ.+ n))))))
--  in <-·sk-cancel {0} {ℕ.quotient (2 ℕ.+ n) / 2 } {k = 1}
--      z



open ℕ.Minimal





opaque
 -- unfolding _<ᵣ_
 ^ⁿ-invℝ : ∀ n x 0＃x 0＃x^ →
             ((invℝ x 0＃x) ^ⁿ n) ≡ (invℝ (x ^ⁿ n) (0＃x^))
 ^ⁿ-invℝ zero x _ _ = sym (invℝ1 _)
 ^ⁿ-invℝ (suc n) x 0＃x _ =
   cong (_·ᵣ invℝ x _) (^ⁿ-invℝ n x _ z) ∙
     sym (invℝ· _ _ _ _ _)
  where

  z' : ∀ n → x <ᵣ 0 → 0 ＃ (x ^ⁿ n)
  z' zero _ = inl (decℚ<ᵣ? {x = 0})
  z' (suc n) x<0 =
   ⊎.rec (λ p → inr
      (isTrans≡<ᵣ _ _ _
       (sym (-ᵣ·-ᵣ _ _) ∙ -ᵣ· (x ^ⁿ n) _)
       (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ (<ᵣ₊Monotone·ᵣ _ _ _ _
        (≤ᵣ-refl 0) (≤ᵣ-refl _ )
      p 0<-x)) ℝ!) )) --
     (λ p →
       inl (isTrans≡<ᵣ _ _ _ (rat·ᵣrat 0 0)
          (isTrans<≡ᵣ _ _ _
             (<ᵣ₊Monotone·ᵣ _ _ _ _
               (≤ᵣ-refl 0) (≤ᵣ-refl 0)
               (isTrans≡<ᵣ _ _ _ (sym (-ᵣ-rat 0)) (-ᵣ<ᵣ _ _ p)) 0<-x) -- (-ᵣ<ᵣ _ _ p)
                          (-ᵣ·-ᵣ _ _))))
     (z' n x<0)
   where
    0<-x : 0 <ᵣ -ᵣ x
    0<-x = isTrans≡<ᵣ _ _ _ (sym (-ᵣ-rat 0)) (-ᵣ<ᵣ _ _ x<0)

  z : 0 ＃ (x ^ⁿ n)
  z = ⊎.rec (inl ∘ 0<x^ⁿ x n)
        (z' n) 0＃x

^ⁿDist·ᵣ : ∀ n x y →
            ((x ·ᵣ y) ^ⁿ n) ≡ (x ^ⁿ n) ·ᵣ (y ^ⁿ n)
^ⁿDist·ᵣ zero x y = rat·ᵣrat _ _
^ⁿDist·ᵣ (suc n) x y =
   cong (_·ᵣ (x ·ᵣ y)) (^ⁿDist·ᵣ n x y)
 ∙ (sym (·ᵣAssoc _ _ _)
     ∙∙ cong ((x ^ⁿ n) ·ᵣ_)
       ((·ᵣAssoc _ _ _)
     ∙∙ cong (_·ᵣ y) (·ᵣComm _ _)
     ∙∙ sym (·ᵣAssoc _ _ _))
     ∙∙ ·ᵣAssoc _ _ _)



／^ⁿ : ∀ n x y 0＃y 0＃y^ⁿ →
         (x ^ⁿ n) ／ᵣ[ y ^ⁿ n , 0＃y^ⁿ ] ≡
           ((x ／ᵣ[ y , 0＃y ]) ^ⁿ n)
／^ⁿ n x y 0＃y 0＃y^ⁿ =
  cong ((x ^ⁿ n) ·ᵣ_) (sym (^ⁿ-invℝ n y _ _))
    ∙ sym (^ⁿDist·ᵣ n _ _)


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
            ∙∙ seqSumUpTo≡seqSumUpTo' (geometricProgression a r) (suc n)
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

-- SₙLem : ∀ a r (0＃1-r : 0 ＃ (1 +ᵣ (-ᵣ r))) n →
--               (Sₙ a r n)   ≡
--                    a ·ᵣ ((1 +ᵣ (-ᵣ (r ^ⁿ n)))
--                      ／ᵣ[ (1 +ᵣ (-ᵣ r)) , 0＃1-r ])
-- SₙLem a r 0＃1-r n =
--      x·y≡z→x≡z/y (Sₙ a r n)
--        (a ·ᵣ (1 +ᵣ (-ᵣ (r ^ⁿ n))))
--         _ 0＃1-r (SₙLem' a n r)
--       ∙ sym (·ᵣAssoc _ _ _)

-- Sₙ-sup : ∀ a r n → (0 <ᵣ a) → (0 <ᵣ r) → (r<1 : r <ᵣ 1) →
--                 (Sₙ a r n)
--                 <ᵣ (a ·ᵣ (invℝ (1 +ᵣ (-ᵣ r)) (inl (x<y→0<y-x _ _ r<1))))
-- Sₙ-sup a r n a<0 0<r r<1  =
--    isTrans≤<ᵣ _ _ _ (≡ᵣWeaken≤ᵣ _ _ (SₙLem a r _ n))
--      (<ᵣ-o·ᵣ _ _ (a , a<0)
--       (isTrans<≤ᵣ _ _ _
--           (<ᵣ-·ᵣo (1 +ᵣ (-ᵣ (r ^ⁿ n))) 1
--             (invℝ (1 +ᵣ (-ᵣ r)) (inl (x<y→0<y-x _ _ r<1)) ,
--               0<1/x _ _ (( (x<y→0<y-x _ _ r<1))))
--             (isTrans<≤ᵣ _ _ _
--                (<ᵣ-o+ _ _ 1 (-ᵣ<ᵣ 0 (r ^ⁿ n) (0<x^ⁿ r n 0<r)))
--                (≡ᵣWeaken≤ᵣ _ _ ((𝐑'.+IdR' _ _ (-ᵣ-rat 0)))) ))
--           (≡ᵣWeaken≤ᵣ _ _ (·IdL _ ) )))

Seq<→Σ< : (s s' : Seq) → ∀ n →
  (∀ m → m ℕ.≤ n  → s m <ᵣ s' m) →
   seqSumUpTo s (suc n) <ᵣ seqSumUpTo s' (suc n)
Seq<→Σ< s s' zero x = subst2 _<ᵣ_
  (sym (+IdR _)) (sym (+IdR _)) (x 0 ℕ.≤-refl)
Seq<→Σ< s s' (suc n) x =
 <ᵣMonotone+ᵣ _ _ _ _
  (x 0 ℕ.zero-≤) (Seq<→Σ< (s ∘ suc) (s' ∘ suc) n
   (λ m x₁ → x (suc m) (ℕ.suc-≤-suc x₁ )))



Seq<→Σ<-+1 : (s s' : Seq) →
  (s 0 ≤ᵣ s' 0) →
  (∀ n → s (suc n) <ᵣ s' (suc n)) →
   ∀ n → seqSumUpTo s (suc (suc n)) <ᵣ seqSumUpTo s' (suc (suc n))
Seq<→Σ<-+1 s s' x0 x n = ≤<ᵣMonotone+ᵣ _ _ _ _
  x0 (Seq<→Σ< (s ∘ suc) (s' ∘ suc) n (const ∘ x))

Seq≤→Σ≤ : (s s' : Seq) →
  (∀ n → s n ≤ᵣ s' n) →
   ∀ n → seqSumUpTo s n ≤ᵣ seqSumUpTo s' n
Seq≤→Σ≤ s s' x zero = ≤ᵣ-refl _
Seq≤→Σ≤ s s' x (suc n) = ≤ᵣMonotone+ᵣ _ _ _ _
 (x 0) (Seq≤→Σ≤ (s ∘ suc) (s' ∘ suc) (x ∘ suc) n)

Seq≤→Σ≤-upto : (s s' : Seq) → ∀ N →
  (∀ n → n ℕ.< N → s n ≤ᵣ s' n) →
   seqSumUpTo s N ≤ᵣ seqSumUpTo s' N
Seq≤→Σ≤-upto s s' zero x = ≤ᵣ-refl _
Seq≤→Σ≤-upto s s' (suc N) x = ≤ᵣMonotone+ᵣ _ _ _ _
 (x 0 ℕ.zero-<-suc) (Seq≤→Σ≤-upto (s ∘ suc) (s' ∘ suc) N
   λ n u → x (suc n) (ℕ.suc-≤-suc u))


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
  isTrans≡≤ᵣ _ _ _
    (sym (+ᵣ-rat _ _)) (≤ᵣMonotone+ᵣ _ _ _ _ (0≤seqΣ s x n) (x n))


abs[seqΣ]≤seqΣ[abs] : ∀ s n → absᵣ (seqΣ s n) ≤ᵣ seqΣ (absᵣ ∘ s) n
abs[seqΣ]≤seqΣ[abs] s zero = ≡ᵣWeaken≤ᵣ _ _ absᵣ0
abs[seqΣ]≤seqΣ[abs] s (suc n) =
 isTrans≤ᵣ _ _ _
   (absᵣ-triangle _ _)
   (≤ᵣ-+o _ _ _ (abs[seqΣ]≤seqΣ[abs] s n))

absᵣIdemp : ∀ x → absᵣ (absᵣ x) ≡ absᵣ x
absᵣIdemp x = absᵣNonNeg _ (0≤absᵣ _)

0≤seqΣ' : ∀ s → (∀ n → 0 ≤ᵣ s n)
            → ∀ n → 0 ≤ᵣ seqΣ' s n
0≤seqΣ' s x zero = ≤ᵣ-refl _
0≤seqΣ' s x (suc n) =
  isTrans≡≤ᵣ _ _ _
    (sym (+ᵣ-rat _ _))
    $ ≤ᵣMonotone+ᵣ _ _ _ _ (x 0) (0≤seqΣ' (s ∘ suc) (x ∘ suc) n)


seqΣ'-truncateNonNeg : ∀ f → (∀ k → 0 ≤ᵣ f k) →
  ∀ n m → n ℕ.≤ m → seqΣ' f n ≤ᵣ seqΣ' f m
seqΣ'-truncateNonNeg f f-nonNeg zero m n≤m = 0≤seqΣ' f f-nonNeg m
seqΣ'-truncateNonNeg f f-nonNeg (suc n) zero n≤m =
  ⊥.rec (ℕ.¬-<-zero n≤m )
seqΣ'-truncateNonNeg f f-nonNeg (suc n) (suc m) n≤m =
    (≤ᵣ-o+ _ _ _
      (seqΣ'-truncateNonNeg (f ∘ suc)
       (f-nonNeg ∘ suc) n m (ℕ.pred-≤-pred n≤m)))


-- seqΣ-truncateNonNeg : ∀ f → (∀ k → 0 ≤ᵣ f k) →
--   ∀ n m → n ℕ.≤ m → seqΣ f n ≤ᵣ seqΣ f m
-- seqΣ-truncateNonNeg f f-nonNeg n m n≤m =
--   subst2 _≤ᵣ_
--     (sym (seqSumUpTo≡seqSumUpTo' f n) )
--     (sym (seqSumUpTo≡seqSumUpTo' f m))
--    (seqΣ'-truncateNonNeg f f-nonNeg n m n≤m)

-- series-subSeqLemma : (s : ℕ → ℝ) → (∀ n → 0 ≤ᵣ s n)
--    → (spd : ∀ n → Σ _ (n ℕ.≤_))
--    → (∀ k → (fst (spd k) ℕ.< fst (spd (suc k))))
--    → ∀ m m'
--    → seqΣ (λ z → s (fst (spd (z ℕ.+ m)))) m' ≤ᵣ
--      seqΣ (λ z → s (z ℕ.+ m)) ((m' ℕ.+ fst (snd (spd (predℕ m' ℕ.+ m)))))

-- series-subSeqLemma s 0≤s spd _ m zero =
--    0≤seqΣ _
--      (λ n → 0≤s (n ℕ.+ m))
--      ((fst (snd (spd m))))
-- series-subSeqLemma s 0≤s spd sIncr m (suc m') =

--   isTrans≤≡ᵣ _ _ _
--     (≤ᵣ-+o _ _ _
--       (isTrans≤ᵣ _ _ _ (series-subSeqLemma s 0≤s spd sIncr m m')
--         (seqΣ-truncateNonNeg (s ∘ (ℕ._+ m)) (0≤s ∘ (ℕ._+ m)) _ _
--           (spdMon m'))))
--     (cong₂ _+ᵣ_ refl
--      (cong s (sym (snd (snd (spd (m' ℕ.+ m)))) ∙
--         (ℕ.+-assoc _ _ _)
--          ∙ cong (ℕ._+ m) (ℕ.+-comm _ _))))
--   where
--    spdMon : ∀ m' → m' ℕ.+ (fst (snd (spd (predℕ m' ℕ.+ m)))) ℕ.≤
--         m' ℕ.+ fst (snd (spd (m' ℕ.+ m)))
--    spdMon zero = ℕ.≤-refl
--    spdMon (suc m') =
--      let p = snd (snd (spd (m' ℕ.+ m)))
--          p' = snd (snd (spd (suc m' ℕ.+ m)))
--      in subst2 ℕ._≤_
--           (cong suc (ℕ.+-comm _ _))
--           (ℕ.+-comm _ _)
--           (ℕ.≤-+k-cancel {k = m}
--             (subst2 ℕ._≤_
--                (cong suc (sym p ∙ ℕ.+-assoc _ _ _))
--                (sym p' ∙ ℕ.+-assoc _ _ _)
--                (sIncr (m' ℕ.+ m))))


0<seqΣ' : ∀ s → (∀ n → 0 <ᵣ s n)
            → ∀ n → 0 <ᵣ seqΣ' s (suc n)
0<seqΣ' s x zero = isTrans<≡ᵣ _ _ _ (x 0) (sym (+IdR (s 0)))
0<seqΣ' s x (suc n) =
    isTrans≡<ᵣ _ _ _
    (sym (+ᵣ-rat _ _))
    $ <ᵣMonotone+ᵣ _ _ _ _ (x 0) (0<seqΣ' (s ∘ suc) (x ∘ suc) n)

-- abs[seqΣ]≡seqΣ : ∀ s n → (∀ n → 0 ≤ᵣ s n) →  absᵣ (seqΣ s n) ≡ seqΣ s n
-- abs[seqΣ]≡seqΣ s n 0≤s =
--   absᵣNonNeg _ (isTrans≡≤ᵣ _ _ _
--        (sym (𝐑'.0LeftAnnihilates _)
--      ∙∙ sym (seqSumUpToConst 0 n)
--      ∙∙ sym (seqSumUpTo≡seqSumUpTo' (const 0) n)) (Seq'≤→Σ≤ (λ _ → 0) s 0≤s n))


-- seqΣ[abs]≡abs[seqΣ[abs]] : ∀ s n → absᵣ (seqΣ (absᵣ ∘ s) n) ≡ seqΣ (absᵣ ∘ s) n
-- seqΣ[abs]≡abs[seqΣ[abs]] s n =
--  abs[seqΣ]≡seqΣ (absᵣ ∘ s) n λ _ → 0≤absᵣ _

seriesDiff : (s : Seq)  →
  ∀ N n → (seqΣ s (n ℕ.+ N) +ᵣ (-ᵣ seqΣ s N)) ≡
     seqΣ (s ∘ (ℕ._+ N)) n
seriesDiff s N zero = +-ᵣ (seqΣ s N)
seriesDiff s N (suc n) =
  cong (_+ᵣ _) (+ᵣComm _ _) ∙∙
  sym (+ᵣAssoc _ _ _) ∙∙
   cong (s (n ℕ.+ N) +ᵣ_) (seriesDiff s N n)
    ∙ +ᵣComm (s (n ℕ.+ N)) (seqΣ (s ∘ (ℕ._+ N)) n)

opaque

 0＃· : ∀ x y → 0 ＃ x → 0 ＃ y → 0 ＃ (x ·ᵣ y)
 0＃· x y =
  ⊎.rec (λ 0<x → ⊎.rec
         (λ 0<y → inl (isTrans≡<ᵣ _ _ _ (rat·ᵣrat _ _)
             (<ᵣ₊Monotone·ᵣ _ _ _ _
               (≤ᵣ-refl _) (≤ᵣ-refl _) 0<x 0<y)))
             λ y<0 → inr (
               let z = isTrans≡<ᵣ _ _ _ (rat·ᵣrat _ _) $
                        <ᵣ₊Monotone·ᵣ _ _ _ _
                         (≤ᵣ-refl _) (≤ᵣ-refl _) 0<x ((isTrans≡<ᵣ _ _ _ (sym (-ᵣ-rat 0)) (-ᵣ<ᵣ _ _  y<0)))
               in isTrans≡<ᵣ _ _ _ (cong (x ·ᵣ_) (sym (-ᵣInvol _))
                     ∙  (·-ᵣ _ _)) ((isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ z) (-ᵣ-rat 0))))) -- (-ᵣ<ᵣ _ _ z)
        λ x<0 → ⊎.rec
          (λ 0<y → inr (
               let z = isTrans≡<ᵣ _ _ _ (rat·ᵣrat _ _) $
                        <ᵣ₊Monotone·ᵣ _ _ _ _
                         (≤ᵣ-refl _) (≤ᵣ-refl _) ((isTrans≡<ᵣ _ _ _ (sym (-ᵣ-rat 0)) ((-ᵣ<ᵣ _ _  x<0)))) 0<y

               in isTrans≡<ᵣ _ _ _ (sym (-ᵣInvol _)
                  ∙ cong (-ᵣ_) (sym (-ᵣ· _ _))) (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ z) (-ᵣ-rat 0))))
          λ y<0 → inl
             let z = isTrans≡<ᵣ _ _ _ (rat·ᵣrat _ _) $
                        <ᵣ₊Monotone·ᵣ _ _ _ _
                         (≤ᵣ-refl _) (≤ᵣ-refl _) (isTrans≡<ᵣ _ _ _ (sym (-ᵣ-rat 0)) ((-ᵣ<ᵣ _ _  x<0)))
                          (isTrans≡<ᵣ _ _ _ (sym (-ᵣ-rat 0)) (-ᵣ<ᵣ _ _  y<0))

               in isTrans<≡ᵣ _ _ _ z (-ᵣ·-ᵣ x y)

＃Δ : ∀ x y → (0 ＃ (x -ᵣ y)) ≃ y ＃ x
＃Δ x y = ⊎.⊎-equiv
  (invEquiv (x<y≃0<y-x _ _))
  (invEquiv (x<y≃x-y<0 _ _))

invℝ<invℝ-pos : ∀ x y → ∀ 0<x 0<y →
                   (x <ᵣ y) ≃ (invℝ y (inl 0<y) <ᵣ invℝ x (inl 0<x))
invℝ<invℝ-pos x y 0<x 0<y =
 z<x≃y₊·z<y₊·x y x (invℝ y (inl 0<y) ·ᵣ invℝ x (inl 0<x) ,
   ℝ₊· (invℝ y (inl 0<y) , invℝ-pos y 0<y)
       (invℝ x (inl 0<x) , invℝ-pos x 0<x))
  ∙ₑ substEquiv' (_<ᵣ (invℝ y (inl 0<y) ·ᵣ invℝ x (inl 0<x) ·ᵣ y))
      (sym (·ᵣAssoc _ _ _) ∙∙
       cong (invℝ y (inl 0<y) ·ᵣ_)
        (·ᵣComm _ _ ∙ x·invℝ[x] _ _)
        ∙∙ ·IdR _)
  ∙ₑ substEquiv' (invℝ y (inl 0<y) <ᵣ_)
    (cong (_·ᵣ y) (·ᵣComm _ _)
     ∙ ((sym (·ᵣAssoc _ _ _) ∙∙
       cong (invℝ x (inl 0<x) ·ᵣ_)
        (·ᵣComm _ _ ∙ x·invℝ[x] _ _)
        ∙∙ ·IdR _)))

1<x/y : ∀ x y → (0 <ᵣ x) → (0<y : 0 <ᵣ y)  →
  (y <ᵣ x) ≃ (1 <ᵣ (x ／ᵣ[ y , inl 0<y ]))
1<x/y x y 0<x 0<y =
  ((substEquiv' (_<ᵣ x) (sym (·IdR y))) ∙ₑ
    substEquiv' (y ·ᵣ 1 <ᵣ_)
     (sym ([x/y]·yᵣ _ _ (inl 0<y)) ∙ ·ᵣComm _ _ )
    ∙ₑ invEquiv (z<x≃y₊·z<y₊·x (x ／ᵣ[ y , inl 0<y ]) 1 (y , 0<y)))

x/y<1 : ∀ x y → (0 <ᵣ x) → (0<y : 0 <ᵣ y)  →
  (x <ᵣ y) ≃ ((x ／ᵣ[ y , inl 0<y ]) <ᵣ 1)
x/y<1 x y 0<x 0<y =
  (((substEquiv' (x <ᵣ_) (sym (·IdR y))) ∙ₑ
    substEquiv' (_<ᵣ (y ·ᵣ 1))
     (sym ([x/y]·yᵣ _ _ (inl 0<y)) ∙ ·ᵣComm _ _ ))
    ∙ₑ invEquiv (z<x≃y₊·z<y₊·x 1 (x ／ᵣ[ y , inl 0<y ]) (y , 0<y)))

-- x/y≤z : ∀ x y z → (0 ≤ᵣ x) → (0<y : 0 <ᵣ y)  →
--   (x ≤ᵣ z ·ᵣ y) ≃ ((x ／ᵣ[ y , inl 0<y ]) ≤ᵣ z)
-- x/y≤z x y z 0≤x 0<y = {!!}
--   -- (((substEquiv' (x <ᵣ_) (sym (·IdR y))) ∙ₑ
--   --   substEquiv' (_<ᵣ (y ·ᵣ 1))
--   --    (sym ([x/y]·yᵣ _ _ (inl 0<y)) ∙ ·ᵣComm _ _ ))
--   --   ∙ₑ invEquiv (z<x≃y₊·z<y₊·x 1 (x ／ᵣ[ y , inl 0<y ]) (y , 0<y)))

-- x≤z/y : ∀ x y z → (0 ≤ᵣ x) → (0<y : 0 <ᵣ y)  →
--   (x ·ᵣ y ≤ᵣ z) ≃ (x ≤ᵣ (z  ／ᵣ[ y , inl 0<y ]))
-- x≤z/y x y z 0≤x 0<y = {!!}
--   -- (((substEquiv' (x <ᵣ_) (sym (·IdR y))) ∙ₑ
--   --   substEquiv' (_<ᵣ (y ·ᵣ 1))
--   --    (sym ([x/y]·yᵣ _ _ (inl 0<y)) ∙ ·ᵣComm _ _ ))
--   --   ∙ₑ invEquiv (z<x≃y₊·z<y₊·x 1 (x ／ᵣ[ y , inl 0<y ]) (y , 0<y)))


1＃x/y : ∀ x y → (0 <ᵣ x) → (0<y : 0 <ᵣ y)  →
  (y ＃ x) ≃ 1 ＃ (x ／ᵣ[ y , inl 0<y ])
1＃x/y x y 0<x 0<y =
 ⊎.⊎-equiv
  (1<x/y x y 0<x 0<y)
  (x/y<1 x y 0<x 0<y)



1<^ : ∀ x  → ∀ n → (1 <ᵣ x) → (1 <ᵣ (x ^ⁿ (suc n)))
1<^ x zero = subst (1 <ᵣ_) (sym (·IdR _) ∙  ·ᵣComm _ _)
1<^ x (suc n) 1<x =
 isTrans≡<ᵣ _ _ _ (sym (·IdR _))
   (<ᵣ₊Monotone·ᵣ _ _ _ _
     decℚ≤ᵣ? decℚ≤ᵣ?  (1<^ x (n) 1<x) 1<x)

^<1 : ∀ x → 0 ≤ᵣ x  → ∀ n → (x <ᵣ 1) → ((x ^ⁿ (suc n)) <ᵣ 1)
^<1 x _ zero = subst (_<ᵣ 1) (sym (·IdR _) ∙  ·ᵣComm _ _)
^<1 x 0≤x (suc n) x<1 =
 isTrans<≡ᵣ _ _ _
   (<ᵣ₊Monotone·ᵣ _ _ _ _
     (0≤x^ⁿ x (suc n) 0≤x) 0≤x (^<1 x 0≤x n x<1) x<1)
   (·IdR _)


^≤1 : ∀ x → 0 ≤ᵣ x  → ∀ n → (x ≤ᵣ 1) → ((x ^ⁿ n) ≤ᵣ 1)
^≤1 x _  zero _ = ≤ᵣ-refl 1
^≤1 x 0≤x (suc n) x≤1 =
 isTrans≤≡ᵣ _ _ _
   (≤ᵣ₊Monotone·ᵣ _ _ _ _
     decℚ≤ᵣ? 0≤x ((^≤1 _ 0≤x n x≤1)) x≤1)
   (·IdR _)




1＃^ : ∀ x → 0 ≤ᵣ x → ∀ n → (1 ＃ x) → (1 ＃ (x ^ⁿ (suc n)))
1＃^ x 0≤x n = ⊎.map (1<^ x n) (^<1 x 0≤x n)

-- bⁿ-aⁿ : ℝ → ℝ → ℕ → ℝ
-- bⁿ-aⁿ a b n = (b -ᵣ a) ·ᵣ seqΣ (λ k → b ^ⁿ k ·ᵣ (a ^ⁿ (n ∸ suc k))) n


^ⁿ-StrictMonotone : ∀ {x y : ℝ} (n : ℕ) → (0 ℕ.< n)
 → 0 ≤ᵣ x → 0 ≤ᵣ y → x <ᵣ y → (x ^ⁿ n) <ᵣ (y ^ⁿ n)

^ⁿ-StrictMonotone {x} {y} 0 0<n 0≤x 0≤y x<y = ⊥.rec (ℕ.¬-<-zero 0<n)
^ⁿ-StrictMonotone {x} {y} 1 0<n 0≤x 0≤y x<y =
  subst2 _<ᵣ_ (sym (·IdL _)) (sym (·IdL _)) x<y
^ⁿ-StrictMonotone {x} {y} (suc (suc n)) 0<n 0≤x 0≤y x<y =
  <ᵣ₊Monotone·ᵣ _ _ _ _
    (0≤x^ⁿ x (suc n) 0≤x)
    0≤x
    ((^ⁿ-StrictMonotone (suc n) (ℕ.suc-≤-suc (ℕ.zero-≤ {n})) 0≤x 0≤y x<y))
    x<y

^ⁿ-Monotone : ∀ {x y : ℝ} (n : ℕ)
 → 0 ≤ᵣ x → x ≤ᵣ y → (x ^ⁿ n) ≤ᵣ (y ^ⁿ n)
^ⁿ-Monotone zero _ _ = ≤ᵣ-refl _
^ⁿ-Monotone (suc n) 0≤x x≤y =
   ≤ᵣ₊Monotone·ᵣ _ _ _ _
    (0≤x^ⁿ _ n (isTrans≤ᵣ _ _ _ 0≤x x≤y)) 0≤x (^ⁿ-Monotone n 0≤x x≤y) x≤y



ℚ^ⁿ-Monotone : ∀ {x y : ℚ} (n : ℕ) → 0 ℚ.≤ x → 0 ℚ.≤ y → x ℚ.≤ y
 → (x ℚ^ⁿ n) ℚ.≤ (y ℚ^ⁿ n)
ℚ^ⁿ-Monotone zero 0≤x 0≤y x≤y = ℚ.isRefl≤ 1
ℚ^ⁿ-Monotone {x} {y} (suc n) 0≤x 0≤y x≤y =
  ℚ.≤Monotone·-onNonNeg _ _ _ _
    (ℚ^ⁿ-Monotone n 0≤x 0≤y x≤y)
    x≤y
    (ℚ.0≤ℚ^ⁿ x 0≤x n)
    0≤x

ℚ^ⁿ-StrictMonotone : ∀ {x y : ℚ} (n : ℕ) → (0 ℕ.< n) → 0 ℚ.≤ x → 0 ℚ.≤ y → x ℚ.< y → (x ℚ.ℚ^ⁿ n) ℚ.< (y ℚ.ℚ^ⁿ n)
ℚ^ⁿ-StrictMonotone {x} {y} 0 0<n 0≤x 0≤y x<y = ⊥.rec (ℕ.¬-<-zero 0<n)
ℚ^ⁿ-StrictMonotone {x} {y} 1 0<n 0≤x 0≤y x<y =
  subst2 ℚ._<_ (sym (ℚ.·IdL _)) (sym (ℚ.·IdL _)) x<y
ℚ^ⁿ-StrictMonotone {x} {y} (suc (suc n)) 0<n 0≤x 0≤y x<y =
  ℚ.<Monotone·-onPos _ _ _ _
    (ℚ^ⁿ-StrictMonotone (suc n) (ℕ.suc-≤-suc (ℕ.zero-≤ {n})) 0≤x 0≤y x<y)
    x<y
    (ℚ.0≤ℚ^ⁿ x 0≤x (suc n))
    0≤x


ℚ^ⁿ-Monotone⁻¹ : ∀ {x y : ℚ} (n : ℕ) → (0 ℕ.< n) → 0 ℚ.≤ x → 0 ℚ.≤ y
 → (x ℚ^ⁿ n) ℚ.≤ (y ℚ^ⁿ n) → x ℚ.≤ y
ℚ^ⁿ-Monotone⁻¹ n 0<n 0≤x 0≤y xⁿ≤yⁿ =
 ℚ.≮→≥ _ _ (ℚ.≤→≯ _ _ xⁿ≤yⁿ ∘ ℚ^ⁿ-StrictMonotone n 0<n 0≤y 0≤x  )

^ⁿ-StrictMonotoneR : ∀ {x : ℝ} (m n : ℕ)
 → 1 <ᵣ x → m ℕ.< n → (x ^ⁿ m) <ᵣ (x ^ⁿ n)
^ⁿ-StrictMonotoneR m zero x x₁ = ⊥.rec (ℕ.¬-<-zero x₁)
^ⁿ-StrictMonotoneR {x} zero (suc n) 1<x m<n = 1<^ x n 1<x
^ⁿ-StrictMonotoneR (suc m) (suc n) 1<x sm<sn =
 <ᵣ-·ᵣo _ _ (_ , isTrans<ᵣ 0 1 _ (<ℚ→<ᵣ _ _ ℚ.decℚ<?) 1<x)
  (^ⁿ-StrictMonotoneR m n 1<x (ℕ.predℕ-≤-predℕ sm<sn))

IsContinuous^ⁿ : ∀ n → IsContinuous (_^ⁿ n)
IsContinuous^ⁿ zero = IsContinuousConst _
IsContinuous^ⁿ (suc n) = cont₂·ᵣ _ _ (IsContinuous^ⁿ n) IsContinuousId



module bⁿ-aⁿ n'  where

 n = suc (suc n')

 nᵣ₊ : ℝ₊
 nᵣ₊ = fromNat n


 module factor a b (0<a : 0 <ᵣ a) (0<b : 0 <ᵣ b) where



  0＃b : 0 ＃ b
  0＃b = inl 0<b
  r = (a ／ᵣ[ b , 0＃b ])

  S = Sₙ (b ^ⁿ (suc n')) r n


  0<r : 0 <ᵣ r
  0<r = isTrans<≡ᵣ _ _ _
   (  (fst (0<x≃0<y₊·x a (invℝ₊ (b , 0<b))) 0<a))
      (·ᵣComm _ _ ∙
        cong (a ·ᵣ_) (invℝ₊≡invℝ _ _ ))


  0<S : 0 <ᵣ S
  0<S = 0<seqΣ' (geometricProgression (b ^ⁿ (suc n')) r)
        (λ n → subst (0 <ᵣ_)
           (sym (geometricProgressionClosed (b ^ⁿ (suc n')) r n))
            (ℝ₊· (_ , (0<x^ⁿ b (suc n') 0<b)) (_ , (0<x^ⁿ r n 0<r))))
        (suc n')

  S₊ : ℝ₊
  S₊ = S , 0<S

  0≤r : 0 ≤ᵣ r
  0≤r = <ᵣWeaken≤ᵣ _ _ 0<r



  [b-a]·S≡bⁿ-aⁿ : (b -ᵣ a) ·ᵣ Sₙ ((b ^ⁿ (suc n'))) r n ≡ (b ^ⁿ n) -ᵣ (a ^ⁿ n)
  [b-a]·S≡bⁿ-aⁿ =
     ·ᵣComm _ _ ∙ cong ((Sₙ ((b ^ⁿ (suc n'))) r n) ·ᵣ_)
        (cong₂ _+ᵣ_ (sym (·IdL b)) (cong (-ᵣ_) (sym ([x/y]·yᵣ a b 0＃b))
         ∙ sym (-ᵣ· _ _)) ∙ sym (·DistR+ _ _ _))
       ∙ ·ᵣAssoc _ _ _ ∙ cong (_·ᵣ b) (SₙLem' (b ^ⁿ (suc n')) n r)
        ∙  cong (_·ᵣ b) (·ᵣComm _ _)
       ∙ sym (·ᵣAssoc _ _ _)
       ∙ ·DistR+ _ _ _
       ∙ cong₂ _+ᵣ_ (·IdL _)
          (-ᵣ· _ _ ∙ cong (-ᵣ_)
           (sym (x/y≡z→x≡z·y _ _ _ _ (／^ⁿ n _ _ _ (inl (0<x^ⁿ b n 0<b))))) )

  module _ A B (0<A : 0 <ᵣ A) (A<b : A <ᵣ b)
    (0<B : 0 <ᵣ B) (A<B : A <ᵣ B) (b≤B : b ≤ᵣ B) (a<b : a <ᵣ b) where

   a＃b : a ＃ b
   a＃b = inl a<b


   p : 0 ＃ ((1 -ᵣ (r ^ⁿ n)) ·ᵣ b )
   p = 0＃· ((1 -ᵣ (r ^ⁿ n))) b (invEq (＃Δ 1 ((a ·ᵣ invℝ b (inl 0<b)) ^ⁿ suc (suc n')))
     (isSym＃ _ _ ((1＃^ _ ((
       <ᵣWeaken≤ᵣ _ _ (isTrans<≡ᵣ _ _ _
        (fst (0<x≃0<y₊·x a (invℝ₊ (b , 0<b))) 0<a) (·ᵣComm _ _ ∙
           cong (a ·ᵣ_) (invℝ₊≡invℝ _ _)))))
       (suc n') (((fst ((1＃x/y _ _ 0<a 0<b)) (isSym＃ _ _ (a＃b))))))))) 0＃b


   r<1 : r <ᵣ 1
   r<1 = fst (x/y<1 a b 0<a 0<b) a<b


   S≤Bⁿ·n : S ≤ᵣ ((B ^ⁿ (suc n')) ·ᵣ (fromNat n))
   S≤Bⁿ·n =
       (isTrans≤≡ᵣ _ _ _ (Seq≤→Σ≤ (geometricProgression (b ^ⁿ (suc n')) r)
      (const (B ^ⁿ (suc n')))
       (λ m →
         isTrans≡≤ᵣ _ _ _
           (geometricProgressionClosed _ r m)
            (isTrans≤≡ᵣ _ _ _ (
             isTrans≤ᵣ _ _ _
              (≤ᵣ-·ᵣo _ _ _  (0≤x^ⁿ r m 0≤r) (
                ^ⁿ-Monotone (suc n')
                 (<ᵣWeaken≤ᵣ _ _ 0<b) b≤B))
                 (≤ᵣ-o·ᵣ (r ^ⁿ m) 1 (B ^ⁿ (suc n'))
                  (0≤x^ⁿ B (suc n') (<ᵣWeaken≤ᵣ _ _ 0<B))
                    (^≤1 r 0≤r m (<ᵣWeaken≤ᵣ _ _  r<1))))
                (·IdR _)))
       (suc (suc n')))
       ((seqSumUpToConst (B ^ⁿ (suc n')) n)))



   Aⁿ≤S : (A ^ⁿ suc n') ≤ᵣ S
   Aⁿ≤S = <ᵣWeaken≤ᵣ _ _ $
     isTrans<≤ᵣ _ _ _
      (^ⁿ-StrictMonotone (suc n') (ℕ.suc-≤-suc (ℕ.zero-≤ {n'}))
          (<ᵣWeaken≤ᵣ _ _ 0<A) (<ᵣWeaken≤ᵣ _ _ 0<b) A<b)
           (isTrans≡≤ᵣ _ _ _  (sym (+IdR _)) (≤ᵣ-o+ 0 _ _
                  (0≤seqΣ' (λ x → geometricProgression ((b ^ⁿ n') ·ᵣ b) r (suc x))
                       (λ n → isTrans≤≡ᵣ _ _ _
                          (<ᵣWeaken≤ᵣ _ _ (ℝ₊· (_ , 0<x^ⁿ _ (suc n') 0<b)
                               (_ , 0<x^ⁿ r (suc n) 0<r)))
                           (((sym (geometricProgressionClosed
                           ((b ^ⁿ n') ·ᵣ b) r (suc n))))))
                        (suc n'))))
 open factor public


^ⁿMonotone⁻¹ : ∀ {x y : ℝ} (n : ℕ) → (0 ℕ.< n) → 0 <ᵣ x → 0 <ᵣ y
 → (x ^ⁿ n) ≤ᵣ (y ^ⁿ n) → x ≤ᵣ y
^ⁿMonotone⁻¹ zero 0<n 0≤x 0≤y xⁿ≤yⁿ = ⊥.rec (ℕ.¬-<-zero 0<n)
^ⁿMonotone⁻¹ (suc zero) 0<n 0≤x 0≤y xⁿ≤yⁿ =
  subst2 _≤ᵣ_ (·IdL _) (·IdL _) xⁿ≤yⁿ
^ⁿMonotone⁻¹ {x} {y} (suc (suc n)) 0<n 0<x 0<y xⁿ<yⁿ =
 let z = isTrans≤≡ᵣ _ _ _ (x≤y→0≤y-x _ _ xⁿ<yⁿ)
          (sym $ bⁿ-aⁿ.[b-a]·S≡bⁿ-aⁿ n x y 0<x 0<y)
 in invEq (x≤y≃0≤y-x x y)
      ((invEq (z≤x≃y₊·z≤y₊·x (y -ᵣ x) 0
          ((bⁿ-aⁿ.S n x y 0<x 0<y ,
                  bⁿ-aⁿ.0<S n x y 0<x 0<y)))
         (subst2 _≤ᵣ_
           (sym (𝐑'.0RightAnnihilates (bⁿ-aⁿ.S n x y 0<x 0<y)))
            (·ᵣComm (y -ᵣ x) _) z)))


^ⁿMonotone⁻¹-with0 : ∀ {x y : ℝ} (n : ℕ) → (0 ℕ.< n) → 0 ≤ᵣ x → 0 <ᵣ y
 → (x ^ⁿ n) ≤ᵣ (y ^ⁿ n) → x ≤ᵣ y
^ⁿMonotone⁻¹-with0 {x} {y} n 0<n 0≤x 0<y xⁿ≤yⁿ =
  PT.rec (isProp≤ᵣ _ _)
    (⊎.rec
      (<ᵣWeaken≤ᵣ _ _ )
      (λ y/2<x →
        ^ⁿMonotone⁻¹ {x} {y} n 0<n
         (isTrans<ᵣ _ _ _ (snd ((y , 0<y) ₊·ᵣ ℚ₊→ℝ₊ [ 1 / 2 ]₊))
           y/2<x) 0<y xⁿ≤yⁿ))
    (Dichotomyℝ' (y ·ᵣ rat [ 1 / 2 ]) x y
      (isTrans<≡ᵣ _ _ _ (<ᵣ-o·ᵣ _ _ (_ , 0<y) decℚ<ᵣ?) (·IdR _) ))


^ⁿStrictMonotone⁻¹ : ∀ {x y : ℝ} (n : ℕ) → (0 ℕ.< n) → 0 <ᵣ x → 0 <ᵣ y
 → (x ^ⁿ n) <ᵣ (y ^ⁿ n) → x <ᵣ y
^ⁿStrictMonotone⁻¹ zero 0<n 0≤x 0≤y xⁿ<yⁿ = ⊥.rec (ℕ.¬-<-zero 0<n)
^ⁿStrictMonotone⁻¹ (suc zero) 0<n 0≤x 0≤y xⁿ<yⁿ =
  subst2 _<ᵣ_ (·IdL _) (·IdL _) xⁿ<yⁿ
^ⁿStrictMonotone⁻¹ {x} {y} (suc (suc n)) 0<n 0<x 0<y xⁿ<yⁿ =
 let z = isTrans<≡ᵣ _ _ _ (x<y→0<y-x _ _ xⁿ<yⁿ)
          (sym $ bⁿ-aⁿ.[b-a]·S≡bⁿ-aⁿ n x y 0<x 0<y)
 in 0<y-x→x<y _ _
      (invEq (z<x≃y₊·z<y₊·x (y -ᵣ x) 0
          ((bⁿ-aⁿ.S n x y 0<x 0<y ,
                  bⁿ-aⁿ.0<S n x y 0<x 0<y)))
         (subst2 _<ᵣ_
           (sym (𝐑'.0RightAnnihilates (bⁿ-aⁿ.S n x y 0<x 0<y)))
            (·ᵣComm (y -ᵣ x) _) z))

-- _~seq_ : Seq → Seq → Type
-- s ~seq s' = ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ m n → N ℕ.< n → N ℕ.< m →
--    absᵣ ((s n) +ᵣ (-ᵣ (s' m))) <ᵣ rat (fst ε)   )


-- IsCauchySequence : Seq → Type
-- IsCauchySequence s =
--   ∀ (ε : ℝ₊) → Σ[ N ∈ ℕ ] (∀ m n → N ℕ.< n → N ℕ.< m →
--     absᵣ ((s n) +ᵣ (-ᵣ (s m))) <ᵣ fst ε)


IsCauchySequence' : Seq → Type
IsCauchySequence' s =
  ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ m n → N ℕ.< n → N ℕ.< m →
    absᵣ ((s n) +ᵣ (-ᵣ (s m))) <ᵣ rat (fst ε)   )


-- IsCauchySequence'-via-~seq : ∀ s s' → s ~seq s' → IsCauchySequence' s → IsCauchySequence' s'
-- IsCauchySequence'-via-~seq s s' s~s' icS ε =
--   let (N , X) = icS (/2₊ ε)
--       (M , Y) = s~s' (/2₊ ε)
--   in M , (λ m n <m <n →
--      let zz = Y m n <m <n
--          yy = Y n n <m <m
--          uu = isTrans≡<ᵣ _ _ _ (cong absᵣ (sym L𝐑.lem--060))
--                 (isTrans≤<ᵣ _ _ _
--                  (absᵣ-triangle _ _)
--                   (<ᵣMonotone+ᵣ _ _ _ _ (isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _) yy) zz))
--       in isTrans<≡ᵣ _ _ _ uu (+ᵣ-rat _ _ ∙ cong rat (ℚ.ε/2+ε/2≡ε _)))



-- IsCauchySequence'ℚ : (ℕ → ℚ) → Type
-- IsCauchySequence'ℚ s =
--   ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ m n → N ℕ.< n → N ℕ.< m →
--     ℚ.abs ((s n) ℚ.- (s m)) ℚ.< (fst ε)   )


-- IsConvSeries : Seq → Type
-- IsConvSeries s =
--     ∀ (ε : ℝ₊) →
--      Σ[ N ∈ ℕ ] ∀ n m →
--        absᵣ (seqΣ (s ∘ (ℕ._+ (n ℕ.+ (suc N)))) m) <ᵣ fst ε

-- IsConvSeries' : Seq → Type
-- IsConvSeries' s =
--     ∀ (ε : ℚ₊) →
--      Σ[ N ∈ ℕ ] ∀ n m →
--        absᵣ (seqΣ (s ∘ (ℕ._+ (n ℕ.+ (suc N)))) m) <ᵣ rat (fst ε)


-- IsoIsConvSeriesIsCauchySequenceSum : (s : Seq) →
--   Iso (IsConvSeries s) (IsCauchySequence (seqΣ s))
-- IsoIsConvSeriesIsCauchySequenceSum s =
--    codomainIsoDep λ ε →
--      Σ-cong-iso-snd λ N →
--         isProp→Iso (isPropΠ2 λ _ _ → isProp<ᵣ _ _)
--          (isPropΠ4 λ _ _ _ _ → isProp<ᵣ _ _ )
--          (λ f → ℕ.elimBy≤
--            (λ n n' X <n <n' → subst (_<ᵣ fst ε)
--              (minusComm-absᵣ _ _) (X <n' <n))
--            λ n n' n≤n' N<n' N<n →
--               subst ((_<ᵣ fst ε) ∘ absᵣ)
--                  (cong (λ x → seqΣ (s ∘ (ℕ._+ x)) (n' ∸ n))
--                     (ℕ.[n-m]+m (suc N) n N<n)
--                    ∙∙ sym (seriesDiff s n (n' ∸ n)) ∙∙
--                    cong (_+ᵣ (-ᵣ seqΣ s n))
--                      (cong (seqΣ s)
--                        (ℕ.[n-m]+m n n' n≤n')))
--                  (f (n ∸ (suc N)) (n' ∸ n)))
--          λ f n m →
--            subst ((_<ᵣ fst ε) ∘ absᵣ)
--              (seriesDiff s (n ℕ.+ suc N) m)
--                (f (n ℕ.+ (suc N)) (m ℕ.+ (n ℕ.+ suc N))
--                (subst (N ℕ.<_) (sym (ℕ.+-assoc _ _ _))
--                  (ℕ.≤SumRight {suc N} {m ℕ.+ n}))
--                (ℕ.≤SumRight {suc N} {n}))


-- IsConvSeries≃IsCauchySequenceSum : (s : Seq) →
--   IsConvSeries s ≃ IsCauchySequence (seqΣ s)
-- IsConvSeries≃IsCauchySequenceSum s =
--   isoToEquiv (IsoIsConvSeriesIsCauchySequenceSum s)

-- IsoIsConvSeries'IsCauchySequenceSum' : (s : Seq) →
--   Iso (IsConvSeries' s) (IsCauchySequence' (seqΣ s))
-- IsoIsConvSeries'IsCauchySequenceSum' s =
--  codomainIsoDep λ ε →
--      Σ-cong-iso-snd λ N →
--         isProp→Iso (isPropΠ2 λ _ _ → isProp<ᵣ _ _)
--          (isPropΠ4 λ _ _ _ _ → isProp<ᵣ _ _)

--          (λ f → ℕ.elimBy≤
--            (λ n n' X <n <n' → subst (_<ᵣ rat (fst ε))
--              (minusComm-absᵣ _ _) (X <n' <n))
--            λ n n' n≤n' N<n' N<n →
--               subst ((_<ᵣ rat (fst ε)) ∘ absᵣ)
--                  (cong (λ x → seqΣ (s ∘ (ℕ._+ x)) (n' ∸ n))
--                     (ℕ.[n-m]+m (suc N) n N<n)
--                    ∙∙ sym (seriesDiff s n (n' ∸ n)) ∙∙
--                    cong (_+ᵣ (-ᵣ seqΣ s n))
--                      (cong (seqΣ s)
--                        (ℕ.[n-m]+m n n' n≤n')))
--                  (f (n ∸ (suc N)) (n' ∸ n)))
--          λ f n m →
--            subst ((_<ᵣ rat (fst ε)) ∘ absᵣ)
--              (seriesDiff s (n ℕ.+ suc N) m)
--                (f (n ℕ.+ (suc N)) (m ℕ.+ (n ℕ.+ suc N))
--                (subst (N ℕ.<_) (sym (ℕ.+-assoc _ _ _))
--                  (ℕ.≤SumRight {suc N} {m ℕ.+ n}))
--                (ℕ.≤SumRight {suc N} {n}))


-- IsConvSeries'≃IsCauchySequence'Sum : (s : Seq) →
--   IsConvSeries' s ≃ IsCauchySequence' (seqΣ s)
-- IsConvSeries'≃IsCauchySequence'Sum s =
--   isoToEquiv (IsoIsConvSeries'IsCauchySequenceSum' s)

-- isCauchyAprox : (ℚ₊ → ℝ) → Type
-- isCauchyAprox f = (δ ε : ℚ₊) →
--   (absᵣ (f δ +ᵣ (-ᵣ  f ε)) <ᵣ rat (fst (δ ℚ₊+ ε)))

-- lim' : ∀ x → isCauchyAprox x → ℝ
-- lim' x y = lim x λ δ ε  → (invEq (∼≃abs<ε _ _ _)) (y δ ε)

-- -- HoTT 11.3.49

-- fromCauchySequence : ∀ s → IsCauchySequence s → ℝ
-- fromCauchySequence s ics =
--   lim x y

--  where
--  x : ℚ₊ → ℝ
--  x q = s (suc (fst (ics (ℚ₊→ℝ₊ q))))

--  y : (δ ε : ℚ₊) → x δ ∼[ δ ℚ₊+ ε ] x ε
--  y δ ε = invEq (∼≃abs<ε _ _ _)
--     (ww (ℕ.Dichotomyℕ δₙ εₙ) )
--   where
--   δₙ = fst (ics (ℚ₊→ℝ₊ δ))
--   εₙ = fst (ics (ℚ₊→ℝ₊ ε))

--   ww : _ ⊎ _ → absᵣ (x δ +ᵣ (-ᵣ x ε)) <ᵣ rat (fst (δ ℚ₊+ ε))
--   ww (inl δₙ≤εₙ) =
--    let z = snd (ics (ℚ₊→ℝ₊ δ)) (suc εₙ) (suc δₙ)
--               ℕ.≤-refl  (ℕ.suc-≤-suc δₙ≤εₙ )
--    in isTrans<ᵣ (absᵣ (x δ +ᵣ (-ᵣ x ε)))
--            (rat (fst (δ))) (rat (fst (δ ℚ₊+ ε)))
--            z (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' (fst δ) (fst δ) ε (ℚ.isRefl≤ (fst δ))))
--   ww (inr εₙ<δₙ) =
--     let z = snd (ics (ℚ₊→ℝ₊ ε)) (suc εₙ) (suc δₙ)
--                (ℕ.≤-suc εₙ<δₙ) ℕ.≤-refl
--     in isTrans<ᵣ (absᵣ (x δ +ᵣ (-ᵣ x ε)))
--            (rat (fst (ε))) (rat (fst (δ ℚ₊+ ε)))
--            z ((<ℚ→<ᵣ _ _
--                (subst ((fst ε) ℚ.<_) (ℚ.+Comm _ _)
--                (ℚ.<+ℚ₊' (fst ε) (fst ε) δ (ℚ.isRefl≤ (fst ε))))))


-- TODO HoTT 11.3.50.


fromCauchySequence'-isCA : ∀ s → (ics : IsCauchySequence' s) →
      (δ ε : ℚ₊) → s (suc (fst (ics δ)))  ∼[ δ ℚ₊+ ε ]
                    s (suc (fst (ics ε)))
fromCauchySequence'-isCA s ics δ ε = invEq (∼≃abs<ε _ _ _)
    (ww (ℕ.Dichotomyℕ δₙ εₙ) )
  where

  x : ℚ₊ → ℝ
  x q = s (suc (fst (ics q)))

  δₙ = fst (ics δ)
  εₙ = fst (ics ε)

  ww : _ ⊎ _ → absᵣ (x δ +ᵣ (-ᵣ x ε)) <ᵣ rat (fst (δ ℚ₊+ ε))
  ww (inl δₙ≤εₙ) =
   let z = snd (ics δ) (suc εₙ) (suc δₙ)
              ℕ.≤-refl  (ℕ.suc-≤-suc δₙ≤εₙ )
   in isTrans<ᵣ (absᵣ (x δ +ᵣ (-ᵣ x ε)))
           (rat (fst (δ))) (rat (fst (δ ℚ₊+ ε)))
           z (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' (fst δ) (fst δ) ε (ℚ.isRefl≤ (fst δ))))
  ww (inr εₙ<δₙ) =
    let z = snd (ics ε) (suc εₙ) (suc δₙ)
               (ℕ.≤-suc εₙ<δₙ) ℕ.≤-refl
    in isTrans<ᵣ (absᵣ (x δ +ᵣ (-ᵣ x ε)))
           (rat (fst (ε))) (rat (fst (δ ℚ₊+ ε)))
           z ((<ℚ→<ᵣ _ _
               (subst ((fst ε) ℚ.<_) (ℚ.+Comm (ε .fst) (fst δ))
               (ℚ.<+ℚ₊' (fst ε) (fst ε) δ (ℚ.isRefl≤ (fst ε))))))


fromCauchySequence' : ∀ s → IsCauchySequence' s → ℝ
fromCauchySequence' s ics =
  lim _ (fromCauchySequence'-isCA s ics)



-- open ℚ.HLP


-- fromCauchySequence'-≡-lem : ∀ s ics ics'
--         →  fromCauchySequence' s ics ≡ fromCauchySequence' s ics'
-- fromCauchySequence'-≡-lem s ics ics' =
--   eqℝ _ _
--     λ ε →
--       let (n , N) = ics (/4₊ ε)
--           (m , M) = ics' (/4₊ ε)
--           n⊔m = ℕ.max (suc n) (suc m)
--        in lim-lim _ _ _ (/4₊ ε) (/4₊ ε) _ _
--            (distℚ0<! ε (
--                ge1 +ge (neg-ge ((ge[ ℚ.[ 1 / 4 ] ] +ge ge[ ℚ.[ 1 / 4 ] ]))) ))
--            (subst∼ distℚ! (fst ε) ·[ (ge[ ℚ.[ 1 / 4 ] ] +ge ge[ ℚ.[ 1 / 4 ] ]) ≡
--                ge1 +ge (neg-ge ((ge[ ℚ.[ 1 / 4 ] ] +ge ge[ ℚ.[ 1 / 4 ] ]))) ]
--           (triangle∼
--             (invEq (∼≃abs<ε _ _ (/4₊ ε)) (N n⊔m (suc n) ℕ.≤-refl ℕ.left-≤-max))
--             (invEq (∼≃abs<ε _ _ (/4₊ ε)) (M (suc m) n⊔m ℕ.right-≤-max ℕ.≤-refl))))

-- fromCauchySequence'-≡ : ∀ s s' ics ics'
--   → (∀ n → s n ≡ s' n)
--   → fromCauchySequence' s ics ≡ fromCauchySequence' s' ics'
-- fromCauchySequence'-≡ s s' ics ics' p =
--   cong (uncurry fromCauchySequence')
--     (ΣPathP (funExt p , toPathP refl))
--     ∙ fromCauchySequence'-≡-lem s' _ _

-- fromCauchySequence'₁ : ∀ s → ∥ IsCauchySequence' s ∥₁ → ℝ
-- fromCauchySequence'₁ s = PT.rec→Set isSetℝ
--   (fromCauchySequence' s)
--   (fromCauchySequence'-≡-lem s)

opaque
 fromCauchySequence'≡ : ∀ s ics x
          → ((∀ (ε : ℚ₊) →
              ∃[ N ∈ ℕ ] (∀ n → N ℕ.< n →
                   absᵣ ((s n) -ᵣ x) <ᵣ rat (fst ε))))
          → fromCauchySequence' s ics ≡ x
 fromCauchySequence'≡ s ics x p =
    eqℝ _ _
   λ ε → PT.rec (isProp∼ _ _ _)
     (λ (N , X) →
      let z = ℕ.max (suc N) (suc (fst (ics (/4₊ ε))))
          uu = invEq (∼≃abs<ε _ _ ((/4₊ ε))) ((X z (ℕ.left-≤-max {n = suc (fst (ics (/4₊ ε)))})))
          uuu = triangle∼ (sym∼ _ _ _
           (𝕣-lim-self _ (fromCauchySequence'-isCA s ics) (/4₊ ε) (/4₊ ε)))
             (triangle∼
           (invEq (∼≃abs<ε _ _ (/4₊ ε))
             ((snd (ics (/4₊ ε))
               z ((suc (fst (ics (/4₊ ε))))) ℕ.≤-refl
                ℕ.right-≤-max))) uu)
      in subst∼ (cong₂ ℚ._+_ (cong fst (ℚ./4₊+/4₊≡/2₊ ε))
         ((cong fst (ℚ./4₊+/4₊≡/2₊ ε))) ∙ ℚ.ε/2+ε/2≡ε _) uuu)
     (p (/4₊ ε))

-- fromCauchySequence'₁≡ : ∀ s ics x
--          → ((∀ (ε : ℚ₊) →
--              ∃[ N ∈ ℕ ] (∀ n → N ℕ.< n →
--                   absᵣ ((s n) -ᵣ x) <ᵣ rat (fst ε))))
--          → fromCauchySequence'₁ s ics ≡ x
-- fromCauchySequence'₁≡ s ics x p =
--   PT.elim {P = λ ics → fromCauchySequence'₁ s ics ≡ x}
--     (λ _ → isSetℝ _ _)
--     (λ ics → fromCauchySequence'≡ s ics x p)
--     ics



-- limₙ→∞_is_ : Seq → ℝ → Type
-- limₙ→∞ s is x =
--   ∀ (ε : ℝ₊) → Σ[ N ∈ ℕ ]
--     (∀ n → N ℕ.< n →
--       absᵣ ((s n) +ᵣ (-ᵣ x)) <ᵣ (fst ε))

-- lim'ₙ→∞_is_ : Seq → ℝ → Type
-- lim'ₙ→∞ s is x =
--   ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ]
--     (∀ n → N ℕ.< n →
--       absᵣ ((s n) +ᵣ (-ᵣ x)) <ᵣ (rat (fst ε)))


-- fromCauchySequence'-lim : ∀ s ics → lim'ₙ→∞ s is (fromCauchySequence' s ics)
-- fromCauchySequence'-lim s ics ε =
--  let (N , X) = ics (/4₊ ε)
--  in N , λ n N<n →
--       let u = (𝕣-lim-self _ (fromCauchySequence'-isCA s ics) (/4₊ ε) (/4₊ ε))
--           u' = fst (∼≃abs<ε _ _ _)
--                (triangle∼ (invEq (∼≃abs<ε _ _ (/4₊ ε)) ((X  _ _  N<n (ℕ.≤-refl {suc N})) )) u)
--        in isTrans<ᵣ _ _ _ u'
--             (<ℚ→<ᵣ _ _
--               distℚ<! ε [ ge[ ℚ.[ 1 / 4 ] ]
--                             +ge  (ge[ ℚ.[ 1 / 4 ] ] +ge ge[ ℚ.[ 1 / 4 ] ]) < ge1 ])



-- cauchySequenceFaster : ∀ s
--   → (spd : ∀ n → Σ _ (n ℕ.≤_))
--     (ics : IsCauchySequence' s)

--   → Σ[ ics' ∈ IsCauchySequence' (s ∘ fst ∘ spd) ]
--       fromCauchySequence' s ics ≡
--        fromCauchySequence' (λ z → (s ∘ (λ r → fst r) ∘ spd) z) ics'
-- cauchySequenceFaster s spd ics =
--   ics' ,
--    sym (fromCauchySequence'≡ (s ∘ fst ∘ spd) ics' _
--       (λ ε →
--          let (N , X) = fromCauchySequence'-lim s ics ε
--          in ∣ N , (λ n <n → X _ (ℕ.<≤-trans <n (snd (spd _)))) ∣₁))
--  where
--  ics' = map-snd (λ X _ _ n< m< →
--    X _ _ (ℕ.<≤-trans n< (snd (spd _))) (ℕ.<≤-trans m< (snd (spd _)))) ∘ ics


-- fromCauchySequence'₁-∘+ : ∀ s k ics ics' →
--        fromCauchySequence'₁ s ics
--      ≡ fromCauchySequence'₁ (s ∘ (k ℕ.+_)) ics'
-- fromCauchySequence'₁-∘+ s k =
--   PT.elim2 (λ _ _ → isSetℝ _ _)
--    λ ics ics' →
--     fromCauchySequence'≡ _ _ _
--       (λ ε →
--          let (N , X) = fromCauchySequence'-lim (s ∘ (k ℕ.+_)) ics' ε
--          in ∣ k ℕ.+ N , (λ n x →
--             isTrans≡<ᵣ _ _ _
--               (cong absᵣ (cong₂ _-ᵣ_ (cong s (sym (snd x) ∙
--                  (   ℕ.+-assoc (x .fst) (suc k) N
--                   ∙∙ cong (ℕ._+ N) (ℕ.+-comm (fst x) (suc k))
--                    ∙ sym (+-suc _ _)
--                   ∙∙ sym (ℕ.+-assoc k (x .fst) (suc N)))))
--                refl))
--               (X (fst x ℕ.+ suc N) (ℕ.≤SumRight {suc N})) ) ∣₁)

-- Limₙ→∞ : Seq → Type
-- Limₙ→∞ s = Σ _ (limₙ→∞ s is_)


ε<2ⁿ : (ε : ℚ₊) → Σ[ n ∈ ℕ ] fst ε ℚ.< 2 ℚ^ⁿ n
ε<2ⁿ ε = let n = fst (ℕ.log2ℕ (ℕ₊₁→ℕ  (fst (ℚ.ceilℚ₊ ε)))) in n ,
         subst (fst ε ℚ.<_) (sym (ℚ.fromNat-^ 2 n))
          (ℚ.isTrans< _ _ (fromNat (2 ^ n))
                  ((snd (ℚ.ceilℚ₊ ε)))
                   (ℚ.<ℤ→<ℚ (ℤ.pos (ℕ₊₁→ℕ (fst (ℚ.ceilℚ₊ ε))))
                     _ (ℤ.ℕ<→pos-<-pos _ _ ((fst (snd (ℕ.log2ℕ (ℕ₊₁→ℕ (fst (ℚ.ceilℚ₊ ε))))))))))


1/2ⁿ<ε : (ε : ℚ₊) → Σ[ n ∈ ℕ ] [ 1 / 2 ] ℚ^ⁿ n ℚ.< fst ε
1/2ⁿ<ε ε =
 let (n , 1/ε<n) = ε<2ⁿ (invℚ₊ ε)
 in n , invEq (ℚ.invℚ₊-<-invℚ₊ (([ 1 / 2 ]₊) ℚ₊^ⁿ n) ε)
         (subst (fst (invℚ₊ ε) ℚ.<_)
           (sym (ℚ.invℚ₊-ℚ^ⁿ ([ 1 / 2 ]₊) n)) 1/ε<n)




-- ratio→ℚseqLimit : ∀ (s : Seq) → (∀ n → Σ[ r ∈ ℚ ] (s n ≡ rat r))
--   → (sPos : ∀ n → rat 0 <ᵣ (s n))
--   → lim'ₙ→∞ (λ n →  s (suc n) ／ᵣ[ s n , inl ((sPos n)) ]) is 0
--   → lim'ₙ→∞ s is 0
-- ratio→ℚseqLimit s sRat sPos l (ε , 0<ε) =
--  (uncurry w)
--     (l ([ 1 / 2 ] , _))

--  where
--  opaque
--   unfolding -ᵣ_
--   w : ∀ N → ((n : ℕ) →  N ℕ.< n →
--            absᵣ ((s (suc n) ／ᵣ[ s n , inl (sPos n) ]) +ᵣ (-ᵣ 0)) <ᵣ
--            rat [ 1 / 2 ]) →
--         Σ ℕ (λ N → (n : ℕ) → N ℕ.< n → absᵣ (s n +ᵣ (-ᵣ 0)) <ᵣ rat ε)
--   w N f =
--       let 0<s' = ((subst (0 <ᵣ_) (snd (sRat (suc N))))
--                     (sPos (suc N)))
--           δ₊ = (ε , 0<ε) ℚ₊· invℚ₊ (fst (sRat (suc N)) ,
--                   (ℚ.<→0< _  (<ᵣ→<ℚ 0 _
--                     0<s')))
--           (m½ , q) = 1/2ⁿ<ε δ₊
--           pp : rat ([ 1 / 2 ] ℚ^ⁿ m½)  <ᵣ
--                   ((rat ε ·ᵣ invℝ (s (suc N)) (inl (sPos _))))
--           pp = isTrans<≡ᵣ _ _ _ (<ℚ→<ᵣ _ _ q)
--                   (rat·ᵣrat _ _ ∙
--                     cong (rat ε ·ᵣ_)
--                       (cong rat (sym (ℚ.invℚ₊≡invℚ _
--                         (inl (<ᵣ→<ℚ 0 _ 0<s'))))
--                         ∙ sym (invℝ-rat _ (inl 0<s') _) ∙
--                         cong₂ invℝ (sym (snd (sRat (suc N))))
--                           (isProp→PathP (λ i → isProp＃ _ _)  _ _)))
--           pp' = subst ((rat ([ ℤ.pos 1 / 1+ 1 ] ℚ^ⁿ m½) ·ᵣ s (suc N)) <ᵣ_)
--                    ([x/y]·yᵣ _ _ _) (<ᵣ-·ᵣo _ _ (s (suc N) , (sPos _)) pp)
--           zzz : ∀ m → s (((suc (suc (m ℕ.+ m½))) ℕ.+ N))
--                       ≤ᵣ
--                        s (suc N) ·ᵣ  (rat ([ ℤ.pos 1 / 1+ 1 ] ℚ^ⁿ m½))
--           zzz m  = isTrans≤ᵣ _ _ _ (g (m ℕ.+ m½))
--                       (≤ᵣ-o·ᵣ _ _ (s (suc N)) (<ᵣWeaken≤ᵣ _ _ (sPos _))
--                         (≤ℚ→≤ᵣ _ _ (subst2 ℚ._≤_ (ℚ.·-ℚ^ⁿ (suc m) m½ [ 1 / 2 ])
--                             (ℚ.·IdL _)
--                            (ℚ.≤-·o (([ ℤ.pos 1 / 1+ 1 ] ℚ^ⁿ (suc m)))
--                                 1 _ ((ℚ.0≤ℚ₊ (_ ℚ₊^ⁿ m½)))
--                                    (ℚ.x^ⁿ≤1 [ ℤ.pos 1 / 1+ 1 ] (suc m)
--                                      (𝟚.toWitness
--                                         {Q = ℚ.≤Dec 0  [ ℤ.pos 1 / 1+ 1 ]} tt)
--                                      (𝟚.toWitness
--                                         {Q = ℚ.≤Dec [ ℤ.pos 1 / 1+ 1 ] 1} tt))
--                                    ))) )
--       in (1 ℕ.+ m½) ℕ.+ N ,
--            λ m <m →
--             isTrans≤<ᵣ _ _ _ (
--                 subst2 (_≤ᵣ_)
--                 (cong s ((cong (ℕ._+ N) (cong suc (sym (+-suc _ _))
--                  ∙ sym (+-suc _ _)) ∙ sym (ℕ.+-assoc _ _ N) )
--                     ∙ snd <m) ∙ sym (absᵣPos _ (sPos _))
--                   ∙ cong absᵣ (sym (+IdR (s m))) )
--                   (·ᵣComm _ _)
--                  (zzz (fst <m)) --(zzz m <m)
--                  ) pp'
--            --   (lowerℚBound (ε ·ᵣ invℝ (s (suc N)) (inl (sPos _)))
--            -- (ℝ₊· (ε , 0<ε) (_ , invℝ-pos (s (suc N)) (sPos _))))
--    where

--     f' : ((n : ℕ) →  N ℕ.< n →
--            (s (suc n)) <ᵣ
--            s n ·ᵣ rat [ 1 / 2 ])
--     f' n n< =
--      subst2 _<ᵣ_
--        ((congS (_·ᵣ s n) (+IdR _) ∙
--          [x/y]·yᵣ _ _ _)) (·ᵣComm _ _)
--       (<ᵣ-·ᵣo _ _ (s n , sPos _)
--        (isTrans≤<ᵣ _ _ _ (≤absᵣ _) (f n n<)))

--     g : ∀ m → s ((suc (suc m)) ℕ.+ N)
--               ≤ᵣ (s (suc N)) ·ᵣ rat ([ 1 / 2 ] ℚ^ⁿ (suc m))
--     g zero = subst (s (suc (suc N)) ≤ᵣ_)
--                  (cong ((s (suc N) ·ᵣ_) ∘ rat) (sym (ℚ.·IdR _)))
--                   (<ᵣWeaken≤ᵣ _ _ (f' (suc N) (ℕ.≤-refl {suc N})))
--     g (suc m) =
--       isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ (f' (2 ℕ.+ m ℕ.+ N)
--        (subst (N ℕ.<_)
--          (cong suc (ℕ.+-suc _ _)) (ℕ.≤SumRight {suc N} {suc m})))) ww
--      where
--      ww : (s (suc (suc m) ℕ.+ N) ·ᵣ rat [ 1 / 2 ]) ≤ᵣ
--           (s (suc N) ·ᵣ rat ([ 1 / 2 ] ℚ^ⁿ suc (suc m)))

--      ww =
--         subst ((s (suc (suc m) ℕ.+ N) ·ᵣ rat [ 1 / 2 ]) ≤ᵣ_)

--           (sym (·ᵣAssoc _ _ _) ∙
--             cong (s (suc N) ·ᵣ_) (sym (rat·ᵣrat _ _)))
--              (≤ᵣ-·o _ _ [ 1 / 2 ] (ℚ.decℚ≤? {0} {[ 1 / 2 ]}) (g m))



-- ratioTest₊ : ∀ (s : Seq) → (sPos : ∀ n → rat 0 <ᵣ (s n))
--      → lim'ₙ→∞ s is 0
--      → (lim'ₙ→∞ (λ n →  s (suc n) ／ᵣ[ s n , inl ((sPos n)) ]) is 0)
--      → IsConvSeries' s
-- ratioTest₊ s sPos l' l ε₊@(ε , 0<ε) =
--   N , ww

--  where
--  ½ᵣ = (ℚ₊→ℝ₊ ([ 1 / 2 ] , _))
--  N½ = l ([ 1 / 2 ] , _)
--  ε/2 : ℚ₊
--  ε/2 = /2₊ ε₊

--  Nε = (l' ε/2)

--  N : ℕ
--  N = suc (ℕ.max (suc (fst N½)) (fst Nε))

--  ww : ∀ m n → absᵣ (seqΣ (λ x → s (x ℕ.+ (m ℕ.+ suc N))) n) <ᵣ (rat ε)
--  ww m n = isTrans≤<ᵣ _ _ _
--    (≡ᵣWeaken≤ᵣ _ _
--      (absᵣNonNeg (seqΣ (λ x → s (x ℕ.+ (m ℕ.+ suc N))) n)
--      (0≤seqΣ _ (λ n → <ᵣWeaken≤ᵣ _ _ (sPos (n ℕ.+ (m ℕ.+ suc N)))) _))) pp

--   where
--   opaque
--    unfolding -ᵣ_ _+ᵣ_

--    s' : Seq
--    s' = s ∘ (ℕ._+ (suc (m ℕ.+ N)))


--    f' : ((n : ℕ) →  N ℕ.≤ n →
--           (s (suc n)) ≤ᵣ
--           s n ·ᵣ rat [ 1 / 2 ])
--    f' n n< =
--       subst2 {x = ((s (suc n) ／ᵣ[ s n , inl (sPos n) ])
--                      +ᵣ 0 ) ·ᵣ s n }
--          _≤ᵣ_ (congS (_·ᵣ s n) (+IdR _) ∙
--            [x/y]·yᵣ _ _ _) (·ᵣComm _ _)
--         ((<ᵣWeaken≤ᵣ _ _
--            (<ᵣ-·ᵣo _ _ (s n , sPos _)
--             (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
--               (snd N½ n (
--                ℕ.<-trans (ℕ.left-≤-max {suc (fst N½)} {fst Nε})
--                 n<))))))


--    p : ∀ n → s' n ≤ᵣ geometricProgression (s (m ℕ.+ N)) (fst ½ᵣ) n
--    p zero =
--       isTrans≤ᵣ _ _ _ ((f' (m ℕ.+ N) (ℕ.≤SumRight {N} {m}) ))
--               (subst ((s (m ℕ.+ N) ·ᵣ rat [ ℤ.pos 1 / 1+ 1 ]) ≤ᵣ_)
--                  (·IdR _)
--                   (≤ᵣ-o·ᵣ (fst ½ᵣ) 1 (s (m ℕ.+ N))
--                     (<ᵣWeaken≤ᵣ _ _ (sPos _))
--                    (≤ℚ→≤ᵣ _ _ ((𝟚.toWitness {Q = ℚ.≤Dec ([ 1 / 2 ]) 1} _)))))

--    p (suc n) =
--      isTrans≤ᵣ _ _ _ (f' _
--        (subst (N ℕ.≤_) (sym (ℕ.+-assoc n (1 ℕ.+ m) N))
--          ℕ.≤SumRight))
--        (≤ᵣ-·o _ _ ([ 1 / 2 ]) ((𝟚.toWitness {Q = ℚ.≤Dec 0 ([ 1 / 2 ])} _)) (p n))

--    p' : ∀ n → seqSumUpTo' s' n ≤ᵣ seqSumUpTo' (geometricProgression (s (m ℕ.+ N)) (fst ½ᵣ)) n
--    p' = Seq'≤→Σ≤ s' (geometricProgression (s (m ℕ.+ N)) (fst ½ᵣ))
--          p

--    s<ε : (s (m ℕ.+ N)) <ᵣ rat (fst ε/2)
--    s<ε = subst (_<ᵣ rat (fst ε/2)) (+IdR _)
--             ((isTrans≤<ᵣ _ _ _
--            (≤absᵣ ((s (m ℕ.+ N)) +ᵣ (-ᵣ 0))) (snd Nε _
--             (ℕ.≤<-trans ℕ.right-≤-max ℕ.≤SumRight))))


--    pp : (seqΣ (λ x → s (x ℕ.+ (m ℕ.+ suc N))) n) <ᵣ (rat ε)
--    pp =
--        subst {x = ℕ._+ suc (m ℕ.+ N) } {y = λ z → z ℕ.+ (m ℕ.+ suc N)}
--             (λ h → seqΣ (s ∘S h) n <ᵣ rat ε)

--            (funExt (λ x → cong (x ℕ.+_) (sym (ℕ.+-suc _ _)) ))
--            (isTrans≤<ᵣ _ _ _ (p' n)
--              (isTrans≤<ᵣ _ _ _
--                (≡ᵣWeaken≤ᵣ _ _ (seqSumUpTo≡seqSumUpTo' _ _))
--                  (isTrans<≤ᵣ _ _ _
--                   (Sₙ-sup (s (m ℕ.+ N)) (fst ½ᵣ)
--                     n (sPos _) (snd ½ᵣ)
--                      (<ℚ→<ᵣ _ _ ((𝟚.toWitness {Q = ℚ.<Dec [ 1 / 2 ] 1} tt))))
--                  (isTrans≤ᵣ _ _ _
--                    (≤ᵣ₊Monotone·ᵣ _ _ _ 2
--                          (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ (ℚ.0<ℚ₊ ε/2)))
--                            (<ᵣWeaken≤ᵣ _ _
--                               ((0<1/x _ _ (
--                         <ℚ→<ᵣ _ _
--                         (𝟚.toWitness {Q = ℚ.<Dec 0 [ 1 / 2 ]} tt)))))

--                      (<ᵣWeaken≤ᵣ _ _ s<ε)
--                      (≡ᵣWeaken≤ᵣ _ _
--                         (invℝ-rat _ _
--                          (inl ((𝟚.toWitness {Q = ℚ.<Dec 0 [ 1 / 2 ]} tt))))))
--                          (≡ᵣWeaken≤ᵣ _ _ (sym (rat·ᵣrat _  _) ∙
--                            cong rat (sym (ℚ.·Assoc _ _ _) ∙
--                              cong (ε ℚ.·_) ℚ.decℚ? ∙ ℚ.·IdR _)))

--                          ))))


expSeq : ℝ → Seq
expSeq x zero = 1
expSeq x (suc n) = /nᵣ (1+ n) (expSeq x n ·ᵣ x)


expSeq-rat : ∀ (q : ℚ) → (n : ℕ) → Σ[ r ∈ ℚ ] (expSeq (rat q) n ≡ rat r)
expSeq-rat q zero = 1 , refl
expSeq-rat q (suc n) =
  let (e , p) = expSeq-rat q n
  in (e ℚ.· q)  ℚ.· [ 1 / (1+ n) ] ,
       cong (/nᵣ (1+ n)) (cong (_·ᵣ (rat q)) p ∙ sym (rat·ᵣrat _ _))
       ∙ fromLipschitz-rat
       
expSeries-rat : ∀ (q : ℚ) → (n : ℕ) →
  Σ[ r ∈ ℚ ] (seqΣ (expSeq (rat q)) n ≡ rat r)
expSeries-rat q zero = 0 , refl
expSeries-rat q (suc n) =
  let (e , p) = expSeries-rat q n
      (e' , p') = expSeq-rat q n
  in (e ℚ.+ e') , cong₂ _+ᵣ_ p p' ∙ +ᵣ-rat _ _

-- _ : ℚ
-- _ = {!10000 ℚ.· ℚ.[ (fst (ℚ.reduced $ fst (expSeries-rat 1 30))) ]!}

expSeqPos : ∀ x → 0 <ᵣ x → ∀ n → 0 <ᵣ expSeq x n
expSeqPos x 0<x zero = decℚ<ᵣ?
expSeqPos x 0<x (suc n) =
 /nᵣ-pos (1+ n) _ (ℝ₊· (_ , expSeqPos x 0<x n) (_ , 0<x))

-- limₙ→∞[expSeqRatio]=0 : ∀ x → ∀ (0<x : 0 ℚ.< x)  → lim'ₙ→∞
--       (λ n →
--          expSeq (rat x) (suc n) ／ᵣ[ expSeq (rat x) n ,
--          inl (expSeqPos (rat x) (<ℚ→<ᵣ 0 x 0<x) n) ])
--       is 0
-- limₙ→∞[expSeqRatio]=0 x 0<x =
--   subst (lim'ₙ→∞_is 0)
--     (funExt (w (rat x) (<ℚ→<ᵣ 0 x 0<x)))
--     w'

--  where
--  opaque
--   unfolding -ᵣ_

--   x₊ : ℚ₊
--   x₊ = x , ℚ.<→0< _ 0<x

--   0<ᵣx : 0 <ᵣ rat x
--   0<ᵣx = <ℚ→<ᵣ 0 x 0<x
--   w : ∀ x 0<x n → (x ·ᵣ rat ([ 1 / 1+ n ])) ≡ (expSeq x (suc n) ／ᵣ[ expSeq x n ,
--                      inl (expSeqPos x 0<x n) ])
--   w x 0<x zero = cong₂ {y = expSeq x 1} _·ᵣ_
--          (( sym (·IdR x) ∙
--          (cong
--              (x ·ᵣ_) (sym (invℝ-rat _
--                (invEq (rat＃ _ _) (inl (ℚ.decℚ<? {0} {1})))
--                 (inl (ℚ.decℚ<? {0} {1}))))) ∙ sym (/nᵣ-／ᵣ 1 (x)
--            (invEq (rat＃ _ _) (inl (ℚ.decℚ<? {0} {1}))))
--             ∙ (cong (/nᵣ 1) (sym (·IdL x))) ) )
--       (sym (invℝ-rat 1 (inl ((expSeqPos x 0<x zero)))
--              ((inl (ℚ.decℚ<? {0} {1})))))

--   w x 0<x (suc n) =
--     let z = _
--         z' = _
--     in ((cong (x ·ᵣ_) ((sym (·IdL _) ∙
--           cong₂ _·ᵣ_ (sym (x·invℝ[x] _ _))
--             (cong rat (sym (ℚ.fromNat-invℚ _
--                  (inl (ℚ.<ℤ→<ℚ _ _ (ℤ.suc-≤-suc ℤ.zero-≤pos )))))
--               ∙ sym (invℝ-rat _ _ _)))
--                 ∙ sym (·ᵣAssoc _ _ _))
--           ∙ ·ᵣAssoc _ (expSeq x (suc n)) _)
--             ∙ cong₂ (_·ᵣ_) (·ᵣComm _ _) (·ᵣComm z' z))
--         ∙ (·ᵣAssoc _ z z'
--           ∙ cong (_／ᵣ[ expSeq x (suc n) ,
--                      inl (expSeqPos x 0<x (suc n)) ])
--                       (sym (/nᵣ-／ᵣ (2+ n) (/nᵣ (1+ n) (expSeq x n ·ᵣ x) ·ᵣ x)
--                         (inl (<ℚ→<ᵣ 0 _ (ℚ.<ℤ→<ℚ _ _
--                           (ℤ.suc-≤-suc ℤ.zero-≤pos )))))))

--   w' : lim'ₙ→∞ (λ n → (rat x ·ᵣ rat ([ 1 / 1+ n ]))) is 0
--   w' ε =
--    let (cN , X) = ℚ.ceilℚ₊ (x₊ ℚ₊· (invℚ₊ ε))

--        X'' = subst (ℚ._< [ pos (ℕ₊₁→ℕ cN) / 1+ 0 ])
--                 (cong (x ℚ.·_) (sym (ℚ.invℚ₊≡invℚ ε _) ))
--               X
--        X' : x ℚ.· [ pos 1 / 1+ (ℕ₊₁→ℕ cN) ] ℚ.< fst ε

--        X' = subst (ℚ._< fst ε)
--               ((cong (x ℚ.·_) (ℚ.fromNat-invℚ _ _)))
--              (ℚ.ℚ-x/y<z→x/z<y x [ pos (suc (ℕ₊₁→ℕ cN)) / 1 ] (fst ε)
--                          0<x (ℚ.<ℤ→<ℚ _ _ (ℤ.suc-≤-suc ℤ.zero-≤pos))
--                           (ℚ.0<→< _ (snd ε))
--                           (ℚ.isTrans< _ [ pos ((ℕ₊₁→ℕ cN)) / 1+ 0 ] _
--                             X'' (ℚ.<ℤ→<ℚ _ _ ℤ.isRefl≤ )))
--    in (suc (ℕ₊₁→ℕ cN)) , (λ n' <n' →
--        let 0<n' = ℚ.<ℤ→<ℚ _ _
--               (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.suc-≤-suc ℕ.zero-≤))
--        in isTrans≡<ᵣ _ _ _
--            (cong absᵣ (+IdR _) ∙ absᵣPos _
--              (ℝ₊· (_ , <ℚ→<ᵣ 0 x 0<x)
--                         (_ ,
--                            <ℚ→<ᵣ _ _
--                             (ℚ.invℚ-pos [ pos (suc n') / 1 ]
--                              (inl 0<n') 0<n')))
--                               ∙ sym (rat·ᵣrat _ _))
--             (<ℚ→<ᵣ _ _ (ℚ.isTrans< _ _ _
--               (ℚ.<-o· [ 1 / 1+ n' ]
--                       [ 1 / 1+ (ℕ₊₁→ℕ cN) ] x 0<x
--                        ((ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-suc <n'))))
--                            X')))


-- limₙ→∞[expSeq]=0 : ∀ x → (0<x : 0 ℚ.< x) →  lim'ₙ→∞ expSeq (rat x) is 0
-- limₙ→∞[expSeq]=0 x 0<x =
--   ratio→ℚseqLimit _ (expSeq-rat x)
--       (expSeqPos (rat x) _) (limₙ→∞[expSeqRatio]=0 x 0<x)

opaque
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
         let
             3ε/4<ε = ℚ.<- _ _ (subst (0 ℚ.<_)
                          ℚ! (ℚ.0<ℚ₊ (/4₊ ε)))
             z' = invEq (∼≃abs<ε _ _ (/4₊ ε)) (X' ((suc N')) n
                  (ℕ.<-trans (ℕ.suc-≤-suc (ℕ.right-≤-max {N'} {N})) midN<n)
                   ℕ.≤-refl )

             zzzz' =
                 (𝕣-lim-self _ (fromCauchySequence'-isCA s ics)
                       ((invℚ₊ L ℚ₊· (/4₊ ε))) ( (invℚ₊ L ℚ₊· (/4₊ ε))))

         in fst (∼≃abs<ε _ _ ε)
              (∼-monotone< 3ε/4<ε
                 (triangle∼ z' (lf _ _ _ zzzz')))) ∣₁

-- map-fromCauchySequence'₁ : ∀ L s ics f → (Lipschitz-ℝ→ℝ L f) →
--     Σ _ λ icsf →
--       f (fromCauchySequence'₁ s ics) ≡ fromCauchySequence'₁ (f ∘ s) icsf
-- map-fromCauchySequence'₁ L s ics f lipLf =
--   PT.elim
--     (λ ics → isPropΣ squash₁
--       λ icsf → isSetℝ (f (fromCauchySequence'₁ s ics))
--                     (fromCauchySequence'₁ (f ∘ s) icsf))
--     (λ ics → ∣ _ ∣₁ , snd (map-fromCauchySequence' L s ics f lipLf))
--     ics


-- map-fromCauchySequence'ℙ : ∀ L s ics P f → (Lipschitz-ℝ→ℝℙ L P f) →
--    ∀ lim∈ →
--    (s∈ : ∀ n → s n ∈ P) →
--     Σ _ λ icsf →
--        f (fromCauchySequence' s ics) lim∈ ≡
--         fromCauchySequence' (λ n → f (s n) (s∈ n))
--           icsf
-- map-fromCauchySequence'ℙ L s ics P f lf lim∈ s∈ =
--   icsf , sym (fromCauchySequence'≡ _ _ _ h)


--  where
--  open ℚ.HLP

--  icsf : IsCauchySequence' (λ n → f (s n) (s∈ n))
--  icsf ε = map-snd
--    (λ X m n <m <n →
--       let z = X m n <m <n
--           z' = lf (s n) (s∈ n) (s m) (s∈ m) (invℚ₊ L ℚ₊· ε)
--                 (invEq (∼≃abs<ε _ _ _) z)
--        in fst (∼≃abs<ε _ _ ε) (subst∼ (ℚ.y·[x/y] L (fst ε)) z'))
--    (ics (invℚ₊ L ℚ₊· ε))

--  h : (ε : ℚ₊) →
--        ∃-syntax ℕ
--        (λ N →
--           (n : ℕ) →
--           N ℕ.< n →
--           absᵣ (f (s n) (s∈ n)
--             -ᵣ f (fromCauchySequence' s ics) lim∈) <ᵣ rat (fst ε))
--  h ε =
--    let (N , X) = ics ((invℚ₊ L ℚ₊· (/4₊ ε)))
--        (N' , X') = icsf (/4₊ ε)
--        midN = suc (ℕ.max N N')
--        midV = f (s midN)

--    in ∣ midN , (λ n midN<n →
--         let 3ε/4<ε = subst (ℚ._< (fst ε))
--                             (cong (fst (/4₊ ε) ℚ.+_)
--                               (sym (ℚ.y·[x/y] L _)
--                                ∙ cong (fst L ℚ.·_) (ℚ.·DistL+ _ _ _) ))

--                                (distℚ<! ε [ ((ge[ ℚ.[ 1 / 4 ] ]) +ge
--                                    (ge[ ℚ.[ 1 / 4 ] ] +ge ge[ ℚ.[ 1 / 4 ] ]))
--                                    < ge1 ])
--             z' = invEq (∼≃abs<ε _ _ (/4₊ ε)) (X' ((suc N')) n
--                  (ℕ.<-trans (ℕ.suc-≤-suc ℕ.right-≤-max) midN<n)
--                   ℕ.≤-refl )

--             zzzz' =
--                 (𝕣-lim-self _ (fromCauchySequence'-isCA s ics)
--                       ((invℚ₊ L ℚ₊· (/4₊ ε))) ( (invℚ₊ L ℚ₊· (/4₊ ε))))

--         in fst (∼≃abs<ε _ _ ε)
--              (∼-monotone< 3ε/4<ε
--                 (triangle∼ z' (lf _ _ _ _ _ zzzz')))) ∣₁

-- isCauchySequence'-const : ∀ C → IsCauchySequence' λ _ → C
-- isCauchySequence'-const C ε = 0 ,
--   λ _ _ _ _ → isTrans≡<ᵣ _ _ _
--    (cong absᵣ (CRℝ.+InvR C) ∙ absᵣ0) (snd (ℚ₊→ℝ₊ ε))


-- fromCauchySequence'-const : ∀ C ics →
--  fromCauchySequence' (λ _ → C) ics ≡ C
-- fromCauchySequence'-const C ics =
--   fromCauchySequence'≡ _ _ C
--    λ ε →  ∣ (0 , λ _ _  → isTrans≡<ᵣ _ _ _
--    (cong absᵣ (CRℝ.+InvR C) ∙ absᵣ0) (snd (ℚ₊→ℝ₊ ε))) ∣₁

-- cauchySequenceSpeedup : ∀ s
--     → (ics : IsCauchySequence' s)
--     → (spd : ℚ₊ → ℕ)
--     → (∀ ε → fst (ics ε) ℕ.≤ spd ε)

--     → IsCauchySequence' s
-- cauchySequenceSpeedup s  ics spd ≤spd ε =
--  let (N , X) = ics ε
--  in spd ε ,
--      λ m n spdN<n spdN<m →

--         X m n (ℕ.≤<-trans (≤spd ε) spdN<n)
--                (ℕ.≤<-trans (≤spd ε) spdN<m)
-- opaque
--  unfolding _≤ᵣ_
--  cauchySequenceSpeedup≡ : ∀ s ics spd ≤spd →
--    fromCauchySequence' s ics ≡
--     fromCauchySequence' s (cauchySequenceSpeedup s ics spd ≤spd   )
--  cauchySequenceSpeedup≡ s ics spd ≤spd =
--    fromCauchySequence'-≡-lem _ _ _

--  fromCauchySequence'≤ : ∀ s ics s' ics'
--    → (∀ n → s n ≤ᵣ s' n)
--    → fromCauchySequence' s ics ≤ᵣ fromCauchySequence' s' ics'
--  fromCauchySequence'≤ s ics s' ics' x =
--    cong₂ maxᵣ
--       (cauchySequenceSpeedup≡ s  ics
--          (λ ε → ℕ.max (ℕ.max (fst (ics ε)) (fst (ics' ε))) ((fst (ics' (2 ℚ₊· ε)))))
--            λ ε → ℕ.≤-trans ℕ.left-≤-max ℕ.left-≤-max)
--       (cauchySequenceSpeedup≡ s' ics'
--          ((λ ε → ℕ.max (ℕ.max (fst (ics ε)) (fst (ics' ε))) ((fst (ics' (2 ℚ₊· ε))))))
--            λ ε → ℕ.≤-trans ℕ.right-≤-max ℕ.left-≤-max) ∙
--    snd (NonExpanding₂.β-lim-lim/2 maxR _ _ _ _) ∙
--      (congLim _ _ _ _
--       λ q →  x (suc (fastS q)))
--       ∙
--        sym (cauchySequenceSpeedup≡ s' ics'
--          fastS λ ε → subst (ℕ._≤ fastS ε) (cong (fst ∘ ics')
--            ((ℚ₊≡ (cong (2 ℚ.·_) (ℚ.·Comm _ _) ∙ ℚ.y·[x/y] 2 _)))) ℕ.right-≤-max)

--   where
--    fastS : ℚ₊ → ℕ
--    fastS ε = ℕ.max (ℕ.max (fst (ics (/2₊ ε)))
--         (fst (ics' (/2₊ ε))))
--                (fst (ics' (2 ℚ₊· /2₊ ε)))

--  fromCauchySequence'₁≤ : ∀ s s' ics ics'
--    → (∀ n → s n ≤ᵣ s' n)
--    → fromCauchySequence'₁ s ics ≤ᵣ fromCauchySequence'₁ s' ics'
--  fromCauchySequence'₁≤ s s' =
--    PT.elim2
--      (λ ics ics' → isPropΠ λ _ → isProp≤ᵣ
--        (fromCauchySequence'₁ s ics) (fromCauchySequence'₁ s' ics'))
--      λ ics ics' p → fromCauchySequence'≤ s ics s' ics' p

-- mapNE-fromCauchySequence' : ∀ {h} (ne : NonExpanding₂ h) s ics s' ics' →
--     Σ (IsCauchySequence'
--          λ k → NonExpanding₂.go ne (s k) (s' k)) λ icsf →
--       NonExpanding₂.go ne
--         (fromCauchySequence' s ics)
--         (fromCauchySequence' s' ics')
--           ≡
--            fromCauchySequence' _ icsf
-- mapNE-fromCauchySequence' ne s ics s' ics' =
--  (λ  ε →
--   let (N , X) = ics (/2₊ ε)
--       (N' , X') = ics' (/2₊ ε)
--   in ℕ.max N N' , λ m n <n <m →
--        isTrans<≡ᵣ _ _ _ (fst (∼≃abs<ε _ _ _) (go∼₂ (/2₊ ε) (/2₊ ε)
--            (invEq (∼≃abs<ε _ _ _)
--              (X m n (ℕ.≤<-trans ℕ.left-≤-max <n)
--                     (ℕ.≤<-trans ℕ.left-≤-max <m)))
--            (invEq (∼≃abs<ε _ _ _)
--               ((X' m n (ℕ.≤<-trans ℕ.right-≤-max <n)
--                        (ℕ.≤<-trans ℕ.right-≤-max <m)))))
--           ) (cong rat (ℚ.ε/2+ε/2≡ε (fst ε))))
--    , cong₂ go
--        (cauchySequenceSpeedup≡ _ _
--           (λ ε → ℕ.max (fst (ics ε)) (fst (ics' ε)))
--             λ _ → ℕ.left-≤-max)
--        (cauchySequenceSpeedup≡ _ _
--           (λ ε → ℕ.max (fst (ics ε)) (fst (ics' ε)))
--             λ _ → ℕ.right-≤-max)
--       ∙ snd (β-lim-lim/2 _ _ _ _)
--          ∙ congLim _ _ _ _ λ _ → refl

--  where
--  open NonExpanding₂ ne



-- fromConvAbs : (s : Seq)
--       → IsConvSeries' (absᵣ ∘ s)
--       → IsConvSeries' s
-- fromConvAbs s =
--   map-snd (λ X n m →
--     isTrans≤<ᵣ _ _ _
--       (isTrans≤≡ᵣ _ _ _
--         (abs[seqΣ]≤seqΣ[abs] _ _)
--         (sym (seqΣ[abs]≡abs[seqΣ[abs]] _ _)))
--       (X n m))
--     ∘_

-- ratioTest : ∀ (s : Seq)
--      → (0＃sₙ : ∀ n → 0 ＃ s n )
--      → lim'ₙ→∞ s is 0
--      → lim'ₙ→∞ (λ n →  s (suc n) ／ᵣ[ s n , 0＃sₙ n ]) is 0
--      → IsConvSeries' s
-- ratioTest s 0＃sₙ l' l =
--   fromConvAbs s
--     (ratioTest₊ (absᵣ ∘ s)
--       (0＃→0<abs _ ∘ 0＃sₙ)
--       abs-l' abs-l)
--  where
--  abs-l' : lim'ₙ→∞ (λ x → absᵣ (s x)) is 0
--  abs-l' = map-snd (λ X →
--    λ n x → isTrans≡<ᵣ _ _ _
--           (cong absᵣ (cong₂ _+ᵣ_ refl (-ᵣ-rat 0) ∙ +IdR _)
--              ∙∙ absᵣNonNeg _ (0≤absᵣ _)
--              ∙∙ cong absᵣ (sym (cong₂ _+ᵣ_ refl (-ᵣ-rat 0) ∙ +IdR _)))
--           (X n x)) ∘ l'

--  abs-l : lim'ₙ→∞
--           (λ n →
--              absᵣ (s (suc n)) ／ᵣ[ absᵣ (s n) , inl (0＃→0<abs (s n) (0＃sₙ n)) ])
--           is 0
--  abs-l = map-snd (λ X →
--    λ n x → isTrans≡<ᵣ _ _ _
--           (cong absᵣ (cong₂ _+ᵣ_ refl (-ᵣ-rat 0) ∙ +IdR _)
--              ∙∙ cong absᵣ (
--                   cong₂ _·ᵣ_
--                     refl
--                     (sym (invℝ₊≡invℝ _ _)
--                      ∙ sym (absᵣ-invℝ _ _))
--                 ∙ sym (·absᵣ _ _))
--               ∙ absᵣNonNeg _ (0≤absᵣ _)
--              ∙∙ cong absᵣ (sym (cong₂ _+ᵣ_ refl (-ᵣ-rat 0) ∙ +IdR _)))
--           (X n x)) ∘ l


-- expSeriesConvergesAtℚ₊ : ∀ x → 0 ℚ.< x → IsConvSeries' (expSeq (rat x))
-- expSeriesConvergesAtℚ₊ x 0<x =
--  ratioTest₊ (expSeq (rat x)) (expSeqPos (rat x) (<ℚ→<ᵣ _ _ 0<x))
--       (limₙ→∞[expSeq]=0 x  0<x)
--       (limₙ→∞[expSeqRatio]=0 x 0<x)



-- expℚ₊ : ℚ₊ → ℝ
-- expℚ₊ q = fromCauchySequence' _
--   (fst (IsConvSeries'≃IsCauchySequence'Sum (expSeq (rat (fst q))))
--     (expSeriesConvergesAtℚ₊ (fst q) (ℚ.0<ℚ₊ q)))


-- expℝ-convSeriesF : ∀ r r' → absᵣ r <ᵣ r' → ∀ (ε : ℚ₊) →
--         ∀ N →
--          ((n m : ℕ) →
--            absᵣ (seqΣ (λ x → expSeq r' (x ℕ.+ (n ℕ.+ suc N))) m) <ᵣ
--            rat (fst ε))
--          → (n m : ℕ) →
--             absᵣ (seqΣ (λ x → expSeq r (x ℕ.+ (n ℕ.+ suc N))) m) <ᵣ rat (fst ε)
-- expℝ-convSeriesF r r' ∣r∣<r' ε a X n m =
--     isTrans≤<ᵣ _ _ _
--       (isTrans≤ᵣ _ _ _
--        (abs[seqΣ]≤seqΣ[abs] _ _)
--        (isTrans≤≡ᵣ _ (seqΣ (λ x → expSeq r' (x ℕ.+ (n ℕ.+ suc a))) m) _
--          (Seq'≤→Σ≤ _ _ (λ n →
--            zzz' _)
--           m)
--          (sym (abs[seqΣ]≡seqΣ _ _
--            λ _ → <ᵣWeaken≤ᵣ _ _ $
--               expSeqPos r' (isTrans≤<ᵣ _ _ _
--               (0≤absᵣ r) ∣r∣<r') _))))
--       (X n m)
--    where

--    zzz' : ∀ n → absᵣ (expSeq r n) ≤ᵣ expSeq r' n
--    zzz' zero = ≡ᵣWeaken≤ᵣ _ _ (absᵣ-rat 1)
--    zzz' (suc n) = subst2 _≤ᵣ_
--      (cong₂ _·ᵣ_ (sym (·absᵣ _ _))
--       (sym (absᵣPos _ (invℝ-pos _ _)))
--        ∙ sym (·absᵣ _ _) ∙
--       cong absᵣ (sym (/nᵣ-／ᵣ _ _ (inl (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _))))))
--      (sym (/nᵣ-／ᵣ _ _ (inl (<ℚ→<ᵣ _ _ (ℚ.0<pos _ _)))))
--      (≤ᵣ-·ᵣo _ _ _
--        (<ᵣWeaken≤ᵣ _ _
--          (invℝ-pos _ _))
--        ((≤ᵣ₊Monotone·ᵣ _ _ _ _
--         (<ᵣWeaken≤ᵣ _ _
--           (expSeqPos r'
--             (isTrans≤<ᵣ _ _ _
--               (0≤absᵣ r) ∣r∣<r')
--             n))
--         (0≤absᵣ r)
--         (zzz' n) (<ᵣWeaken≤ᵣ _ _ ∣r∣<r'))))


-- expℝ-convSeries : ∀ r r' → absᵣ r <ᵣ r' →
--         IsConvSeries' (expSeq r') → IsConvSeries' (expSeq r)
-- expℝ-convSeries r r' ∣r∣<r' X ε =
--   map-snd (expℝ-convSeriesF r r' ∣r∣<r' ε _) (X ε)

-- expℝ-cauchySeq : ∀ (r : ℝ) → _
-- expℝ-cauchySeq r = (PT.map
--      (fst (IsConvSeries'≃IsCauchySequence'Sum (expSeq r)) ∘
--       (λ (δ , ∣r∣<δ , _) →
--         expℝ-convSeries r (rat δ) ∣r∣<δ
--          (expSeriesConvergesAtℚ₊ δ
--            (<ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _
--               (0≤absᵣ r) ∣r∣<δ)))))
--     (denseℚinℝ (absᵣ r) (absᵣ r +ᵣ 1)
--        (isTrans≡<ᵣ _ _ _
--          (sym (+IdR _))
--          (<ᵣ-o+ _ _ _
--            decℚ<ᵣ?))))

-- expℝ : ℝ → ℝ
-- expℝ r =
--  fromCauchySequence'₁ (seqΣ (expSeq r)) (expℝ-cauchySeq r)




expSeriesVal : ℕ → ℚ
expSeriesVal n = fst (expSeries-rat 1 n)


-- digits : ℕ → ℚ → ℕ 
-- digits n r =
--  let qq = map-snd ℕ₊₁→ℕ (fst (ℚ.reduced ((ℚ.reduce r) ℚ.· fromNat (10 ℕ.^ n)))) 
--  in {!!}
-- expSeriesValT : Σ ℤ.ℤ (λ _ → ℕ₊₁)
-- expSeriesValT = {!fst (ℚ.reduced (expSeriesVal 100))!}

-- 𝑒 : ℝ
-- 𝑒 = expℚ₊ 1
