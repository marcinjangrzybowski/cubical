{-# OPTIONS --safe #-}
module Cubical.Data.Int.PropertiesAlt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.NatPlusOne.Base as ℕ₊₁
open import Cubical.Data.Nat as ℕ
  hiding   (+-assoc ; +-comm ; min ; max ; minComm ; maxComm)
  renaming (_·_ to _·ℕ_; _+_ to _+ℕ_ ; ·-assoc to ·ℕ-assoc ;
            ·-comm to ·ℕ-comm ; isEven to isEvenℕ ; isOdd to isOddℕ)
open import Cubical.Data.Sum
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties


open import Cubical.Data.Int.Base as ℤ hiding (_+_ ; _·_) renaming (_+f_ to _+_ ; _·f_ to _·_)
open import Cubical.Data.Int.Properties as P  public
 hiding (·lCancel ; ·rCancel; +Assoc ;+Comm;-DistL·;-DistR·;minusPlus;plusMinus
   ;·Assoc;·Comm;·DistL+;·DistR+;·IdL;·IdR;·DistPosRMin;·DistPosRMax;·DistPosLMin;·DistPosLMax;abs·
   ; inj-z+)

-- open import Cubical.Data.Int.Order as P public
--  hiding (<-+-≤; <-+o; <-o+; <-o+-cancel; <-pos+-trans; <Monotone+; ≤-+o; ≤-+o-cancel; ≤-o+; ≤-o+-cancel; ≤-pos+-trans; ≤Monotone+; ≤SumRightPos; 0<o→≤-·o-cancel; 0≤o→≤-·o; 0≤x²; ·suc≤0; ≤-o·-cancel; ≤-·o; ≤-·o-cancel; 0<o→<-·o; 0<o→<-·o-cancel; <-o·-cancel; <-·o; <-·o-cancel; ·suc<0; ·0<; 0<·ℕ₊₁; +0<; 0<→ℕ₊₁; inj-z+)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring


subst-f : (A : (ℤ → ℤ → ℤ) → (ℤ → ℤ → ℤ) → Type) → A ℤ._+_ ℤ._·_ → A _+_ _·_
subst-f A = subst2 A (λ i x y → +≡+f x y i) (λ i x y → ·≡·f x y i)


ℤCommRing : CommRing ℓ-zero
ℤCommRing .fst = ℤ
ℤCommRing .snd .CommRingStr.0r = 0
ℤCommRing .snd .CommRingStr.1r = 1
ℤCommRing .snd .CommRingStr._+_ = _+_
ℤCommRing .snd .CommRingStr._·_ = _·_
CommRingStr.- ℤCommRing .snd = -_
ℤCommRing .snd .CommRingStr.isCommRing = isCommRingℤ'
  where
  abstract
    isCommRingℤ : IsCommRing (pos 0) (pos 1) ℤ._+_ ℤ._·_ (-_)
    isCommRingℤ =
      makeIsCommRing isSetℤ P.+Assoc (λ _ → refl)
                                 P.-Cancel P.+Comm P.·Assoc
                                 P.·IdR P.·DistR+ P.·Comm

    isCommRingℤ' : IsCommRing (pos 0) (pos 1) _+_ _·_ (-_)
    isCommRingℤ' =
     subst-f (λ _+_ _·_ → IsCommRing (pos 0) (pos 1) _+_ _·_ (-_))
       isCommRingℤ


open RingTheory (CommRing→Ring ℤCommRing) public
open CommRingTheory (ℤCommRing) public
-- open RingStr (snd (CommRing→Ring ℤCommRing)) public
open CommRingStr (snd (ℤCommRing)) public hiding (_·_;-_;_+_;_-_)

sucℤ[negsuc]-pos : ∀ k → sucℤ (negsuc k) ≡ - pos k 
sucℤ[negsuc]-pos zero = refl
sucℤ[negsuc]-pos (suc k) = refl

sucℤ+pos-f : ∀ n m → sucℤ (m + pos n) ≡ (sucℤ m) + pos n
sucℤ+pos-f n (pos n₁) = refl
sucℤ+pos-f zero (negsuc n₁) = sym (+IdR _)
sucℤ+pos-f (suc n) (negsuc n₁) = {!sucℤ+pos-f n (negsuc n₁)!}
-- zero m = refl
-- sucℤ+pos-f (suc n) m = cong sucℤ (sucℤ+pos n m)


-- ·lCancel : (c m n : ℤ) → c · m ≡ c · n → ¬ c ≡ 0 → m ≡ n
-- ·lCancel c m n = subst-f
--   (λ _+_ _·_ → c · m ≡ c · n → ¬ c ≡ 0 → m ≡ n) (P.·lCancel c m n)

-- ·rCancel : (c m n : ℤ) → m · c ≡ n · c → ¬ c ≡ 0 → m ≡ n
-- ·rCancel c m n = subst-f
--   (λ _+_ _·_ → m · c ≡ n · c → ¬ c ≡ 0 → m ≡ n) (P.·rCancel c m n)

-- ·DistPosRMin : (x : ℕ) (y z : ℤ) → pos x · min y z ≡ min (pos x · y) (pos x · z)
-- ·DistPosRMin x y z = subst-f
--   (λ _+_ _·_ → pos x · P.min y z ≡ P.min (pos x · y) (pos x · z)) (P.·DistPosRMin x y z)


-- ·DistPosRMax : (x : ℕ) (y z : ℤ) → pos x · P.max y z ≡ P.max (pos x · y) (pos x · z)
-- ·DistPosRMax x y z = subst-f
--   (λ _+_ _·_ → pos x · P.max y z ≡ P.max (pos x · y) (pos x · z)) (P.·DistPosRMax x y z)

-- ·DistPosLMin : (x y : ℤ) (z : ℕ) → min x y · pos z ≡ min (x · pos z) (y · pos z)
-- ·DistPosLMin x y z = subst-f
--   (λ _+_ _·_ → min x y · pos z ≡ min (x · pos z) (y · pos z)) (P.·DistPosLMin x y z)

-- ·DistPosLMax : (x y : ℤ) (z : ℕ) → max x y · pos z ≡ max (x · pos z) (y · pos z)
-- ·DistPosLMax x y z = subst-f
--   (λ _+_ _·_ → max x y · pos z ≡ max (x · pos z) (y · pos z)) (P.·DistPosLMax x y z)

-- inj-z+ : ∀ {z l n} → z + l ≡ z + n → l ≡ n
-- inj-z+ {z} {l} {n} =
--  subst-f
--   (λ _+_ _·_ → z + l ≡ z + n → l ≡ n) (P.inj-z+ {z} {l} {n})

-- -- <-+-≤ : {m n o s : ℤ} → m < n → o ≤ s → m + o < n + s
-- -- <-+-≤ {m} {n} {o} {s} = subst-f
-- --   (λ _+_ _·_ → m < n → o ≤ s → m + o < n + s) (P.<-+-≤ {m} {n} {o} {s})

-- -- <-+o : {m n o : ℤ} → m < n → m + o < n + o
-- -- <-+o {m} {n} {o} = subst-f
-- --   (λ _+_ _·_ → m < n → m + o < n + o) (P.<-+o {m} {n} {o})

-- -- <-o+ : {m n o : ℤ} → m < n → o + m < o + n
-- -- <-o+ {m} {n} {o} = subst-f
-- --   (λ _+_ _·_ → m < n → o + m < o + n) (P.<-o+ {m} {n} {o})

-- -- <-o+-cancel : {o m n : ℤ} → o + m < o + n → m < n
-- -- <-o+-cancel {o} {m} {n} = subst-f
-- --   (λ _+_ _·_ → o + m < o + n → m < n) (P.<-o+-cancel {o} {m} {n})

-- -- <-o·-cancel : {k : ℕ} {m n : ℤ} → m + pos k · m < n + pos k · n → m < n
-- -- <-o·-cancel {k} {m} {n} = subst-f
-- --   (λ _+_ _·_ → m + (pos k · m) < n + (pos k · n) → m < n) (P.<-o·-cancel {k} {m} {n})

-- -- <-pos+-trans : {k : ℕ} {m n : ℤ} → pos k + m < n → m < n
-- -- <-pos+-trans {k} {m} {n} = subst-f
-- --   (λ _+_ _·_ → pos k + m < n → m < n) (P.<-pos+-trans {k} {m} {n})

-- -- <Monotone+ : {m n o s : ℤ} → m < n → o < s → m + o < n + s
-- -- <Monotone+ {m} {n} {o} {s} = subst-f
-- --   (λ _+_ _·_ → m < n → o < s → m + o < n + s) (P.<Monotone+ {m} {n} {o} {s})

-- -- ≤-+o : {m n o : ℤ} → m ≤ n → m + o ≤ n + o
-- -- ≤-+o {m} {n} {o} = subst-f
-- --   (λ _+_ _·_ → m ≤ n → m + o ≤ n + o) (P.≤-+o {m} {n} {o})

-- -- ≤-+o-cancel : {m o n : ℤ} → m + o ≤ n + o → m ≤ n
-- -- ≤-+o-cancel {m} {o} {n} = subst-f
-- --   (λ _+_ _·_ → m + o ≤ n + o → m ≤ n) (P.≤-+o-cancel {m} {o} {n})

-- -- ≤-o+ : {m n o : ℤ} → m ≤ n → o + m ≤ o + n
-- -- ≤-o+ {m} {n} {o} = subst-f
-- --   (λ _+_ _·_ → m ≤ n → o + m ≤ o + n) (P.≤-o+ {m} {n} {o})

-- -- ≤-o+-cancel : {o m n : ℤ} → o + m ≤ o + n → m ≤ n
-- -- ≤-o+-cancel {o} {m} {n} = subst-f
-- --   (λ _+_ _·_ → o + m ≤ o + n → m ≤ n) (P.≤-o+-cancel {o} {m} {n})

-- -- ≤-o·-cancel : {k : ℕ} {m n : ℤ} → m + pos k · m ≤ n + pos k · n → m ≤ n
-- -- ≤-o·-cancel {k} {m} {n} = subst-f
-- --   (λ _+_ _·_ → m + (pos k · m) ≤ n + (pos k · n) → m ≤ n) (P.≤-o·-cancel {k} {m} {n})

-- -- ≤-pos+-trans : {k : ℕ} {m n : ℤ} → pos k + m ≤ n → m ≤ n
-- -- ≤-pos+-trans {k} {m} {n} = subst-f
-- --   (λ _+_ _·_ → pos k + m ≤ n → m ≤ n) (P.≤-pos+-trans {k} {m} {n})

-- -- ≤Monotone+ : {m n o s : ℤ} → m ≤ n → o ≤ s → m + o ≤ n + s
-- -- ≤Monotone+ {m} {n} {o} {s} = subst-f
-- --   (λ _+_ _·_ → m ≤ n → o ≤ s → m + o ≤ n + s) (P.≤Monotone+ {m} {n} {o} {s})

-- -- ≤SumRightPos : {n : ℤ} {k : ℕ} → n ≤ pos k + n
-- -- ≤SumRightPos {n} {k} = subst-f
-- --   (λ _+_ _·_ → n ≤ pos k + n) (P.≤SumRightPos {n} {k})

-- -- 0<o→≤-·o-cancel : {o m n : ℤ} → pos 0 < o → m · o ≤ n · o → m ≤ n
-- -- 0<o→≤-·o-cancel {o} {m} {n} = subst-f
-- --   (λ _+_ _·_ → pos 0 < o → m · o ≤ n · o → m ≤ n) (P.0<o→≤-·o-cancel {o} {m} {n})

-- -- 0≤o→≤-·o : {o m n : ℤ} → pos 0 ≤ o → m ≤ n → m · o ≤ n · o
-- -- 0≤o→≤-·o {o} {m} {n} = subst-f
-- --   (λ _+_ _·_ → pos 0 ≤ o → m ≤ n → m · o ≤ n · o) (P.0≤o→≤-·o {o} {m} {n})

-- -- 0≤x² : (n : ℤ) → pos 0 ≤ n · n
-- -- 0≤x² n = subst-f
-- --   (λ _+_ _·_ → pos 0 ≤ n · n) (P.0≤x² n)

-- -- ·suc≤0 : {m : ℤ} {k : ℕ} → m · pos (suc k) ≤ pos 0 → m ≤ pos 0
-- -- ·suc≤0 {m} {k} = subst-f
-- --   (λ _+_ _·_ → m · pos (suc k) ≤ pos 0 → m ≤ pos 0) (P.·suc≤0 {m} {k})


-- -- ≤-·o : {m n : ℤ} {k : ℕ} → m ≤ n → m · pos k ≤ n · pos k
-- -- ≤-·o {m} {n} {k} = subst-f
-- --   (λ _+_ _·_ → m ≤ n → m · pos k ≤ n · pos k) (P.≤-·o {m} {n} {k})

-- -- ≤-·o-cancel : {m : ℤ} {k : ℕ} {n : ℤ} → m · pos (suc k) ≤ n · pos (suc k) → m ≤ n
-- -- ≤-·o-cancel {m} {k} {n} = subst-f
-- --   (λ _+_ _·_ → m · pos (suc k) ≤ n · pos (suc k) → m ≤ n) (P.≤-·o-cancel {m} {k} {n})

-- -- 0<o→<-·o : {o m n : ℤ} → pos 0 < o → m < n → m · o < n · o
-- -- 0<o→<-·o {o} {m} {n} = subst-f
-- --   (λ _+_ _·_ → pos 0 < o → m < n → m · o < n · o) (P.0<o→<-·o {o} {m} {n})

-- -- 0<o→<-·o-cancel : {o m n : ℤ} → pos 0 < o → m · o < n · o → m < n
-- -- 0<o→<-·o-cancel {o} {m} {n} = subst-f
-- --   (λ _+_ _·_ → pos 0 < o → m · o < n · o → m < n) (P.0<o→<-·o-cancel {o} {m} {n})


-- -- <-·o : {m n : ℤ} {k : ℕ} → m < n → m · pos (suc k) < n · pos (suc k)
-- -- <-·o {m} {n} {k} = subst-f
-- --   (λ _+_ _·_ → m < n → m · pos (suc k) < n · pos (suc k)) (P.<-·o {m} {n} {k})

-- -- <-·o-cancel : {m : ℤ} {k : ℕ} {n : ℤ} → m · pos (suc k) < n · pos (suc k) → m < n
-- -- <-·o-cancel {m} {k} {n} = subst-f
-- --   (λ _+_ _·_ → m · pos (suc k) < n · pos (suc k) → m < n) (P.<-·o-cancel {m} {k} {n})

-- -- ·suc<0 : {m : ℤ} {k : ℕ} → m · pos (suc k) < pos 0 → m < pos 0
-- -- ·suc<0 {m} {k} = subst-f
-- --   (λ _+_ _·_ → m · pos (suc k) < pos 0 → m < pos 0) (P.·suc<0 {m} {k})


-- -- ·0< : ∀ m n → 0< m → 0< n → 0< (m · n)
-- -- ·0< m n p q = subst-f
-- --   (λ _+_ _·_ → 0< m → 0< n → 0< (m · n))
-- --   (P.·0< m n) p q

-- -- 0<·ℕ₊₁ : ∀ m n → 0< (m · pos (ℕ₊₁→ℕ n)) → 0< m
-- -- 0<·ℕ₊₁ m n x = subst-f
-- --   (λ _+_ _·_ → 0< (m · pos (ℕ₊₁→ℕ n)) → 0< m)
-- --   (P.0<·ℕ₊₁ m n) x

-- -- +0< : ∀ m n → 0< m → 0< n → 0< (m + n)
-- -- +0< m n p q = subst-f
-- --   (λ _+_ _·_ → 0< m → 0< n → 0< (m + n))
-- --   (P.+0< m n) p q

-- -- 0<→ℕ₊₁ : ∀ n → 0< n → Σ ℕ₊₁ λ m → n ≡ pos (ℕ₊₁→ℕ m)
-- -- 0<→ℕ₊₁ n x = subst-f
-- --   (λ _+_ _·_ → Σ ℕ₊₁ λ m → n ≡ pos (ℕ₊₁→ℕ m))
-- --   (P.0<→ℕ₊₁ n x)


-- abs· : (m n : ℤ) → abs (m · n) ≡ abs m ·ℕ abs n
-- abs· (pos m) (pos n) = refl
-- abs· (pos zero) (negsuc n) = refl
-- abs· (pos (suc m)) (negsuc n) = refl
-- abs· (negsuc m) (pos zero) = 0≡m·0 m
-- abs· (negsuc m) (pos (suc n)) = refl
-- abs· (negsuc m) (negsuc n) = refl

-- -1·x≡-x : ∀ x → -1 · x ≡ - x
-- -1·x≡-x x = (-DistL· 1 x) ∙ cong (-_) (·IdL x)


-- -- _≤'_ : ℤ → ℤ → Type₀
-- -- m ≤' n = Σ[ k ∈ ℕ ] m + pos k ≡ n

-- -- _<'_ : ℤ → ℤ → Type₀
-- -- m <' n = sucℤ m ≤' n
