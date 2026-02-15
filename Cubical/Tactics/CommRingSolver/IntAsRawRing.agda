module Cubical.Tactics.CommRingSolver.IntAsRawRing where

open import Cubical.Data.Nat hiding (_+_; _·_)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Fast.Int

open import Cubical.Foundations.Prelude

open import Cubical.Tactics.CommRingSolver.RawRing
open import Cubical.Tactics.CommRingSolver.Solver
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Algebra.CommRing.Instances.Fast.Int


ℤAsRawRing : RawRing ℓ-zero
ℤAsRawRing = rawring ℤ (pos zero) (pos (suc zero)) _+_ _·_ (λ k → - k)

private
 variable
  ℓ : Level

module SolverOverFastℤ (ring : CommRing ℓ) where

 module R where
  open CommRingStr (snd ring) public
  open RingTheory (CommRing→Ring ring) public

 module 𝐙 = CommRingStr (snd ℤCommRing)

 fromℕ : ℕ → fst ring
 fromℕ zero = R.0r
 fromℕ (suc n) = R.1r R.+ fromℕ n
 
 fromℤ : ℤ → fst ring
 fromℤ (pos n) = fromℕ n
 fromℤ (negsuc n) = R.- (fromℕ (suc n))


 fromℕ-pres-+ : (x y : ℕ) → fromℕ (x ℕ.+ y) ≡ fromℕ x R.+ fromℕ y
 fromℕ-pres-+ zero y = sym (R.+IdL _)
 fromℕ-pres-+ (suc x) y = cong (R.1r R.+_) (fromℕ-pres-+ x y) ∙ R.+Assoc _ _ _

 
 fromℤ-pres-minus : (x : ℤ) → fromℤ (- x) ≡ R.- fromℤ x
 fromℤ-pres-minus (pos zero) = sym R.0Selfinverse
 fromℤ-pres-minus (pos (suc n)) = refl
 fromℤ-pres-minus (negsuc n) = sym (R.-Idempotent _)


 suc-fromℤ : ∀ z → fromℤ (1 + z) ≡ R.1r R.+ fromℤ (z)
 suc-fromℤ (pos n) = refl
 suc-fromℤ (negsuc zero) =
     sym (R.+InvR _)
   ∙ cong₂ R._-_ refl (sym (R.+IdR _))
 suc-fromℤ (negsuc (suc n)) =
      sym (R.+IdL' _ _ (R.+InvR _))
   ∙∙ sym (R.+Assoc _ _ _)
   ∙∙ cong (R.1r R.+_) (R.-Dist _ _)
   
 fromℤ-pres-+' : (n n₁ : ℕ) →
      fromℤ (pos n + negsuc n₁) ≡
      fromℤ (pos n) R.+ fromℤ (negsuc n₁)
 fromℤ-pres-+' zero n₁ = sym (R.+IdL _)
 fromℤ-pres-+' (suc n) n₁ = 
    (cong fromℤ (sym (𝐙.+Assoc 1 (pos n) (negsuc n₁)))
     ∙ suc-fromℤ (pos n + negsuc n₁))
    ∙∙ cong (R.1r R.+_) (fromℤ-pres-+' n n₁)
    ∙∙ R.+Assoc _ _ _
 
 fromℤ-pres-+ : (x y : ℤ) → fromℤ (x + y) ≡ fromℤ x R.+ fromℤ y
 fromℤ-pres-+ (pos n) (pos n₁) = fromℕ-pres-+ n n₁
 fromℤ-pres-+ (pos n) (negsuc n₁) = fromℤ-pres-+' n n₁
 fromℤ-pres-+ (negsuc n) (pos n₁) = 
       fromℤ-pres-+' n₁ n
     ∙ R.+Comm _ _
    
 fromℤ-pres-+ (negsuc n) (negsuc n₁) =
     cong (R.-_)
       (cong (R.1r R.+_) (cong fromℕ (sym (ℕ.+-suc n n₁)))
        ∙ fromℕ-pres-+ (suc n) (suc n₁))
   ∙ sym (R.-Dist _ _)


 fromℕ-pres-· : (x y : ℕ) → fromℕ (x ℕ.· y) ≡ fromℕ x R.· fromℕ y
 fromℕ-pres-· zero y = sym (R.0LeftAnnihilates _)
 fromℕ-pres-· (suc x) y =
     fromℕ-pres-+ y (x ℕ.· y)
   ∙∙ cong₂ (R._+_) (sym (R.·IdL _)) (fromℕ-pres-· x y) 
   ∙∙ sym (R.·DistL+ _ _ _)

 fromℤ-pres-· : (x y : ℤ) → fromℤ (x · y) ≡ fromℤ x R.· fromℤ y
 fromℤ-pres-· (pos n) (pos n₁) = fromℕ-pres-· n n₁
 fromℤ-pres-· (pos zero) (negsuc n₁) = {!!}
 fromℤ-pres-· (pos (suc n)) (negsuc n₁) = {!!}
 fromℤ-pres-· (negsuc n) (pos zero) = {!!}
 fromℤ-pres-· (negsuc n) (pos (suc n₁)) = {!!}
 fromℤ-pres-· (negsuc n) (negsuc n₁) =
        fromℕ-pres-· (suc n) (suc n₁)
    ∙∙ cong₂ R._·_ (sym (R.-Idempotent _)) refl
    ∙∙ R.-Swap· _ _
 
 isHomFromℤ : IsCommRingHom (ℤCommRing .snd) fromℤ (ring .snd)
 isHomFromℤ .IsCommRingHom.pres0 = refl
 isHomFromℤ .IsCommRingHom.pres1 = R.+IdR _
 isHomFromℤ .IsCommRingHom.pres+ = fromℤ-pres-+
 isHomFromℤ .IsCommRingHom.pres· = fromℤ-pres-·
 isHomFromℤ .IsCommRingHom.pres- = fromℤ-pres-minus

 open EqualityToNormalform ℤCommRing discreteℤ ring (fromℤ , isHomFromℤ) public
